
//
// Conversion utility for cvs to git migration.
//
// 2009-10-02 Henrik Grubbström
//

//! Fuzz in seconds (5 minutes).
constant FUZZ = 5*60;

class RCSFile
{
  inherit Parser.RCS;

  //! Mapping from branch revision (a.b.c) to the most recent commit on
  //! the branch.
  mapping(string:string) branch_heads = ([]);

  //! Find the heads of all branches, and reverse the linkage
  //! so that it is consistent with the trunk.
  void find_branch_heads()
  {
    foreach(branches; string branch_rev; string name) {
      string branch_point = (branch_rev/".")[..<1] * ".";
      Revision rev = revisions[branch_point];
      if (!rev) {
	werror("%s: Failed to find branch point for branch %s:%s (%s)\n",
	       rcs_file_name, name, branch_rev, branch_point);
	continue;
      }
      foreach(rev->branches, string br) {
	if (has_prefix(br, branch_rev + ".")) {
	  // Typically branch_rev + ".1".
	  rev->branches -= ({ br });
	  do {
	    rev = revisions[br];
	    branch_point = br;
	    br = rev->next;
	  } while (br);
	  break;
	}
      }
      branch_heads[branch_rev] = branch_point;
    }
  }

  void tag_revisions()
  {
    foreach(tags; string tag; string tag_rev) {
      if (branches[tag_rev] || symbol_is_branch(tag_rev)) continue;
      Revision rev = revisions[tag_rev];
      if (!rev) {
	werror("%s: Failed to find revision %s for tag %s\n",
	       rcs_file_name, tag_rev, tag);
	werror("%s: branches: %O\n", rcs_file_name, branches);
	continue;
      }
      rev->tags[tag] = 1;
    }
  }

  void create(string rcs_file, string data)
  {
    ::create(rcs_file, data);

    find_branch_heads();

    tag_revisions();
  }

  class Revision
  {
    inherit RCS::Revision;

    multiset(string) tags = (<>);
  }
}

//! Mapping from path to rcs file.
mapping(string:RCSFile) rcs_files = ([]);

//! Mapping from tag to path.
mapping(string:multiset(string)) tagged_files = ([]);

void read_rcs_file(string rcs_file, string path)
{
  string data = Stdio.read_bytes(rcs_file);
  RCSFile rcs = rcs_files[path] = RCSFile(rcs_file, data);
  foreach(rcs->tags; string tag;) {
    if (tagged_files[tag]) {
      tagged_files[tag][path] = 1;
    } else {
      tagged_files[tag] = (< path >);
    }
  }

  // Set up an RCS work directory.
  string destdir = "work/" + dirname(path) + "/RCS";
  Stdio.mkdirhier(destdir);
  Stdio.cp(rcs_file, destdir + "/" + basename(path));
}

void read_repository(string repository, string|void path)
{
  foreach(sort(get_dir(repository)), string fname) {
    string fpath = repository + "/" + fname;
    string subpath = path;
    if (Stdio.is_dir(fpath)) {
      if (fname != "Attic") {
	if (subpath)
	  subpath += "/" + fname;
	else
	  subpath = fname;
      }
      read_repository(fpath, subpath);
    } else if (has_suffix(fname, ",v")) {
      if (subpath)
	subpath += "/" + fname[..sizeof(fname)-3];
      else
	subpath = fname[..sizeof(fname)-3];
      read_rcs_file(fpath, subpath);
    } else {
      werror("Warning: Skipping %s.\n", fpath);
    }
  }
}

class GitRepository
{

  //! Heap that only allows one element of each value.
  protected class PushOnceHeap
  {
    inherit ADT.Heap;

    protected mapping(mixed:int) pushed_elements = ([]);

    void push(mixed value)
    {
      if (!pushed_elements[value]) {
	pushed_elements[value] = 1;
	::push(value);
      } else {
	adjust(value);
      }
    }

    mixed pop()
    {
      mixed ret = ::pop();
      m_delete(pushed_elements, ret);
      return ret;
    }

    void remove(mixed value)
    {
      if (pushed_elements[value]) {
	int pos = search(values, value);
	if (pos < 0) error("Inconsistent heap!\n");
	values[pos] = values[--num_values];
	values[num_values] = 0;
	if (pos < num_values) {
	  adjust_down(pos);
	}
      }
    }
  }

  protected PushOnceHeap dirty_commits;

  string master_branch = "master";

  mapping(string:GitCommit) git_commits = ([]);
  mapping(string:GitCommit) dead_commits = ([]);

  mapping(string:GitCommit) git_refs = ([]);

  class GitCommit
  {
    string git_id;
    string uuid;
    string message;
    int timestamp = 0x7ffffffe;
    int timestamp_low = 0x7ffffffe;
    string author;
    string committer;
    mapping(string:int) parents = ([]);
    mapping(string:int) children = ([]);
    mapping(string:int) leaves = ([]);

    //! Known set of successors (ie partial set).
    mapping(string:int) successors = ([]);

    //! Mapping from path to rcs revision for files contained
    //! in this commit (delta against parent(s)).
    mapping(string:string) revisions = ([]);

    //! Mapping from path to rcs revision for files contained
    //! in this commit (full set including files from predecessors).
    mapping(string:string) full_revision_set;

    // Double purpose; indicates dead commit, and contains the
    // set of leaves that may NOT be reattached during resurrection.
    mapping(string:int) dead_leaves;

    mapping(string:int) is_leaf;

    int trace_mode;

    static void create(string path, string|RCSFile.Revision|void rev)
    {
      if (rev) {
	if (stringp(rev)) {
	  revisions[path] = rev;
	  uuid = path + ":" + rev;
	} else {
	  revisions[path] = rev->revision;
	  uuid = path + ":" + rev->revision;
	  author = committer = rev->author;
	  message = rev->log;
	  timestamp = timestamp_low = rev->time->unix_time();
	  if (rev->state == "dead") {
	    dead_leaves = ([]);
	    dead_commits[uuid] = this_object();
	    revisions[path] = 0;	// For easier handling later on.
	  }
	}
      } else {
	uuid = path + ":";
	leaves[uuid] = 1;
	is_leaf = ([ uuid: 1 ]);
      }
      git_commits[uuid] = this_object();

      if (0 && (uuid == ".cvsignore:1.5")) {
	werror("Enabling tracing for %O.\n", this_object());
	trace_mode = 1;
      }
    }

    static string _sprintf(int c, mixed|void x)
    {
      return sprintf("GitCommit(%O /* %d/%d/%d p/c/l */)",
		     uuid, sizeof(parents), sizeof(children),
		     sizeof(leaves));
    }

    // Note: `< and `> are defined so that the newest will be sorted first.
    int `<(mixed x)
    {
      return -timestamp < x;
    }

    int `>(mixed x)
    {
      return -timestamp > x;
    }

    void propagate_leaves(mapping(string:int) leaves,
			  mapping(string:int) successor_set)
    {
      mapping(string:int) new_leaves = leaves - this_program::leaves;
      if (trace_mode) {
	werror("Adding %O as successors to %O\n",
	       indices(successor_set - successors), this_object());
      }
      successors |= successor_set;
      if (sizeof(new_leaves)) {
	this_program::leaves |= new_leaves;
	if (dirty_commits) {
	  // Unification code is active.
	  map(map(indices(children), git_commits), dirty_commits->push);
	}
	map(indices(parents), git_commits)->
	  propagate_leaves(new_leaves, successors);
      }
    }

    //! Detach a parent from this commit.
    void detach_parent(GitCommit parent)
    {
      m_delete(parent->children, uuid);
      m_delete(parents, parent->uuid);
    }

    //! Add a parent for this commit.
    void hook_parent(GitCommit parent)
    {
      parents[parent->uuid] = 1;
      parent->children[uuid] = 1;
      parent->successors[uuid] = 1;
      parent->propagate_leaves(leaves, successors);
    }

    // Assumes same leaves, author and commit message.
    //
    //                    Before                  After
    //
    //              +-+ +-+   +-+ +-+       +-+ +-+  +-+ +-+
    //    Parents:  | | | |   | | | |       | | | |  | | | |
    //              +-+ +-+   +-+ +-+       +-+ +-+  +-+ +-+
    //                \ /       \ /            \ \    / /
    //               +----+     +-+             +------+     +-+
    //               |this|     |c|    ==>      | this |     |c|
    //               +----+     +-+             +------+     +-+
    //                |  \     / |               /  |		\
    //               +-+  +---+ +-+           +-+ +---+  +-+
    //    Children:  | |  |   | | |           | | |   |  | |
    //               +-+  +---+ +-+           +-+ +---+  +-+
    //
    void merge(GitCommit c)
    {
      if (timestamp < c->timestamp) timestamp = c->timestamp;
      if (timestamp_low > c->timestamp_low) timestamp_low = c->timestamp_low;

      if (message != c->message) {
	error("Different messages: %O != %O\n", message, c->message);
      }

      if (author != c->author) {
	error("Different messages: %O != %O\n", author, c->author);
      }

      if (!equal(leaves, c->leaves)) {
	error("Different sets of leaves: %O != %O\n", leaves, c->leaves);
      }

      if (trace_mode || c->trace_mode) {
	werror("Adopting children from %s to %s...\n",
	       pretty_git(c, 1), pretty_git(this_object(), 1));
      }

      // Adopt c's children.
      foreach(c->children; string c_uuid;) {
	GitCommit cc = git_commits[c_uuid];

	if (!cc) {
	  error("Missing child to %s\n%s\n",
		pretty_git(c), pretty_git(c_uuid));
	}

	if (cc->trace_mode) {
	  werror("Detaching child %O from %O during merge of %O to %O\n",
		 cc, c, this_object(), c);
	}

	cc->detach_parent(c);
	cc->hook_parent(this);
	if (cc->timestamp < timestamp) {
	  if (cc->timestamp + FUZZ < timestamp) {
	    error("Parent: %s\n Child: %s\n",
		  pretty_git(this), pretty_git(c_uuid));
	  } else {
	    // Fudge the timestamp for the child.
	    // FIXME: Ought to propagate...
	    cc->timestamp = timestamp;
	  }
	}
      }

      if (trace_mode || c->trace_mode) {
	werror("Stealing parents from %s to %s...\n",
	       pretty_git(c, 1), pretty_git(this_object(), 1));
      }

      // And from its parents, and hook us to them.
      foreach(c->parents; string p_uuid;) {
	GitCommit p = git_commits[p_uuid];

	if (p->trace_mode) {
	  werror("Detaching parent %O from %O during merge of %O to %O\n",
		 p, c, this_object(), c);
	}

	c->detach_parent(p);
	hook_parent(p);
	if (p->timestamp > timestamp) {
	  if (p->timestamp - FUZZ > timestamp) {
	    error("Parent: %s\n Child: %s\n",
		  pretty_git(p), pretty_git(this));
	  } else {
	    // Fudge the timestamp for the child.
	    // FIXME: Ought to propagate...
	    timestamp = p->timestamp;
	  }
	}
      }

      if (trace_mode || c->trace_mode) {
	werror("Stealing the rest from %s to %s...\n",
	       pretty_git(c, 1), pretty_git(this_object(), 1));
      }

      revisions += c->revisions;

      if (trace_mode || c->trace_mode) {
	werror("Adding %O as successors to %O\n",
	       indices(c->successors - successors), c);
      }
      successors |= c->successors;

      trace_mode |= c->trace_mode;

      if (c->is_leaf) {
	is_leaf = is_leaf?(is_leaf + c->is_leaf):c->is_leaf;
	foreach(git_refs; string ref; GitCommit r) {
	  if (r == c) {
	    git_refs[ref] = this_object();
	  }
	}
      }

      if (dead_leaves && c->dead_leaves) {
	dead_leaves |= c->dead_leaves;
      } else {
	dead_leaves = UNDEFINED;
	m_delete(dead_commits, uuid);
      }
    }

    void generate()
    {
      if (git_id) return;	// Already done.

      // First ensure that our parents are generated.
      array(GitCommit) git_parents = map(indices(parents), git_commits);
      git_parents->generate();
#if 0
      // Check out the files that we need in our tree.
      foreach(revisions; string path; string rev) {
	cmd("co", "-f", "-r"+rev, path);
	cmd("git", "add", path);
      }
      string treeid = cmd("git", "write-tree");
#endif
      git_id = "FAKE";
    }
  }

#define TRACE_MSG(GC1, GC2, MSG ...) do {	\
    if (((GC1) && ((GC1)->trace_mode)) ||	\
	((GC2) && ((GC2)->trace_mode))) {	\
      werror(MSG);				\
    }						\
  } while(0)

  void init_git_branch(string path, string tag, string branch_rev,
		       string rcs_rev, RCSFile rcs_file,
		       mapping(string:GitCommit) rcs_commits)
  {
    GitCommit prev_commit;
    //werror("initing branch: %O %O %O %O\n", path, tag, branch_rev, rcs_rev);
    if (!(prev_commit = git_refs[tag])) {
      prev_commit = git_refs[tag] = GitCommit(tag);
    }
    //werror("L:%O\n", prev_commit);
    if (branch_rev) {
      GitCommit commit = rcs_commits[branch_rev];
      if (commit) {
	prev_commit->hook_parent(commit);
	return;
      }
      commit = rcs_commits[branch_rev] = GitCommit(path, branch_rev);
      prev_commit->hook_parent(commit);
      prev_commit = commit;
      //werror("B:%O (%O:%O)\n", prev_commit, path, branch_rev);
    }
    while (rcs_rev) {
      RCSFile.Revision rev = rcs_file->revisions[rcs_rev];
      GitCommit commit = rcs_commits[rcs_rev];
      if (commit) {
	//werror("E:%O (%O:%O)\n", commit, path, rcs_rev);
	prev_commit->hook_parent(commit);
	break;
      }

      commit = rcs_commits[rcs_rev] = GitCommit(path, rev);
      //werror("N:%O (%O:%O)\n", commit, path, rcs_rev);
      prev_commit->hook_parent(commit);
      prev_commit = commit;
      rcs_rev = rev->ancestor;
    }
    //werror("\n");
#ifdef GIT_VERIFY
    verify_git_commits();
#endif
  }

  string pretty_git(string|GitCommit c_uuid, int|void skip_leaves)
  {
    GitCommit c = objectp(c_uuid)?c_uuid:git_commits[c_uuid];
    if (!c) { return sprintf("InvalidCommit(%O)", c_uuid); }
    return sprintf("GitCommit(%O /* %s%s */\n"
		   "/* Parents: %{%O, %}\n"
		   "   Children: %{%O, %}\n"
		   "   Leaves: %{%O, %}\n"
		   "   Revisions: %O\n"
		   "*/)",
		   c->uuid, c->dead_leaves?"DEAD ":"", ctime(c->timestamp) - "\n",
		   indices(c->parents), indices(c->children),
		   (skip_leaves?({sizeof(c->leaves)}):indices(c->leaves)),
		   c->revisions);
  }

  static void verify_git_loop(GitCommit r, mapping(string:int) state)
  {
    if (state[r->uuid] == 2)
      error("Loop detected involving %O\n"
	    "  %{%s\n%}", r->uuid,
	    map(filter(indices(state),
		       lambda(string uuid, mapping(string:int) state) {
			 return state[uuid] == 2;
		       }, state), pretty_git));
    else if (state[r->uuid]) return; // Already checked.
    state[r->uuid] = 2;
    foreach(r->parents; string uuid;) {
      verify_git_loop(git_commits[uuid], state);
    }
    state[r->uuid] = 1;
  }

  void verify_git_commits(int|void ignore_leaves)
  {
    //#ifdef GIT_VERIFY
    //werror("Verifying...");
    foreach(git_commits; string uuid; GitCommit c) {
      if (!c) error("Destructed commit %O in git_commits.\n", uuid);
      if (c->uuid != uuid) error("Invalid uuid %O != %O.\n%s\n",
				 uuid, c->uuid, pretty_git(c));
      foreach(c->parents; string p_uuid;) {
	GitCommit p = git_commits[p_uuid];
	if (!p) error("Invalid parent %O for commit %O\n"
		      "Commit: %s\n"
		      "Parent:%s\n", p_uuid, uuid,
		      pretty_git(uuid), pretty_git(p_uuid));
	if (!p->children[uuid])
	  error("Parent %O is missing child %O.\n", p_uuid, uuid);
	if (sizeof(p->leaves & c->leaves) != sizeof(c->leaves)) {
	  error("Parent %O is missing leaves from child %O:\n"
		"%O is not a subset of %O\n"
		"Commit: %s\n"
		"Parent: %s\n",
		p_uuid, uuid, c->leaves, p->leaves,
		pretty_git(c), pretty_git(p));
	}
	if (p->timestamp > c->timestamp + FUZZ)
	  error("Parent %O is more recent than %O.\n"
		"Parent: %s\n"
		"Child: %s",
		p_uuid, uuid,
		pretty_git(p), pretty_git(c));
      }

      mapping(string:int) leaves = ([]);
      if (c->is_leaf) {
	// Node is a leaf.
	leaves = c->is_leaf + ([]);
      }
      foreach(c->children; string p_uuid;) {
	GitCommit p = git_commits[p_uuid];
	if (!p) error("Invalid child %O for commit %O\n", p_uuid, uuid);
	if (!p->parents[uuid])
	  error("Child %O is missing parent %O.\n", p_uuid, uuid);
	if (sizeof(p->leaves & c->leaves) != sizeof(p->leaves)) {
	  error("Child %O is missing leaves from parent %O:\n"
		"%O is not a subset of %O\n"
		"Child: %s\n"
		"Parent: %s",
		p_uuid, uuid, p->leaves, c->leaves,
		pretty_git(p), pretty_git(c));
	}
	if (p->timestamp + FUZZ < c->timestamp)
	  error("Child %O is older than %O.\n"
		"Child: %s\n"
		"Parent: %s\n",
		p_uuid, uuid,
		pretty_git(p), pretty_git(c));
	leaves |= p->leaves;
      }
      if (!ignore_leaves && !equal(leaves, c->leaves))
	error("The set of leaves for %O is invalid.\n"
	      "Got %O, expected %O.\n"
	      "%s\n",
	      uuid, c->leaves, leaves, pretty_git(c));
    }

    // Check that the successor sets are valid.
    array(GitCommit) gcs = git_sort(values(git_commits));
    // First clean out any uuids that don't exist anymore.
    foreach(gcs, GitCommit c) {
      foreach(indices(c->successors), string uuid) {
	if (!git_commits[uuid]) {
	  m_delete(c->successors, uuid);
	}
      }
    }
    foreach(gcs, GitCommit c) {
      ADT.Stack to_check = ADT.Stack();
      to_check->push(0);	// End sentinel.
      to_check->push(c);
      mapping(string:int) successors = c->successors - c->children;
      GitCommit tmp;
      while (sizeof(successors) && (tmp = to_check->pop())) {
	foreach(map(indices(tmp->children), git_commits), GitCommit cc) {
	  successors -= cc->successors;
	  to_check->push(cc);
	}
      }
      if (sizeof(successors)) {
	error("Invalid successors for %O.\n"
	      "Got: %O\n"
	      "Lost: %O\n"
	      "Node: %s\n",
	      c, c->successors, successors, pretty_git(c, 1));
      }
    }

#ifdef GIT_VERIFY
    // Detect loops.
    mapping(string:int) state = ([]);	// 0: Unknown, 1: Ok, 2: Loop.
    foreach(git_commits; string uuid; GitCommit c) {
      if (state[uuid]) continue; // Already checked.
      verify_git_loop(c, state);
    }
#endif

    //werror(" OK\n");
  }

  void fix_git_ts(GitCommit r)
  {
    int ts = -0x7fffffff;
    foreach(r->parents; string p_uuid;) {
      GitCommit p = git_commits[p_uuid];
      if (p->timestamp == 0x7ffffffe) fix_git_ts(p);
      if (ts < p->timestamp) ts = p->timestamp;
    }

    // Make sure we have some margin...
    r->timestamp = r->timestamp = ts + FUZZ*16;
  }

  void add_rcs_file(string path, RCSFile rcs_file)
  {
    mapping(string:GitCommit) rcs_commits = ([]);

    init_git_branch(path, "heads/" + master_branch, UNDEFINED,
		    rcs_file->head, rcs_file, rcs_commits);
    foreach(rcs_file->tags; string tag; string tag_rev) {
      if (rcs_file->symbol_is_branch(tag_rev)) {
	tag_rev = (tag_rev/"." - ({"0"})) * ".";
      }
      string rcs_rev;
      if ((rcs_rev = rcs_file->branch_heads[tag_rev])) {
	init_git_branch(path, "heads/cvs/" + tag, tag_rev,
			rcs_rev, rcs_file, rcs_commits);
      } else {
	init_git_branch(path, "tags/cvs/" + tag, UNDEFINED,
			tag_rev, rcs_file, rcs_commits);
      }
    }

    // FIXME: Identify merges.
  }

  void init_git_commits()
  {
    werror("Initializing Git commmit tree from RCS...\n");
    foreach(rcs_files; string path; RCSFile rcs_file) {
      werror("\r%-75s", path);
      add_rcs_file(path, rcs_file);
    }
    werror("\r%-75s\n", "");

    foreach(git_refs;; GitCommit r) {
      // Fix the timestamp for the ref.
      fix_git_ts(r);
    }

    // Collect the dead leaves, they have collected at the root commit
    // for each RCS file.
    foreach(dead_commits;; GitCommit dead) {
      GitCommit p = dead;
      while (sizeof(p->parents)) {
	// We know that there can at most be a single parent
	// at this stage, since RCS doesn't allow for more.
	p = git_commits[indices(p->parents)[0]];
	p->successors[dead->uuid] = 1; // Since it's cheap to do here.
      }
      dead->dead_leaves = p->leaves - dead->leaves;
    }
 
    verify_git_commits();
  }

  static void low_unify_git_commits()
  {
    while (sizeof(dirty_commits)) {
      GitCommit child = dirty_commits->pop();

      werror("\r%d(%d):                  ",
	     sizeof(dirty_commits), sizeof(git_commits));

      if (sizeof(child->parents) < 2) continue;

      array(GitCommit) sorted_parents =
	git_sort(map(indices(child->parents), git_commits));

      int cnt;
      // Attempt to reduce the number of parents by merging or sequencing them.
      // Note: O(n²) or more!
      for (int i = 0; i < sizeof(sorted_parents); i++) {
	// Foreach of the parents attempt to push it down as a parent to
	// its older spouses (recursively).
	GitCommit p = sorted_parents[i];
	if (!p) continue;	// Already handled.

	if (p->trace_mode || child->trace_mode) {
	  verify_git_commits();
	}
	TRACE_MSG(child, p, "Detaching %O from %O.\n", p, child);

	child->detach_parent(p);
	sorted_parents[i] = 0;
	int found;
	if (!(cnt--)) {
	  cnt = 9;	// Write every 10th loop.
	  werror("\r%d(%d):%d  ",
		 sizeof(dirty_commits), sizeof(git_commits),
		 sizeof(sorted_parents) - i);
	}
	for (int j = sizeof(sorted_parents); j--;) {
	  GitCommit spouse = sorted_parents[j];
	  if (!spouse) continue;	// Already handled.
	  if (spouse->timestamp + FUZZ < p->timestamp) break;
	  if (p->successors[spouse->uuid]) {
	    // We're already present somewhere in the parents of spouse.
	    TRACE_MSG(p, spouse, "%O is already a parent to %O.\n", p, spouse);
	    found |= 1;
	    continue;
	  } else if (p->parents[spouse->uuid]) {
	    // We may not reparent our parents...
	    TRACE_MSG(p, spouse, "%O is a parent to %O.\n", spouse, p);
	    continue;
	  }
	  mapping(string:int) common_leaves = p->leaves & spouse->leaves;
	  if (sizeof(common_leaves) != sizeof(spouse->leaves)) {
	    // The spouse has leaves we don't.
	    if (p->dead_leaves) {
	      // Dead commit. Attempt to resurrect...
	      common_leaves = p->dead_leaves & spouse->leaves;
	      if (sizeof(common_leaves)) {
		// The spouse has conflicting leaves.
		continue;
	      }
	      // Let the code below reattach the missing leaves.
	    } else {
	      // Spouse is incompatible.
	      // Nothing to see here -- go away.
	      continue;
	    }
	  } else {
	    // Spouse doesn't have any leaves that we don't.
	    // So we should be able to find somewhere to reparent
	    // or merge.

	    do {
	      // Accellerator for common cases.
	      if (p->successors[spouse->uuid]) {
		break;
	      } else if (sizeof(spouse->parents) &&
			 (sizeof(spouse->parents) == 1) &&
			 (spouse->timestamp > p->timestamp + FUZZ)) {
		GitCommit inlaw = git_commits[indices(spouse->parents)[0]];
		if (inlaw->timestamp + FUZZ < p->timestamp) {
		  // Inlaw is older than us.
		  break;
		}
		if (sizeof(inlaw->children) > 1) {
		  mapping(string:int) inlaw_leaves = inlaw->leaves & p->leaves;
		  if (sizeof(inlaw_leaves) != sizeof(inlaw->leaves)) break;
		}
		if (p->parents[inlaw->uuid]) break;
#if 0
		// There seems to be a problem with the successor handling
		// in this code.
		if (p->timestamp < spouse->timestamp) {
		  // We're certain to either merge or hook.
		  if (p->trace_mode || spouse->trace_mode) {
		    werror("Registering %O as a successor to %O\n",
			   spouse, p);
		  }
		  p->successors |= inlaw->successors;
		}
#endif
		spouse = inlaw;
	      } else break;
	    } while (1);
	  }

	  // The spouse is compatible.

	  if (p->successors[spouse->uuid] || (p == spouse)) {
	    TRACE_MSG(p, spouse, "%O is already a parent to %O (2).\n", p, spouse);
	    found |= 1;
	    continue;
	  } else if (p->parents[spouse->uuid]) {
	    TRACE_MSG(p, spouse, "%O is a parent to %O (2).\n", spouse, p);
	    continue;
	  }
	  if ((spouse->timestamp < p->timestamp + FUZZ) &&
	      (sizeof(p->leaves) == sizeof(common_leaves)) &&
	      (p->message == spouse->message) &&
	      (p->author == spouse->author)) {
	    // Spouse in merge interval and merge ok.
	    TRACE_MSG(p, spouse, "Merge %O and %O.\n", p, spouse);
	    p->merge(spouse);
	    dirty_commits->remove(spouse);
	    dirty_commits->push(p);
	    m_delete(git_commits, spouse->uuid);
	    m_delete(dead_commits, spouse->uuid);
	    destruct(spouse);
	    found |= 2;
	  } else if (p->timestamp < spouse->timestamp) {
	    // Spouse not valid for merge, but we still can be parent.
	    TRACE_MSG(p, spouse, "Hook %O as a parent to %O.\n", p, spouse);
	    spouse->hook_parent(p);
	    dirty_commits->push(spouse);
	    found |= 1;
	  }
	}
	if (found != 1) {
	  // We either didn't find a place for p among its spouses,
	  // or we've performed a merge, so we can't be sure that
	  // the link to child is intact.
	  // Restore p as a parent to child.
	  TRACE_MSG(p, child, "Rehook %O as a parent to %O.\n", p, child);
	  child->hook_parent(p);
	  sorted_parents[i] = p;
	  if (found & 2) {
	    // Force a rescan of child.
	    dirty_commits->push(child);
	  }
	} else if (!sizeof(p->children)) {
	  error("Parent claimed to be found, but no children!\n"
		"%s\n", pretty_git(p, 1));
	}
	if (1 || p->trace_mode || child->trace_mode) {
	  verify_git_commits();
	}
      }

      // verify_git_commits();

    }
    werror("\b ");

#if 0
    array(GitCommit) sorted_commits = git_sort(values(git_commits));
    foreach(sorted_commits, GitCommit c) {
      werror("%s\n\n", pretty_git(c));
    }
#endif /* 0 */

    verify_git_commits();
  }

  // Attempt to unify as many commits as possible given
  // the following invariants:
  //
  //   * The set of reachable leaves from a commit containing a revision.
  //   * The commit order must be maintained (ie a node may not reparent
  //     one of its parents).
  void unify_git_commits()
  {
    // First attempt to reduce the number of ref nodes.
    werror("Unifying the references...\n");
    array(GitCommit) sorted_refs = git_sort(values(git_refs));
    for(int i = sizeof(sorted_refs); i--;) {
      GitCommit r = sorted_refs[i];
      if (!r) continue;
      GitCommit best_parent;
      for(int j = i; j--;) {
	GitCommit c = sorted_refs[j];
	if (!c) continue;

	mapping(string:int) common_parents = r->parents & c->parents;
	if (!sizeof(common_parents)) continue;
	if (sizeof(c->parents) == sizeof(common_parents)) {
	  if (!best_parent ||
	      (sizeof(c->parents) > sizeof(best_parent->parents)))
	    best_parent = c;
	}
      }
      if (best_parent) {
	foreach(best_parent->parents; string p_uuid; ) {
	  r->detach_parent(git_commits[p_uuid]);
	}
	r->hook_parent(best_parent);
      }
    }

    verify_git_commits();

    dirty_commits = PushOnceHeap();

    werror("Quick'n dirty unification pass...\n");
    array(GitCommit) sorted_commits = git_sort(values(git_commits));
    for (int i = 0; i < sizeof(sorted_commits);) {
      GitCommit prev = sorted_commits[i];
      mapping(string:array(GitCommit)) partitioned_commits = ([]);
      for(; i < sizeof(sorted_commits); i++) {
	GitCommit tmp = sorted_commits[i];
	if (tmp->timestamp > prev->timestamp + FUZZ) break;
	string key = sort(indices(tmp->leaves)) * "\0";
	if (partitioned_commits[key]) {
	  partitioned_commits[key] += ({ tmp });
	} else {
	  partitioned_commits[key] += ({ tmp });
	}
	prev = tmp;
      }
      foreach(partitioned_commits;; array(GitCommit) partition) {
	prev = partition[0];
	int ok = 1;
	foreach(partition, GitCommit tmp) {
	  if ((tmp->message != prev->message) ||
	      (tmp->author != prev->author)) {
	    ok = 0;
	    break;
	  }
	}
	if (ok && (sizeof(partition) > 1)) {
	  foreach(partition[1..], GitCommit tmp) {
	    TRACE_MSG(prev, tmp, "Merging %O and %O\n", prev, tmp);
	    prev->merge(tmp);
	    m_delete(git_commits, tmp->uuid);
	    m_delete(dead_commits, tmp->uuid);
	  }
	  dirty_commits->push(prev);
	  if (prev->trace_mode) {
	    verify_git_commits();
	  }
	}
      }
    }

    verify_git_commits();

    werror("Unifying the commits...\n");
    foreach(git_refs; ; GitCommit r) {
      if (sizeof(r->parents) > 1) {
	dirty_commits->push(r);
      }
    }
    low_unify_git_commits();

#if 0
    werror("\n\nResurrecting the dead...\n");
    // CVS doesn't tag dead revisions, so we need to identify the probable tags.
    while (sizeof(dead_commits)) {
      // Heuristic: Check if we have a compatible younger spouse
      //            that has leaves we don't.
      foreach(dead_commits; string d_uuid; GitCommit dead) {
	int glue_applied;
	foreach(map(indices(dead->children), git_commits), GitCommit c) {
	  array(GitCommit) spouses =
	    git_sort(map(indices(c->parents), git_commits));
	  mapping(string:int) fallen_leaves = ([]);

	  for(int i = sizeof(spouses);
	      i-- && spouses[i]->timestamp >= dead->timestamp;) {
	    GitCommit spouse = spouses[i];
	    if (spouse == dead) continue;
	    c->detach_parent(dead);
	    spouse->hook_parent(dead);
	    dirty_commits->push(spouse);
	    glue_applied = 1;
	    break;
	  }
	  if (glue_applied) break;
	}
	if (glue_applied) {
	  verify_git_commits();
	}
      }
      if (!sizeof(dirty_commits)) break; // Nothing happened.
      low_unify_git_commits();
    }
#endif /* 0 */

    // Perform a full pass to clean up in case we missed anything.
    werror("\n\nFinal cleanup...\n");
    foreach(git_commits; ; GitCommit r) {
      if (sizeof(r->parents) > 1) {
	dirty_commits->push(r);
      }
    }
    low_unify_git_commits();

    werror("\n\n");
  }

  void generate(string workdir)
  {
#if 0
    cd(workdir);

    cmd("git", "init");

    foreach(git_commits; string uuid; GitCommit c) {
      c->generate();
    }
#endif
  }

  //! Returns a canonically sorted array of commits in time order.
  array(GitCommit) git_sort(array(GitCommit) commits)
  {
    sort(commits->uuid, commits);
    sort(commits->timestamp, commits);
    return commits;
  }
}

void parse_config(string config)
{
}

int main(int argc, array(string) argv)
{
  string repository;
  string config;

  GitRepository git = GitRepository();

  foreach(Getopt.find_all_options(argv, ({
	   ({ "help",       Getopt.NO_ARG,  ({ "-h", "--help" }), 0, 0 }),
	   ({ "branch",     Getopt.HAS_ARG, ({ "-b" }), 0, 0 }),
	   ({ "repository", Getopt.HAS_ARG, ({ "-d" }), 0, 0 }),
				  })),
	  [string arg, string val]) {
    switch(arg) {
    case "help":
      write("%s [-d repository] [-h|--help]\n", argv[0]);
      exit(0);
    case "branch":
      git->master_branch = argv[0];
      break;
    case "repository":
      repository = val;
      break;
    default:
      werror("Unsupported option: %O:%O\n", arg, val);
      exit(1);
    }
  }

  if (!config && Stdio.is_file(".pcvs2git.rc")) {
    config = ".pcvs2git.rc";
  }
  if (config) {
    parse_config(config);
  }

  read_repository(repository);

  // werror("Repository: %O\n", rcs_files);
  // werror("Tagged_files: %O\n", tagged_files);

  // FIXME: Filter here.

  git->init_git_commits();

  werror("Git refs: %O\n", git->git_refs);

  // Unify commits.
  git->unify_git_commits();

  werror("Git refs: %O\n", git->git_refs);

  GitRepository.GitCommit c = git->git_refs["heads/" + git->master_branch];

  array(GitRepository.GitCommit) ccs =
    map(indices(c->parents), git->git_commits);
  sort(ccs->timestamp, ccs);
  foreach(reverse(ccs); int i; GitRepository.GitCommit cc) {
    werror("\n%d:%s\n", i, git->pretty_git(cc));
    foreach(sort(indices(cc->children)); int j; string c_uuid) {
      werror("%d:%d:%s\n", i, j, git->pretty_git(c_uuid));
    }
  }

  werror("\nRoots:\n");
  ccs = values(git->git_commits);
  sort(ccs->timestamp, ccs);  
  foreach(reverse(ccs), GitRepository.GitCommit cc) {
    if (!sizeof(cc->parents)) {
      werror("%s\n", git->pretty_git(cc, 1));
    }
  }

#if 0

  int cnt;

  while(c) {
    cnt++;
    c = sizeof(c->parents) && git_commits[((array)c->parents)[0]];
  }

  werror("Path from head to root: %d commits\n", cnt);
#endif

  // FIXME: Generate a merged history?

  // FIXME: Generate a git repository.

  git->generate("work");

}
