
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
}

void read_repository(string repository, string|void path)
{
  foreach(get_dir(repository), string fname) {
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

int git_uuid;
string new_git_uuid() { return (string)(++git_uuid); }

class GitCommit
{
  string git_id;
  string uuid = new_git_uuid();//Standards.UUID.make_version4()->str();
  string message;
  int timestamp = 0x7ffffffe;
  int timestamp_low = 0x7ffffffe;
  string author;
  string committer;
  mapping(string:int) parents = ([]);
  mapping(string:int) children = ([]);
  mapping(string:int) leaves = ([]);

  //! Mapping from path to rcs revision for files contained
  //! in this commit.
  mapping(string:string) revisions = ([]);

  static void create(string|void path, string|RCSFile.Revision|void rev)
  {
    git_commits[uuid] = this_object();
    if (rev) {
      if (stringp(rev)) {
	revisions[path] = rev;
      } else {
	revisions[path] = rev->revision;
	author = committer = rev->author;
	message = rev->log;
	timestamp = timestamp_low = rev->time->unix_time();
      }
    } else {
      leaves[uuid] = 1;
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

  void propagate_leaves(mapping(string:int) leaves)
  {
    mapping(string:int) new_leaves = leaves - this_program::leaves;
    if (sizeof(new_leaves)) {
      this_program::leaves |= new_leaves;
      map(indices(parents), git_commits)->propagate_leaves(new_leaves);
    }
  }

  //! Add a parent for this commit.
  void hook_parent(GitCommit parent)
  {
    parents[parent->uuid] = 1;
    parent->children[uuid] = 1;
    parent->propagate_leaves(leaves);
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
  //                |  \     / |               /  |  
  //               +-+  +---+ +-+           +-+ +---+      +-+
  //    Children:  | |  |   | | |           | | |   |      | |
  //               +-+  +---+ +-+           +-+ +---+      +-+
  //
  void merge(GitCommit c)
  {
    if (timestamp < c->timestamp) timestamp = c->timestamp;
    if (timestamp_low > c->timestamp_low) timestamp_low = c->timestamp_low;

    if (!equal(leaves, c->leaves)) {
      error("Different sets of leaves: %O != %O\n", leaves, c->leaves);
    }

    // Unhook c from its children.
    foreach(c->children; string c_uuid;) {
      GitCommit cc = git_commits[c_uuid];

      if (c_uuid == "3") {
	werror("D(%s)", c_uuid);
      }
      m_delete(cc->parents, c->uuid);
      m_delete(c->children, c_uuid);
    }

    // And from its parents, and hook us to them.
    foreach(c->parents; string p_uuid;) {
      GitCommit p = git_commits[p_uuid];

      if (uuid == "3") {
	werror("A(%s)", p_uuid);
      }
      m_delete(p->children, c->uuid);
      m_delete(c->parents, p_uuid);
      p->children[uuid] = 1;
      parents[p_uuid] = 1;
    }

    revisions += c->revisions;
  }
}

string master_branch = "master";

mapping(string:GitCommit) git_commits = ([]);

mapping(string:GitCommit) git_refs = ([]);

void init_git_branch(string path, string tag, string branch_rev,
		     string rcs_rev, RCSFile rcs_file,
		     mapping(string:GitCommit) rcs_commits)
{
  GitCommit prev_commit;
  //werror("initing branch: %O %O %O %O\n", path, tag, branch_rev, rcs_rev);
  if (!(prev_commit = git_refs[tag])) {
    prev_commit = git_refs[tag] = GitCommit();
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
  verify_git_commits();
}

string pretty_git(string|GitCommit c_uuid)
{
  GitCommit c = objectp(c_uuid)?c_uuid:git_commits[c_uuid];
  if (!c) { return sprintf("InvalidCommit(%O)", c_uuid); }
  return sprintf("GitCommit(%O /* %s */\n"
		 "/* Parents: %{%O, %}\n"
		 "   Children: %{%O, %}\n"
		 "   Leaves: %{%O, %}\n"
		 "   Revisions: %O\n"
		 "*/)",
		 c->uuid, ctime(c->timestamp) - "\n",
		 indices(c->parents), indices(c->children),
		 indices(c->leaves), c->revisions);
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
#ifdef GIT_VERIFY
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
	      p_uuid, uuid, c->leaves, p->leaves, pretty_git(c), pretty_git(p));
      }
      if (p->timestamp > c->timestamp)
	error("Parent %O is more recent than %O.\n"
	      "Parent: %s\n"
	      "Child: %s",
	      p_uuid, uuid,
	      pretty_git(p), pretty_git(c));
    }

    mapping(string:int) leaves = ([]);
    if (!sizeof(c->children)) {
      // Node is a leaf.
      leaves[uuid] = 1;
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
      if (p->timestamp < c->timestamp)
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

  // Detect loops.
  mapping(string:int) state = ([]);	// 0: Unknown, 1: Ok, 2: Loop.
  foreach(git_commits; string uuid; GitCommit c) {
    if (state[uuid]) continue; // Already checked.
    verify_git_loop(c, state);
  }
#endif
}

void fix_git_ts(GitCommit r)
{
  int ts = -0x7fffffff;
  foreach(r->parents; string p_uuid;) {
    GitCommit p = git_commits[p_uuid];
    if (p->timestamp == 0x7ffffffe) fix_git_ts(p);
    if (ts < p->timestamp) ts = p->timestamp;
  }
  r->timestamp = r->timestamp = ts + FUZZ;
}

void init_git_commits()
{
  foreach(rcs_files; string path; RCSFile rcs_file) {
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

  foreach(git_refs;; GitCommit r) {
    // Fix the timestamp for the ref.
    fix_git_ts(r);
  }

  verify_git_commits();
}

// Attempt to unify as many commits as possible given the following invariants:
//
//   * The set of reachable leaves from a commit containing a revision.
//   * The commit order must be maintained.
void unify_git_commits()
{
  ADT.Heap commits = ADT.Heap();
  mapping(string:int) pushed_commits = ([]);
  foreach(git_refs; ; GitCommit r) {
    if (sizeof(r->parents) > 1) {
      commits->push(r);
      pushed_commits[r->uuid] = 1;
    }
  }
  while (sizeof(commits)) {
    GitCommit child = commits->pop();
    m_delete(pushed_commits, child->uuid);
    werror("\n%d(%d)%s(%d)   ",
	   sizeof(commits), sizeof(git_commits),
	   child->uuid, sizeof(child->parents));

    int trace_on = child->uuid == "3";

    array(GitCommit) sorted_parents = map(indices(child->parents), git_commits);
    sort(sorted_parents->timestamp, sorted_parents);

    // Attempt to reduce the number of parents by merging or sequencing them.
    // Note: O(n²)!
    for (int i = sizeof(sorted_parents); i--;) {
      GitCommit root;
      if (!(root = sorted_parents[i])) continue; // Already handled.
      if (trace_on) {
	werror("<%d>", i);
      }
      for (int j = i; j--;) {
	GitCommit c;
	if (!(c = sorted_parents[j])) continue; // Already handled.
	if (trace_on) {
	  werror(":%d:", j);
	}
	mapping(string:int) common_leaves = root->leaves & c->leaves;
	if (sizeof(common_leaves) != sizeof(root->leaves)) {
	  // Not a superset of the root set.
	  // FIXME: Check if this is a deletion node, in which
	  //        case we will attempt joining it later by
	  //        adding leaves.
	  werror("$");
	  continue;
	}
	// Find the insertion/merge point among the parents of root.
	GitCommit prev = root;
	for (GitCommit p = root; p && (p->timestamp > c->timestamp); ) {
	  if ((sizeof(p->children) > 1) && (p != root)) {
	    // Found a (temporary?) sibling.
	    if (sizeof(common_leaves = (p->leaves & c->leaves)) !=
		sizeof(p->leaves)) {
	      werror("#(%d)", sizeof(p->children));
	      break;
	    }
	  }
	  if (c->timestamp + FUZZ < p->timestamp) {
	    // Not in range of FUZZ (yet).
	    root = p; // Cache.
	  } else if ((sizeof(c->leaves) == sizeof(common_leaves)) &&
		     (p->message == c->message) && (p->author == c->author)) {
	    werror("*");
	    // Unhook c from the work list.
	    sorted_parents[j] = 0;
	    p->merge(c);
	    if (pushed_commits[p->uuid]) {
	      commits->adjust(p);
	    } else if (sizeof(p->parents) > 1) {
	      commits->push(p);
	      pushed_commits[p->uuid] = 1;
	    }
	    if (pushed_commits[c->uuid]) {
	      m_delete(pushed_commits, c->uuid);
	      c->timestamp = 0x7fffffff;
	      commits->adjust(c);
	      if (commits->peek() == c) commits->pop();
	    }
	    m_delete(git_commits, c->uuid);
	    destruct(c);
	    prev = 0;
	    verify_git_commits();
	    break;
	  }
	  prev = p;
	  // Find the most recent parent of p.
	  p = 0;
	  foreach(map(indices(prev->parents), git_commits), GitCommit pp) {
	    if (!p || (p->timestamp < pp->timestamp)) p = pp;
	  }
	}
	if (prev) {
	  // Unhook c from the work list.
	  sorted_parents[j] = 0;
	  
	  // Unhook c from children that are in the successor set of the
	  // new child (prev).
	  if (sizeof(prev->leaves) == sizeof(c->leaves)) {
	    // Common special case.
	    if (!equal(prev->leaves, c->leaves)) {
	      error("Leaves not same: %O, %O\n", prev->leaves, c->leaves);
	    }
	    foreach(map(indices(c->children), git_commits), GitCommit cc) {
	      m_delete(cc->parents, c->uuid);
	      m_delete(c->children, cc->uuid);
	    }
	  } else {
	    // We need to keep those children that have leaves that
	    // aren't reachable from the new
	    mapping(string:int) other_leaves = c->leaves - prev->leaves;
	    foreach(map(indices(c->children), git_commits), GitCommit cc) {
	      if (!sizeof(cc->leaves & other_leaves)) {
		m_delete(cc->parents, c->uuid);
		m_delete(c->children, cc->uuid);
	      }
	    }
	  }
	  // Hook prev to c.
	  werror("-");
	  prev->hook_parent(c);
	  if (!pushed_commits[prev->uuid] &&
	      (sizeof(prev->parents) > 1)) {
	    commits->push(prev);
	    pushed_commits[prev->uuid] = 1;
	  }
	  verify_git_commits();
	} else {
	  werror("|");
	}
      }
    }
    if (trace_on) {
      werror("\nRemaining parents for %s: %d\n"
	     "%O\n",
	     child->uuid, sizeof(child->parents), child->parents);
    }
  }
  werror("\n");
}

void parse_config(string config)
{
}

int main(int argc, array(string) argv)
{
  string repository;
  string config;

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
      master_branch = argv[0];
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

  init_git_commits();

  werror("Git refs: %O\n", git_refs);

  // Unify commits.
  unify_git_commits();

  werror("Git refs: %O\n", git_refs);

  GitCommit c = git_refs["heads/" + master_branch];

  array(GitCommit) ccs = map(indices(c->parents), git_commits);
  sort(ccs->timestamp, ccs);
  foreach(reverse(ccs); int i; GitCommit cc) {
    werror("%d:%s(%d):%O\n",
	   i, ctime(cc->timestamp) - "\n",
	   sizeof(cc->leaves), cc->revisions);
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
}
