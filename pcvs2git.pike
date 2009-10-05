
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
	    branch_point = br;
	    rev = revisions[br];
	    br = rev->next;
	    rev->next = branch_point;
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

class GitCommit
{
  string git_id;
  string uuid = Standards.UUID.make_version4()->str();
  string message;
  int timestamp = 0x7ffffffe;
  int timestamp_high = 0x7ffffffe;
  string author;
  string committer;
  multiset(string) parents = (<>);
  multiset(string) children = (<>);

  //! Mapping from path to rcs revision for files contained
  //! in this commit.
  mapping(string:string) revisions = ([]);

  static void create(string|void path, RCSFile.Revision|void rev)
  {
    git_commits[uuid] = this_object();
    if (rev) {
      revisions[path] = rev->revision;
      author = committer = rev->author;
      message = rev->log;
      timestamp = timestamp_high = rev->time->unix_time();
    }
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

  //! Add a parent for this commit.
  void hook_parent(GitCommit parent)
  {
    parents[parent->uuid] = 1;
    parent->children[uuid] = 1;
  }

  // Assumes same children, author and commit message.
  //
  //                    Before                  After
  //
  //              +-+ +-+   +-+ +-+       +-+ +-+  +-+ +-+
  //    Parents:  | | | |   | | | |       | | | |  | | | |
  //              +-+ +-+   +-+ +-+       +-+ +-+  +-+ +-+
  //                \ /       \ /            \ \    / /
  //               +----+     +-+             +------+
  //               |this|     |c|    ==>      | this |
  //               +----+     +-+             +------+
  //                   \     /                   |
  //                    +---+                  +---+
  //    Children:       |   |                  |   |
  //                    +---+                  +---+
  void merge(GitCommit c)
  {
    if (timestamp > c->timestamp) timestamp = c->timestamp;
    if (timestamp_high < c->timestamp_high) timestamp_high = c->timestamp_high;

    // Unhook c from its children.
    foreach(c->children; string c_uuid;) {
      GitCommit cc = git_commits[c_uuid];
      cc->parents[c->uuid] = 0;
      // Paranoia...
      cc->parents[uuid] = 1;
      children[cc->uuid] = 1;
    }

    // And from its parents.
    foreach(c->parents; string p_uuid;) {
      GitCommit p = git_commits[p_uuid];
      p->children[c->uuid] = 0;
      p->children[uuid] = 1;
      parents[p->uuid] = 1;
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
  if (!(prev_commit = git_refs[tag])) {
    if (branch_rev) {
      prev_commit = git_refs[tag] = rcs_commits[branch_rev];
    }
    if (!prev_commit) {
      prev_commit = git_refs[tag] = GitCommit();
      if (branch_rev) {
	rcs_commits[branch_rev] = prev_commit;
      }
    }
  }
  while (rcs_rev) {
    RCSFile.Revision rev = rcs_file->revisions[rcs_rev];
    GitCommit commit = rcs_commits[rcs_rev];
    if (commit) {
      prev_commit->hook_parent(commit);
      break;
    }

    commit = rcs_commits[rcs_rev] = GitCommit(path, rev);
    prev_commit->hook_parent(commit);
    prev_commit = commit;
    rcs_rev = rev->next;
  }
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
    int ts = -0x7fffffff;
    foreach(r->parents; string p_uuid;) {
      GitCommit p = git_commits[p_uuid];
      if (ts < p->timestamp_high) ts = p->timestamp_high;
    }
    r->timestamp_high = r->timestamp = ts + FUZZ;
  }
}

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
    werror("\r%d(%d)  ", sizeof(commits), sizeof(git_commits));
    GitCommit child = commits->pop();
    m_delete(pushed_commits, child->uuid);

    // Partition the parents into sets with the same number of children
    // and the same commit message.
    mapping(int:mapping(string:multiset(GitCommit)))
      partitioned_parents = ([]);
    foreach(child->parents; string uuid;) {
      GitCommit c = git_commits[uuid];
      mapping(string:multiset(GitCommit)) tmp =
	partitioned_parents[sizeof(c->children)];
      if (!tmp) {
	partitioned_parents[sizeof(c->children)] = ([c->message:(< c >)]);
	continue;
      }
      if (tmp[c->message]) {
	tmp[c->message][c] = 1;
      } else {
	tmp[c->message] = (< c >);
      }
    }
    // For each partition, check if it is possible to merge these commits.
    // Note: This is a O(n²) operation.
    foreach(partitioned_parents; ;
	    mapping(string:multiset(GitCommit)) partition) {
      foreach(partition;; multiset(GitCommit) sub_partition) {
	if (sizeof(sub_partition) < 2) continue;
	foreach(sub_partition; GitCommit first;) {
	  if (!first) continue;
	  sub_partition[first] = 0;
	  foreach(sub_partition; GitCommit second;) {
	    if (first->author == second->author) {
	      // FIXME: Check timestamps as well.
	      multiset(string) common_children =
		first->children & second->children;
	      if (!((sizeof(common_children) == sizeof(first->children)) &&
		    (sizeof(common_children) == sizeof(second->children)))) {
		continue;
	      }
	      // Merge the second commit into the first.
	      first->merge(second);
	      if (pushed_commits[first->uuid]) {
		commits->adjust(first);
	      } else if (sizeof(first->parents) > 1) {
		commits->push(first);
		pushed_commits[first->uuid] = 1;
	      }
	      sub_partition[second] = 0;
	      if (pushed_commits[second->uuid]) {
		m_delete(pushed_commits, second->uuid);
		second->timestamp = 0x7fffffff;
		commits->adjust(second);
		if (commits->peek() == second) commits->pop();
	      }
	      m_delete(git_commits, second->uuid);
	      destruct(second);
#if 0
	      foreach(first->parents; string uuid;) {
		if (!pushed_commits[uuid] && (uuid != parent->uuid)) {
		  GitCommit p = git_commits[uuid];
		  if (sizeof(p->parents) > 1) {
		    commits->push(p);
		    pushed_commits[uuid] = 1;
		  }
		}
	      }
#endif
	    }
	  }
	}
      }
#if 0
      // Attempt to sequence the commits.
      foreach(parent->parents; string uuid;) {
	GitCommit candidate;
      }
#endif /* 0 */
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

  // FIXME: Unify commits.
  unify_git_commits();

  // FIXME: Generate a merged history?

  // FIXME: Generate a git repository.
}
