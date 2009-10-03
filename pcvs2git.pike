
//
// Conversion utility for cvs to git migration.
//
// 2009-10-02 Henrik Grubbström
//

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
      branch_point = branch_rev + ".";
      foreach(rev->branches, string br) {
	if (has_prefix(br, branch_point)) {
	  // Typically branch_point + "1".
	  branch_point = br;
	  break;
	}
      }
      if (has_suffix(branch_point, ".")) {
	werror("%s: Revision %s doesn't branch into branch %s %s\n",
	       rcs_file_name, rev->revision, name, branch_rev);
	continue;
      }
      rev->branches -= ({ branch_point });
      do {
	string prev = rev->revision;
	rev = revisions[branch_point];
	branch_point = rev->next;
	rev->next = prev;
      } while (branch_point);
      branch_heads[branch_rev] = rev->revision;
    }
  }

  void tag_revisions()
  {
    foreach(tags; string tag; string tag_rev) {
      if (branches[tag_rev]) continue;
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
  int timestamp;
  int timestamp_high;
  string author;
  string committer;
  multiset(string) parents = (<>);
  multiset(string) children = (<>);
  multiset(string) tags = (<>);

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

  void hook_child(GitCommit child)
  {
    children[child->uuid] = 1;
    child->parents[uuid] = 1;
  }
}

string master_branch = "master";

mapping(string:GitCommit) git_commits = ([]);

mapping(string:GitCommit) git_heads = ([]);

void init_git_branch(string path, string branch, string branch_rev,
		     string rcs_rev, RCSFile rcs_file,
		     mapping(string:GitCommit) rcs_commits)
{
  GitCommit prev_commit;
  if (!(prev_commit = git_heads[branch])) {
    if (branch_rev) {
      prev_commit = git_heads[branch] = rcs_commits[branch_rev];
    }
    if (!prev_commit) {
      prev_commit = git_heads[branch] = GitCommit();
      if (branch_rev) {
	rcs_commits[branch_rev] = prev_commit;
      }
    }
  }
  while (rcs_rev) {
    RCSFile.Revision rev = rcs_file->revisions[rcs_rev];
    GitCommit commit = rcs_commits[rcs_rev];
    if (commit) {
      prev_commit->hook_child(commit);
      break;
    }

    commit = rcs_commits[rcs_rev] = GitCommit(path, rev);
    prev_commit->hook_child(commit);
    prev_commit = commit;
    rcs_rev = rev->next;
  }
}

void init_git_commits()
{
  foreach(rcs_files; string path; RCSFile rcs_file) {
    mapping(string:GitCommit) rcs_commits = ([]);

    init_git_branch(path, master_branch, UNDEFINED,
		    rcs_file->head, rcs_file, rcs_commits);
    foreach(rcs_file->tags; string branch; string branch_rev) {
      string rcs_rev;
      if (!(rcs_rev = rcs_file->branch_heads[branch_rev])) continue;
      init_git_branch(path, "cvs/" + branch, branch_rev,
		      rcs_rev, rcs_file, rcs_commits);
    }
  }
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

  werror("Repository: %O\n", rcs_files);
  werror("Tagged_files: %O\n", tagged_files);

  init_git_commits();

  werror("Git heads: %O\n", git_heads);
}
