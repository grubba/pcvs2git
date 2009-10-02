
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

mapping(string:RCSFile) rcs_files = ([]);

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

void parse_config(string config)
{
}

int main(int argc, array(string) argv)
{
  string repository;
  string config;

  foreach(Getopt.find_all_options(argv, ({
	   ({ "help",       Getopt.NO_ARG,  ({ "-h", "--help" }), 0, 0 }),
	   ({ "repository", Getopt.HAS_ARG, ({ "-d" }), 0, 0 }),
				  })),
	  [string arg, string val]) {
    switch(arg) {
    case "help":
      write("%s [-d repository] [-h|--help]\n", argv[0]);
      exit(0);
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
}
