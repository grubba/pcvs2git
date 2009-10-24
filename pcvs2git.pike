
//
// Conversion utility for cvs to git migration.
//
// 2009-10-02 Henrik Grubbström
//

// Problem:
//
//  * CVS maintains a separate revision history for each file.
//  * CVS tags may span a subset of all files.
//  * CVS does not tag files which were dead at tag time.
//
//  * Git maintains a common commit history for all files in the repository.
//  * Git tags the entire set of files belonging to a commit.
//
//  * We want as much of the original history as possible to be converted.
//
// Approach:
//
//   From a graph-theoretical point of view, what we want to do
//   is to construct a minimum spanning DAG of a partial order relation:
//
//     Commit(X) <= Commit(Y)   if (X.timestamp <= Y.timestamp)
//
//     Commit(X) < Commit(Y)    if (Y.parent == X)
//
//     Commit(X) < Commit(Y)    if (Y == X.child)
//
//     Commit(X) <= Commit(Y)   if (Y.leaves <= X.leaves)
//
//   while maintaining the reachability from the tags (leaves).
//   Note also that the assignment of original leaves to nodes
//   may not change (leaves that aren't original may be added
//   though).
//
// Method:
//
//   To convert from CVS to Git, we first generate single file commit graphs
//   for each of the files from CVS. We then create join nodes for all of
//   the branches and tags spanning the set of revisions associated with the
//   tag or branch.
//
//   We at this point then typically have a commit-graph where we have
//   a few commits with lots of parents, and lots of commits with just
//   a single parent, as well as lots of roots (one per CVS file).
//
//   Note: The graph from this stage could be exported and contains all
//   the history, but wouldn't be very useful. All the following passes
//   attempt to make the graph more like what was in CVS at the time
//   the files were committed.
//
//   Next we generate a total order that attempts to preserve the
//   parent-child order with a primary timestamp-based ordering.
//
//   Then we attempt to identify mergeable nodes that have the same
//   set of timestamp, author, message and leaves. This pass is
//   separated from the next due to the unreliability of the timestamps.
//
//   The next step is building the DAG from scratch, by starting with
//   the oldest node, and then attaching nodes in total ordering order
//   to the most recent nodes in the DAG that aren't yet reachable
//   (ie in the ancestor set) and are compatible.
//   
//   At the final phase, we attempt to reduce the amount of extra nodes,
//   by replacing leaf nodes having a single parent with their parent.
//
// Each commit node contains two sets of leaves: leaves and dead_leaves.
//   leaves is the set of leaves that the node is reachable from via
//          parent links.
//   dead_leaves - leaves is the set of leaves that the node is
//                        incompatible with.
//   Any other leaves may be (re-)attached during processing.
//

// TODO:
//
//  o Analyze the committed $Id$ strings to find renames and merges.
//    Note that merge links must be kept separate from the ordinary
//    parent-child links, since leafs shouldn't propagate over them.
//
//  o Use git-hash-object and git-update-index and the builtin support
//    for checking out RCS file revisions to speed up the generation
//    stage.
//
//  o For paranoia reasons, the git-gc ought to be disabled during
//    the generation stage. cf "git-config gc.auto 0".

#define USE_BITMASKS

#define USE_HASH_OBJECT

//! Fuzz in seconds (5 minutes).
constant FUZZ = 5*60;

enum Flags {
  FLAG_PRETEND = 1,
  FLAG_DETECT_MERGES = 2,
  FLAG_QUIET = 4,
  FLAG_NO_KEYWORDS = 8,
};

#if 0
constant termination_uuid = "src/modules/_Crypto/Makefile:1.2";
#else
constant termination_uuid = 0;
#endif

void progress(Flags flags, sprintf_format fmt, sprintf_args ... args)
{
  if (flags & FLAG_QUIET) return;
  werror(fmt, @args);
}

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

  void calculate_root_distances()
  {
    foreach(revisions; ; Revision rev) {
      if (rev->root_distance >= 0) continue;
      ADT.Stack stack = ADT.Stack();
      stack->push(0); // End sentinel;
      while (rev->root_distance < 0) {
	if (!rev->ancestor) {
	  rev->root_distance = 0;
	  break;
	}
	stack->push(rev);
	if ((rev->revision != "1.1.1.1") && revisions["1.1.1.1"] &&
	    (rev->ancestor == revisions["1.1.1.1"]->ancestor)) {
	  // Special case for vendor branch.
	  rev = revisions["1.1.1.1"];
	} else {
	  rev = revisions[rev->ancestor];
	}
      }
      int distance = rev->root_distance;
      while (rev = stack->pop()) {
	rev->root_distance = ++distance;
      }
    }
  }

  void create(string rcs_file, string data)
  {
    ::create(rcs_file, data);

    find_branch_heads();

    tag_revisions();

    calculate_root_distances();
  }

  class Revision
  {
    inherit RCS::Revision;

    multiset(string) tags = (<>);

    int root_distance = -1;
  }
}

//! Mapping from path to rcs file.
mapping(string:RCSFile) rcs_files = ([]);

#ifndef __NT__
//! Mapping from path to file mode.
mapping(string:int) rcs_file_modes = ([]);
#endif

void read_rcs_file(string rcs_file, string path, Flags|void flags)
{
  string data = Stdio.read_bytes(rcs_file);
  RCSFile rcs = rcs_files[path] = RCSFile(rcs_file, data);

  if (!(flags & FLAG_PRETEND)) {
#ifdef USE_HASH_OBJECT
    string destdir = "work/" + dirname(path);
    Stdio.mkdirhier(destdir);
    foreach(rcs->revisions; string r; RCSFile.Revision rev) {
      // We use the same filename convention that recent cvs does.
      Stdio.write_file("work/" + path + ".~" + rev->revision + ".~",
		       rcs->get_contents_for_revision(rev));
    }
    // Cleanup the memory use...
    foreach(rcs->revisions; string r; RCSFile.Revision rev) {
      if (rev->revision == rcs->head) continue;
      rev->text = UNDEFINED;
    }
#ifndef __NT__
    rcs_file_modes[path] = file_stat(rcs_file)->mode;
#endif
#else
    // Set up an RCS work directory.
    string destdir = "work/" + dirname(path) + "/RCS";
    Stdio.mkdirhier(destdir);
    string destname = destdir + "/" + basename(rcs_file);
    Stdio.write_file(destname + ".txt", rcs_file + "\n");
    Stdio.cp(rcs_file, destname);
#ifndef __NT__
    Stdio.Stat st = file_stat(rcs_file);
    chmod(destname, st->mode);
#endif
#endif
  }
}

void read_repository(string repository, Flags|void flags, string|void path)
{
  foreach(sort(get_dir(repository)), string fname) {
    string fpath = repository + "/" + fname;
    string subpath = path;
    if (Stdio.is_dir(fpath)) {
      if ((fname != "Attic") && (fname != "RCS")) {
	if (subpath)
	  subpath += "/" + fname;
	else
	  subpath = fname;
      }
      read_repository(fpath, flags, subpath);
    } else if (has_suffix(fname, ",v")) {
      if (subpath)
	subpath += "/" + fname[..sizeof(fname)-3];
      else
	subpath = fname[..sizeof(fname)-3];
      progress(flags, "\r%d: %-65s ", sizeof(rcs_files) + 1, subpath[<64..]);
      read_rcs_file(fpath, subpath, flags);
    } else {
      progress(flags, "\n");
      werror("Warning: Skipping %s.\n", fpath);
    }
  }
}

//! @appears Handler
//!
//! A custom repository handler.
//!
//! This class is @[add_constant()]ed before compiling the
//! configuration file.
class Handler
{
  void repair_rcs_file(GitRepository git, string path, RCSFile rcs_file);
}

//! @appears GitRepository
//!
//! A git repository.
//!
//! This class is @[add_constant()]ed before compiling the
//! configuration file.
class GitRepository
{
  //! More space-efficient implementation of non-sparse multisets of ints.
  protected class IntRanges
  {
    array(int) ranges = ({});

    int find(int i)
    {
      int lo, hi = sizeof(ranges);
      //werror("Finding %O in { %{%O, %}}...\n", i, ranges);
      while (lo < hi) {
	int mid = (lo + hi)/2;
	if (ranges[mid] <= i) {
	  lo = mid + 1;
	} else {
	  hi = mid;
	}
      }
      if (sizeof(ranges)) {
	if (hi && (ranges[hi-1] > i)) {
	  error("Find: Range error (1). %O, %O, %O\n", ranges, i, hi);
	}
	if ((hi < sizeof(ranges)) && (ranges[hi] <= i)) {
	  error("Find: Range error (2). %O, %O, %O\n", ranges, i, hi);
	}
      }
      //werror("Finding %O in { %{%O, %}} ==> %O\n", i, ranges, hi);
      return hi;
    }

    int `[](int i)
    {
      // ranges[find(i)-1] <= i < ranges[find(i)].
      // i even ==> between ranges.
      // i odd ==> in a range.
      return find(i) & 1;
    }

    void `[]=(int i, int one)
    {
      if (!one) error("Removal of elements is not supported.\n");

      int pos = find(i);
      if (pos & 1) return; // Already in the set.

      // werror("Adding %O to the set { %{%O, %}} at pos %O...\n", i, ranges, pos);

      if ((pos < sizeof(ranges)) && (ranges[pos] == i+1)) {
	// We can lower the boundary for the range starting at pos.
	ranges[pos] = i;
	if (pos && (ranges[pos-1] == i)) {
	  // The range ending at pos-1 has a last value of i-1,
	  // so we can merge the ranges.
	  ranges = ranges[..pos-2] + ranges[pos+1..];
	}
      } else if (pos && (ranges[pos-1] == i)) {
	// There's a range ending at pos-1, and its last value is i-1.
	// Move the end, so that i is covered as well.
	ranges[pos-1] = i+1;
      } else {
	// Insert a range covering just i.
	ranges = ranges[..pos-1] + ({ i, i+1 }) + ranges[pos..];
      }

      if (!(find(i) & 1)) {
	error("IntRanges: Failed to add element %d to range:\n"
	      " { %{%O, %}}\n",
	      i, ranges);
      }

      for (i = 1; i < sizeof(ranges); i++) {
	if (ranges[i-1] >= ranges[i]) {
	  error("Bad ranges: { %{%O, %}}\n", ranges);
	}
      }

      // werror("  ==> { %{%O, %}}\n", ranges);
    }

    void union(IntRanges other)
    {
      // werror("Adding { %{%O, %}} to the set { %{%O, %}}...\n", other->ranges, ranges);

      // First some trivial cases.
      if (!sizeof(other->ranges)) return;
      if (!sizeof(ranges)) {
	ranges = other->ranges + ({});
	return;
      }

      int i, j;
      array(int) new_ranges = ({});
      array(int) old_ranges = ranges;

#if 1
      array(array(int)) segments = (ranges + other->ranges)/2;

      sort(map(segments, predef::`[], 0), segments);

      for (i = 0; i < sizeof(segments); i = j) {
	for (j = i+1;
	     (j < sizeof(segments)) && (segments[j][0] <= segments[i][1]);
	     segments[j++] = 0) {
	  if (segments[j][1] > segments[i][1]) {
	    segments[i][1] = segments[j][1];
	  }
	}
      }

      ranges = new_ranges = (segments - ({ 0 })) * ({});
#else
      // Merge-sort...

      for (i = 0, j = 0;
	   ((i < sizeof(ranges)) &&
	    (j < sizeof(other->ranges)));) {
	int a_start = ranges[i];
	int b_start = other->ranges[j];
	int a_end = ranges[i+1];
	int b_end = other->ranges[j+1];
	int start;
	int end;
	if (a_start < b_start) {
	  start = a_start;
	  end = a_end;
	} else {
	  start = b_start;
	  end = b_end;
	}
	int merged = 1;
	while (merged &&
	       ((i < sizeof(ranges)) || (j < sizeof(other->ranges)))) {
	  merged = 0;
	  while (a_start <= end) {
	    if (a_end > end) {
	      end = a_end;
	    }
	    i += 2;
	    if (i < sizeof(ranges)) {
	      a_start = ranges[i];
	      a_end = ranges[i+1];
	    } else {
	      a_start = 0x7fffffff;
	      a_end = -0x7fffffff;
	    }
	  }
	  while (b_start <= end) {
	    merged = 1;
	    if (b_end > end) {
	      end = b_end;
	    }
	    j += 2;
	    if (j < sizeof(other->ranges)) {
	      b_start = other->ranges[j];
	      b_end = other->ranges[j+1];
	    } else {
	      b_start = 0x7fffffff;
	      b_end = -0x7fffffff;
	    }
	  }
	}
	new_ranges += ({ start, end });
      }
      ranges = new_ranges + ranges[i..] + other->ranges[j..];

#endif

      for (i = 0; i < sizeof(old_ranges); i += 2) {
	if (!(find(old_ranges[i]) & 1)) {
	  error("Failed to merge ranges (element %d):\n"
		"old: { %{%O, %}}\n"
		"other: { %{%O, %}}\n"
		"new: { %{%O, %}}\n"
		"merged: { %{%O, %}}\n",
		old_ranges[i], old_ranges, other->ranges, new_ranges, ranges);
	}
      }
      if (!(find(old_ranges[-1]-1) & 1)) {
	error("Failed to merge ranges (element %d):\n"
	      "old: { %{%O, %}}\n"
	      "other: { %{%O, %}}\n"
	      "new: { %{%O, %}}\n"
	      "merged: { %{%O, %}}\n",
	      old_ranges[-1]-1, old_ranges, other->ranges, new_ranges, ranges);
      }
      for (j = 0; j < sizeof(other->ranges); j += 2) {
	if (!(find(other->ranges[j]) & 1)) {
	  error("Failed to merge ranges (element %d):\n"
		"old: { %{%O, %}}\n"
		"other: { %{%O, %}}\n"
		"new: { %{%O, %}}\n"
		"merged: { %{%O, %}}\n",
		other->ranges[j], old_ranges, other->ranges,
		new_ranges, ranges);
	}
      }
      if (!(find(other->ranges[-1]-1) & 1)) {
	error("Failed to merge ranges (element %d):\n"
	      "old: { %{%O, %}}\n"
	      "other: { %{%O, %}}\n"
	      "new: { %{%O, %}}\n"
	      "merged: { %{%O, %}}\n",
	      other->ranges[-1]-1, old_ranges, other->ranges,
	      new_ranges, ranges);
      }
      for (i = 1; i < sizeof(ranges); i++) {
	if (ranges[i-1] >= ranges[i]) {
	  error("Bad merged ranges:\n"
		"old: { %{%O, %}}\n"
		"other: { %{%O, %}}\n"
		"new: { %{%O, %}}\n"
		"merged: { %{%O, %}}\n",
		old_ranges, other->ranges, new_ranges, ranges);
	}
      }

      // werror("  ==> { %{%O, %}}\n", ranges);
    }

  }

  string master_branch = "master";

  mapping(string:GitCommit) git_commits = ([]);

  mapping(string:GitCommit) git_refs = ([]);

#ifdef USE_HASH_OBJECT
  // Mapping from path to mapping from revision to git_blob.
  mapping(string:mapping(string:string)) git_blobs = ([]);
#endif

  int fuzz = FUZZ;

  mapping(string:array(string)) authors = ([]);

#ifdef USE_BITMASKS
  typedef int Leafset;

  Leafset next_leaf = 1;

  Leafset get_next_leaf(string uuid)
  {
    Leafset res = next_leaf;
    next_leaf <<= 1;
    return res;
  }
#else
  typedef mapping(string:int) Leafset;

  Leafset get_next_leaf(string uuid)
  {
    return ([ uuid : 1 ]);
  }
#endif

  array(Handler) handlers = ({});

  void add_handler(Handler h)
  {
    handlers += ({ h });
  }

  array(string) parse_email_addr(string login, string email_addr)
  {
    string gecos = login;
    string email = login;
    sscanf(email_addr, "%s<%s>", gecos, email);

    gecos = String.trim_all_whites(gecos);
    email = String.trim_all_whites(email);

    if (!sizeof(gecos)) gecos = login;
    if (!sizeof(email)) email = login;
    
    if (catch(string tmp = utf8_to_string(gecos))) {
      // Not valid UTF-8. Fall back to iso-8859-1.
      gecos = string_to_utf8(gecos);
    }
    return ({ gecos, email });
  }

  mapping(string:array(string)) read_authors_file(string filename)
  {
    string data = Stdio.read_bytes(filename);
    mapping(string:array(string)) res = ([]);
    foreach(data/"\n"; int no; string raw_line) {
      string line = raw_line;
      sscanf(line, "%s#", line);
      line = String.trim_all_whites(line);
      if (!sizeof(line)) continue;
      if (sscanf(line, "%s=%s", string login, string email_addr) == 2) {
	login = String.trim_all_whites(login);
	res[login] = parse_email_addr(login, email_addr);
      } else {
	werror("%s:%d: Failed to parse line: %O\n",
	       filename, no+1, raw_line);
      }
    }
    return res;
  }

  array(string) author_lookup(GitCommit c, string login)
  {
    array(string) res = authors[login];

    if (!res) {
      res = parse_email_addr(login, login);
      if (sizeof(authors)) {
	werror("Warning: %s: Author %O is not in the authors file.\n",
	       c->uuid, login);
	authors[login] = res;
      }
    }
    return res;
  }

  string cmd(array(string) cmd_line, mapping(string:mixed)|void opts)
  {
    mapping(string:string|int) res = Process.run(cmd_line, opts);
    if (res->exitcode) {
      werror("Command failed with code %d: %{%O %}:\n"
	     "%s\n",
	     res->exitcode, cmd_line, res->stderr);
	error("Remote command failed.\n");
    }
    return res->stdout;
  }

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
    mapping(string:int) soft_parents = ([]);
    mapping(string:int) soft_children = ([]);
    Leafset leaves;

    //! Contains the set of leaves that may NOT be reattached
    //! during merging and graphing.
    Leafset dead_leaves;

    Leafset is_leaf;

    //! Mapping from path to rcs revision prefixed by the distance
    //! to the root for files contained in this commit (delta
    //! against parent(s)). Deleted file revisions are suffixed by "(DEAD)".
    mapping(string:string) revisions = ([]);

    //! Mapping from path to rcs revision for files contained
    //! in this commit (full set including files from predecessors).
    //! Same conventions as in @[revisions].
    mapping(string:string) full_revision_set;

    int is_dead;

    int trace_mode;

    static void create(string path, string|RCSFile.Revision|void rev)
    {
#ifdef USE_BITMASKS
      dead_leaves = -1;
#else
      leaves = ([]);
#endif
      if (rev) {
	if (stringp(rev)) {
	  // revisions[path] = rev;
	  uuid = path + ":" + rev;
	} else {
	  revisions[path] =
	    sprintf("%4c%s", rev->root_distance, rev->revision);
	  uuid = path + ":" + rev->revision;
	  author = committer = rev->author;
	  message = rev->log;
	  timestamp = timestamp_low = rev->time->unix_time();
	  if (rev->state == "dead") {
	    revisions[path] += "(DEAD)";  // For easier handling later on.
	    is_dead = 1;
	    // trace_mode = 1;
	  }
	}
      } else {
	uuid = path + ":";
	leaves = is_leaf = get_next_leaf(uuid);
      }
      git_commits[uuid] = this_object();
    }

    static string _sprintf(int c, mixed|void x)
    {
      return sprintf("GitCommit(%O /* %d/%d/%d p/c/l */)",
		     uuid, sizeof(parents), sizeof(children),
#ifdef USE_BITMASKS
		     leaves
#else
		     sizeof(leaves)
#endif
		     );
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

    void propagate_leaves(Leafset leaves)
    {
      ADT.Stack stack = ADT.Stack();
      stack->push(0);	// End sentinel.
      stack->push(this_object());

      while (GitCommit c = stack->pop()) {
#ifdef USE_BITMASKS
	Leafset new_leaves = leaves & ~c->leaves;
	if (new_leaves) {
	  c->leaves |= new_leaves;
	  map(map(indices(c->parents), git_commits), stack->push);
	}
#else
	Leafset new_leaves = leaves - c->leaves;
	if (sizeof(new_leaves)) {
	  c->leaves |= new_leaves;
	  map(map(indices(c->parents), git_commits), stack->push);
	}
#endif
      }
    }

    void propagate_dead_leaves(Leafset dead_leaves)
    {
      ADT.Stack stack = ADT.Stack();
      stack->push(0);	// End sentinel.
      stack->push(this_object());

#ifdef USE_BITMASKS
      while (GitCommit c = stack->pop()) {
	int old = c->dead_leaves;
	c->dead_leaves |= dead_leaves;
	if (c->dead_leaves != old) {
	  map(map(indices(c->children), git_commits), stack->push);
	}
      }
#else
      while (GitCommit c = stack->pop()) {
	int sz = sizeof(c->dead_leaves);
	c->dead_leaves |= dead_leaves;
	if (sizeof(c->dead_leaves) != sz) {
	  map(map(indices(c->children), git_commits), stack->push);
	}
      }
#endif
    }

    void rake_dead_leaves()
    {
#ifdef USE_BITMASKS
      if (dead_leaves >= 0) return;
#else
      if (dead_leaves) return;
#endif
      if (!sizeof(parents)) {
	dead_leaves = leaves;
	return;
      }
      array(GitCommit) ps = git_sort(map(indices(parents), git_commits));
      foreach(ps, GitCommit p) {
#ifdef USE_BITMASKS
	if (p->dead_leaves < 0) p->rake_dead_leaves();
#else
	if (!p->dead_leaves) p->rake_dead_leaves();
#endif
      }
      array(Leafset) leaf_mounds = Array.uniq(ps->dead_leaves);
#ifdef USE_BITMASKS
      leaf_mounds = sort(leaf_mounds);
#else
      sort(map(leaf_mounds, sizeof), leaf_mounds);
#endif
      foreach(reverse(leaf_mounds), Leafset leaves) {
#ifdef USE_BITMASKS
	// Avoid creating new sets of dead leaves if possible.
	if (dead_leaves < 0) {
	  dead_leaves = leaves;
	} else if ((dead_leaves & leaves) != leaves) {
	  dead_leaves |= leaves;
	}
#else
	// Avoid creating new sets of dead leaves if possible.
	if (!dead_leaves) {
	  dead_leaves = leaves;
	} else if (sizeof(dead_leaves & leaves) != sizeof(leaves)) {
	  dead_leaves |= leaves;
	}
#endif
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
      parent->propagate_leaves(leaves);
#ifdef USE_BITMASKS
      if (dead_leaves >= 0) {
	propagate_dead_leaves(parent->dead_leaves & ~parent->leaves);
      }
#else
      if (dead_leaves) {
	propagate_dead_leaves(parent->dead_leaves - parent->leaves);
      }
#endif
    }

    //! Detach a soft parent (aka merge link) from this commit.
    void detach_soft_parent(GitCommit parent)
    {
      m_delete(parent->soft_children, uuid);
      m_delete(soft_parents, parent->uuid);
    }

    //! Add a soft parent (aka merge link) for this commit.
    void hook_soft_parent(GitCommit parent)
    {
      soft_parents[parent->uuid] = 1;
      parent->soft_children[uuid] = 1;
    }

    // Assumes compatible leaves, and same author and commit message.
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
    //                |  \     / |               /  |   \
    //               +-+  +---+ +-+           +-+ +---+  +-+
    //    Children:  | |  |   | | |           | | |   |  | |
    //               +-+  +---+ +-+           +-+ +---+  +-+
    //
    // Note that changed leafs propagate towards the parents, and
    // changed dead leafs propagate towards the children.
    void merge(GitCommit c)
    {
      if (message != c->message) {
	error("Different messages: %O != %O\n", message, c->message);
      }

      if (author != c->author) {
	error("Different authors: %O != %O\n", author, c->author);
      }

      trace_mode |= c->trace_mode;

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

	if (trace_mode || cc->trace_mode) {
	  werror("Detaching child %O from %O during merge of %O to %O\n",
		 cc, c, this_object(), c);
	}

	cc->detach_parent(c);
	cc->hook_parent(this);
	if (cc->timestamp < timestamp) {
	  if (cc->timestamp + fuzz < timestamp) {
	    error("Parent: %s\n Child: %s\n",
		  pretty_git(this), pretty_git(c_uuid));
	  } else {
	    // Fudge the timestamp for the child.
	    // FIXME: Ought to propagate...
	    cc->timestamp = timestamp;
	  }
	}
      }
      foreach(c->soft_children; string c_uuid;) {
	GitCommit cc = git_commits[c_uuid];

	if (!cc) {
	  error("Missing child to %s\n%s\n",
		pretty_git(c), pretty_git(c_uuid));
	}

	if (trace_mode || cc->trace_mode) {
	  werror("Detaching child %O from %O during merge of %O to %O\n",
		 cc, c, this_object(), c);
	}

	cc->detach_soft_parent(c);
	cc->hook_soft_parent(this);
      }

      if (trace_mode) {
	werror("Stealing parents from %s to %s...\n",
	       pretty_git(c, 1), pretty_git(this_object(), 1));
      }

      // And from its parents, and hook us to them.
      foreach(c->parents; string p_uuid;) {
	GitCommit p = git_commits[p_uuid];

	if (trace_mode || p->trace_mode) {
	  werror("Detaching parent %O from %O during merge of %O to %O\n",
		 p, c, this_object(), c);
	}

	c->detach_parent(p);
	hook_parent(p);
	if (p->timestamp > timestamp) {
	  if (p->timestamp - fuzz > timestamp) {
	    error("Parent: %s\n Child: %s\n",
		  pretty_git(p), pretty_git(this));
	  } else {
	    // Fudge the timestamp for the child.
	    // FIXME: Ought to propagate...
	    timestamp = p->timestamp;
	  }
	}
      }
      foreach(c->soft_parents; string p_uuid;) {
	GitCommit p = git_commits[p_uuid];

	if (trace_mode || p->trace_mode) {
	  werror("Detaching parent %O from %O during merge of %O to %O\n",
		 p, c, this_object(), c);
	}

	c->detach_soft_parent(p);
	hook_soft_parent(p);
      }

      if (trace_mode) {
	werror("Stealing the rest from %s to %s...\n",
	       pretty_git(c, 1), pretty_git(this_object(), 1));
      }

      if (timestamp < c->timestamp) timestamp = c->timestamp;
      if (timestamp_low > c->timestamp_low) timestamp_low = c->timestamp_low;

      propagate_leaves(c->leaves);
      if (dead_leaves != c->dead_leaves) {
#ifdef USE_BITMASKS
	// Note: Leaves that were reattached aren't dead.
	propagate_dead_leaves(c->dead_leaves & ~leaves);
#else
	// Note: Leaves that were reattached aren't dead.
	propagate_dead_leaves(c->dead_leaves - leaves);
#endif
      }

      revisions += c->revisions;

      if (c->is_leaf) {
#ifdef USE_BITMASKS
	is_leaf = is_leaf|c->is_leaf;
#else
	is_leaf = is_leaf?(is_leaf + c->is_leaf):c->is_leaf;
#endif
	foreach(git_refs; string ref; GitCommit r) {
	  if (r == c) {
	    git_refs[ref] = this_object();
	  }
	}
      }

      is_dead &= c->is_dead;

      m_delete(git_commits, c->uuid);
      destruct(c);
    }

    void generate(mapping(string:string) rcs_state,
		  mapping(string:string) git_state)
    {
      if (git_id) return;

      // First ensure that our parents have been generated.
      array(GitCommit) parent_commits =
	git_sort(map(indices(parents), git_commits));
      parent_commits->generate(rcs_state, git_state);
      array(GitCommit) soft_parent_commits =
	git_sort(map(indices(soft_parents - parents), git_commits));
      soft_parent_commits->generate(rcs_state, git_state);

      // Then generate a merged history.

      if (sizeof(parent_commits)) {
	// Merge the revisions from our (true) parents.
	full_revision_set = parent_commits[0]->full_revision_set;
	if (sizeof(parent_commits) > 1) {
	  full_revision_set += ([]);
	  foreach(parent_commits[1..]->full_revision_set,
		  mapping(string:string) rev_set) {
	    foreach(rev_set; string path; string rev_info) {
	      if (!full_revision_set[path] ||
		(full_revision_set[path] < rev_info)) {
		full_revision_set[path] = rev_info;
	      }
	    }
	  }
	}
	// Add our own revisions.
	full_revision_set += revisions;
      } else {
	full_revision_set = revisions;
      }

      // Then we can start actually messing with git...

      // werror("Generating commit for %s\n", pretty_git(this_object(), 1));

#ifdef USE_HASH_OBJECT
      array(string) index_info = ({});

      foreach(git_state; string path; string rev_info) {
	if (!full_revision_set[path] ||
	    has_suffix(full_revision_set[path], "(DEAD)")) {
	  index_info += ({
	    "0 0000000000000000000000000000000000000000\t" + path + "\n"
	  });
	  m_delete(git_state, path);
	}
      }

      // Add the blobs for the revisions to the git index.
      foreach(full_revision_set; string path; string rev_info) {
	if (!has_suffix(rev_info, "(DEAD)")) {
	  if (git_state[path] != rev_info) {
	    index_info += ({
	      sprintf("%6o %s 0\t%s\n",
		      0100644
#ifndef __NT__
		      | (rcs_file_modes[path] & 0111)
#endif
		      ,
		      git_blobs[path][rev_info], path)
	    });
	    git_state[path] = rev_info;
	  }
	}
      }

      if (sizeof(index_info)) {
	cmd(({ "git", "update-index", "--index-info" }),
	    ([ "stdin": index_info*"" ]));
      }
#else
      mapping(string:int) paths = ([]);
      foreach(git_state; string path; string rev_info) {
	if (!full_revision_set[path] ||
	    hash_suffix(full_revision_set[path], "(DEAD)")) {
	  paths[path] = 1;
	  m_delete(git_state, path);
	}
      }
      if (sizeof(paths)) {
	cmd(({ "git", "rm", "--cached", }) + indices(paths));
	paths = ([]);
      }

      // Check out our revisions and add them to the git index.
      foreach(full_revision_set; string path; string rev_info) {
	if (rev) {
	  if (rcs_state[path] != rev_info) {
	    cmd(({ "co", "-f", "-r" + rev_info[4..], path }));
	    rcs_state[path] = rev_info;
	  }
	  if (git_state[path] != rev_info) {
	    paths[path] = 1;
	    git_state[path] = rev_info;
	  }
	}
      }
      if (sizeof(paths)) {
	cmd(({ "git", "add" }) + indices(paths));
	paths = ([]);
      }
#endif

      if ((sizeof(parent_commits) == 1) &&
	  equal(parent_commits[0]->full_revision_set, full_revision_set)) {
	// Noop commit, probably a tag.
	git_id = parent_commits[0]->git_id;
      } else {
	// Create a git tree object from the git index.
	string tree_id =
	  String.trim_all_whites(cmd(({ "git", "write-tree" })));

	array(string) commit_cmd = ({ "git", "commit-tree", tree_id });
	foreach(Array.uniq(parent_commits->git_id), string git_id) {
	  commit_cmd += ({ "-p", git_id });
	}
	foreach(Array.uniq(soft_parent_commits->git_id), string git_id) {
	  commit_cmd += ({ "-p", git_id });
	}

	if (!message) {
	  message = "Joining branches.\n";
	} else if (catch(string tmp = utf8_to_string(message))) {
	  // Not valid UTF-8. Fall back to iso-8859-1.
	  message = string_to_utf8(message);
	}

	message += "\nID: " + uuid + "\n";
	foreach(sort(indices(revisions)), string path) {
	  message += "Rev: " + path + ":" + revisions[path][4..] + "\n";
	}
#if 0
#ifndef USE_BITMASKS
	foreach(sort(indices(leaves)), string leaf) {
	  message += "Leaf: " + leaf + "\n";
	}
	foreach(sort(indices(dead_leaves - leaves)), string leaf) {
	  message += "Dead-leaf: " + leaf + "\n";
	}
#endif
#endif

	array(string) author_info = author_lookup(this_object(), author);
	array(string) committer_info = author_lookup(this_object(),
						     committer || author);

	// Commit.
	git_id =
	  String.trim_all_whites(cmd(commit_cmd,
				     ([
				       "stdin":message,
				       "env":([ "PATH":getenv("PATH"),
						"GIT_AUTHOR_NAME":
						author_info[0],
						"GIT_AUTHOR_EMAIL":
						author_info[1],
						"GIT_AUTHOR_DATE":
						"" + timestamp,
						"GIT_COMMITTER_NAME":
						committer_info[0],
						"GIT_COMMITTER_EMAIL":
						committer_info[1],
						"GIT_COMMITTER_DATE":
						"" + timestamp,
				     ]),
				     ])));
      }
      foreach(parent_commits, GitCommit p) {
	// The full sets take quite a bit of memory for large repositories.
	// Free them as soon as we don't need them anymore.
	detach_parent(p);
	if (!sizeof(p->children)) {
	  p->full_revision_set = UNDEFINED;
	}
      }
      if (!sizeof(children)) {
	full_revision_set = UNDEFINED;
      }
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
    if (tag && !(prev_commit = git_refs[tag])) {
      prev_commit = git_refs[tag] = GitCommit(tag);
    }
    //werror("L:%O\n", prev_commit);
    if (branch_rev) {
      GitCommit commit = rcs_commits[branch_rev];
      if (commit) {
	prev_commit->hook_parent(commit);
	return;
      }
    } else if (tag && has_prefix(tag, "heads/") &&
	       rcs_file->revisions["1.1.1.1"] &&
	       (rcs_file->revisions["1.1.1.1"]->ancestor == rcs_rev)) {
      // Move the head for the trunk of a single revision file from the
      // root revision to the first vendor commit (if any), to emulate
      // the order that cvs uses...
      rcs_rev = "1.1.1.1";
    }
    while (rcs_rev) {
      RCSFile.Revision rev = rcs_file->revisions[rcs_rev];
      GitCommit commit = rcs_commits[rcs_rev];
      if (commit) {
	//werror("E:%O (%O:%O)\n", commit, path, rcs_rev);
	if (prev_commit) {
	  prev_commit->hook_parent(commit);
	}
#if 1
	if (branch_rev) {
	  rcs_commits[branch_rev] = commit;
	  branch_rev = UNDEFINED;
	}
#endif
	break;
      }

      commit = rcs_commits[rcs_rev] = GitCommit(path, rev);
#if 1
      if (branch_rev) {
	rcs_commits[branch_rev] = commit;
	branch_rev = UNDEFINED;
      }
#endif
      //werror("N:%O (%O:%O)\n", commit, path, rcs_rev);
      if (prev_commit) {
	prev_commit->hook_parent(commit);
      }
      prev_commit = commit;

      if ((rcs_rev != "1.1.1.1") && rcs_file->revisions["1.1.1.1"] &&
	  (rev->ancestor == rcs_file->revisions["1.1.1.1"]->ancestor)) {
	// Make commits that branch from the trunk branch from
	// the first vendor commit (if any), to emulate the order
	// that cvs uses...
	//
	// ie The cvs number series goes 1.1 ==> 1.1.1.1 ==> 1.2 ==> 1.3 ...
	rcs_rev = "1.1.1.1";
      } else {
	rcs_rev = rev->ancestor;
      }
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
    return sprintf("GitCommit(%O /* %s */\n"
		   "/* %O:%O */\n"
		   "/* Parents: %{%O, %}\n"
		   "   Children: %{%O, %}\n"
		   "   Leaves: %{%O, %}\n"
		   "   Revisions: %O\n"
		   "*/)",
		   c->uuid, ctime(c->timestamp) - "\n",
		   c->author, c->message,
		   indices(c->parents), indices(c->children),
#ifdef USE_BITMASKS
		   ({ c->leaves }),
#else
		   (skip_leaves?({sizeof(c->leaves)}):indices(c->leaves)),
#endif
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
#ifndef USE_BITMASKS
	if (sizeof(p->leaves & c->leaves) != sizeof(c->leaves)) {
	  error("Parent %O is missing leaves from child %O:\n"
		"%O is not a subset of %O\n"
		"Commit: %s\n"
		"Parent: %s\n",
		p_uuid, uuid, c->leaves, p->leaves,
		pretty_git(c), pretty_git(p));
	}
#endif
	if (p->timestamp > c->timestamp + fuzz)
	  error("Parent %O is more recent than %O.\n"
		"Parent: %s\n"
		"Child: %s",
		p_uuid, uuid,
		pretty_git(p), pretty_git(c));
      }

#ifdef USE_BITMASKS
      Leafset leaves;
#else
      Leafset leaves = ([]);
#endif
      if (c->is_leaf) {
	// Node is a leaf.
	leaves = c->is_leaf;
      }
      foreach(c->children; string p_uuid;) {
	GitCommit p = git_commits[p_uuid];
	if (!p) error("Invalid child %O for commit %O\n", p_uuid, uuid);
	if (!p->parents[uuid])
	  error("Child %O is missing parent %O.\n", p_uuid, uuid);
#ifndef USE_BITMASKS
	if (sizeof(p->leaves & c->leaves) != sizeof(p->leaves)) {
	  error("Child %O is missing leaves from parent %O:\n"
		"%O is not a subset of %O\n"
		"Child: %s\n"
		"Parent: %s",
		p_uuid, uuid, p->leaves, c->leaves,
		pretty_git(p), pretty_git(c));
	}
#endif
	if (p->timestamp + fuzz < c->timestamp)
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
    string a;
    foreach(r->parents; string p_uuid;) {
      GitCommit p = git_commits[p_uuid];
      if (p->timestamp == 0x7ffffffe) fix_git_ts(p);
      if (ts < p->timestamp) {
	ts = p->timestamp;
	a = p->author;
      }
    }

    // Make sure we have some margin...
    r->timestamp = r->timestamp = ts + fuzz*16;
    r->author = a;
  }

  string fix_cvs_tag(string tag)
  {
    array(string) frags = tag/"_";
    string res = "";
    foreach(frags; int i; string frag) {
      if (!i) {
	res = frag;
      } else if (sizeof(res) && sizeof(frag) &&
		 (res[-1] >= '0') && (res[-1] <= '9') &&
		 (frag[0] >= '0') && (frag[0] <= '9')) {
	res += "." + frag;
      } else {
	res += "_" + frag;
      }
    }
    return res;
  }

  mapping(string:int) starters = ([]);

  void detect_merges(RCSFile rcs_file, mapping(string:GitCommit) rcs_commits)
  {
    string rcs_name = basename(rcs_file->rcs_file_name);
    int found;
    foreach(sort(indices(rcs_file->revisions)), string rr) {
      RCSFile.Revision rev = rcs_file->revisions[rr];
      string text = rev->rcs_text;
      mapping(string:int) entries = ([]);
      while (sscanf(text, "%*s$Id: %[- a-z,A-Z/0-9_.:]$%s",
		    string id_string, text) == 3) {
	if (sscanf(id_string, "%s %s ", string file, string r) == 2) {
	  entries[file + ":" + r] = 1;
	}
      }
      if (sizeof(entries) == 1) {
	string revision = indices(entries)[0];
	string file;
	string r;
	sscanf(revision, "%s:%s", file, r);
	if ((file == rcs_name) && (r == rev->ancestor)) continue;
	if (file != rcs_name) {
	  werror("\nCopy of %s:%s to %s:%s",
		 file, r, rcs_name, rev->revision);
	  found = 1;
	} else if ((r == "1.1.1.1") && rcs_file->revisions[r] &&
		   (rev->ancestor == rcs_file->revisions[r]->ancestor)) {
	  // CVS prefers using the vendor branch revision
	  // to the root revision...
	  continue;
	} else if (rcs_commits[r] && (r != rev->revision) &&
		   (rcs_commits[r]->timestamp <=
		    rcs_commits[rev->revision]->timestamp)) {
	  werror("\nDetected merge with revision %s in %s",
		 r, rev->revision);
	  rcs_commits[r]->hook_soft_parent(rcs_commits[rev->revision]);
	  found = 1;
	} else {
	  werror("\nStrange merge with revision %s in %s",
		 r, rev->revision);
	  found = 1;
	}
      }
    }
    if (found) werror("\n");
  }

  void add_rcs_file(string path, RCSFile rcs_file, Flags|void flags)
  {
    mapping(string:GitCommit) rcs_commits = ([]);

    init_git_branch(path, "heads/" + master_branch, UNDEFINED,
		    rcs_file->head, rcs_file, rcs_commits);
    foreach(rcs_file->tags; string tag; string tag_rev) {
      if ((tag == "start") && (tag_rev == "1.1.1.1")) {
	// This is the automatic vendor branch tag.
	// We handle it later, see below.
	if (!rcs_commits["1.1.1.1"]) {
	  init_git_branch(path, UNDEFINED, UNDEFINED, "1.1.1.1",
			  rcs_file, rcs_commits);
	}
	starters[rcs_commits["1.1.1.1"]->uuid] = 1;
	continue;
      }
      tag = fix_cvs_tag(tag);

      if (rcs_file->symbol_is_branch(tag_rev)) {
	tag_rev = (tag_rev/"." - ({"0"})) * ".";
      }
      string rcs_rev;
      if ((rcs_rev = rcs_file->branch_heads[tag_rev])) {
	init_git_branch(path, "heads/" + tag, tag_rev,
			rcs_rev, rcs_file, rcs_commits);
      } else {
	init_git_branch(path, "tags/" + tag, UNDEFINED,
			tag_rev, rcs_file, rcs_commits);
      }
    }

    // Identify merges.
    if (flags & FLAG_DETECT_MERGES) {
      this_program::detect_merges(rcs_file, rcs_commits);
    }
  }

  void init_git_commits(mapping(string:RCSFile) rcs_files, Flags|void flags)
  {
    progress(flags, "Initializing Git commmit tree from RCS...\n");
    int cnt;
    foreach(sort(indices(rcs_files)), string path) {
      RCSFile rcs_file = rcs_files[path];
      progress(flags, "\r%d: %-65s", sizeof(rcs_files) - cnt++, path[<64..]);
      add_rcs_file(path, rcs_file, flags);
    }
    progress(flags, "\n");

    // Now we can handle the automatic vendor branch tag.
    if (sizeof(starters)) {
      GitCommit start = git_refs["tags/start"];
      if (start) {
	// Apparently the tag start has been used for other purposes
	// than the automatic vendor branch tag. Add back any stuff
	// we've kept in starters.
	foreach(git_sort(map(indices(starters), git_commits)),
		GitCommit c) {
	  c->hook_parent(start);
	}
      } else {
	// The automatic vendor branch tag. It's not useful in a git
	// context as is, since it may show up at several points in time.
	// We move it to the earliest commit that had it to begin with.
	start = git_refs["tags/start"] = GitCommit("tags/start");
	start->hook_parent(git_sort(map(indices(starters), git_commits))[0]);
      }
      starters = ([]);
    }

    foreach(git_refs;; GitCommit r) {
      // Fix the timestamp for the ref.
      fix_git_ts(r);
    }

    progress(flags, "Raking dead leaves...\n");
    // Collect the dead leaves, they have collected at the root commit
    // for each RCS file.
    foreach(git_sort(values(git_commits)), GitCommit c) {
      c->rake_dead_leaves();
    }

    progress(flags, "Verifying initial state...\n");
 
    verify_git_commits();
  }

  // Attempt to unify as many commits as possible given
  // the following invariants:
  //
  //   * The set of reachable leaves from a commit containing a revision.
  //   * The commit order must be maintained (ie a node may not reparent
  //     one of its parents).
  void unify_git_commits(Flags|void flags)
  {
    // First perform a total ordering that is compatible with the
    // parent-child partial order and the commit timestamp order.

    progress(flags, "Sorting...\n");
    ADT.Stack commit_stack = ADT.Stack();
    array(GitCommit) sorted_commits = allocate(sizeof(git_commits));

    commit_stack->push(0);	// End sentinel.
    // Push the root commits
    array(GitCommit) root_commits =
      filter(values(git_commits),
	     lambda(GitCommit c) {
	       return !sizeof(c->parents);
	     });
    // Get a canonical order.
    foreach(git_sort(root_commits), GitCommit c) {
      commit_stack->push(c);
    }

    int i;
    while (GitCommit c = commit_stack->pop()) {
      if (c->is_leaf) continue;	// Handle the leafs later.
      sorted_commits[i++] = c;
      foreach(git_sort(map(indices(c->children), git_commits)), GitCommit cc) {
	commit_stack->push(cc);
      }
    }

    array(GitCommit) leaf_commits =
      filter(values(git_commits),
	     lambda(GitCommit c) {
	       return c->is_leaf;
	     });
    foreach(git_sort(leaf_commits), GitCommit c) {
      sorted_commits[i++] = c;
    }

    if (i != sizeof(sorted_commits)) {
      error("Lost track of commits: %d != %d\n",
	    i, sizeof(sorted_commits));
    }

    sort(sorted_commits->timestamp, sorted_commits);

    int cnt;

#if 1
    // Then we merge the nodes that are mergeable.
    // FIXME: This is probably broken; consider the case
    //        A ==> B ==> C merged with B ==> C ==> A
    //        merged with C ==> A ==> B in a fuzz timespan.
    progress(flags, "Merging...\n");
    for (i = 0; i < sizeof(sorted_commits); i++) {
      GitCommit c = sorted_commits[i];
      for (int j = i; j--;) {
	GitCommit p = sorted_commits[j];
	if (!p) continue;
	if (c->timestamp >= p->timestamp + fuzz) break;
	if (!(cnt--)) {
	  cnt = 0;
	  progress(flags, "\r%d:%d(%d): %-60s  ",
		   sizeof(sorted_commits) - i, j,
		   sizeof(git_commits), p->uuid[<59..]);
	}
	Leafset common_leaves = p->leaves & c->leaves;
#ifdef USE_BITMASKS
	if ((common_leaves != p->leaves) || (common_leaves != c->leaves)) {
	  // Check if any of the uncommon leaves are dead.
	  if ((c->leaves & ~common_leaves) & p->dead_leaves) continue;
	  if ((p->leaves & ~common_leaves) & c->dead_leaves) continue;
	}
#else
	if ((sizeof(common_leaves) != sizeof(p->leaves)) ||
	    (sizeof(common_leaves) != sizeof(c->leaves))) {
	  // Check if any of the uncommon leaves are dead.
	  if (sizeof((c->leaves - common_leaves) & p->dead_leaves)) continue;
	  if (sizeof((p->leaves - common_leaves) & c->dead_leaves)) continue;
	}
#endif
	// p is compatible with c.
	if ((c->timestamp < p->timestamp + fuzz) &&
	    !p->children[c->uuid] &&
	    (p->author == c->author) &&
	    (p->message == c->message) &&
#ifdef USE_BITMASKS
	    !((p->leaves & ~common_leaves) & c->dead_leaves)
#else
	    !sizeof((p->leaves - common_leaves) & c->dead_leaves)
#endif
	    ) {
	  // Close enough in time for merge...
	  // c isn't a child of p.
	  // and the relevant fields are compatible.
	  // FIXME: Check that none of sorted_parents[i+1 .. j-1]
	  //        is a parent to c.
	  c->merge(p);
	  sorted_commits[j] = 0;
	}
      }
    }

    sorted_commits -= ({ 0 });
#endif

    cnt = 0;
    // To reduce strange behaviour on behalf of fully dead commits, we
    // first scan for their closest child. This will give it some leaves
    // to reduce excessive adding of merge links.
    // Note: This is O(n²)!
    progress(flags, "\nResurrecting dead nodes...\n");
    for (i = 0; i < sizeof(sorted_commits); i++) {
      GitCommit p = sorted_commits[i];
      if (!p || !p->is_dead) continue;

      // Check if we should trace...
      int trace_mode = p->trace_mode
#if 0
	|| (< "tutorial/Image.wmml:1.7",
	      "src/modules/Image/encodings/pnm.c:1.5",
	      "tutorial/Makefile:1.10",
	      "src/modules/Image/encodings/configure.in:1.2",
      >)[p->uuid]
#endif
	;
      
      if (trace_mode) {
	werror("\nTRACE ON.\n");
      }

      for (int j = i+1; j < sizeof(sorted_commits); j++) {
	GitCommit c = sorted_commits[j];
	if (!c) continue;
	if (!(cnt--) || trace_mode) {
	  cnt = 99;
	  progress(flags, "\r%d:%d(%d): %-55s  ",
		   sizeof(sorted_commits)-i, j, sizeof(git_commits),
		   p->uuid[<54..]);
	  if (trace_mode) werror("\n");
	}
	Leafset common_leaves = p->leaves & c->leaves;
#ifdef USE_BITMASKS
	if (common_leaves != c->leaves) {
	  // p doesn't have all the leaves that c has.
	  // Check if the leaves may be reattached.
	  if ((c->leaves & ~common_leaves) & p->dead_leaves) {
	    if (trace_mode) {
	      werror("%O(%d) is not valid as a parent.\n"
		     "  Conflicting leaves: %O\n",
		     p, j, (c->leaves & ~common_leaves) & p->dead_leaves);
	    }
	    continue;
	  }
	}
#else
	if (sizeof(common_leaves) != sizeof(c->leaves)) {
	  // p doesn't have all the leaves that c has.
	  // Check if the leaves may be reattached.
	  if (sizeof((c->leaves - common_leaves) & p->dead_leaves)) {
	    if (trace_mode) {
	      werror("%O(%d) is not valid as a parent.\n"
		     "  Conflicting leaves: %O\n",
		     p, j, (c->leaves - common_leaves) & p->dead_leaves);
	    }
	    continue;
	  }
	}
#endif
	// p is compatible with c.

	if (trace_mode) {
	  werror("Hooking %O(%d) as a parent to %O(%d)...\n", p, j, c, i);
	}

	// Make c a child to p.
	c->hook_parent(p);

	break;
      }

      if (p && (p->uuid == termination_uuid)) {
	break;
      }
    }

    cnt = 0;
    // Now we can generate a DAG by traversing from the root toward the leafs.
    // Note: This is O(n²)! But since we utilize information in the ancestor
    //       sets, it's usually quite fast.
    progress(flags, "\nGraphing...\n");
    array(IntRanges) ancestor_sets =
      allocate(sizeof(sorted_commits), IntRanges)();
    for (i = 0; i < sizeof(sorted_commits); i++) {
      GitCommit c = sorted_commits[i];
      if (!c) continue;
      mapping(string:int) orig_parents = c->parents;
      IntRanges ancestors = ancestor_sets[i];

      // Check if we should trace...
      int trace_mode = c->trace_mode
#if 0
	|| (< "tutorial/Image.wmml:1.7",
	      "src/modules/Image/encodings/pnm.c:1.5",
	      "tutorial/Makefile:1.10",
	      "src/modules/Image/encodings/configure.in:1.2",
      >)[c->uuid]
#endif
	;
      
      if (trace_mode) {
	werror("\nTRACE ON.\n");
      }

#if 1
      if (!c->message && sizeof(orig_parents)) {
	array(GitCommit) parents =
	  git_sort(map(indices(orig_parents), git_commits));
	Leafset leaves = `&(@parents->leaves);
	Leafset dead_leaves = `|(@parents->dead_leaves);
	if (trace_mode) {
	  werror("Attaching extra leaves to %O: %{%O, %}\n"
		 "Dead leaves: %{%O, %}\n",
#ifdef USE_BITMASKS
		 c, ({ leaves & ~c->leaves }),
		 ({ dead_leaves & ~c->dead_leaves })
#else
		 c, sort(indices(leaves - c->leaves)),
		 sort(indices(dead_leaves - c->dead_leaves))
#endif
		 );
	}
	// Note: Due to these being the common subset of our parents
	//       leaves, we won't need to propagate them.
	c->leaves = c->is_leaf = leaves;
	c->dead_leaves = dead_leaves;
      }
#endif

      // We rebuild these...
      c->children = ([]);
      c->parents = ([]);
      for (int j = i; j--;) {
	GitCommit p = sorted_commits[j];
	// if (!c) continue;
	if (!p /* || !p->message */) {
	  // Make sure leaves stay leaves...
	  // Attempt to make the range tighter.
	  ancestors[j] = 1;
	  continue;
	}
	if (ancestors[j]) {
	  // Accellerate by skipping past the range.
	  int t = ancestors->find(j);
	  j = ancestors->ranges[t-1];
	  continue;
	}
	if (!(cnt--) || trace_mode) {
	  cnt = 99;
	  progress(flags, "\r%d:%d(%d): %-55s  ",
		   sizeof(sorted_commits)-i, j, sizeof(git_commits),
		   c->uuid[<54..]);
	  if (trace_mode) werror("\n");
	}
	Leafset common_leaves = p->leaves & c->leaves;
#ifdef USE_BITMASKS
	if (common_leaves != c->leaves) {
	  // p doesn't have all the leaves that c has.
	  // Check if the leaves may be reattached.
	  if ((c->leaves & ~common_leaves) & p->dead_leaves) {
	    if (trace_mode) {
	      werror("%O(%d) is not valid as a parent.\n"
		     "  Conflicting leaves: %O\n",
		     p, j, (c->leaves & ~common_leaves) & p->dead_leaves);
	    }
	    continue;
	  }
	}
#else
	if (sizeof(common_leaves) != sizeof(c->leaves)) {
	  // p doesn't have all the leaves that c has.
	  // Check if the leaves may be reattached.
	  if (sizeof((c->leaves - common_leaves) & p->dead_leaves)) {
	    if (trace_mode) {
	      werror("%O(%d) is not valid as a parent.\n"
		     "  Conflicting leaves: %O\n",
		     p, j, (c->leaves - common_leaves) & p->dead_leaves);
	    }
	    continue;
	  }
	}
#endif
	// p is compatible with c.
#if 0
	if ((c->timestamp < p->timestamp + fuzz) &&
	    !orig_parents[p->uuid]) {
	  // Close enough in time for merge...
	  // c doesn't have to be a child of p.
	  if ((p->author == c->author) &&
	      (p->message == c->message) &&
#ifdef USE_BITMASKS
	      !((p->leaves & ~common_leaves) & c->dead_leaves)
#else
	      !sizeof((p->leaves - common_leaves) & c->dead_leaves)
#endif
	      ) {
	    ancestors->union(ancestor_sets[j]);
	    c->merge(p);
	    sorted_commits[j] = 0;
	    ancestor_sets[j] = 0;
	    // Fixup the ancestor sets.
	    foreach(ancestor_sets, IntRanges set) {
	      if (set && set[j]) {
		// p was an ancestor, and was replaced by us.
		set->union(ancestors);
		set[i] = 1;
	      }
	    }
	    continue;
	  }
	  // Check if there's any alternatives in range.
	  int k;
	  for (k = j; k--;) {
	    GitCommit t = sorted_commits[k];
	    if (!t || ancestors[k]) continue;
	    Leafset common_leaves = t->leaves & c->leaves;
#ifdef USE_BITMASKS
	    if (common_leaves != c->leaves) {
	      // t doesn't have all the leaves that c has.
	      // Check if the leaves may be reattached.
	      if ((c->leaves & ~common_leaves) & t->dead_leaves)
		continue;
	    }
#else
	    if (sizeof(common_leaves) != sizeof(c->leaves)) {
	      // t doesn't have all the leaves that c has.
	      // Check if the leaves may be reattached.
	      if (sizeof((c->leaves - common_leaves) & t->dead_leaves))
		continue;
	    }
#endif
	    if ((c->timestamp >= t->timestamp + fuzz) &&
		!orig_parents[t->uuid]) {
	      // No.
	      k = -1;
	    }
	    break;
	  }
	  if (k > 0) {
	    j = k+1;
	    continue;
	  }
	}
#endif

	if (trace_mode) {
	  werror("Hooking %O(%d) as a parent to %O(%d)...\n"
		 "  ancestors: { %{[%d,%d), %}}\n"
		 "  other: { %{[%d,%d), %}}\n",
		 p, j, c, i, ancestors->ranges/2, ancestor_sets[j]->ranges/2);
	}

	// Make c a child to p.
	c->hook_parent(p);
	// All of j's ancestors are ancestors to us.
	ancestors->union(ancestor_sets[j]);
	// And so is j as well.
	ancestors[j] = 1;

	if (trace_mode) {
	  werror("  joined: { %{[%d,%d), %}}\n", ancestors->ranges/2);
	}
      }

#if 1
      // Refresh the leaf nodes.
      if (!c->message && sizeof(c->parents)) {
	array(GitCommit) parents =
	  git_sort(map(indices(c->parents), git_commits));
	if (sizeof(parents) == 1) {
	  // No need to keep us around...
	  GitCommit p = parents[0];
	  if (trace_mode) {
	    werror("Merging leaf %O into stem %O\n", c, p);
	  }
	  c->detach_parent(p);
	  c->leaves = p->leaves;
	  c->timestamp = p->timestamp;
	  c->message = p->message;
	  c->author = p->author;
	  p->merge(c);
	  sorted_commits[i] = 0;
	  ancestor_sets[i] = 0;
	  // Note: No need to update any of the ancestor sets, since
	  //       we're the most recent node to have been looked at.
	} else {
	  Leafset leaves = `&(@parents->leaves);
	  Leafset dead_leaves = `|(@parents->dead_leaves);
	  if (trace_mode) {
	    werror("Attaching extra leaves to %O: %{%O, %}\n"
		   "Dead leaves: %{%O, %}\n",
#ifdef USE_BITMASKS
		   c, ({ leaves & ~c->leaves }),
		   ({ dead_leaves & ~c->dead_leaves })
#else
		   c, sort(indices(leaves - c->leaves)),
		   sort(indices(dead_leaves - c->dead_leaves))
#endif
		   );
	  }
	  // Note: Due to these being the common subset of our parents
	  //       leaves, we won't need to propagate them.
	  c->leaves = c->is_leaf = leaves;
	  c->dead_leaves = dead_leaves;
	  c->timestamp = parents[-1]->timestamp;
	}
      }
#endif

      if (c && (c->uuid == termination_uuid)) {
	break;
      }
    }

    sorted_commits -= ({ 0 });

    progress(flags, "\nDone\n");

    // exit(0);

    verify_git_commits();
  }

#ifdef USE_HASH_OBJECT
  protected void blob_reader(Stdio.File blobs, Thread.Queue processing)
  {
    string buf = "";
    do {
      string bytes = blobs->read();
      if (!sizeof(bytes)) break;
      buf += bytes;
      array(string) b = buf/"\n";
      foreach(b[..<1], string blob) {
	[string path, string r] = processing->read();
	git_blobs[path][r] = blob;
	rm(path + ".~" + r + ".~");
      }
      buf = b[-1];
    } while (1);
    blobs->close();
  }
#endif /* USE_HASH_OBJECT */

  void generate(string workdir, Flags|void flags)
  {
    cd(workdir);

    mapping(string:string) rcs_state = ([]);
    mapping(string:string) git_state = ([]);

    progress(flags, "Preparing to generate %d git commits...\n",
	     sizeof(git_commits));

    cmd(({ "git", "init" }));

    // Turn off the gc during our processing.
    cmd(({ "git", "config", "gc.auto", "0" }));

#ifdef USE_HASH_OBJECT
    progress(flags, "Importing files...\n");

    Stdio.File paths = Stdio.File();
    Stdio.File blobs = Stdio.File();

    // Start the file object hasher.
    Process.Process pid = 
      Process.create_process(({ "git", "hash-object", "-w", "--stdin-paths" }),
			     ([ "stdin": paths->pipe(Stdio.PROP_REVERSE),
				"stdout": blobs->pipe(),
			     ]));

    Thread.Queue processing = Thread.Queue();

    Thread.Thread reader = Thread.thread_create(blob_reader, blobs, processing);

    foreach(git_sort(values(git_commits)); int i; GitCommit c) {
      progress(flags, "\r%d: %-70s ", sizeof(git_commits) - i, c->uuid[<69..]);
      foreach(c->revisions; string path; string rev_info) {
	if (has_suffix(rev_info, "(DEAD)")) continue;
	if (zero_type(git_blobs[path])) {
	  git_blobs[path] = ([]);
	}
	if (zero_type(git_blobs[path][rev_info])) {
	  git_blobs[path][rev_info] = 0;
	  processing->write(({ path, rev_info }));
	  paths->write(path + ".~" + rev_info[4..] + ".~\n");
	}
      }
    }
    paths->close();

    reader->wait();

    int e = pid->wait();
    if (e) exit(e);
#endif /* USE_HASH_POBJECT */

    progress(flags, "\nCommitting...\n");

    // Loop over the commits oldest first to reduce recursion.
    foreach(git_sort(values(git_commits)); int i; GitCommit c) {
      progress(flags, "\r%d: %-70s ", sizeof(git_commits) - i, c->uuid[<69..]);
      c->generate(rcs_state, git_state);
    }

    progress(flags, "\nTagging ...\n");

    foreach(git_refs; string ref; GitCommit c) {
      if (!c->git_id) continue;
      progress(flags, "\r%s: %-65s", c->git_id[..7], ref[<64..]);
      if (has_prefix(ref, "heads/")) {
	cmd(({ "git", "branch", "-f", ref[sizeof("heads/")..],
		       c->git_id }));
      } else if (has_prefix(ref, "tags/")) {
	cmd(({ "git", "tag", "-f", ref[sizeof("tags/")..],
		       c->git_id }));
      } else {
	werror("\r%-75s\rUnsupported reference identifier: %O\n", "", ref);
      }
    }
    progress(flags, "\r%-75s\nDone\n", "");

    // Turn on the git gc again.
    cmd(({ "git", "config", "--unset", "gc.auto" }));

    cmd(({ "git", "gc", "--aggressive" }));

    cmd(({ "git", "reset", "--mixed", master_branch }));
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

void usage(array(string) argv)
{
  write("%s [-h | --help] [-p] [-d <repository>] [-A <authors>]\n"
	"%*s [(-C | --git-dir) <gitdir>]\n"
	"%*s [-o <branch>] [(-r | --remote) <remote>]\n"
	"%*s [-z <fuzz>] [-m] [-k] [-q | --quiet]\n",
	argv[0], sizeof(argv[0]), "",
	sizeof(argv[0]), "", sizeof(argv[0]), "");
}

int main(int argc, array(string) argv)
{
  string repository;
  string config;

  GitRepository git = GitRepository();

  Flags flags;

  foreach(Getopt.find_all_options(argv, ({
	   ({ "help",       Getopt.NO_ARG,  ({ "-h", "--help" }), 0, 0 }),
	   ({ "authors",    Getopt.HAS_ARG, ({ "-A", "--authors" }), 0, 0 }),
	   ({ "git-dir",    Getopt.HAS_ARG, ({ "-C", "--git-dir" }), 0, 0 }),
	   ({ "branch",     Getopt.HAS_ARG, ({ "-o" }), 0, 0 }),
	   ({ "remote",     Getopt.HAS_ARG, ({ "-r", "--remote" }), 0, 0 }),
	   ({ "repository", Getopt.HAS_ARG, ({ "-d" }), 0, 0 }),
	   ({ "fuzz",       Getopt.HAS_ARG, ({ "-z" }), 0, 0 }),
	   ({ "nokeywords", Getopt.HAS_ARG, ({ "-k" }), 0, 0 }),
	   ({ "merges",     Getopt.NO_ARG,  ({ "-m" }), 0, 0 }),
	   ({ "pretend",    Getopt.NO_ARG,  ({ "-p" }), 0, 0 }),
	   ({ "quiet",      Getopt.NO_ARG,  ({ "-q", "--quiet" }), 0, 0 }),
				  })),
	  [string arg, string val]) {
    switch(arg) {
    case "help":
      usage(argv);
      exit(0);
    case "authors":
      git->authors |= git->read_authors_file(val);
      break;
    case "branch":
      git->master_branch = val;
      break;
    case "repository":
      repository = val;
      break;
    case "fuzz":
      git->fuzz = (int)val;
      break;
    case "merges":
      flags |= FLAG_DETECT_MERGES;
      break;
    case "pretend":
      flags |= FLAG_PRETEND;
      break;
    case "quiet":
      flags |= FLAG_QUIET;
      break;
    case "nokeywords":
      flags |= FLAG_NO_KEYWORDS;
      break;
    default:
      werror("Unsupported option: %O:%O\n", arg, val);
      exit(1);
    }
  }

  if (!repository) {
    usage(argv);
    exit(0);
  }

  if (!config && Stdio.is_file(".pcvs2git.rc")) {
    config = ".pcvs2git.rc";
  }
  if (config) {
    parse_config(config);
  }

  progress(flags, "Reading RCS files...\n");

  read_repository(repository, flags);

  progress(flags, "\n");

  // werror("Repository: %O\n", rcs_files);

  // FIXME: Filter here.

  git->init_git_commits(rcs_files, flags);

  // No need to keep these around anymore.
  rcs_files = ([]);

  // werror("Git refs: %O\n", git->git_refs);

  // Unify commits.
  git->unify_git_commits(flags);

  // werror("Git refs: %O\n", git->git_refs);

  // return 0;

  // FIXME: Generate a git repository.

  if (!(flags & FLAG_PRETEND)) {
    git->generate("work", flags);
  }
}
