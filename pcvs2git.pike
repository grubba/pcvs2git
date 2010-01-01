
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
//   dead_leaves is the set of leaves that the node is incompatible with.
//   Any other leaves may be (re-)attached during processing.
//

// TODO:
//
//  o Analyze the committed $Id$ strings to find renames and merges.
//    Note that merge links must be kept separate from the ordinary
//    parent-child links, since leafs shouldn't propagate over them.
//
//  o Implement support for -r and --remote.
//
//  o Implement keyword expansion and filtering (support for -k).
//
//  o Backdate commits that have been bumped in time.
//
//  o Identify why the virtual root commits are sometimes committed.
//
// FEATURES
//
//  o Uses git-fast-import to do the actual import into git
//    for optimal speed.
//
//  o The git import phase is started in parallel with the
//    init git from RCS phase. This reduces the working set
//    and potentially speed up the total running time
//    (at least on multi-cpu machines).
//
//  o The tags (and branches) are created at commit time.
//    This allows for observing of the git repository
//    during its creation if suitable sequence points are
//    added.



#define USE_BITMASKS

#define USE_HASH_OBJECT

#define USE_FAST_IMPORT

//! Fuzz in seconds (5 minutes).
constant FUZZ = 5*60;

enum Flags {
  FLAG_PRETEND = 1,
  FLAG_DETECT_MERGES = 2,
  FLAG_QUIET = 4,
  FLAG_NO_KEYWORDS = 8,
  FLAG_HEADER = 16,
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
	  // rev->branches -= ({ br });
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

  protected void set_default_path(string path)
  {
    foreach(revisions;;Revision rev) {
      rev->path = path;
    }
  }

  void create(string rcs_file, string path, string|void data)
  {
    ::create(rcs_file, data);

    set_default_path(path);

    find_branch_heads();
  }

  Revision append_revision(string ancestor, Calendar.TimeRange rcs_time,
			   string author, string message, string|void rev,
			   string|void state)
  {
    Revision parent = revisions[ancestor];
    if (!parent) return UNDEFINED;

    Revision new_rev;
    if (!rev) {
      int i;
      do {
	// Use a revision number that isn't used by cvs.
	rev = sprintf("%s%c", ancestor, i + 'a');
	i++;
      } while (revisions[rev]);
    } else if (new_rev = revisions[rev]) return new_rev;

    new_rev = FakeRevision(rev, parent, rcs_time, author, message);
    new_rev->state = state || parent->state;
    new_rev->ancestor = ancestor;
    // Reparent the other children to parent, so that we are inserted
    // in their history, but only if we're not on a new branch.
    if (!has_prefix(rev, ancestor + ".")) {
      foreach(revisions;; Revision r) {
	if ((r->ancestor == ancestor) && (r->time > rcs_time)) {
	  r->ancestor = rev;
	}
      }
    }
    revisions[rev] = new_rev;
    return new_rev;
  }

  string get_contents_for_revision(string|Revision rev)
  {
    if (stringp(rev)) rev = revisions[rev];
    if (!rev) return 0;
    if (!rev->rcs_text) rev->rcs_text = "";	// Paranoia.
    string data = ::get_contents_for_revision(rev);
    if (data && rev->state != "dead") {
      rev->sha = Crypto.SHA1()->update(data)->digest();
    } else {
      rev->sha = "\0"*20;	// Death marker.
    }
    return data;
  }

  class Revision
  {
    inherit RCS::Revision;

    string path;

    string sha;
  }

  class FakeRevision
  {
    inherit Revision;
    constant is_fake_revision = 1;

    //! Create the specified revision based on @[parent].
    protected void create(string rev, Revision parent, Calendar.TimeRange time,
			  string author, string message)
    {
      revision = rev;
      path = parent->path;
      sha = parent->sha;
      text = parent->text;
      this_program::time = time;
      this_program::author = author;
      this_program::log = message;
      // Some magic to get the content correct...
      rcs_text = "";			// No differences from
      rcs_prev = parent->revision;	// our parent.
    }
  }
}

//! @appears GitRepository
//!
//! A git repository.
//!
//! This class is @[add_constant()]ed before compiling the
//! configuration file.
class GitRepository
{

  //! @appears GitHandler
  //!
  //! A custom repository handler.
  //!
  //! This class is @[add_constant()]ed before compiling the
  //! configuration file.
  class GitHandler(GitRepository git, Flags git_flags)
  {
    //! The RCS file was renamed at revision @[rev].
    //!
    //! @param rev
    //!   The first revision on @[new_path].
    protected void rename_revision(RCSFile rcs_file, string old_path,
				   string new_path, string rev)
    {
      werror("rename_revision(%O, %O, %O, %O)\n",
	     rcs_file, old_path, new_path, rev);
      RCSFile.Revision root_rev = rcs_file->revisions[rev];
      if (!root_rev) return;
      RCSFile.Revision r = root_rev;
      while (r = rcs_file->revisions[r->ancestor]) {
	if (r->path == new_path) r->path = old_path;
      }
      foreach(rcs_file->revisions;; r) {
	if ((r->path == new_path) && (r->time < root_rev->time)) {
	  r->path = old_path;
	}
      }
#if 0
      foreach(map(sort(indices(rcs_file->revisions)), rcs_file->revisions),
	      RCSFile.Revision r) {
	werror("\t%O\t%O\n", r->revision, r->path);
      }
#endif /* 0 */
    }

    //! Hide a specific revision.
    protected void hide_revision(RCSFile rcs_file, string rev)
    {
      RCSFile.Revision r = rcs_file->revisions[rev];
      if (r) r->path = UNDEFINED;
    }

    //! Find the revision that was current on branch @[branch] at
    //! @[rcs_time].
    protected string find_revision(RCSFile rcs_file, string branch,
				   string rcs_time)
    {
      if (rcs_time[2] == '.') rcs_time = "19" + rcs_time;
      Calendar.TimeRange time = Calendar.ISO.parse("%y.%M.%D.%h.%m.%s %z",
						   rcs_time + " UTC");
      // Get a suitable starting revision.
      string prev_rev = rcs_file->tags[branch] || rcs_file->branch ||
	rcs_file->head;
      if (rcs_file->symbol_is_branch(prev_rev) || (prev_rev == "1.1.1")) {
	string branch_prefix;
	if (prev_rev == "1.1.1") {
	  branch_prefix = "1.1.1.";
	  prev_rev = "1.1";
	} else {
	  array(string) frags = prev_rev/".";
	  prev_rev = frags[..<2]*".";
	  branch_prefix = prev_rev + "." + frags[-1] + ".";
	}
	foreach(rcs_file->revisions[prev_rev]->branches||({}), string b) {
	  if (has_prefix(b, branch_prefix)) {
	    // Advance to the head of the branch.
	    for (RCSFile.Revision r = rcs_file->revisions[b];
		 r; r = rcs_file->revisions[r->rcs_next]) {
	      prev_rev = r->revision;
	    }
	    break;
	  }
	}
      }
      // At this point prev_rev is a revision at the end of a branch.
      // Search for the first revision that is older than rcs_time.
      for(RCSFile.Revision r = rcs_file->revisions[prev_rev];
	  r && r->time >= time; r = rcs_file->revisions[prev_rev]) {
	prev_rev = r->ancestor;
      }
      return prev_rev;
    }

    //! Add a new branch @[branch] rooted at @[rev].
    //!
    //! @returns
    //!   Returns the new branch prefix.
    protected string add_branch(RCSFile rcs_file, string branch, string rev)
    {
      if (!rev) return UNDEFINED;
      string branch_prefix;
      if (branch_prefix = rcs_file->tags[branch]) {
	// The branch already exists.
	// FIXME: Not supported yet.
	error("Branch %O already exists!\n", branch);
      }
      // Create a new branch.
      branch_prefix = rev + ".0.";
      multiset(string) existing_branches = (<>);
      foreach(rcs_file->tags;;string r) {
	if (has_prefix(r, branch_prefix)) {
	  existing_branches[r] = 1;
	}
      }
      int i;
      for (i = 2; existing_branches[branch_prefix + i]; i+=2)
	;
      werror("Creating a new branch: %O\n", branch_prefix + i);
      rcs_file->tags[branch] = branch_prefix + i;
      branch_prefix = rev + "." + i;
      rcs_file->branches[branch_prefix] = branch;
      rcs_file->branch_heads[branch_prefix] = rev;
      return branch_prefix;
    }

    //! Add a new fake revision to an RCS file.
    //!
    //! @param branch
    //!   Branch to adjust. @expr{0@} is the default branch.
    //!   If the branch doesn't exist, it will be created.
    //!
    //! @param prev_rev
    //!   The revision immediately preceeding the created revision
    //!   if known. Otherwise a suitable revision will be selected.
    //!
    //! @param rcs_time
    //!   The RCS timestamp of the created revision.
    //!
    //! @param committer
    //!   The committer of the created revision.
    //!
    //! @param message
    //!   The commit message for the created revision.
    //!
    //! @param state
    //!   The state of the created revision.
    //!   Defaults to the same state as @[prev_rev].
    //!
    //! This function is typically used to create artificial commits
    //! when there's no suitable commit to hook an out-of-band event
    //! to.
    //!
    //! @returns
    //!   Returns the new revision.
    protected string append_revision(RCSFile rcs_file, string|void branch,
				     string|void prev_rev, string rcs_time,
				     string committer, string message,
				     string|void state)
    {
      if (rcs_time[2] == '.') rcs_time = "19" + rcs_time;
      Calendar.TimeRange time = Calendar.ISO.parse("%y.%M.%D.%h.%m.%s %z",
						   rcs_time + " UTC");
      werror("time: %O\n", time);
      if (!prev_rev) {
	// Get a suitable starting revision.
	prev_rev = find_revision(rcs_file, branch, rcs_time);
      }
      // We now have a suitable prev_rev.

      werror("append_revision(%O, %O, %O, %O, %O, %O, %O)\n",
	     rcs_file, branch, prev_rev, rcs_time, committer, message, state);

      if (!prev_rev) return UNDEFINED;

      // Now it's time to generate a suitable result_rev.
      string result_rev;
      if (branch) {
	string branch_prefix = add_branch(rcs_file, branch, prev_rev);
	// We add a revision to our new branch...
	result_rev = branch_prefix + ".1";
	rcs_file->branch_heads[branch_prefix] = result_rev;
      } else {
	int i;
	for (i = 'a'; rcs_file->revisions[sprintf("%s%c", prev_rev, i)]; i++)
	  ;
	result_rev = sprintf("%s%c", prev_rev, i);
      }
      werror("Result rev: %O\n", result_rev);
      // FIXME!
      RCSFile.Revision rev = rcs_file->append_revision(prev_rev, time,
						       committer, message,
						       result_rev, state);
      if (branch) {
	RCSFile.Revision brev = rcs_file->revisions[prev_rev];
	if (brev->branches) {
	  brev->branches += ({ rev->revision });
	} else {
	  brev->branches = ({ rev->revision });
	}
      } else if (rcs_file->head == prev_rev) {
	rcs_file->head = rev->revision;
      } else if (rcs_file->branch == prev_rev) {
	rcs_file->branch = rev->revision;
      }
      werror("Revision: %O\n", rev->revision);
      return rev->revision;
    }

    //! This handler is called on entering a directory during RCS import.
    //!
    //! @param path
    //!   The destination path in the git repository.
    //!
    //! @param files
    //!   The set of RCS files and directories that are about to be imported.
    //!
    //! @param state
    //!   For use by the handler. Intended use is to hold information
    //!   to pass along to the corresponding call of @[leave_directory()].
    //!
    //! Typical uses are to reorder the directory scanning order, or to
    //! convert certain directories into branches.
    //!
    //! @returns
    //!   Returns an array:
    //!   @array
    //!     @elem string 0
    //!       The (possibly altered) @[path].
    //!     @elem array(string) 1
    //!       The (possibly altered) set of @[files].
    //!   @endarray
    //!
    //! @seealso
    //!   @[leave_directory()]
    array(string|array(string)) enter_directory(GitRepository git,
						string path,
						array(string) files,
						Flags flags,
						mapping state);

    //! This handler is called on leaving a directory during RCS import.
    //!
    //! @param path
    //!   The original destination path in the git repository (ie not
    //!   as modified by @[enter_directory()].
    //!
    //! @param files
    //!   The set of RCS files and directories that were imported.
    //!
    //! @param state
    //!   For use by the handler. Intended use is to hold information
    //!   passed along from the corresponding call of @[enter_directory()].
    //!
    //! Typical use is to restore any state altered by @[enter_directory()].
    //!
    //! @seealso
    //!   @[enter_directory()]
    array(string) leave_directory(GitRepository git, string orig_path,
				  array(string) files, Flags flags,
				  mapping state);

    //! This handler is called once for each imported RCS file.
    //!
    //! It is typically used to perform various stuff that isn't supported
    //! natively by the RCS fileformat, eg renames.
    void repair_rcs_file(GitRepository git, string path, RCSFile rcs_file,
			 Flags flags);

    //! This function is used to notify about dependencies between
    //! branches.
    //!
    //! It is typically called from @[rake_leaves()].
    protected void branch_dependancy(GitRepository git, string orig_tag,
				     string dependant_tag,
				     string|int split_time)
    {
      GitRepository.GitCommit orig = git->git_refs[orig_tag] ||
	git->git_refs["heads/" + orig_tag];
      GitRepository.GitCommit dependant = git->git_refs[dependant_tag] ||
	git->git_refs["heads/" + dependant_tag];
      if (!orig || !dependant) {
	werror("Warning: The branches %O and %O aren't both present.\n",
	       orig_tag, dependant_tag);
	return;
      }
      if (stringp(split_time)) {
	if (split_time[2] == '.') {
	  split_time = "19" + split_time;
	}
	split_time = Calendar.ISO.parse("%y.%M.%D.%h.%m.%s %z",
					split_time + " UTC")->unix_time();
      }
      int orig_mask = orig->is_leaf;
      int dependant_mask = dependant->is_leaf;
      foreach(git->git_sort(values(git->git_commits)),
	      GitRepository.GitCommit c) {
	if (!(c->commit_flags & GitRepository.COMMIT_DEAD)) continue;
	if (c->timestamp > split_time) continue;
	if (!(c->leaves & orig_mask)) continue;
	if (c->dead_leaves & dependant_mask) continue;
	if (c->leaves & dependant_mask) continue;
	dependant->hook_parent(c);
      }
    }

    //! This handler hook is called directly after the initial raking of leaves,
    //! but before the untangling pass. This allows for custom handling
    //! of leaves.
    void rake_leaves(GitRepository git);

    //! Perform forced merges.
    void force_merges(GitRepository git);

    //! This handler hook is called just before starting to commit
    //! the files to git.
    void final_check(GitRepository git);
  }

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

  multiset(string) master_branches = (<>);

  string master_branch;

  mapping(string:GitCommit) git_commits = ([]);

  mapping(string:GitCommit) git_refs = ([]);

  //! Mapping from path:revision_id[8..] (cf @[commit_factory()]) to uuid.
  mapping(string:string) revision_lookup = ([]);

  //! Mapping from (binary) sha to (ascii) mark for a blob.
  mapping(string:string) git_blobs = ([]);

  int fuzz = FUZZ;

  mapping(string:array(string)) authors = ([]);

#ifdef USE_BITMASKS
  typedef int Leafset;

  Leafset next_leaf = 1;

  // NB: For performance with old pikes reasons, this mapping is
  //     from base-256 string of the leaf mask (rather than directly
  //     from leaf mask) to the leaf uuid.
  mapping(string:string) leaf_lookup = ([]);

  Leafset get_next_leaf(string uuid)
  {
    Leafset res = next_leaf;
    next_leaf <<= 1;
    leaf_lookup[res->digits(256)] = uuid;
    return res;
  }

  void describe_leaves(string prefix, Leafset leaves, string suffix)
  {
    while (leaves) {
      Leafset leaf = leaves & ~(leaves-1);
      leaves -= leaf;
      werror("%s%s%s", prefix, leaf_lookup[leaf->digits(256)] || (string)leaf,
	     suffix);
    }
  }
#else
  typedef mapping(string:int) Leafset;

  Leafset get_next_leaf(string uuid)
  {
    return ([ uuid : 1 ]);
  }
#endif

  protected int mark_counter = 1;
  string new_mark()
  {
    return ":" + ++mark_counter;
  }

  GitHandler handler;

  void set_handler(GitHandler h)
  {
    handler = h;
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
      if (!login) return ({ "A. Nonymous", "anonymous" });
      res = parse_email_addr(login, login);
      if (sizeof(authors)) {
	werror("Warning: %s: Author %O is not in the authors file.\n",
	       c->uuid, login);
	authors[login] = res;
      }
    }
    return res;
  }

  enum CommitFlags {
    COMMIT_DEAD = 1,	// Commit contains only deletions.
    COMMIT_HIDE = 2,	// Don't export this commit to git.
    COMMIT_FAKE = 4,	// This is a CVS out-of-band node.
    COMMIT_TRACE = 128,	// Trace this node.
  };

  class GitCommit
  {
    string git_id;
    string uuid;
    string message;
    int timestamp = 0x7ffffffe;
    int timestamp_low = 0x7ffffffe;
    int time_offset;
    string author;
    string committer;
    mapping(string:int) parents = ([]);
    mapping(string:int) children = ([]);
    mapping(string:int) soft_parents = ([]);
    mapping(string:int) soft_children = ([]);
    Leafset leaves;

    CommitFlags commit_flags;

    //! Contains the set of leaves that may NOT be reattached
    //! during merging and graphing.
    Leafset dead_leaves;

    Leafset is_leaf;

    //! Mapping from path to rcs revision prefixed by the timestamp
    //! for files contained in this commit (delta against parent(s)).
    //! Deleted file revisions are suffixed by "(DEAD)".
    mapping(string:string) revisions = ([]);

    //! Mapping from path to rcs revision for files contained
    //! in this commit (full set including files from predecessors).
    //! Same conventions as in @[revisions].
    mapping(string:string) full_revision_set;

    static void create(string path, string|void rev, string|void uuid)
    {
#ifdef USE_BITMASKS
      dead_leaves = -1;
#else
      leaves = ([]);
#endif
      if (!uuid) {
	if (rev) {
	  uuid = path + ":" + rev;
	} else {
	  uuid = path + ":";
	}
      }
      if (!rev) {
	leaves = is_leaf = get_next_leaf(uuid);
	commit_flags |= COMMIT_FAKE;
      }
      this_program::uuid = uuid;
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
    //       (Which is the opposite order of what git_sort() does.)
    int `<(mixed x)
    {
      if (!objectp(x)) return 1;
      if (parents[x->uuid]) return 1;
      return x->timestamp < timestamp;
    }

    int `>(mixed x)
    {
      if (!objectp(x)) return 0;
      if (children[x->uuid]) return 1;
      return x->timestamp > timestamp;
    }

    void propagate_leaves(Leafset leaves)
    {
      ADT.Stack stack = ADT.Stack();
      stack->push(0);	// End sentinel.
      stack->push(this_object());

      Leafset previous = this_program::leaves;
      while (GitCommit c = stack->pop()) {
#ifdef USE_BITMASKS
	Leafset new_leaves = leaves & ~c->leaves;
	if (new_leaves) {
	  c->leaves |= new_leaves;
	  if (c->leaves == previous) {
	    c->leaves = previous;
	  } else {
	    previous = c->leaves;
	  }
	  map(map(indices(c->parents), git_commits), stack->push);
	}
#else
	Leafset new_leaves = leaves - c->leaves;
	if (sizeof(new_leaves)) {
	  c->leaves |= new_leaves;
	  map(map(indices(c->parents), git_commits), stack->push);
	}
#endif
	if (c->commit_flags & COMMIT_TRACE) {
	  werror("%O: Propagated new_leaves: %O...\n",
		 c->uuid, new_leaves);
	}
      }
    }

    void propagate_dead_leaves(Leafset dead_leaves)
    {
      ADT.Stack stack = ADT.Stack();
      stack->push(0);	// End sentinel.
      stack->push(this_object());

      while (GitCommit c = stack->pop()) {
#ifdef USE_BITMASKS
	int old = c->dead_leaves;
	c->dead_leaves |= dead_leaves;
	if (c->dead_leaves != old) {
	  map(map(indices(c->children), git_commits), stack->push);
	} else {
	  c->dead_leaves = old;
	}
#else
	int sz = sizeof(c->dead_leaves);
	c->dead_leaves |= dead_leaves;
	if (sizeof(c->dead_leaves) != sz) {
	  map(map(indices(c->children), git_commits), stack->push);
	}
#endif
	if (c->commit_flags & COMMIT_TRACE) {
	  werror("%O: Propagated dead leaves: %O...\n",
		 c->uuid, c->dead_leaves - old);
	}
      }
    }

    void rake_dead_leaves()
    {
#ifdef USE_BITMASKS
      if (dead_leaves >= 0) return;
      if (!sizeof(parents)) {
	dead_leaves = 0;
	return;
      }
#else
      if (dead_leaves) return;
      if (!sizeof(parents)) {
	dead_leaves = ([]);
	return;
      }
#endif
      array(GitCommit) ps = git_sort(map(indices(parents), git_commits));
      foreach(ps, GitCommit p) {
	p->rake_dead_leaves();
      }
      if ((sizeof(ps) == 1) && equal(ps[0]->leaves, leaves)) {
	// Common case.
	dead_leaves = ps[0]->dead_leaves;
	return;
      }
      Leafset all_leaves;
#ifndef USE_BITMASKS
      all_leaves = ([]);
#endif
      foreach(ps, GitCommit p) {
	all_leaves |= p->leaves | p->dead_leaves;
      }
      dead_leaves = all_leaves - leaves;
      if (commit_flags & COMMIT_TRACE) {
	werror("%O: Raked dead leaves: %O...\n", uuid, dead_leaves);
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
	propagate_dead_leaves(parent->dead_leaves);
      }
#else
      if (dead_leaves) {
	propagate_dead_leaves(parent->dead_leaves);
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
    void merge(GitCommit c, int(0..1)|void force)
    {
      if (!force) {
	if (message != c->message) {
	  error("Different messages: %O != %O\n", message, c->message);
	}

	if (author != c->author) {
	  error("Different authors: %O != %O\n", author, c->author);
	}
      }
      int trace_mode = (commit_flags | c->commit_flags) & COMMIT_TRACE;

      if (trace_mode) {
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

	if (trace_mode || (cc->commit_flags & COMMIT_TRACE)) {
	  werror("Detaching child %O from %O during merge of %O to %O\n",
		 cc, c, this_object(), c);
	}

	cc->detach_parent(c);
	if (cc->timestamp < timestamp) {
	  if (force) continue;
	  if (cc->timestamp + fuzz < timestamp) {
	    error("Parent: %s\n Child: %s\n",
		  pretty_git(this), pretty_git(c_uuid));
	  } else {
	    // Fudge the timestamp for the child.
	    // FIXME: Ought to propagate...
	    cc->timestamp = timestamp;
	  }
	}
	if (force &&
#ifdef USE_BITMASKS
	    (cc->leaves & dead_leaves)
#else
	    sizeof(cc->leaves & dead_leaves)
#endif
	    ) continue;
	if (cc->timestamp >= timestamp) {
	  cc->hook_parent(this);
	}
      }
      foreach(c->soft_children; string c_uuid;) {
	GitCommit cc = git_commits[c_uuid];

	if (!cc) {
	  error("Missing child to %s\n%s\n",
		pretty_git(c), pretty_git(c_uuid));
	}

	if (trace_mode || (cc->commit_flags & COMMIT_TRACE)) {
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

	if (trace_mode || (p->commit_flags & COMMIT_TRACE)) {
	  werror("Detaching parent %O from %O during merge of %O to %O\n",
		 p, c, this_object(), c);
	}

	c->detach_parent(p);
	if (p->timestamp > timestamp) {
	  if (force) continue;
	  if (p->timestamp - fuzz > timestamp) {
	    error("Parent: %s\n Child: %s\n",
		  pretty_git(p), pretty_git(this));
	  } else {
	    // Fudge the timestamp for the child.
	    // FIXME: Ought to propagate...
	    timestamp = p->timestamp;
	  }
	}
	if (force &&
#ifdef USE_BITMASKS
	    (p->dead_leaves & leaves)
#else
	    sizeof(p->dead_leaves & leaves)
#endif
	    ) continue;
	if (p->timestamp <= timestamp) {
	  hook_parent(p);
	}
      }
      foreach(c->soft_parents; string p_uuid;) {
	GitCommit p = git_commits[p_uuid];

	if (trace_mode || (p->commit_flags & COMMIT_TRACE)) {
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

      if (!force) {
	if (timestamp < c->timestamp) timestamp = c->timestamp;
	if (timestamp_low > c->timestamp_low) timestamp_low = c->timestamp_low;
      }

      if (!force) {
	// In the force case, the leaves should be propagated via
	// hook_parent() exclusively.
	propagate_leaves(c->leaves);
	if (dead_leaves != c->dead_leaves) {
	  propagate_dead_leaves(c->dead_leaves);
	}
      }

      foreach(c->revisions; string path; string rev_id) {
	string key = path + ":" + rev_id[8..];
	if (!revisions[path] ||
	    (revisions[path] < rev_id)) {
	  // Make sure deletions don't overwrite changes.
	  // This typically occurs when an RCS file has
	  // been copied (ie not renamed).
	  revisions[path] = c->revisions;
	}
	if (revision_lookup[key] == c->uuid) {
	  revision_lookup[key] = uuid;
	}
      }

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

      commit_flags &= c->commit_flags;

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

      array(string) author_info = author_lookup(this_object(), author);
      array(string) committer_info = author_lookup(this_object(),
						   committer || author);

      // Then we can start actually messing with git...
      if ((sizeof(parent_commits) == 1) &&
	  ((commit_flags & COMMIT_HIDE) ||
	   equal(parent_commits[0]->full_revision_set, full_revision_set))) {
	// Hidden commit or a noop commit, probably a tag.
	git_id = parent_commits[0]->git_id;
      } else {
#ifdef USE_BITMASKS
	// Attempt to sort the parents so that the parent that
	// is the most similar to us (leaf-wise) comes first.
	sort(parent_commits->timestamp, parent_commits);
	sort(parent_commits->leaves, parent_commits);
	sort(map(parent_commits,
		 lambda(GitCommit c) {
		   return c->leaves - c->is_leaf;
		 }), parent_commits);
#endif
	if (!message) {
	  message = "Joining branches.\n";
	} else if (catch(string tmp = utf8_to_string(message))) {
	  // Not valid UTF-8. Fall back to iso-8859-1.
	  message = string_to_utf8(message);
	}

	message += "\nID: " + uuid + "\n";
	foreach(sort(indices(revisions)), string path) {
	  message += "Rev: " + path + ":" + revisions[path][28..] + "\n";
	}
#if 0
#ifdef USE_BITMASKS
	if (commit_flags & COMMIT_TRACE) {
	  string leaf_hex = leaves->digits(16);
	  string dead_hex = dead_leaves->digits(16);
	  if (sizeof(leaf_hex) < sizeof(dead_hex)) {
	    leaf_hex = "0"*(sizeof(dead_hex) - sizeof(leaf_hex)) + leaf_hex;
	  } else {
	    dead_hex = "0"*(sizeof(leaf_hex) - sizeof(dead_hex)) + dead_hex;
	  }
	  foreach(leaf_hex/32.0, string hex) {
	    message += "Leaf-mask: 0x" + hex + "\n";
	  }
	  foreach(dead_hex/32.0, string hex) {
	    message += "Dead-mask: 0x" + hex + "\n";
	  }
	  for (Leafset remaining = leaves; remaining; ) {
	    Leafset mask = remaining & ~(remaining - 1);
	    message += "Leaf: " + leaf_lookup[mask->digits(256)] + "\n";
	    remaining -= mask;
	  }
	  for (Leafset remaining = dead_leaves; remaining; ) {
	    Leafset mask = remaining & ~(remaining - 1);
	    message += "Dead-leaf: " + leaf_lookup[mask->digits(256)] + "\n";
	    remaining -= mask;
	  }
	}
#else
	foreach(sort(indices(leaves)), string leaf) {
	  message += "Leaf: " + leaf + "\n";
	}
	foreach(sort(indices(dead_leaves)), string leaf) {
	  message += "Dead-leaf: " + leaf + "\n";
	}
#endif
#endif

	string main_leaf = leaf_lookup[(leaves & ~(leaves-1))->digits(256)];
	if (sizeof(parent_commits) && sizeof(parent_commits[0]->git_id)) {
	  // Make sure the ref is in the place we expect...
	  write("reset refs/%s\n"
		"from %s\n",
		main_leaf[..<1], parent_commits[0]->git_id);
	}
	write("# Committing %s\n"
	      "commit refs/%s\n"
	      "mark %s\n"
	      "author %s <%s> %d +0000\n"
	      "committer %s <%s> %d +0000\n"
	      "data %d\n"
	      "%s\n",
	      uuid,
	      main_leaf[..<1],
	      git_id = new_mark(),
	      author_info[0], author_info[1], timestamp,
	      committer_info[0], committer_info[1], timestamp,
	      sizeof(message),
	      message);
	if (sizeof(parent_commits) && sizeof(parent_commits[0]->git_id)) {
	  write("from %s\n", parent_commits[0]->git_id);
	  git_state = parent_commits[0]->full_revision_set + ([]);
	  foreach(parent_commits[1..], GitCommit p) {
	    if (sizeof(p->git_id)) {
	      write("merge %s\n", p->git_id);
	    }
	  }
	  if (!sizeof(git_state)) {
	    // The parent is probably a fake commit masking
	    // the set of files. Make sure to clear the state.
	    write("deleteall\n");
	  }
	} else {
	  write("deleteall\n");
	  git_state = ([]);
	}

	// werror("Generating commit for %s\n", pretty_git(this_object(), 1));
	array(string) index_info = ({});

	// Remove files from the git index that we don't want anymore.
	foreach(git_state; string path; string rev_info) {
	  if (full_revision_set[path] == rev_info) continue;
	  if (!full_revision_set[path] ||
	      has_suffix(full_revision_set[path], "(DEAD)")) {
	    write("D %s\n", path);
	    m_delete(git_state, path);
	  }
	}

	// Add the blobs for the revisions to the git index.
	foreach(full_revision_set; string path; string rev_info) {
	  if (git_state[path] == rev_info) continue;
	  string sha = rev_info[8..27];
	  if (!has_suffix(rev_info, "(DEAD)") &&
	      (sha != "\0"*20)) {
	    int mode = 0100644;
	    int raw_mode;
	    sscanf(rev_info[4..7], "%4c", raw_mode);
	    if (raw_mode & 0111) mode |= 0111;
	    write("M %6o %s %s\n", 
		  mode, git_blobs[sha], path);
	    git_state[path] = rev_info;
	  }
	}

	// End marker (compat with old fast-import).
	write("\n");
      }
      Leafset remaining = leaves;
      remaining -= leaves & ~(leaves-1); // Already updated.
      // Skip leaves that our children hold.
      foreach(map(indices(children), git_commits), GitCommit c) {
	remaining &= ~c->leaves;
      }
      if (remaining) {
	write("# Updating tags...\n");
	while (remaining) {
	  int mask = remaining & ~(remaining-1);
	  string leaf = leaf_lookup[mask->digits(256)][..<1];
	  if (git_refs[leaf]) {
	    write("reset refs/%s\n"
		  "from %s\n",
		  leaf, git_id);
	  }
	  remaining -= mask;
	}
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

#define TRACE_MSG(GC1, GC2, MSG ...) do {			\
    if ((((GC1) && ((GC1)->commit_flags)) |			\
	 ((GC2) && ((GC2)->commit_flags))) & COMMIT_TRACE) {	\
      werror(MSG);						\
    }								\
  } while(0)

  int num_roots;
#ifdef USE_BITMASKS
  Leafset root_commits;
#else
  Leafset root_commits = ([]);
#endif

  void set_master_branch(string master)
  {
    master_branch = master;
    master = "heads/" + master;
    GitCommit m = git_refs[master];
    if (!m) {
      m = git_refs[master] = GitCommit(master);
    }
    if (!master_branches[master]) {
      master_branches[master] = 1;
      Leafset roots = root_commits;
#ifdef USE_BITMASKS
      while(roots) {
	Leafset mask = roots & ~(roots - 1);
	GitCommit r = git_commits[leaf_lookup[mask->digits(256)]];
	m->hook_parent(r);
	roots -= mask;
      }
#else
      foreach(map(indices(roots), git_commits), GitCommit r) {
	m->hook_parent(r);
      }
#endif
    }
  }

  void add_root_commit(string git_id)
  {
    GitCommit root_commit =
      GitCommit("ROOTS/" + (num_roots++) + "/" + git_id);

    // This is somewhat magic...
    // Since the root commits are older than all existing commits,
    // and are compatible with all other leaves, they will automatically
    // be hooked as parents to the relevant nodes during the graphing.

    // Ensure that files aren't propagated between archives...
    root_commit->full_revision_set = ([]);
    // Ensure that the root commits won't be merged to each other...
    root_commit->dead_leaves = root_commits;
    root_commits |= root_commit->is_leaf;
    if (GitCommit head = (git_refs[git_id] || git_refs["heads/" + git_id])) {
      // Copy stuff from the existing branch (since it might move...).
      root_commit->git_id = head->git_id;
      root_commit->timestamp = head->timestamp;
      foreach(map(indices(head->parents), git_commits), GitCommit p) {
	root_commit->hook_parent(p);
      }
    } else {
      root_commit->git_id = git_id;
      root_commit->timestamp = -0x7fffffff;
    }
    if (master_branch) {
      // Make sure the root is compatible with the current master branch.
      if (!git_refs["heads/" + master_branch]) {
	git_refs["heads/" + master_branch] = GitCommit("heads/" + master_branch);
      }
      git_refs["heads/" + master_branch]->hook_parent(root_commit);
    }
  }

  GitCommit commit_factory(string path, RCSFile.Revision|string rev,
			   int|void mode, int|void no_create)
  {
    string r = stringp(rev)?rev:rev->revision;
    // Check if the handler wants to hide this revision.
    int kill_revision;
    if (handler && handler->hide_rcs_revision &&
	((kill_revision =
	  handler->hide_rcs_revision(this_object(), path, r)) == 1)) {
      return UNDEFINED;
    }

    if (stringp(rev)) {
      path += ":";
      GitCommit found;
      int found_cnt = -1;
      foreach(revision_lookup; string rev_id; string uuid) {
	if (!has_prefix(rev_id, path) ||
	    !has_suffix(uuid, ":" + r)) continue;
	GitCommit c = git_commits[uuid];
	if (found) {
	  int cnt = -1;
	  sscanf(uuid, path + "%d:" + rev, cnt);
	  if (cnt > found_cnt) {
	    found = c;
	    found_cnt = cnt;
	  }
	} else {
	  found = c;
	  sscanf(uuid, path + "%d:" + rev, found_cnt);
	}
      }
      // Fallback, and handling of rev == "DEAD".
      if (!found) found = git_commits[path + rev];
      if (found || no_create) return found;
      error("Creating new revisions in blanco is not supported here.\n");
    }

    string rev_id;
    if ((rev->state == "dead") || kill_revision) {
      kill_revision = 1;
      rev_id = sprintf("%4c%4c%s%s(DEAD)", rev->time->unix_time(), 0,
		       "\0"*20, rev->revision);
    } else {
      // Ensure a valid file mode for git.
      if (mode & 0111) {
	mode = 0100755;
      } else {
	mode = 0100644;
      }
      rev_id = sprintf("%04c%4c%s%s", rev->time->unix_time(), mode,
			rev->sha, rev->revision);
    }

    // NB: We don't care about modification time or mode bits in the lookup.
    string uuid = revision_lookup[path + ":" + rev_id[8..]];
    if (uuid) {
      GitCommit c = git_commits[uuid];
      if ((c->author == rev->author) && (c->committer == rev->author) &&
	  (c->message == rev->log) &&
	  (c->timestamp == rev->time->unix_time()) &&
	  (c->timestamp_low == rev->time->unix_time()) &&
	  (c->revisions[path] == rev_id)) {
	return c;
      }
    }

    if (no_create) return UNDEFINED;

    uuid = path + ":" + rev->revision;
    int cnt;
    while (git_commits[uuid]) {
      uuid = path + ":" + cnt++ + ":" + rev->revision;
    }

    GitCommit commit = GitCommit(path, rev->revision, uuid);
    revision_lookup[path + ":" + rev_id[8..]] = uuid;

    commit->timestamp = commit->timestamp_low = rev->time->unix_time();
    commit->revisions[path] = rev_id;
    commit->author = commit->committer = rev->author;
    commit->message = rev->log;
    if (kill_revision || (rev->state == "dead")) {
      // The handler wants this revision dead.
      commit->commit_flags |= COMMIT_DEAD;
    }

    if (rev->is_fake_revision && (rev->state != "dead")) {
      // The set of leaves may lack some tags. Make sure we don't
      // get excessive dead leaves.
      //
      // But make sure not to propagate tags from live revisions to dead...
      commit->commit_flags |= COMMIT_FAKE;
    }

    if (handler && handler->living_dead) {
      handler->living_dead(this_object(), path, rev->revision, commit);
    }

    return commit;
  }

  void init_git_branch(string tag, string branch_rev,
		       string rcs_rev, RCSFile rcs_file, int mode,
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
    } else if (!rcs_rev) {
      rcs_rev = rcs_file->head;
    }
    string prev_revision;
    while (rcs_rev) {
      RCSFile.Revision rev = rcs_file->revisions[rcs_rev];

      if (!rev) {
	error("Unknown revision: %O\n", rcs_rev);
      }

      string path = rev->path;

      if (path) {
	// Check for rename.
	if (prev_revision && !prev_commit->revisions[path]) {
	  // The file was renamed with the previous commit.
	  prev_commit->revisions[path] =
	    sprintf("%4c%4c%20s%s(DEAD)",
		    prev_commit->timestamp, 0, "\0"*20, prev_revision);
	}

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

	commit = commit_factory(path, rev, mode);

	if (commit) {
	  rcs_commits[rcs_rev] = commit;
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

	  if (sizeof(commit->parents)) {
	    // The factory found us an existing commit with a history.
	    // Let's keep it that way...
	    break;
	  }

	  if ((rcs_rev == "1.1") && rcs_file->revisions["1.1.1.1"] &&
	      (rev->log == "Initial revision\n") &&
	      (rcs_file->revisions["1.1.1.1"]->rcs_text == "")) {
	    // This is the automatic commit from running cvs import.
	    // Hide it.
	    commit->commit_flags |= COMMIT_HIDE;
	  }

	  prev_commit = commit;
	  prev_revision = rcs_rev;
	}
      }

      rcs_rev = rev->ancestor;
    }
    //werror("\n");
#ifdef GIT_VERIFY
    verify_git_commits(1);
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
		   "   Dead-Leaves: %{%O, %}\n"
		   "   Revisions: %O\n"
		   "*/)",
		   c->uuid, ctime(c->timestamp) - "\n",
		   c->author, c->message,
		   indices(c->parents), indices(c->children),
#ifdef USE_BITMASKS
		   ({ c->leaves }),
		   ({ c->dead_leaves }),
#else
		   (skip_leaves?({sizeof(c->leaves)}):indices(c->leaves)),
		   (skip_leaves?({sizeof(c->dead_leaves)}):indices(c->dead_leaves)),
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

  void verify_git_commits(int|void ignore_times)
  {
    //#ifdef GIT_VERIFY
    //werror("Verifying...");
    foreach(git_commits; string uuid; GitCommit c) {
      if (!c) error("Destructed commit %O in git_commits.\n", uuid);
      if (c->uuid != uuid) error("Invalid uuid %O != %O.\n%s\n",
				 uuid, c->uuid, pretty_git(c));
#ifdef USE_BITMASKS
      Leafset leaves;
      Leafset dead_leaves;
#else
      Leafset leaves = ([]);
      Leafset dead_leaves = ([]);
#endif
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
	if (!ignore_times && (p->timestamp > c->timestamp + fuzz))
	  error("Parent %O is more recent than %O.\n"
		"Parent: %s\n"
		"Child: %s",
		p_uuid, uuid,
		pretty_git(p), pretty_git(c));
	dead_leaves |= p->dead_leaves;
      }

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
	if (!ignore_times && (p->timestamp + fuzz < c->timestamp))
	  error("Child %O is older than %O.\n"
		"Child: %s\n"
		"Parent: %s\n",
		p_uuid, uuid,
		pretty_git(p), pretty_git(c));
	leaves |= p->leaves;
      }
      if (!equal(leaves, c->leaves))
	error("The set of leaves for %O is invalid.\n"
	      "Got %O, expected %O.\n"
	      "%s\n"
	      "Children:\n"
	      "%{%s\n%}",
	      uuid, c->leaves, leaves, pretty_git(c),
	      map(indices(c->children), pretty_git));
#ifdef USE_BITMASKS
      dead_leaves &= ~leaves;
      if (c->leaves & c->dead_leaves)
	error("The set of leaves and set of dead leaves for %O intersect.\n"
	      "%s\n",
	      uuid, pretty_git(c));
#else
      dead_leaves -= leaves;
      if (sizeof(c->leaves - c->dead_leaves))
	error("The set of leaves and set of dead leaves for %O intersect.\n"
	      "%s\n",
	      uuid, pretty_git(c));
#endif
      if (!equal(dead_leaves, c->dead_leaves & dead_leaves))
	error("Some dead leaves are missing from %O.\n"
	      "%s\n",
	      uuid, pretty_git(c));
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

  void fix_git_ts(GitCommit r, int margin)
  {
    int ts = -0x7fffffff;
    string a;
    foreach(r->parents; string p_uuid;) {
      GitCommit p = git_commits[p_uuid];
      if (p->timestamp == 0x7ffffffe) fix_git_ts(p, margin);
      if (ts < p->timestamp) {
	ts = p->timestamp;
	a = p->author;
      }
    }

    // Make sure we have some margin...
    r->timestamp = r->timestamp_low = ts + margin;
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
      } else if (sizeof(res) && sizeof(frag) &&
		 (res[-1] == 'E') &&
		 ((sizeof(res) == 1) ||
		  (res[-2] >= '0') && (res[-2] <= '9')) &&
		 (frag[0] >= '0') && (frag[0] <= '9')) {
	// Exponential notation. This is used by ulpc.
	// FIXME: Move this case to handler?
	res += "-" + frag;
      } else {
	res += "_" + frag;
      }
    }
    return res;
  }

  //! Mapping from tagname to mapping from uuid to 1.
  //!
  //! Contains the tags that tag initial vendor branch commits.
  mapping(string:mapping(string:int)) starters = ([]);

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

  void add_rcs_file(string path, RCSFile rcs_file, int mode, Flags|void flags)
  {
    if (handler && handler->repair_rcs_file) {
      handler->repair_rcs_file(this_object(), path, rcs_file, flags);
    }

    if (!(flags & FLAG_PRETEND)) {
      foreach(rcs_file->revisions; string r; RCSFile.Revision rev) {
	if (rev->state == "dead") {
	  rev->sha = "\0"*20;
	  continue;
	}
	string data = rcs_file->get_contents_for_revision(rev);
	if (!git_blobs[rev->sha]) {
	  write("# %s\n"
		"# %s:%s\n"
		"blob\n"
		"mark %s\n"
		"data %d\n"
		"%s\n",
		rcs_file->rcs_file_name, path, r,
		git_blobs[rev->sha] = new_mark(),
		sizeof(data), data);
	}
      }
      // Cleanup the memory use...
      foreach(rcs_file->revisions; string r; RCSFile.Revision rev) {
	if (rev->revision == rcs_file->head) continue;
	rev->text = UNDEFINED;
      }
    }
    mapping(string:GitCommit) rcs_commits = ([]);

    if (!master_branch) {
      set_master_branch("master");
    }

    init_git_branch("heads/" + master_branch, UNDEFINED,
		    UNDEFINED, rcs_file, mode, rcs_commits);
    foreach(rcs_file->tags; string tag; string tag_rev) {
      tag = fix_cvs_tag(tag);

      if (tag_rev == "1.1.1.1") {
	// This might be the automatic vendor branch tag.
	// We handle it later, see below.
	if (!rcs_commits["1.1.1.1"]) {
	  init_git_branch(UNDEFINED, UNDEFINED, "1.1.1.1",
			  rcs_file, mode, rcs_commits);
	  if (!rcs_commits["1.1.1.1"]) {
	    // Hidden.
	    continue;
	  }
	}
	if (!starters[tag]) {
	  starters[tag] = ([ rcs_commits["1.1.1.1"]->uuid:1 ]);
	} else {
	  starters[tag][rcs_commits["1.1.1.1"]->uuid] = 1;
	}
	continue;
      }

      if (rcs_file->symbol_is_branch(tag_rev)) {
	tag_rev = (tag_rev/"." - ({"0"})) * ".";
      }
      string rcs_rev;
      if ((rcs_rev = rcs_file->branch_heads[tag_rev])) {
	init_git_branch("heads/" + tag, tag_rev,
			rcs_rev, rcs_file, mode, rcs_commits);
      } else if (!handler || !handler->hide_rcs_revision ||
		 handler->hide_rcs_revision(this_object(), path, tag_rev)!=1) {
	init_git_branch("tags/" + tag, UNDEFINED,
			tag_rev, rcs_file, mode, rcs_commits);
      }
    }

    // Time to handle vendor branches.
    if (rcs_file->branch) {
      // A (vendor) branch is acting as the main branch.
      init_git_branch("heads/" + master_branch, rcs_file->branch,
		      rcs_file->branch_heads[rcs_file->branch],
		      rcs_file, mode, rcs_commits);      
    }
    // Check if there are any vendor branches. We assume that the
    // first commit on the main branch after a commit on the vendor
    // branch merges the changes of both branches.
    foreach(rcs_file->tags; string tag; string tag_rev) {
      array(string) rev_nos = (tag_rev/".") - ({ "0" });
      if (!(sizeof(rev_nos) & 1) ||
	  !(rev_nos[-1][-1] & 1)) {
	// Not a branch or not a vendor branch.
	continue;
      }
      tag = fix_cvs_tag(tag);

      // Find the branch that was branched from.
      string branch_branch = rev_nos[..<2]*".";

      // The head of the main branch.
      string main_head =
	rcs_file->branch_heads[branch_branch] || rcs_file->head;

      string vendor_head = rcs_file->branch_heads[rev_nos*"."];

      // For each revision on the vendor branch,
      // find its merge point (if any).
      // We don't care about excessive parent links,
      // since they will be consolidated by the later
      // passes.
      // Note however that since we introduce merges,
      // the sorting code must be aware that there
      // may be more than one path from the root to
      // a commit.

      RCSFile.Revision main_rev = rcs_file->revisions[main_head];

      while (vendor_head) {
	RCSFile.Revision vendor_rev;
	do {
	  vendor_rev = rcs_file->revisions[vendor_head];
	  if (!vendor_rev) break;
	  vendor_head = vendor_rev->ancestor;
	} while (vendor_rev->time >= main_rev->time);
	if (!vendor_rev || !rcs_commits[vendor_rev->revision] ||
	    (vendor_rev->revision == main_rev->ancestor)) break;
	while (rcs_file->revisions[main_rev->ancestor] &&
	       (rcs_file->revisions[main_rev->ancestor]->time >
		vendor_rev->time)) {
	  main_rev = rcs_file->revisions[main_rev->ancestor];
	}
	if (!rcs_commits[main_rev->revision]) break;
	rcs_commits[main_rev->revision]->
	  hook_parent(rcs_commits[vendor_rev->revision]);
      }
    }

    // Identify merges.
    if (flags & FLAG_DETECT_MERGES) {
      this_program::detect_merges(rcs_file, rcs_commits);
    }
  }

  //! Contract the node with all its (non-root) ancestors.
  //!
  //! This operation is typically done when splicing together
  //! different histories.
  //!
  //! Root commits are left as is, since they presumably
  //! already exist in the destination git repository.
  //!
  //! @note
  //!   This operation also sets the full_revision_set for the node.
  void contract_ancestors(GitCommit node)
  {
    if (node->git_id) {
      // Not supported for nodes present in the git repository.
      return;
    }
    ADT.Heap ancestors = ADT.Heap();
    ancestors->push(node);
    mapping(string:string) rev_set = node->full_revision_set = ([]);
    mapping(string:int) visited = ([]);
    while (sizeof(ancestors)) {
      // Note: The comparison functions in the GitCommits makes the
      //       most recent commit appear at the head of the heap.
      GitCommit ancestor = ancestors->pop();
      if (visited[ancestor->uuid]) continue;
      visited[ancestor->uuid] = 1;
      if (ancestor->git_id) {
	node->hook_parent(ancestor);
	foreach(ancestor->full_revision_set; string path; string rev_info) {
	  if (!rev_set[path] || (rev_set[path] < rev_info)) {
	    rev_set[path] = rev_info;
	  }
	}
	continue;
      }
      foreach(ancestor->revisions; string path; string rev_info) {
	if (!rev_set[path] || (rev_set[path] < rev_info)) {
	  rev_set[path] = rev_info;
	}
      }
      foreach(git_sort(map(indices(ancestor->parents), git_commits)),
	      GitCommit p) {
	ancestors->push(p);
	if ((ancestor == node) || !sizeof(ancestor->children)) {
	  ancestor->detach_parent(p);
	}
      }
      if ((ancestor != node) && !sizeof(ancestor->children)) {
	// The ancestor is obsolete.
	foreach(git_sort(map(indices(ancestor->soft_parents), git_commits)),
		GitCommit p) {
	  ancestor->detach_soft_parent(p);
	}
	foreach(git_sort(map(indices(ancestor->soft_children), git_commits)),
		GitCommit c) {
	  c->detach_soft_parent(ancestor);
	}
	if (ancestor->is_leaf) {
	  foreach(git_refs; string ref; GitCommit r) {
	    if (r == ancestor) {
	      m_delete(git_refs, ref);
	    }
	  }
	}
	m_delete(git_commits, ancestor->uuid);
      }
    }
  }

  void read_rcs_repository(string repository, Flags|void flags, string|void path)
  {
    array(string) files = sort(get_dir(repository));
    path = path || "";
    string orig_path = path;
    mapping handler_state = ([]);
    if (handler && handler->enter_directory) {
      [path, files] =
	handler->enter_directory(this_object(), orig_path, files, flags,
				 handler_state);
    }
    foreach(files, string fname) {
      string fpath = repository + "/" + fname;
      string subpath = path;
      if (Stdio.is_dir(fpath)) {
	if ((fname != "Attic") && (fname != "RCS")) {
	  if (subpath != "")
	    subpath += "/" + fname;
	  else
	    subpath = fname;
	}
	read_rcs_repository(fpath, flags, subpath);
      } else if (has_suffix(fname, ",v")) {
	if (subpath != "")
	  subpath += "/" + fname[..sizeof(fname)-3];
	else
	  subpath = fname[..sizeof(fname)-3];
	progress(flags, "\r%d: %-65s ", sizeof(git_commits), subpath[<64..]);
	add_rcs_file(subpath, RCSFile(fpath, subpath),
		     file_stat(fpath)->mode, flags);
      } else {
	progress(flags, "\n");
	werror("Warning: Skipping %s.\n", fpath);
      }
    }
    if (handler && handler->leave_directory) {
      handler->leave_directory(this_object(), orig_path, files, flags,
			       handler_state);
    }
  }

  void init_git_commits(mapping(string:RCSFile) rcs_files, Flags|void flags)
  {
    progress(flags, "Initializing Git commmit tree from RCS...\n");
    int cnt;
    foreach(sort(indices(rcs_files)), string path) {
      RCSFile rcs_file = rcs_files[path];
      progress(flags, "\r%d:(%d): %-55s ",
	       sizeof(rcs_files) - cnt++, sizeof(git_commits), path[<54..]);
      add_rcs_file(path, rcs_file, flags);
    }
    progress(flags, "\n");

    if (handler && handler->add_rcs_files) {
      handler->add_rcs_files(this_object(), rcs_files, flags);
    }
  }

  void rake_leaves(Flags flags)
  {
    // All repositories have been loaded.
    // Now we can handle the automatic vendor branch tag.
    foreach(starters; string tag; mapping(string:int) members) {
      GitCommit start = git_refs["tags/" + tag];
      if (start) {
	// Apparently the tag has been used for other purposes
	// than the automatic vendor branch tag. Add back any stuff
	// we've kept in starters.
	foreach(git_sort(map(indices(members), git_commits)), GitCommit c) {
	  start->hook_parent(c);
	}
      } else {
	// An automatic vendor branch tag. It's not useful in a git
	// context as is, since it may show up at several points in time.
	// We move it to the earliest commit that had it to begin with.
	start = git_refs["tags/" + tag] = GitCommit("tags/" + tag);
	start->hook_parent(git_sort(map(indices(members), git_commits))[0]);
      }
    }
    starters = ([]);

    foreach(git_refs;; GitCommit r) {
      // Fix the timestamp for the ref.
      fix_git_ts(r, fuzz*16);
    }

    int cnt;
    int i;

    progress(flags, "Raking dead leaves...\n");
    // Collect the dead leaves.
    foreach(git_sort(values(git_commits)), GitCommit c) {
      i++;
      if (!(cnt--)) {
	cnt = 100;
	progress(flags, "\r%d(%d): %-60s  ",
		 sizeof(git_commits) - i, sizeof(git_commits), c->uuid[<59..]);
      }
      c->rake_dead_leaves();
    }
    progress(flags, "\n");
    foreach(git_sort(values(git_commits)), GitCommit c) {
      if (c->commit_flags & COMMIT_FAKE) {
	// Too many dead leaves accumulate at the fake nodes,
	// since they contain a subset of their proper leaves.
	// Recalculate with a minimum set.
	Leafset dead_leaves;
#ifndef USE_BITMASKS
	dead_leaves = ([]);
#endif
	foreach(map(indices(c->parents), git_commits), GitCommit p) {
	  dead_leaves |= p->dead_leaves;
	}
	c->dead_leaves = dead_leaves;
      }
    }

    if (handler && handler->rake_leaves) {
      // Hook for custom handling of leaves and dead leaves.
      progress(flags, "Raking leaves some more...\n");
      handler->rake_leaves(this_object());
    }

    i = 0;
    cnt = 0;

    if (sizeof(master_branches) > 1) {
      // Make sure the master branches don't tangle into each other.
      progress(flags, "Untangling branches...\n");
      array(GitCommit) branches =
	git_sort(map(indices(master_branches), git_refs));
      Leafset mask;
#ifndef USE_BITMASKS
      mask = ([]);
#endif
      foreach(branches, GitCommit b) {
	mask |= b->is_leaf;
      }
      // We attach dead leaves to the root commits that lack them.
      foreach(values(git_commits), GitCommit c) {
	i++;
	if (!(cnt--)) {
	  cnt = 100;
	  progress(flags, "\r%d(%d): %-60s  ",
		   sizeof(git_commits) - i, sizeof(git_commits), c->uuid[<59..]);
	}
 	if (sizeof(c->parents)) continue;
	// Note: the root commits don't have any dead leaves.
	if (!equal(c->leaves & mask, mask)) {
	  Leafset missing_dead = mask - (c->leaves & mask);
	  c->propagate_dead_leaves(missing_dead);
	}
      }
      progress(flags, "\n");
    }
  }

  array(GitCommit) sorted_commits;

  void verify_sorted_commits(Flags|void flags)
  {
    progress(flags, "Verifying commit tables...\n");
    mapping(string:int) index_lookup =
      mkmapping(sorted_commits->uuid, indices(sorted_commits));
    foreach(sorted_commits; int i; GitCommit c) {
      foreach(c->parents; string uuid; ) {
	if (index_lookup[uuid] >= i) {
	  error("Invalid parent-child relation for %O vs %O: %O >= %O\n",
		git_commits[uuid], c, index_lookup[uuid], i);
	}
      }
      foreach(c->children; string uuid; ) {
	if (index_lookup[uuid] <= i) {
	  error("Invalid parent-child relation for %O vs %O: %O >= %O\n",
		c, git_commits[uuid], i, index_lookup[uuid]);
	}
      }
    }
  }

  int bump_timestamps(Flags|void flags)
  {
    progress(flags, "Bumping timestamps...\n");

    int margin;

    int i;
    int cnt;

    // FIXME: This isn't 100% safe, since we aren't sure the timestamps
    //        are correct, but as long as out-of-order commits aren't
    //        common, it should be safe enough.
    foreach(git_sort(values(git_commits)), GitCommit r) {
      i++;
      if (!(cnt--)) {
	cnt = 100;
	progress(flags, "\r%d(%d): %-60s  ",
		 sizeof(git_commits) - i, sizeof(git_commits), r->uuid[<59..]);
      }
      // Ensure that the commit timestamp order is valid.
      int ts = r->timestamp;
      foreach(git_sort(map(indices(r->parents), git_commits)), GitCommit p) {
	if (p->timestamp > ts) {
	  ts = p->timestamp;
	}
      }
      if (ts != r->timestamp) {
	r->time_offset += ts - r->timestamp;
	r->timestamp = ts;
      }
      if (r->time_offset > margin) margin = r->time_offset;
    }
    progress(flags, "\n");

    return margin;
  }

  void unify_git_commits(Flags|void flags)
  {
    int margin = bump_timestamps(flags);

    progress(flags, "Verifying initial state...\n");
 
    verify_git_commits();

    // First perform a total ordering that is compatible with the
    // parent-child partial order and the commit timestamp order.

    progress(flags, "Sorting...\n");
    ADT.Stack commit_stack = ADT.Stack();
    sorted_commits = allocate(sizeof(git_commits));
    mapping(string:int) added_commits = ([]);

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
      if (!added_commits[c->uuid]) {
	sorted_commits[i++] = c;
	added_commits[c->uuid] = 1;
	foreach(reverse(git_sort(map(indices(c->children), git_commits))),
		GitCommit cc) {
	  commit_stack->push(cc);
	}
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

    verify_sorted_commits(flags);

    int cnt;

    // Then we merge the nodes that are mergeable.
    // FIXME: This is probably broken; consider the case
    //        A ==> B ==> C merged with B ==> C ==> A
    //        merged with C ==> A ==> B in a fuzz timespan.
    progress(flags, "Merging...\n");

    if (handler && handler->force_merges) {
      handler->force_merges(this_object());
    }

    margin += fuzz;

    for (i = 0; i < sizeof(sorted_commits); i++) {
      GitCommit c = sorted_commits[i];
      if (!c) {
	// Probably destructed by a forced merge.
	// Get rid of the object.
	sorted_commits[i] = 0;
	continue;
      }
      if (c->time_offset) {
	// Undo the timestamp bumping.
	c->timestamp -= c->time_offset;
	c->time_offset = 0;
      }
      for (int j = i; j--;) {
	GitCommit p = sorted_commits[j];
	if (!p) continue;
	if (c->timestamp >= p->timestamp + fuzz) {
	  if (c->timestamp >= p->timestamp + margin) {
	    break;
	  }
	  // There might be some node beyond this one within fuzz time.
	  continue;
	}
	// Don't go past our children...
	if (p->children[c->uuid]) break;
	if (!(cnt--)) {
	  cnt = 0;
	  progress(flags, "\r%d:%d(%d): %-55s  ",
		   sizeof(sorted_commits) - i, j,
		   sizeof(git_commits), p->uuid[<54..]);
	}
	// Check if the sets of leaves are compatible.
#ifdef USE_BITMASKS
	if (c->leaves & p->dead_leaves) continue;
	if (p->leaves & c->dead_leaves) continue;
#else
	if (sizeof(c->leaves & p->dead_leaves)) continue;
	if (sizeof(p->leaves & c->dead_leaves)) continue;
#endif
	// p is compatible with c.
	if ((c->timestamp < p->timestamp + fuzz) &&
	    !p->children[c->uuid] &&
	    (p->author == c->author) &&
	    (p->message == c->message)) {
	  // Close enough in time for merge...
	  // c isn't a child of p.
	  // and the relevant fields are compatible.

	  // Check that none of c->parents is a child to p,
	  // and that none of c->children is a parent to p.
	  // We hope that there aren't any larger commit loops...
	  if (!sizeof(c->parents & p->children) &&
	      !sizeof(c->children & p->parents)) {
	    p->merge(c);
	    sorted_commits[i] = 0;
	    c = p;
	  }
	}
      }
    }

    progress(flags, "\n");

    progress(flags, "Adjusting tags...\n");

    foreach(sorted_commits; int i; GitCommit r) {
      if (!r) continue;
      // Fix the timestamp for the ref.
      if (!r->message) {
	// Just a minimal margin needed now.
	fix_git_ts(r, 1);
      }
    }

    sorted_commits -= ({ 0 });

    bump_timestamps(flags);

    // Note: Due to the merging and the changed commit timestamps,
    //       some of the commits may have come out of order.
    sort(sorted_commits->timestamp, sorted_commits);

    verify_sorted_commits(flags);
  }

  // Attempt to unify as many commits as possible given
  // the following invariants:
  //
  //   * The set of reachable leaves from a commit containing a revision.
  //   * The commit order must be maintained (ie a node may not reparent
  //     one of its parents).
  void graph_git_commits(Flags|void flags)
  {
    unify_git_commits(flags);

    int cnt;
    int i;

    // FIXME: By looping on most recent first, it ought to be possible
    //        to unify the resurrection and the graphing passes.
    // Note however that then the reduction of tag commits will have
    // to be done in a separate pass.

    // To reduce strange behaviour on behalf of fully dead commits, we
    // first scan for their closest child. This will give it some leaves
    // to reduce excessive adding of merge links.
    // Note: This is O(n²)!
    progress(flags, "Resurrecting dead nodes...\n");
    for (i = 0; i < sizeof(sorted_commits); i++) {
      GitCommit p = sorted_commits[i];
      if (!p || !(p->commit_flags & COMMIT_DEAD)) continue;

      // Check if we should trace...
      int trace_mode = (p->commit_flags & COMMIT_TRACE)
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

      int k = 10;	// Maximum number of children to add.
      for (int j = i+1; j < sizeof(sorted_commits); j++) {
	GitCommit c = sorted_commits[j];
	if (!c) continue;
	if (!(cnt--) || trace_mode) {
	  cnt = 99;
	  progress(flags, "\r%d:%d(%d): %-55s  ",
		   i, j, sizeof(git_commits), p->uuid[<54..]);
	  if (trace_mode) werror("\n");
	}
	// Check if all of c's leaves are compatible with p.
#ifdef USE_BITMASKS
	if (c->leaves & p->dead_leaves) {
	  if (trace_mode) {
	    werror("%O(%d) is not valid as a parent.\n"
		   "  Conflicting leaves: %O\n",
		   p, j, c->leaves & p->dead_leaves);
	  }
	  continue;
	}
#else
	if (sizeof(c->leaves & p->dead_leaves)) {
	  if (trace_mode) {
	    werror("%O(%d) is not valid as a parent.\n"
		   "  Conflicting leaves: %O\n",
		   p, j, c->leaves & p->dead_leaves);
	  }
	  continue;
	}
#endif
	// p is compatible with c.

	if (trace_mode) {
	  werror("Hooking %O(%d) as a parent to %O(%d)...\n", p, j, c, i);
	}

	// Make c a child to p.
	c->hook_parent(p);

	if (!--k) break;
      }

      if (p && (p->uuid == termination_uuid)) {
	break;
      }
    }

    cnt = 0;
    // Now we can generate a DAG by traversing from the root toward the leaves.
    // Note: This is O(n²)! But since we utilize information in the ancestor
    //       sets, it's usually quite fast.
    progress(flags, "\nGraphing...\n");
    array(IntRanges) ancestor_sets =
      allocate(sizeof(sorted_commits), IntRanges)();
    mapping(string:int) parent_id_lookup =
      mkmapping(sorted_commits->uuid, indices(sorted_commits));
    for (i = 0; i < sizeof(sorted_commits); i++) {
      GitCommit c = sorted_commits[i];
      if (!c) continue;
      mapping(string:int) orig_parents = c->parents;
      IntRanges ancestors = ancestor_sets[i];

      if (c->time_offset) {
	// Undo any timestamp bumping.
	c->timestamp -= c->time_offset;
	c->time_offset = 0;
      }

      // Check if we should trace...
      int trace_mode = (c->commit_flags & COMMIT_TRACE)
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
	// Note: One of the parents may have been a tag,
	//       which has performed a merge in the similar
	//       code futher below. In which case it hasn't
	//       propagated to its children (since they were
	//       cleared above). orig_parents may thus
	//       contain nonexistant git commits.
	array(GitCommit) parents =
	  git_sort(map(indices(orig_parents), git_commits));
	if (sizeof(parents)) {
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
      }
#endif

      // We'll rebuild this...
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
	// Check if all of c's leaves are compatible with p.
#ifdef USE_BITMASKS
	if (c->leaves & p->dead_leaves) {
	  if (trace_mode) {
	    werror("%O(%d) is not valid as a parent.\n"
		   "  Conflicting leaves: %O\n",
		   p, j, c->leaves & p->dead_leaves);
	  }
	  continue;
	}
#else
	if (sizeof(c->leaves & p->dead_leaves)) {
	  if (trace_mode) {
	    werror("%O(%d) is not valid as a parent.\n"
		   "  Conflicting leaves: %O\n",
		   p, j, c->leaves & p->dead_leaves);
	  }
	  continue;
	}
#endif
	// p is compatible with c.
#if 0
	if ((c->timestamp < p->timestamp + fuzz) &&
	    !orig_parents[p->uuid]) {
	  // Close enough in time for merge...
	  // c doesn't have to be a child of p.
	  if ((p->author == c->author) &&
	      (p->message == c->message)) {
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
	    // Check if the sets of leaves are compatible.
#ifdef USE_BITMASKS
	    if (c->leaves & t->dead_leaves) continue;
#else
	    if (sizeof(c->leaves & t->dead_leaves)) continue;
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
		 p, j, c, i, ancestors->ranges/2, ancestor_sets[j]?ancestor_sets[j]->ranges/2:({}));
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

	// If we have the same set of leaves as our (new) parent, then we
	// won't find any further parents that aren't already ancestors to p.
	if (equal(c->leaves, p->leaves)) {
	  if (trace_mode) {
	    werror("  Same set of leaves as parent ==> early termination.\n");
	  }
	  break;
	}
      }

      // This will be rebuilt...
      // We've kept it around to make sure that dead leaves propagate properly.
      c->children = ([]);
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
      if (c) {
	foreach(map(indices(c->parents), git_commits), GitCommit p) {
	  // If we have the same set of dead leaves as our parent,
	  // then the algorithm will always select us before our parent,
	  // so there's no need to keep our parents ancestor set around
	  // anymore.
	  // Note: We need to delay this until after the merging of leafs
	  //       onto the stem.
	  if (equal(c->dead_leaves, p->dead_leaves)) {
	    if (trace_mode) {
	      werror("  zapped ancestors for %d (%O)\n",
		     parent_id_lookup[p->uuid], p);
	    }
	    ancestor_sets[parent_id_lookup[p->uuid]] = UNDEFINED;
	  }
	}

	if (c->uuid == termination_uuid) {
	  break;
	}
      }
    }
    ancestor_sets = UNDEFINED;
    parent_id_lookup = UNDEFINED;
    sorted_commits -= ({ 0 });

    progress(flags, "\nDone\n");

    // exit(0);

    verify_git_commits(1);
  }

  //! Post-processing step for adjusting the author and commit messages.
  void final_check(Flags flags)
  {
    if (handler && handler->final_check) {
      progress(flags, "Final check...\n");
      handler->final_check(this_object());

      // Check that the handler didn't break anything...
      verify_git_commits(1);
    }
  }

  protected void blob_reader(Stdio.File blobs, Thread.Queue processing)
  {
    string buf = "";
    do {
      string bytes = blobs->read();
      if (!sizeof(bytes)) break;
      buf += bytes;
      array(string) b = buf/"\n";
      foreach(b[..<1], string blob) {
	[string sha, string data_path] = processing->read();
	git_blobs[sha] = blob;
	while (rm(data_path)) {
	  data_path = combine_path(data_path, "..");
	}	  
      }
      buf = b[-1];
    } while (1);
    blobs->close();
  }

  void generate(string workdir, Flags|void flags)
  {
    mapping(string:string) rcs_state = ([]);
    mapping(string:string) git_state = ([]);

#ifdef LEAF_DEBUG
    // Let's add some debug to the commits where there are splits and merges.
    foreach(git_sort(values(git_commits)), GitCommit c) {
      if (sizeof(c->parents) != 1) {
	c->commit_flags |= COMMIT_TRACE;
	foreach(map(indices(c->parents), git_commits), GitCommit p) {
	  p->commit_flags |= COMMIT_TRACE;
	}
      }
      if (sizeof(c->children) != 1) {
	c->commit_flags |= COMMIT_TRACE;
	foreach(map(indices(c->children), git_commits), GitCommit cc) {
	  cc->commit_flags |= COMMIT_TRACE;
	}
      }
    }
#endif

    progress(flags, "Committing...\n");

    // Loop over the commits oldest first to reduce recursion.
    foreach(git_sort(values(git_commits)); int i; GitCommit c) {
      if (!(i & 0xff)) {
	progress(flags, "\r%d: %-70s ", sizeof(git_commits) - i, c->uuid[<69..]);
      }
      c->generate(rcs_state, git_state);
    }

    write("checkpoint\n");

    progress(flags, "\r%-75s\rDone\n", "");
  }

  //! Returns a canonically sorted array of commits in time order.
  array(GitCommit) git_sort(array(GitCommit) commits)
  {
    commits -= ({ 0 });
    sort(commits->uuid, commits);
    sort(commits->timestamp, commits);
    return commits;
  }

  //! Reset the state to the initial state.
  void reset(Flags flags)
  {
    master_branches = (<>);
    master_branch = UNDEFINED;
    git_commits = ([]);
    git_refs = ([]);
    revision_lookup = ([]);
    git_blobs = ([]);
#ifdef USE_BITMASKS
    next_leaf = 1;
    leaf_lookup = ([]);
    root_commits = 0;
#else
    root_commits = ([]);
#endif
    num_roots = 0;
  }

  //! Process and flush the accumulated state to git.
  void flush(Flags flags)
  {
    // No need for the revision lookup anymore.
    revision_lookup = ([]);

    rake_leaves(flags);

    // Unify and graph commits.
    graph_git_commits(flags);

    // werror("Git refs: %O\n", git->git_refs);

    final_check(flags);

    // return 0;

    // FIXME: Generate a git repository.

    if (!(flags & FLAG_PRETEND)) {
      generate("work", flags);
    }

    reset(flags);
  }
}

void parse_config(GitRepository git, string config, Flags flags)
{
  git->set_handler(compile_file(config)(git, flags));
}

void usage(array(string) argv)
{
  werror("%s [-h | --help] [-p] [-d <repository>] [-A <authors>]\n"
	 "%*s [(-C | --git-dir) <gitdir> [(-R | --root) <root-commitish>]]\n"
	 "%*s [-o <branch>] [(-r | --remote) <remote>]\n"
	 "%*s [(-c | --config) <config-file>]\n"
	 "%*s [-z <fuzz>] [-m] [-k] [-q | --quiet]\n",
	 argv[0], sizeof(argv[0]), "",
	 sizeof(argv[0]), "", sizeof(argv[0]), "", sizeof(argv[0]), "");
}

int main(int argc, array(string) argv)
{
  GitRepository git = GitRepository();

  // Some constants for the benefit of the configuration files.
  add_constant("GitRepository", GitRepository);
  add_constant("GitHandler", git->GitHandler);
  add_constant("RCSFile", RCSFile);
  add_constant("GitFlags", Flags);
  add_constant("GIT_FLAG_PRETEND", FLAG_PRETEND);
  add_constant("GIT_FLAG_DETECT_MERGES", FLAG_DETECT_MERGES);
  add_constant("GIT_FLAG_QUIET", FLAG_QUIET);
  add_constant("GIT_FLAG_NO_KEYWORDS", FLAG_NO_KEYWORDS);
  add_constant("git_progress", progress);

  Flags flags;

  Process.Process fast_importer;

  array(string) initial_argv = argv + ({});

  foreach(Getopt.find_all_options(argv, ({
	   ({ "help",       Getopt.NO_ARG,  ({ "-h", "--help" }), 0, 0 }),
	   ({ "authors",    Getopt.HAS_ARG, ({ "-A", "--authors" }), 0, 0 }),
	   ({ "config",     Getopt.HAS_ARG, ({ "-c", "--config" }), 0, 0 }),
	   ({ "git-dir",    Getopt.HAS_ARG, ({ "-C", "--git-dir" }), 0, 0 }),
	   ({ "root",       Getopt.HAS_ARG, ({ "-R", "--root" }), 0, 0 }),
	   ({ "branch",     Getopt.HAS_ARG, ({ "-o" }), 0, 0 }),
	   ({ "remote",     Getopt.HAS_ARG, ({ "-r", "--remote" }), 0, 0 }),
	   ({ "repository", Getopt.HAS_ARG, ({ "-d" }), 0, 0 }),
	   ({ "fuzz",       Getopt.HAS_ARG, ({ "-z" }), 0, 0 }),
	   ({ "nokeywords", Getopt.NO_ARG,  ({ "-k" }), 0, 0 }),
	   ({ "merges",     Getopt.NO_ARG,  ({ "-m" }), 0, 0 }),
	   ({ "pretend",    Getopt.NO_ARG,  ({ "-p" }), 0, 0 }),
	   ({ "quiet",      Getopt.NO_ARG,  ({ "-q", "--quiet" }), 0, 0 }),
				  })),
	  [string arg, string val]) {
    switch(arg) {
    case "help":
      usage(argv);
      exit(0);
    case "config":
      if (Stdio.exist(val)) {
      } else if (!has_suffix(val, ".pcvs2git") &&
		 Stdio.exist(val + ".pcvs2git")) {
	val = val + ".pcvs2git";
      } else if (!has_prefix(val, "/")) {
	string c = combine_path(__FILE__, "../config", val);
	if (Stdio.exist(c)) {
	  val = c;
	} else if (!has_suffix(c, ".pcvs2git") &&
		   Stdio.exist(c + ".pcvs2git")) {
	  val = c + ".pcvs2git";
	}
      }
      parse_config(git, val, flags);
      break;
    case "authors":
      git->authors |= git->read_authors_file(val);
      break;
    case "branch":
      git->set_master_branch(val);
      break;
    case "repository":
      if (!(flags & (FLAG_HEADER|FLAG_PRETEND))) {
	flags |= FLAG_HEADER;
	write("#\n"
	      "# pcvs2git.pike started on %s\n"
	      "#\n"
	      "# Command-line:%{ %q%}\n"
	      "#\n"
	      "# This data is intended as input to git fast-import.\n"
	      "#\n"
	      "# git fast-import will be started automatically if\n"
	      "# pcvs2git.pike is invoked with the --git-dir option.\n"
	      "#\n",
	      ctime(time(1))-"\n", initial_argv);
      }

      progress(flags, "Reading RCS files from %s...\n", val);

      git->read_rcs_repository(val, flags);

      progress(flags, "\n");

      break;
    case "root":
      git->add_root_commit(stringp(val)?val:"");
      break;
    case "git-dir":
      if (fast_importer) {
	werror("A git directory has already been specified.\n");
	Stdio.stdout->close();
	fast_importer->wait();
	exit(1);
      } else if (sizeof(git->git_commits)) {
	werror("The target git directory must be specified before any "
	       "RCS directories.\n");
	exit(1);
      } else if (!(flags & FLAG_PRETEND)) {
	if (!Stdio.is_dir(val)) {
	  // No repository existant -- Create one.
	  Process.run(({ "git", "--git-dir", val, "init", "--bare" }));
	}
	werror("Starting a fast importer for git-dir %O...\n", val);
	Stdio.File p = Stdio.File();
	fast_importer =
	  Process.Process(({ "git", "--git-dir", val, "fast-import" }),
			  ([ "stdin":p->pipe() ]));
	// Redirect stdout to our new pipe.
	p->dup2(Stdio.stdout);
	p->close();
      }
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

  if (!sizeof(git->git_commits)) {
    usage(argv);
    exit(0);
  }

  // Graph and flush the state to git.
  git->flush(flags);

  // Wait for the importer to finish.
  if (fast_importer) {
    Stdio.stdout->close();
    return fast_importer->wait();
  }
}
