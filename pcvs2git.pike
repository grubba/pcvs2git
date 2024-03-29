
//
// Conversion utility for cvs to git migration.
//
// 2009-10-02 Henrik Grubbstr�m
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
//  o Analyze the committed Id strings to find renames and merges.
//    Note that merge links must be kept separate from the ordinary
//    parent-child links, since leafs shouldn't propagate over them.
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
//
//  o Converts the expand RCS keyword settings to the corresponding
//    .gitattributes files.
//
//  o Converts .cvsignore files to the corresponding .gitignore files.
//
//  o Keyword expansion and filtering (-k) is supported.
//
//  o Supports differing author and committer.
//
//  o Supports simulating import from a remote git repository (--remote).
//



#define USE_BITMASKS

#define USE_FAST_IMPORT

#ifdef LEAF_DEBUG
#define LEAF_SPLIT_DEBUG
#define LEAF_MERGE_DEBUG
#endif

//! Fuzz in seconds (15 minutes).
constant FUZZ = 15*60;

enum Flags {
  FLAG_PRETEND = 1,
  FLAG_DETECT_MERGES = 2,
  FLAG_QUIET = 4,
  FLAG_NO_KEYWORDS = 8,
  FLAG_HEADER = 16,
  FLAG_LINEAR = 32,
  FLAG_DISABLE_REV = 64,
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

//! The filepatterns that are ignored by CVS by default.
//!
//! The list is taken from the CVS 1.12.12 manual.
constant default_cvsignore = ({
  "RCS",
  "SCCS",
  "CVS",
  "CVS.adm",
  "RCSLOG",
  "cvslog.*",
  "tags",
  "TAGS",
  ".make.state",
  ".nse_depinfo",
  "*~",
  "#*",
  ".#*",
  ",*",
  "_$*",
  "*$",
  "*.old",
  "*.bak",
  "*.BAK",
  "*.orig",
  "*.rej",
  ".del-*",
  "*.a",
  "*.olb",
  "*.o",
  "*.obj",
  "*.so",
  "*.exe",
  "*.Z",
  "*.elc",
  "*.ln",
  "core",
});

//! Mapping from sha string to content for selected files.
//!
//! Currently used for .cvsignore.
mapping(string:string) file_contents = ([]);

//! Convert a cvsignore file to the corresponding gitignore file.
string convert_cvsignore(string data)
{
  // FIXME: Support '!'.
  return map(data/"\n",
	     lambda(string line) {
	       if (sizeof(line)) {
		 return "/" + line;
	       }
	       return line;
	     }) * "\n";
}

//! The set of filename extensions we've seen so far.
//!
//! This is used for creation of the .gitattributes files.
multiset(string) extensions = (<>);

//! Quote against fnmatch(3C) suitable for .gitattributes
//! (or .gitignore).
protected string fnquote(string fname)
{
  // NB: Due to the rules of the .gitattributes parser in
  //     git(1) it is not possible to quote whitespace.
  return replace(fname, ([ "\\": "\\\\",
			   "\"": "\\\"",
			   "\'": "\\\'",
			   "[" : "\\[",
			   "]" : "\\]",
			   " " : "?",
			   "\t": "?",
			   "*" : "\\*",
			   "?" : "\\?" ]));
}

//! Get the file extension glob of a filename.
//!
//! @returns
//!   Returns @expr{basename(filename)@} if there's no extension.
string file_extension_glob(string filename)
{
  filename = basename(filename);
  if (!has_value(filename, ".")) return fnquote(filename);
  return "*." + fnquote((filename/".")[-1]);
}

enum RevisionFlags {
  EXPAND_BINARY = 0,	// -kb
  EXPAND_LF = 1,	// 
  EXPAND_CRLF = 2,	//
  EXPAND_TEXT = 3,	// -ko Text file, don't care about EOL convention.
  EXPAND_KEYWORDS = 4,	//
  EXPAND_ALL = 7,	// -kkv (default)
  EXPAND_GUESS = 8,	// Use the default heuristics to determine flags.

  EXPAND_GOT_KEYWORD = 16,	// File contains an active keyword.

  REVISION_COPY = 32,	// The revision is a copy, don't delete the original.
  REVISION_MERGE = 64,	// The revision is a merge. The ancestor is soft.

  EXPAND_MAGIC = 128,
};

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

  protected void set_default_path(string path, string|void display_path)
  {
    foreach(revisions;;Revision rev) {
      rev->path = path;
      rev->display_path = display_path||path;
    }
  }

  void create(string rcs_file, string path, string|void data,
	      string|void display_path)
  {
    ::create(rcs_file, data);

    set_default_path(path, display_path);

    find_branch_heads();
  }

  //! Append a revision
  //!
  //! @param base
  //!   The revision to base the new revision on.
  //!
  //! @param ancestor
  //!   The revision to have as immediate ancestor for the new revision.
  //!   @expr{0@} (zero) for a new root commit.
  Revision append_revision(string base, string ancestor,
			   Calendar.TimeRange rcs_time,
			   string author, string message, string|void rev,
			   string|void state)
  {
    Revision parent = revisions[ancestor];
    if (ancestor && !parent) return UNDEFINED;

    Revision new_rev;
    if (!rev) {
      int i;
      do {
	// Use a revision number that isn't used by cvs.
	rev = sprintf("%s%c", ancestor || base, i + 'a');
	i++;
      } while (revisions[rev]);
    } else if (new_rev = revisions[rev]) return new_rev;

    Revision base_rev = revisions[base];

    new_rev = FakeRevision(rev, base_rev, rcs_time, author, message);
    new_rev->state = state || base_rev->state;
    new_rev->ancestor = ancestor;
    // Reparent the other children to parent, so that we are inserted
    // in their history, but only if we're not on a new branch.
    if (!ancestor || !has_prefix(rev, ancestor + ".")) {
      foreach(revisions;; Revision r) {
	if ((r->ancestor == ancestor) && (!ancestor || (r->time > rcs_time))) {
	  r->ancestor = rev;
	}
      }
    }
    revisions[rev] = new_rev;
    return new_rev;
  }

  //! Differs from the original in that it updates
  //! the custom fields @expr{sha@} and @expr{expand@} as well.
  string get_contents_for_revision(string|Revision rev)
  {
    if (stringp(rev)) rev = revisions[rev];
    if (!rev) return 0;
    if (!rev->rcs_text) rev->rcs_text = "";	// Paranoia.
    string data = ::get_contents_for_revision(rev);

    if (rev->sha) return data;

    // Update sha
    if (data && rev->state != "dead") {
      rev->sha = Crypto.SHA1()->update(data)->digest();
    } else {
      rev->sha = "\0"*20;	// Death marker.
    }

    // Update expand
    if (rev->revision_flags & EXPAND_GUESS) {
      rev->revision_flags &= ~(EXPAND_GUESS|EXPAND_ALL);
      RevisionFlags flags = EXPAND_ALL;
      if (expand == "b") {
	flags = EXPAND_BINARY;
      } else {
	if (expand == "o") flags = EXPAND_TEXT;
	// A paranoia check for invalid expand markup.
	if (data && (has_prefix(data, "%!PS") || has_value(data, "\0"))) {
	  flags = EXPAND_BINARY;
	} else if (data && has_value(data, "\r")) {
	  if (replace(replace(data, "\r", ""), "\n", "\r\n") == data) {
	    // CRLF-conversion is safe.
	    flags &= ~EXPAND_LF;
	  } else {
	    flags &= ~EXPAND_TEXT;
	  }
	}
      }
      rev->revision_flags |= flags;
    }

    return data;
  }

  //! Differs from the original in that it supports the
  //! custom field @expr{path@} of Id and RCSFile, and
  //! uses a @[String.Buffer] to build the result.
  //!
  //! Also uses a somewhat different approach to find the
  //! RCS keywords to expand.
  //!
  //! It also supports a negative value for @[override_binary]
  //! to enable stripping of keyword data.
  string expand_keywords_for_revision( string|Revision rev, string|void text,
				       int|void override_binary )
  {
    if( stringp( rev ) ) rev = revisions[rev];
    if( !rev ) return 0;
    if( !text ) text = get_contents_for_revision( rev );
    if( !(rev->revision_flags & EXPAND_KEYWORDS) && (override_binary <= 0) )
      return text;

    array(string) segments = text/"$";

    if (sizeof(segments) < 3) return text;	// Common case.

    Calendar.TimeRange time = rev->time;
    string state = rev->state;
    string revision = rev->revision;
    string author = rev->author;

    if (rev->is_fake_revision) {
      // Hide the fake information.
      revision = rev->base_rev;
      state = revisions[revision]->state;
      time = revisions[revision]->time;
      author = revisions[revision]->author;
    }

    string date = replace( time->format_time(), "-", "/" );
    string file;
    if (rev->path) {
      file = basename(rev->path) + ",v";
    } else {
      file = basename(rcs_file_name);
    }

    mapping kws = ([ "Author"	: author,
		     "Date"	: date,
		     "Header"	: ({ rcs_file_name, revision, date,
				     author, state }) * " ",
		     "Id"	: ({ file, revision, date,
				     author, state }) * " ",
		     "Name"	: "", // only applies to a checked-out file
		     "Locker"	: search( locks, revision ) || "",
		     /*"Log"	: "A horrible mess, at best", */
		     "RCSfile"	: file,
		     "Revision"	: revision,
		     "Source"	: rcs_file_name,
		     "State"	: state ]);

    int got_keyword;

    String.Buffer result = String.Buffer();
    int i;
    result->add(segments[0]);
    for (i = 1; i < sizeof(segments)-1; i++) {
      string segment = segments[i];
      if (!has_value(segment, "\n")) {
	sscanf(segment, "%[a-zA-Z]%s", string keyword, string rest);
	if (sizeof(keyword) && (!sizeof(rest) || has_prefix(rest, ":"))) {
	  string expansion;
	  if (expansion = kws[keyword]) {
	    result->add("$", keyword);
	    if (!override_binary) {
	      result->add(": ", expansion, " ");
	    }
	    segment = segments[++i];
	    got_keyword++;
	  }
	}
      }
      result->add("$", segment);
    }
    if (i < sizeof(segments)) {
      // Trailer.
      result->add("$", segments[-1]);
    }
    if (got_keyword) {
      rev->revision_flags |= EXPAND_GOT_KEYWORD;
    }
    return result->get();
  }

  //! Same as @[RCS.Revision], but with some additional fields.
  class Revision
  {
    //! Inherits the generic Revision.
    inherit RCS::Revision;

    //! Actual author (if other than committer).
    string actual_author;

    //! The destination path for checkout.
    string path;

    //! The path to display in the commit message.
    string display_path;

    //! The SHA1 hash of the data as checked out.
    string sha;

    //! The keyword expansion rules and other flags for this revision.
    RevisionFlags revision_flags = EXPAND_GUESS;

    //! Optional list of merge links.
    array(string) merges;
  }

  //! Revisions that don't actually exist in the RCS file.
  //!
  //! Used to keep track of out of band changes.
  class FakeRevision
  {
    inherit Revision;
    constant is_fake_revision = 1;

    string base_rev;

    //! Create the specified revision based on @[base].
    protected void create(string rev, Revision base, Calendar.TimeRange time,
			  string author, string message)
    {
      revision = rev;
      base_rev = base->is_fake_revision?base->base_rev:base->revision;
      path = base->path;
      sha = base->sha;
      text = base->text;
      revision_flags = base->revision_flags & ~(REVISION_COPY|REVISION_MERGE);
      this_program::time = time;
      this_program::author = author;
      this_program::log = message;
      // Some magic to get the content correct...
      rcs_text = "";			// No differences from
      rcs_prev = base->revision;	// our parent.
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

  //! Indicates that the repository needs a pre-commit hook for
  //! handling blocking of commit of expanded CVS identifiers.
  int need_pre_commit_hook;

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
    //!   @[UNDEFINED] to rename all revisions of the file.
    protected void rename_revision(RCSFile rcs_file, string old_path,
				   string new_path, string rev)
    {
#if 0
      werror("rename_revision(%O, %O, %O, %O)\n",
	     rcs_file, old_path, new_path, rev);
#endif
      if (!rev) {
	// Move all revisions.
	foreach(rcs_file->revisions;; RCSFile.Revision r) {
	  if (r->path == new_path) {
	    r->path = old_path;
	    if (r->display_path && has_suffix(r->display_path, new_path)) {
	      r->display_path =
		r->display_path[..<sizeof(new_path)] + old_path;
	    }
	  }
	}
      } else {
	RCSFile.Revision root_rev = rcs_file->revisions[rev];
	if (!root_rev) return;
	RCSFile.Revision r = root_rev;
	while (r = rcs_file->revisions[r->ancestor]) {
	  if (r->path == new_path) r->path = old_path;
	  if (r->display_path && has_suffix(r->display_path, new_path)) {
	    r->display_path =
	      r->display_path[..<sizeof(new_path)] + old_path;
	  }
	}
	foreach(rcs_file->revisions;; r) {
	  if ((r->path == new_path) && (r->time < root_rev->time)) {
	    r->path = old_path;
	    if (r->display_path && has_suffix(r->display_path, new_path)) {
	      r->display_path =
		r->display_path[..<sizeof(new_path)] + old_path;
	    }
	  }
	}
      }
#if 0
      foreach(map(sort(indices(rcs_file->revisions)), rcs_file->revisions),
	      RCSFile.Revision r) {
	werror("\t%O\t%O:%O\n", r->revision, r->path, r->display_path);
      }
#endif /* 0 */
    }

    //! The RCS file was copied from @[old_path] at revision @[rev].
    //!
    //! @param rev
    //!   The first revision on @[new_path].
    protected void copy_revision(RCSFile rcs_file, string old_path,
				 string new_path, string rev)
    {
      rename_revision(rcs_file, old_path, new_path, rev);
      
      // Mark the revision as a copy.
      RCSFile.Revision root_rev = rcs_file->revisions[rev];
      if (!root_rev) return;

      root_rev->revision_flags |= REVISION_COPY;
    }

    //! Hide a specific revision.
    protected void hide_revision(RCSFile rcs_file, string rev)
    {
      RCSFile.Revision r = rcs_file->revisions[rev];
      if (r) r->path = UNDEFINED;
    }

    //! Convert rcs_time to a @[Calendar.TimeRange].
    protected Calendar.TimeRange parse_rcs_time(string rcs_time)
    {
      return Calendar.ISO.parse("%y.%M.%D.%h.%m.%s %z",
				rcs_time + " UTC");
    }

    //! Find the revision that was current on branch @[branch] at
    //! @[rcs_time].
    //!
    //! @param branch
    //!   @mixed
    //!     @value 0
    //!       The main branch.
    //!     @value ""
    //!       The branch indicated by @[rcs_file->branch] if any,
    //!       otherwise the branch @expr{"1.1.1"@}.
    //!     @value "tag"
    //!       The branch with the tag @[branch] if any, otherwise
    //!       the main branch.
    //!   @endmixed
    protected string find_revision(RCSFile rcs_file, string branch,
				   string rcs_time)
    {
      if (rcs_time[2] == '.') rcs_time = "19" + rcs_time;
      Calendar.TimeRange time = Calendar.ISO.parse("%y.%M.%D.%h.%m.%s %z",
						   rcs_time + " UTC");
      // Get a suitable starting revision.
      string prev_rev;
      if (branch == "") {
	prev_rev = rcs_file->branch || "1.1.1";
      } else {
	prev_rev = rcs_file->tags[branch] || rcs_file->head;
      }
      if (rcs_file->symbol_is_branch(prev_rev) || (prev_rev == "1.1.1")) {
	// FIXME: Use rcs_file->branch_heads
	string branch_prefix;
	if (prev_rev == "1.1.1") {
	  branch_prefix = "1.1.1";
	  prev_rev = "1.1";
	  // NB: In some obscure cases version 1.1 doesn't exist.
	  //     In that case we start at HEAD, and scan until we reach
	  //     the root revision.
	  if (!rcs_file->revisions[prev_rev]) {
	    prev_rev = rcs_file->head;
	    while(rcs_file->revisions[prev_rev]->ancestor) {
	      prev_rev = rcs_file->revisions[prev_rev]->ancestor;
	    }
	    branch_prefix = prev_rev + ".1";
	  }
	} else {
	  array(string) frags = prev_rev/".";
	  prev_rev = frags[..<2]*".";
	  branch_prefix = prev_rev + "." + frags[-1];
	}
	prev_rev = rcs_file->branch_heads[branch_prefix];
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
#if 0
      werror("Creating a new branch: %O\n", branch_prefix + i);
#endif
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
    //!   Depending on the state of @[prev_rev] and @[branch], this defaults to:
    //!   @string
    //!     @value "dead"
    //!       If the state of @[prev_rev] is @expr{"dead"@}.
    //!     @value "fake"
    //!       If @[branch] is @expr{0@} (ie the new revision has been
    //!       inserted somewhere potentially inbetween two old revisions).
    //!     @value "Exp"
    //!       (Or rather same as the state of @[prev_rev]), if a
    //!       new branch has been created.
    //!   @endstring
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
      string main_rev = prev_rev;
      if (!prev_rev) {
	// Get a suitable starting revision.
	prev_rev = main_rev = find_revision(rcs_file, branch, rcs_time);
	if (!rcs_file->tags[branch]) {
	  // Check the vendor branch as well.
	  prev_rev = find_revision(rcs_file, "", rcs_time);
	}
	if (!prev_rev ||
	    (rcs_file->revisions[main_rev]->time >
	     rcs_file->revisions[prev_rev]->time)) {
	  // The main branch is more recent than the vendor branch.
	  prev_rev = main_rev;
	} else if (branch) main_rev = prev_rev;
      }
      // We now have a suitable prev_rev and main_rev.

#if 0
      werror("append_revision(%O, %O, %O, %O, %O, %O, %O)\n",
	     rcs_file, branch, prev_rev, rcs_time, committer, message, state);
#endif

      if (!prev_rev) return UNDEFINED;

      int new_branch;

      // Now it's time to generate a suitable result_rev.
      string result_rev;
      if (branch) {
	string branch_prefix;
	if (rcs_file->tags[branch]) {
	  // Note that there are such things as revision "3.0"
	  // in some RCS files...
	  array(string) fields = rcs_file->tags[branch]/".";
	  branch_prefix = (fields[..<2] + fields[<0..]) * ".";
	  if (has_prefix(prev_rev, branch_prefix + ".")) {
	    int i;
	    for (i = 'a'; rcs_file->revisions[sprintf("%s%c", prev_rev, i)]; i++)
	      ;
	    result_rev = sprintf("%s%c", prev_rev, i);
	  }
	} else {
	  branch_prefix = add_branch(rcs_file, branch, prev_rev);
	}
	if (!result_rev) {
	  // We add a revision to our new branch...
	  result_rev = branch_prefix + ".1";
	  new_branch = 1;
	}
	if ((< UNDEFINED, prev_rev >)[rcs_file->branch_heads[branch_prefix]]) {
	  rcs_file->branch_heads[branch_prefix] = result_rev;
	}
      } else {
	int i;
	for (i = 'a'; rcs_file->revisions[sprintf("%s%c", main_rev, i)]; i++)
	  ;
	result_rev = sprintf("%s%c", main_rev, i);
      }
      if (!state && (rcs_file->revisions[main_rev]->state != "dead")) {
	state = "fake";
      }
      // FIXME!
      RCSFile.Revision rev = rcs_file->append_revision(prev_rev, main_rev, time,
						       committer, message,
						       result_rev, state);
      if (branch) {
	if (new_branch) {
	  RCSFile.Revision brev = rcs_file->revisions[prev_rev];
	  if (brev->branches) {
	    brev->branches += ({ rev->revision });
	  } else {
	    brev->branches = ({ rev->revision });
	  }
	}
      } else if (rcs_file->head == main_rev) {
	// We have a new HEAD revision.
	rcs_file->head = rev->revision;
	if (rcs_file->branch &&
	    (time > rcs_file->revisions[rcs_file->branch_heads[rcs_file->branch]]->time)) {
	  // The new revision is newer than the latest vendor branch commit.
	  rcs_file->branch = UNDEFINED;
	}
      }
      //werror("Revision: %O\n", rev->revision);
      return rev->revision;
    }

    //! Split of a branch @[branch] at time @[branch_time], duplicating
    //! all revisions on the path to (and including) @[stop_time].
    //!
    //! @param move_tag
    //!   Filter function that is called with the name of any tags
    //!   that may be considered for moving to the new branch. The
    //!   argument is the name of a tag, and the function should
    //!   return @expr{1@} if the tag should be moved.
    //!
    //! @returns
    //!   Returns the HEAD revision of the new branch (if any).
    //!
    //! @note
    //!   This function does not handle vendor branches properly.
    string split_branch(RCSFile rcsfile, string branch, string branch_time,
			string stop_time, function(string: int(0..1)) move_tag)
    {
      string stop_rev = find_revision(rcsfile, UNDEFINED, stop_time);
      if (!stop_rev) {
	// The file didn't exist yet when the branch stopped being added to.
	return UNDEFINED;
      }
      string start_rev = find_revision(rcsfile, UNDEFINED, branch_time);

      ADT.Stack stack = ADT.Stack();
      stack->push(0);	// Sentinel.
      string r = stop_rev;
      while (r != start_rev) {
	stack->push(r);
	r = rcsfile->revisions[r]->ancestor;
      }

      if (!start_rev) {
	// The split was before the file existed, so we need to add
	// an artificial (and dead) commit before the first commit.
	r = stack->top();
	Calendar.TimeRange t =
	  Calendar.ISO.parse("%y.%M.%D.%h.%m.%s %z", branch_time + " UTC");
	start_rev =
	  rcsfile->append_revision(r, UNDEFINED, t, "pcvs2git",
				   sprintf("Branch point for %s.\n", branch),
				   UNDEFINED, "dead")->revision;
      } else if (!rcsfile->revisions[start_rev]->ancestor &&
		 (rcsfile->revisions[start_rev + ".1.1"])) {
	// Vendor branch.
	start_rev += ".1.1";
      }

      string branch_prefix = add_branch(rcsfile, branch, start_rev);
      int i;
      string prev_rev = start_rev;
      while (r = stack->pop()) {
	RCSFile.Revision rev = rcsfile->revisions[r];
	prev_rev =
	  rcsfile->append_revision(r, prev_rev, rev->time, rev->author,
				   rev->log, branch_prefix + "." + ++i,
				   rev->state)->revision;
	// Check if we need to move any tags.
	foreach(rcsfile->tags; string tag; string tr) {
	  if ((tr != r) || !move_tag(tag)) continue;
	  rcsfile->tags[tag] = prev_rev;
	}
      }
      rcsfile->branch_heads[branch_prefix] = prev_rev;
      return prev_rev;
    }

    //! Make sure the revisions from this file aren't
    //! merged into the branch @[branch].
    void kill_branch(RCSFile rcsfile, string branch)
    {
      rcsfile->tags[branch] = "0.0.0.0";
    }

    //! Make sure the revisions from this file aren't
    //! merged into the tag @[branch].
    void kill_tag(RCSFile rcsfile, string tag)
    {
      rcsfile->tags[tag] = "0.0";
    }

    //! Replace all CRLF's in all revisions with plain LF's.
    void fix_crlf(RCSFile rcsfile)
    {
      foreach(rcsfile->revisions;; RCSFile.Revision rev) {
	rev->rcs_text = replace(rev->rcs_text, "\r\n", "\n");
	if (rev->text) rev->text = replace(rev->text, "\r\n", "\n");
	rev->sha = UNDEFINED;
	rev->revision_flags = EXPAND_GUESS;
      }
    }

    //! Add the branch tag @[branch] at the trunk at time @[branch_time] if
    //! it doesn't already exist.
    //!
    //! @param branch
    //!   Branch to fixup.
    //!
    //! @param branch_time
    //!   Time at which the branch was created.
    //!
    //! This function is typically used to get a more stable
    //! branch point for the common case where a branch only
    //! exists in a few files (often just a single file) in
    //! the repository.
    //!
    //! @note
    //!   This function handles vendor branches.
    //!
    //! @seealso
    //!   @[add_branch()], @[simple_add_tag()]
    void simple_add_branch(RCSFile rcsfile, string branch, string branch_time)
    {
      if (rcsfile->tags[branch]) return;

      string rev = find_revision(rcsfile, UNDEFINED, branch_time);
      string rev2 = find_revision(rcsfile, "", branch_time);
      if (!rev) {
	rev = rev2;
      } else if (rev2) {
	if (rcsfile->revisions[rev2]->time >= rcsfile->revisions[rev]->time) {
	  rev = rev2;
	}
      }
      if (rev) {
	add_branch(rcsfile, branch, rev);
      } else {
	kill_branch(rcsfile, branch);
      }
    }

    //! Add the tag @[branch] at the trunk at time @[tag_time] if
    //! it doesn't already exist.
    //!
    //! @param tag
    //!   Tag to fixup.
    //!
    //! @param tag_time
    //!   Time at which the tag was created.
    //!
    //! This function is typically used to add artificial
    //! tags at some point in time to force merging behaviour.
    //!
    //! @note
    //!   This function handles vendor branches.
    //!
    //! @seealso
    //!   @[simple_add_branch()]
    void simple_add_tag(RCSFile rcsfile, string tag, string tag_time)
    {
      if (rcsfile->tags[tag]) return;

      string rev = find_revision(rcsfile, UNDEFINED, tag_time);
      string rev2 = find_revision(rcsfile, "", tag_time);
      if (!rev) {
	rev = rev2;
      } else if (rev2) {
	if (rcsfile->revisions[rev2]->time >= rcsfile->revisions[rev]->time) {
	  rev = rev2;
	}
      }
      if (rev) {
	rcsfile->tags[tag] = rev;
      } else {
	kill_tag(rcsfile, tag);
      }
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
    //!   Initialized to the empty mapping for the repository root.
    //!   Copied from the parent directory for other directories.
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
    //!     @elem string|void 2
    //!       The (possibly altered) @[display_path].
    //!   @endarray
    //!
    //! @seealso
    //!   @[leave_directory()]
    array(string|array(string)) enter_directory(GitRepository git,
						string path,
						array(string) files,
						Flags flags,
						mapping state,
						string|void display_path);

    //! This handler is called on leaving a directory during RCS import.
    //!
    //! @param orig_path
    //!   The original destination path in the git repository (ie not
    //!   as modified by @[enter_directory()]).
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

    //! This handler is called by @[GitRepository()->find_commit()]
    //! when it finds a candidate commit.
    //!
    //! This function can be used to implement various repository
    //! split policies.
    //!
    //! @returns
    //!   Returns either @expr{0@} (zero) to filter the commit
    //!   (and let @[GitRepository()->find_commit()] continue its
    //!   search), or a @[GitRepository.GitCommit], which will
    //!   become the result from @[GitRepository()->find_commit()]
    //!   (ie typically @[commit]).
    GitRepository.GitCommit filter_commits(GitRepository git,
					   GitRepository.GitCommit commit,
					   RCSFile.Revision rev);

    //! This function is used to notify about dependencies between
    //! branches.
    //!
    //! It performs the following for commits that are independant of the
    //! @[dependant_tag]:
    //! @ul
    //!   @item
    //!     If the commit is independant of @[orig_tag], it is skipped.
    //!   @item
    //!     If the commit is incompatible with @[orig_tag], it
    //!     is made also incompatible with @[dependant_tag].
    //!   @item
    //!     If the commit is on the @[orig_tag] branch, and isn't dead,
    //!     it is skipped.
    //!   @item
    //!     If the commit is newer than @[split_time], and isn't a leaf
    //!     it is made incompatible with @[orig_tag].
    //!   @item
    //!     If the commit is older than @[split_time], it is hooked
    //!     as a parent to @[dependant_tag].
    //! @endul
    //!
    //! @param warn
    //!   Output warnings if non-dead files are present on only one
    //!   of the branches at split time.
    //!
    //! It is typically called from @[rake_leaves()].
    protected void branch_dependancy(GitRepository git, string orig_tag,
				     string dependant_tag,
				     string|int split_time,
				     int|void warn)
    {
      progress(git_flags, "Branch dependancy %O ==> %O...\n",
	       orig_tag, dependant_tag);
      GitRepository.GitCommit orig = git->git_refs[orig_tag] ||
	git->git_refs[remote + orig_tag];
      GitRepository.GitCommit dependant = git->git_refs[dependant_tag] ||
	git->git_refs[remote + dependant_tag];
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
      foreach(reverse(git->git_sort(values(git->git_commits))),
	      GitRepository.GitCommit c) {
	if (c->leaves & dependant_mask) {
	  if (warn && !(c->leaves & orig_mask) &&
	      (c->timestamp < split_time)) {
	    werror("Warning: Commit %O is on %s but not on %s!\n",
		   c->uuid, dependant_tag, orig_tag);
	    werror("Parents: %{%O, %}\n", sort(indices(c->parents)));
	  }
	  continue;
	}
	if (c->dead_leaves & dependant_mask) continue;
	// c is currently independant of dependant_tag.
	if (c->dead_leaves & orig_mask) {
	  // c must not be on the orig_tag branch, and
	  // thus not on the dependant_tag branch either.
	  if (!c->is_leaf) {
	    // But note that leaves on a new branch
	    // typically are dead with respect to
	    // the origin, but aren't on the new yet.
	    c->propagate_dead_leaves(dependant_mask);
	  }
	  continue;
	}
	if (!(c->leaves & orig_mask)) continue;
	if (!(c->commit_flags & GitRepository.COMMIT_DEAD)) {
	  if (warn && (c->timestamp < split_time)) {
	    werror("Warning: Commit %O is on %s but is lost on %s!\n",
		   c->uuid, orig_tag, dependant_tag);
	    werror("Parents: %{%O, %}\n", sort(indices(c->parents)));
	  }
	  continue;
	}
	if (c->timestamp > split_time) {
	  if (!c->is_leaf) {
	    c->propagate_dead_leaves(dependant_mask);
	  }
	  continue;
	}
	dependant->hook_parent(c);
      }
    }

    //! This handler is called when timestamps are about to be bumped.
    //!
    //! It can be used to adjust the stamps more finely grained.
    //!
    //! @note
    //!   Note that the ordinary timestamp bumper will run after this,
    //!   and may bump the timestamps further.
    void bump_timestamps(GitRepository git, Flags flags);

    //! This handler hook is called when a new .gitattributes file
    //! is about to be created.
    void adjust_ext_histogram(GitRepository git, GitRepository.GitCommit commit,
			      mapping(string:array(multiset(string))) ext_hist);

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

  string remote = "heads/";
  string master_branch;

  mapping(string:GitCommit) git_commits = ([]);

  mapping(string:GitCommit) git_refs = ([]);

  //! Mapping from (binary) sha to (ascii) mark for a blob.
  mapping(string:string) git_blobs = ([]);

  int fuzz = FUZZ;

  //! Mapping from login to an ordered array with time-differentiated
  //! author definitions. Each of which is an array of
  //!   @array
  //!     @elem int 0
  //!       Timestamp when this definition starts being valid.
  //!     @elem string 1
  //!       GECOS for the login.
  //!     @elem string 2
  //!       Email-address for the login.
  //!     @elem string|void 3
  //!       Timezone for the login.
  //!   @endarray
  mapping(string:array(array(int|string))) authors = ([]);

  //! Mapping from path to an array of
  //!   @array
  //!     @elem string 0 
  //!       RCS revision if known, zero otherwise.
  //!     @elem int 1
  //!       Revision timestamp if known, zero otherwise.
  //!     @elem string 2
  //!       Contributor or the revision.
  //!   @endarray
  mapping(string:array(array(int|string))) contributors = ([]);

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
    string tz = "";
    sscanf(email_addr, "%s<%s>%s", gecos, email, tz);

    gecos = String.trim_all_whites(gecos);
    email = String.trim_all_whites(email);
    tz = String.trim_all_whites(tz);

    if (!sizeof(gecos)) gecos = login;
    if (!sizeof(email)) email = login;
    
    if (catch(string tmp = utf8_to_string(gecos))) {
      // Not valid UTF-8. Fall back to iso-8859-1.
      gecos = string_to_utf8(gecos);
    }
    if (sizeof(tz)) {
      return ({ gecos, email, tz });
    } else {
      return ({ gecos, email });
    }
  }

  mapping(string:array(array(int|string))) parse_authors(string data,
							 string filename)
  {
    int tstart = -0x80000000;
    mapping(string:array(array(int|string))) res = ([]);
    foreach(data/"\n"; int no; string raw_line) {
      string line = raw_line;
      sscanf(line, "%s#", line);
      line = String.trim_all_whites(line);
      if (!sizeof(line)) continue;
      if (sscanf(line, "%s=%s", string login, string email_addr) == 2) {
	login = String.trim_all_whites(login);
	if (login == "__TIMESTAMP__") {
	  int tnew = tstart;
	  sscanf(email_addr, "%d", tnew);
	  if (tnew < tstart) {
	    werror("%s:%d: Invalid timestamp order %d < %d.\n",
		   filename, no+1, tnew, tstart);
	  } else {
	    tstart = tnew;
	  }
	} else {
	  res[login] += ({ ({ tstart }) +
			   parse_email_addr(login, email_addr) });
	}
      } else {
	werror("%s:%d: Failed to parse line: %O\n",
	       filename, no+1, raw_line);
      }
    }
    return res;
  }

  mapping(string:array(array(int|string))) read_authors_file(string filename)
  {
    return parse_authors(Stdio.read_bytes(filename), filename);
  }

  void merge_authors(mapping(string:array(array(int|string))) more_authors)
  {
    if (!sizeof(authors)) {
      authors = more_authors;
      return;
    }
    foreach(more_authors; string login; array(array(int|string)) entry) {
      if (!authors[login]) {
	authors[login] = entry;
	continue;
      }
      entry = authors[login] + entry;
      sort(map(entry, `[], 0), entry);
      authors[login] = entry;
    }
  }

  array(string) author_lookup(GitCommit c, string login, int|void timestamp)
  {
    array(int|array(string)) res = authors[login];

    if (!res) {
      if (!login) return ({ "A. Nonymous", "anonymous" });
      res = ({ ({ -0x80000000 }) + parse_email_addr(login, login) });
      if (sizeof(authors)) {
	werror("Warning: %s: Author %O is not in the authors file.\n",
	       c->uuid, login);
	authors[login] = res;
      }
    }
    if (zero_type(timestamp)) return res[0][1..];	// Don't care.
    for (int i=sizeof(res); i--;) {
      if (res[i][0] <= timestamp) return res[i][1..];
    }
    werror("Warning: %s: Author %O not defined for times before %d.\n",
	   c->uuid, login, res[0][0]);
    // Move the definition of the first incarnation of author to minint.
    res[0][0] = -0x80000000;
    return res[0][1..];
  }

  void parse_contributors(string data, string filename)
  {
    foreach(data/"\n"; int no; string raw_line) {
      string line = raw_line;
      sscanf(line, "%s#", line);
      line = String.trim_all_whites(line);
      if (!sizeof(line)) continue;
      if (sscanf(line, "%s%*[ \t]%s%*[ \t]%s%*[ \t]%s",
		 string path, string rev, string login, string timestamp) > 2) {
	if (rev == "-") rev = UNDEFINED;
	int ts;
	if (timestamp && (timestamp != "-")) {
	  if (has_value(timestamp, ".")) {
	    // RCS-style timestamp
	    if (timestamp[2..2] == ".") timestamp = "19" + timestamp;
	    ts = Calendar.ISO.parse("%y.%M.%D.%h.%m.%s %z",
				    timestamp + " UTC")->unix_time();
	  } else {
	    ts = (int)timestamp;
	  }
	}
	array(array(string|int)) entry = ({ ({ rev, ts, login }) });
	if (contributors[path]) {
	  contributors[path] += entry;
	} else {
	  contributors[path] = entry;
	}
      } else {
	werror("%s:%d: Failed to parse line: %O\n",
	       filename, no+1, raw_line);
      }
    }
  }

  void read_contributors_file(string filename)
  {
    parse_contributors(Stdio.read_bytes(filename), filename);
  }

  //! Look up the revision @[rev] in the contributors table,
  //! and adjust the actual_author field on match.
  void lookup_contributor(RCSFile.Revision rev)
  {
    array(array(int|string)) entries;
    if (!(entries = contributors[rev->path])) return;
    string revision = rev->revision;
    if (rev->is_fake_revision) revision = rev->base_rev;
    int t = rev->time->unix_time();
    mapping(int:string) weak_matches = ([]);
    foreach(entries, [string r, int ts, string login]) {
      if (r && (rev->revision != r)) continue;
      if (ts) {
	if (t != ts) {
	  if ((t + fuzz > ts) && (t - fuzz < ts)) {
	    weak_matches[ts] = login;
	  }
	  continue;
	}
      }
      rev->actual_author = login;
    }
    if (sizeof(weak_matches) && !rev->actual_author) {
      werror("\nWarning: Timestamp mismatch for %s:%s (actual: %d):\n",
	     rev->path, rev->revision||"", t);
      foreach(sort(indices(weak_matches)), int ts) {
	werror("\t%d: Contributor: %s\n", ts, weak_matches[ts]);
      }
    }
  }

  int|Calendar.Rule.Timezone default_tz = Calendar.Timezone.locale;
  mapping(string:Calendar.Rule.Timezone) tzcache = ([]);
  int tzoffset(int ts, string|void tzname)
  {
    int|Calendar.Rule.Timezone tz = default_tz;
    if (tzname) {
      tz = tzcache[tzname];
      if (!tz && zero_type(tz)) {
	tz = Calendar.Timezone[tzname];
	if (zero_type(tz) &&
	    ((sscanf(tzname, "%d%s", tz, string rest) != 2) || (rest != ""))) {
	  // Fallback: Unknown timezone.
	  werror("Unknown timezone %O.\n", tzname);
	  tz = default_tz;
	}
	tzcache[tzname] = tz;
      }
    }
    if (intp(tz)) return tz;
    // Note: Reversed timezone offset!
    int minutes = -tz->tz_ux(ts)[0]/60;
    int hours = minutes/60;
    minutes -= hours*60;
    return hours*100 + minutes;
  }

  enum CommitFlags {
    COMMIT_DEAD = 1,	// Commit contains only deletions.
    COMMIT_HIDE = 2,	// Don't export this commit to git.
    COMMIT_TS = 4,	// The time stamp is known (only for refs).
    COMMIT_FAKE = 8,	// Commit contains only simulated changes.
    COMMIT_TRACE = 128,	// Trace this node.
  };

  string convert_expansion_flags_to_attrs(RevisionFlags expand,
					  RevisionFlags default_flags)
  {
    if (!(expand & EXPAND_ALL)) {
      // NB: We redefine the binary attribute macro to also disable ident.
      return "binary";
    }
    string res;
    int mask = expand ^ default_flags;
    if (!(default_flags & EXPAND_ALL)) {
      res = "!binary !crlf";
      mask = EXPAND_ALL|EXPAND_MAGIC;
    }
    if (mask & EXPAND_MAGIC) {
      if (res) res += " text";
      else res = "text";
    }
    if (mask & EXPAND_TEXT) {
      if (res) res += " ";
      else res = "";
      switch(expand & EXPAND_TEXT) {
      case EXPAND_TEXT:
	// Text, don't care about EOL.
	res += "!eol";
	break;
      case EXPAND_LF:
	res += "eol=lf";
	break;
      case EXPAND_CRLF:
	res += "eol=crlf";
	break;
      case EXPAND_BINARY:
	res += "-text -crlf";
	break;
      }
    }
    if (mask & EXPAND_KEYWORDS) {
      if (res) res += " ";
      else res = "";
      if (expand & EXPAND_KEYWORDS) {
	res += "ident";
      } else {
	res += "-ident";
      }
    }
    return res;
  }

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

    //! Mapping from path to @expr{rev_info@} string as generated
    //! by @[make_rev_info()].
    //!
    //! @seealso
    //!   @[make_rev_info()], @[full_revision_set]
    mapping(string:string) revisions = ([]);

    //! Mapping from path to @expr{rev_info@} string prefixed by offsetted
    //! timestamp for files contained in this commit (full set including
    //! files from predecessors).
    //!
    //! Note that this variable is only maintained during @[generate()]
    //! time, and only for a subset of all commits, due to memory concerns.
    //!
    //! @seealso
    //!   @[make_rev_info()], @[revisions]
    mapping(string:string) full_revision_set;

    static void create(string path, string|void rev, string|void uuid)
    {
#ifndef USE_BITMASKS
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
	  if (new_leaves & c->dead_leaves) {
	    werror("Propagating conflicting leaves to %O:\n", c);
	    describe_leaves("\t", new_leaves & c->dead_leaves, "\n");
	    error("Conflicting leaves.\n");
	  }

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
	Leafset old = c->dead_leaves;

	if (dead_leaves & c->leaves) {
	  werror("Propagating conflicting dead leaves to %O:\n", c);
	  describe_leaves("\t", dead_leaves & c->leaves, "\n");
	  error("Conflicting dead leaves.\n");
	}

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
	  describe_leaves("\t", c->dead_leaves - old, "\n");
	}
      }
    }

    void rake_dead_leaves()
    {
      if (!sizeof(parents) || is_leaf || (commit_flags & COMMIT_DEAD)) {
	return;
      }
      array(GitCommit) ps = git_sort(map(indices(parents), git_commits));
      Leafset all_leaves;
#ifndef USE_BITMASKS
      all_leaves = ([]);
#endif
      foreach(ps, GitCommit p) {
	all_leaves |= p->leaves | p->dead_leaves;
      }

      Leafset non_vendor_heads = heads - vendor_heads;

      ADT.Stack stack = ADT.Stack();
      stack->push(0);	// End sentinel.
      stack->push(this_object());
      while (GitCommit c = stack->pop()) {
	if (c->commit_flags & COMMIT_FAKE) {
	  // Skip past to the children.
	  map(map(indices(c->children), git_commits), stack->push);
	} else {
	  c->propagate_dead_leaves((all_leaves - c->leaves) &
				   non_vendor_heads);
	}
      }

      if (commit_flags & COMMIT_TRACE) {
	werror("%O: Raked dead leaves: %O...\n", uuid, dead_leaves);
	describe_leaves("\t", dead_leaves, "\n");
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
      if (parent->uuid == uuid) error("Hooking a circular parent!\n");
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
    void merge(GitCommit c, int(0..1)|void force,
	       int(0..1)|void inhibit_destruct)
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
	if (cc != this_object()) {
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
	if (cc != this_object()) {
	  cc->hook_soft_parent(this);
	}
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
	if (p != this_object()) {
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
	if (p != this_object()) {
	  hook_soft_parent(p);
	}
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

      foreach(c->revisions; string path; string rev_info) {
	if (!revisions[path] || (revisions[path] < rev_info)) {
	  // Make sure deletions don't overwrite changes.
	  // This typically occurs when an RCS file has
	  // been copied (ie not renamed).
	  revisions[path] = rev_info;
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

      if (!inhibit_destruct) {
	m_delete(git_commits, c->uuid);
	destruct(c);
      }
    }

    //! Merge the node into all of its parents.
    void implode(mapping(string:mapping(string:int))|void dirty_commits)
    {
      // Detach from our parents and children.

      array(GitCommit) parents =
	map(indices(this_program::parents), git_commits);
      map(parents->children, m_delete, uuid);
      this_program::parents = ([]);

      array(GitCommit) children =
	map(indices(this_program::children), git_commits);
      map(children->parents, m_delete, uuid);
      this_program::children = ([]);

      array(GitCommit) soft_parents =
	map(indices(this_program::soft_parents), git_commits);
      map(soft_parents->soft_children, m_delete, uuid);
      this_program::soft_parents = ([]);

      array(GitCommit) soft_children =
	map(indices(this_program::soft_children), git_commits);
      map(soft_children->soft_parents, m_delete, uuid);
      this_program::soft_children = ([]);

      int trace_mode = commit_flags & COMMIT_TRACE;

      // Merge with our parents.
      foreach(parents, GitCommit p) {
	if (trace_mode) {
	  werror("Merging %s with its parent %s...\n", uuid, p->uuid);
	}
	foreach(children, GitCommit c) {
	  c->hook_parent(p);
	  if (dirty_commits) {
	    if (!dirty_commits[c->uuid]) {
	      dirty_commits[c->uuid] = ([ p->uuid:1 ]);
	    } else {
	      dirty_commits[c->uuid][p->uuid] = 1;
	    }
	  }
	}

	// Inhibit destruct, or we'll be sorry...
	p->merge(this_object(), 1, 1);
      }
      foreach(soft_parents, GitCommit p) {
	if (trace_mode) {
	  werror("Merging %s with its soft parent %s...\n", uuid, p->uuid);
	}
	foreach(soft_children, GitCommit c) {
	  c->hook_soft_parent(p);
	}
      }
      // Now we can die...
      m_delete(git_commits, uuid);
      destruct();
    }

    mapping(string:array(multiset(string))) get_expand_histogram()
    {
      if (!full_revision_set || !sizeof(full_revision_set)) {
	return ([]);
      }
      mapping(string:array(multiset(string))) res = ([]);
      foreach(full_revision_set; string path; string full_rev_info) {
	string rev_info = full_rev_info[4..];
	if (!mode_from_rev_info(rev_info)) continue;	// Deleted.
	string ext = file_extension_glob(path);
	array(multiset(string)) hist = res[ext];
	if (!hist) {
	  // FIXME: Use symbolic limit for the constant.
	  hist = res[ext] = allocate(EXPAND_ALL + 1);
	}
	RevisionFlags expand = expand_from_rev_info(rev_info) & EXPAND_ALL;
	if (!hist[expand]) {
	  hist[expand] = (< path >);
	} else {
	  hist[expand][path] = 1;
	}
      }
      return res;
    }

    array(GitCommit) ordered_parents()
    {
      return git_sort(map(indices(parents), git_commits));
    }

    GitCommit first_parent()
    {
      if (!sizeof(parents)) return UNDEFINED;
      return ordered_parents()[0];
    }

    string format_message()
    {
      string message = this_program::message;
      if (!message) {
	message = "Joining branches.\n";
      } else if (catch(string tmp = utf8_to_string(message))) {
	// Not valid UTF-8. Fall back to iso-8859-1.
	message = string_to_utf8(message);
      }
      if ((message == "") || (message == "\n")) {
	// This is the CVS default log message.
	message = "*** empty log message ***\n";
      }
      if (!has_suffix(message, "\n")) message += "\n";
      message += "\n";

      return message;
    }

    void generate(Flags|void flags)
    {
      if (git_id) return;

      if (!leaves) {
	werror("Warning: Commit %O is not on any branch!\n", uuid);
	return;
      }

      // First ensure that our parents have been generated.
      array(GitCommit) parent_commits = ordered_parents();
      parent_commits->generate();

      array(GitCommit) soft_parent_commits =
	git_sort(map(indices(soft_parents - parents), git_commits));
      soft_parent_commits->generate();
      
      // Generate a merged history, and check whether
      // we need to regenerate the .gitattributes file.
      int generate_gitattributes;

      if (sizeof(parent_commits)) {
	// Merge the revisions from our (true) parents.
	// FIXME: This fails when there are conflicting files that
	//        have modification times in reverse order. Unlikely.
	if (!(full_revision_set = parent_commits[0]->full_revision_set)) {
	  // Probably an out of order hidden initial commit.
	  full_revision_set = ([]);
	} else {
	  full_revision_set += ([]);
	}
	if (sizeof(parent_commits) > 1) {
	  foreach(parent_commits[1..]->full_revision_set,
		  mapping(string:string) rev_set) {
	    foreach(rev_set; string path; string full_rev_info) {
	      if (!full_revision_set[path] ||
		  (full_revision_set[path] < full_rev_info)) {
		string rev_info = full_rev_info[4..];
		if (!generate_gitattributes &&
		    (!full_revision_set[path] ||
		     !mode_from_rev_info(rev_info) ||
		     (expand_from_rev_info(full_revision_set[path][4..]) !=
		      expand_from_rev_info(rev_info)))) {
		    // There might be a need to change the .gitattributes.
		  generate_gitattributes = 1;
		}
		full_revision_set[path] = full_rev_info;
	      }
	    }
	  }
	}
      } else {
	generate_gitattributes = 1;
	full_revision_set = ([]);
      }

      // Add our own revisions.
      foreach(revisions; string path; string rev_info) {
	if (!generate_gitattributes &&
	    (!full_revision_set[path] ||
	     !mode_from_rev_info(rev_info) ||
	     (expand_from_rev_info(full_revision_set[path][4..]) !=
	      expand_from_rev_info(rev_info)))) {
	  // There might be a need to change the .gitattributes.
	  generate_gitattributes = 1;
	}

	full_revision_set[path] = sprintf("%04c%s", timestamp, rev_info);
      }

      int commit_timestamp = timestamp;

      if (time_offset) {
	// Undo the timestamp bumping.
	timestamp -= time_offset;
	time_offset = 0;
      }

      // Then we can start actually messing with git...
      if ((sizeof(parent_commits) == 1) &&
	  ((commit_flags & COMMIT_HIDE) ||
	   equal(parent_commits[0]->full_revision_set, full_revision_set))) {
	// Hidden commit or a noop commit, probably a tag.
	git_id = parent_commits[0]->git_id;
	// Propagate the revision set of our parent.
	full_revision_set = parent_commits[0]->full_revision_set;
      } else if (!sizeof(parent_commits) && (commit_flags & COMMIT_HIDE)) {
	// Hidden initial commit.
	// Unlink from children to not confuse them.
	foreach(map(indices(children), git_commits), GitCommit c) {
	  c->detach_parent(this_object());
	}
      } else {

	if (full_revision_set[".gitattributes"] &&
	    mode_from_rev_info(full_revision_set[".gitattributes"][4..])) {
	  // If there's a top-level .gitattributes, we assume
	  // it contains everything needed.
	  generate_gitattributes = 0;
	}
	    
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
	string message = format_message();

	while( strlen(message) > 2 && has_suffix( message, "\n\n" ) )
	  message = message[..strlen(message)-2];

	// message += "ID: " + uuid + "\n";
	if (!(flags & FLAG_DISABLE_REV)) {
	  message += "\n";
	  foreach(sort(indices(revisions)), string path) {
	    string rev_info = full_revision_set[path][4..];
	    string orig_path = path_from_rev_info(rev_info) || path;
	    message += "Rev: " + orig_path + ":" + rev_from_rev_info(rev_info);
#if 0
	    if (orig_path != path)
	      message += " (now " + path + ")";
#endif
	    message += "\n";
	  }
	}
#ifdef LEAF_SPLIT_DEBUG
	if (sizeof(children) > 1) {
	  Leafset leaves = 0;
	  Leafset dead_leaves = 0;
	  foreach(map(indices(children), git_commits), GitCommit c) {
	    leaves |= c->leaves;
	    dead_leaves |= c->dead_leaves;
	  }
	  foreach(map(sort(indices(children)), git_commits), GitCommit c) {
	    Leafset l = c->leaves & dead_leaves;
	    message += "Child: " + c->uuid + "\n";
	    while(l) {
	      Leafset leaf = l & ~(l - 1);
	      message += "Leaf: " + leaf_lookup[leaf->digits(256)] + "\n";
	      l -= leaf;
	    }
	    l = c->dead_leaves & leaves;
	    while(l) {
	      Leafset leaf = l & ~(l - 1);
	      message += "Dead-Leaf: " + leaf_lookup[leaf->digits(256)] + "\n";
	      l -= leaf;
	    }
	  }
	}
#endif
#ifdef LEAF_MERGE_DEBUG
	if (sizeof(parents) > 1) {
	  Leafset leaves = 0;
	  Leafset dead_leaves = 0;
	  foreach(map(indices(parents), git_commits), GitCommit p) {
	    leaves |= p->leaves;
	    dead_leaves |= p->dead_leaves;
	  }
	  foreach(map(sort(indices(parents)), git_commits), GitCommit p) {
	    Leafset l = p->leaves & dead_leaves;
	    message += "Parent: " + p->uuid + "\n";
	    while(l) {
	      Leafset leaf = l & ~(l - 1);
	      message += "Leaf: " + leaf_lookup[leaf->digits(256)] + "\n";
	      l -= leaf;
	    }
	    l = p->dead_leaves & leaves;
	    while(l) {
	      Leafset leaf = l & ~(l - 1);
	      message += "Dead-Leaf: " + leaf_lookup[leaf->digits(256)] + "\n";
	      l -= leaf;
	    }
	  }
	}
#endif
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

	array(string) author_info =
	  author_lookup(this_object(), author, timestamp);
	array(string) committer_info =
	  author_lookup(this_object(), committer || author, commit_timestamp);

	string main_leaf = leaf_lookup[(leaves & ~(leaves-1))->digits(256)];

	if (sizeof(parent_commits) && parent_commits[0]->git_id &&
	    sizeof(parent_commits[0]->git_id)) {
	  // Make sure the ref is in the place we expect...
	  write("reset refs/%s\n"
		"from %s\n",
		main_leaf[..<1], parent_commits[0]->git_id);
	}
	int atz, ctz;
	if (sizeof(author_info) > 2) {
	  atz = tzoffset(timestamp, author_info[2]);
	} else {
	  atz = tzoffset(timestamp);
	}
	if (sizeof(committer_info) > 2) {
	  ctz = tzoffset(commit_timestamp, committer_info[2]);
	} else {
	  ctz = tzoffset(commit_timestamp);
	}
	write("# Committing %s\n"
	      "commit refs/%s\n"
	      "mark %s\n"
	      "author %s <%s> %d %+05d\n"
	      "committer %s <%s> %d %+05d\n"
	      "data %d\n"
	      "%s\n",
	      uuid,
	      main_leaf[..<1],
	      git_id = new_mark(),
	      author_info[0], author_info[1], timestamp, atz,
	      committer_info[0], committer_info[1], commit_timestamp, ctz,
	      sizeof(message),
	      message);
	
	mapping(string:string) git_state;
	int need_gitignore = !sizeof(parent_commits);

	if (sizeof(parent_commits) && parent_commits[0]->git_id &&
	    sizeof(parent_commits[0]->git_id)) {
	  write("from %s\n", parent_commits[0]->git_id);
	  git_state = parent_commits[0]->full_revision_set + ([]);
	  foreach(parent_commits[1..], GitCommit p) {
	    if (sizeof(p->git_id)) {
	      write("merge %s\n", p->git_id);
	    }
	  }
	  foreach(soft_parent_commits, GitCommit p) {
	    if (sizeof(p->git_id)) {
	      write("merge %s\n", p->git_id);
	    }
	  }
	  if (!sizeof(git_state)) {
	    // The parent is probably a fake commit masking
	    // the set of files. Make sure to clear the state.
	    write("deleteall\n");
	    need_gitignore = 1;
	  }
	} else {
	  if (sizeof(soft_parent_commits) && soft_parent_commits[0]->git_id &&
	      sizeof(soft_parent_commits[0]->git_id)) {
	    write("from %s\n", soft_parent_commits[0]->git_id);
	    foreach(soft_parent_commits[1..], GitCommit p) {
	      if (sizeof(p->git_id)) {
		write("merge %s\n", p->git_id);
	      }
	    }
	  }
	  write("deleteall\n");
	  git_state = ([]);
	  need_gitignore = 1;
	}

	// werror("Generating commit for %s\n", pretty_git(this_object(), 1));

	// Remove files from the git index that we don't want anymore.
	foreach(git_state; string path; string full_rev_info) {
	  if (full_revision_set[path] == full_rev_info) continue;
	  if (!full_revision_set[path] ||
	      !mode_from_rev_info(full_revision_set[path][4..])) {
	    write("D %s\n", path);
	    m_delete(git_state, path);
	    generate_gitattributes = 1;
	    if (has_suffix("/" + path, "/.cvsignore")) {
	      string gitignore = path[..<sizeof(".cvsignore")] + ".gitignore";
	      if (!full_revision_set[gitignore]) {
		// Delete the corresponding automatically generated .gitignore
		// as well.
		write("D %s\n", gitignore);
	      }
	    }
	  }
	}

	// Add the blobs for the revisions to the git index.
	foreach(full_revision_set; string path; string full_rev_info) {
	  if (git_state[path] == full_rev_info) continue;
	  string rev_info = full_rev_info[4..];
	  string sha = sha_from_rev_info(rev_info);
	  if (sha != "\0"*20) {
	    int mode = 0100644;
	    int raw_mode = mode_from_rev_info(rev_info);
	    if (raw_mode & 0111) mode |= 0111;
	    write("M %6o %s %s\n", 
		  mode, git_blobs[sha], path);
	    git_state[path] = full_rev_info;
	    if (has_suffix("/" + path, "/.cvsignore")) {
	      string gitignore = path[..<sizeof(".cvsignore")] + ".gitignore";
	      if (!full_revision_set[gitignore]) {
		// Generate a corresponding .gitignore.
		string data = convert_cvsignore(file_contents[sha]);
		if (path == ".cvsignore") {
		  // Prepend the default recursive cvsignore patterns.
		  data = default_cvsignore * "\n" + "\n" + data;
		}
		write("# Corresponding .gitignore.\n"
		      "M %6o inline %s\n"
		      "data %d\n"
		      "%s\n",
		      mode, gitignore,
		      sizeof(data),
		      data);
	      }
	    }
	  }
	}

	// Handle the top-level .gitignore.
	if (!full_revision_set[".cvsignore"] &&
	    !full_revision_set[".gitignore"] &&
	    need_gitignore) {
	  // Root commit lacking .gitignore generated or otherwise.

	  string data = default_cvsignore * "\n" + "\n";
	  write("# Default .gitignore.\n"
		"M 100644 inline .gitignore\n"
		"data %d\n"
		"%s\n",
		sizeof(data),
		data);
	}

	// Generate .gitattributes.
	if (generate_gitattributes) {

	  // FIXME: There are multiple approaches here; either
	  //        add a rule for * for the most common RevisionFlags,
	  //        and then add exceptions for some extensions,
	  //        and then exceptions for specific files,
	  //        or skip the rule for *.
	  //        To reduce the number of changes to the .gitattributes
	  //        file and its size, we use the first approach.

	  mapping(string:array(multiset(string))) ext_hist =
	    get_expand_histogram();

	  // Some special cases.
	  if (!full_revision_set[".gitignore"]) {
	    ext_hist["*.gitignore"] = ext_hist["*.gitignore"] ||
	      allocate(EXPAND_ALL + 1);
	    if (!ext_hist["*.gitignore"][EXPAND_ALL]) {
	      ext_hist["*.gitignore"][EXPAND_ALL] = (<".gitignore">);
	    } else {
	      ext_hist["*.gitignore"][EXPAND_ALL][".gitignore"] = 1;
	    }
	  }
	  ext_hist["*.gitattributes"] = ext_hist["*.gitattributes"] ||
	    allocate(EXPAND_ALL + 1);
	  if (!ext_hist["*.gitattributes"][EXPAND_ALL]) {
	    ext_hist["*.gitattributes"][EXPAND_ALL] = (<".gitattributes">);
	  } else {
	    ext_hist["*.gitattributes"][EXPAND_ALL][".gitattributes"] = 1;
	  }

	  if (handler && handler->adjust_ext_histogram) {
	    handler->adjust_ext_histogram(GitRepository::this, this_object(),
					  ext_hist);
	  }

	  // Content for the .gitattributes file.
	  // Start by redefining the binary macro to also handle ident.
	  string data = "[attr]binary -text -crlf -diff -ident\n";

	  array(int) compact_hist = allocate(EXPAND_ALL + 1);
	  foreach(ext_hist; ; array(multiset(string)) h) {
	    foreach(h; RevisionFlags ext_flag; multiset(string) l) {
	      // Not quite correct, but probably good enough.
	      if (l) {
		compact_hist[ext_flag] += sizeof(l);
	      }
	    }
	  }
	  array(RevisionFlags) ind = indices(compact_hist);
	  sort(compact_hist, ind);
	  RevisionFlags global_default = ind[-1];

	  if ((global_default == EXPAND_BINARY) && compact_hist[-2]) {
	    // Avoid having a line "* binary".
	    global_default = ind[-2];
	  }

	  // NB: EXPAND_TEXT corresponds to git's default CRLF behaviour.
	  data += "* " +
	    convert_expansion_flags_to_attrs(global_default,
					     EXPAND_TEXT|EXPAND_MAGIC) +
	    "\n";

	  foreach(sort(indices(ext_hist)), string ext) {
	    array(multiset(string)) hist = ext_hist[ext];
	    ind = indices(hist);
	    array(int) val = map(hist, lambda(multiset(string) l) {
					 return l && sizeof(l);
				       });

	    RevisionFlags ext_default = global_default;
	    sort(val, ind);
	    ind = reverse(ind);
	    foreach(ind; int i; RevisionFlags ext_flag) {
	      if (!hist[ext_flag]) break;
	      if (ext_flag == ext_default) continue;
	      string attrs =
		convert_expansion_flags_to_attrs(ext_flag, ext_default);
	      if (!i) {
		// The default rule for the extension.
		data += ext + " " + attrs + "\n";
		ext_default = ext_flag;
	      } else {
		// There are exceptions...
		// FIXME: There are multiple possibilities here.
		//        This is the quick and dirty way.
		foreach(hist[ext_flag]; string path;) {
		  // List each of the exceptional files.
		  // FIXME: What are the quoting rules?
		  data += "/" + fnquote(path) + " " + attrs + "\n";
		}
	      }
	    }
	  }

	  int got_expanded_keyword;
	  foreach(sort(indices(full_revision_set)), string path) {
	    string rev_info = full_revision_set[path][4..];
	    if (!mode_from_rev_info(rev_info)) continue;	// Deleted.
	    RevisionFlags expand = expand_from_rev_info(rev_info);
	    if (!(flags & FLAG_NO_KEYWORDS) && (expand & EXPAND_GOT_KEYWORD)) {
	      if (!got_expanded_keyword) {
		need_pre_commit_hook = 1;
		got_expanded_keyword = 1;
		data += "\n"
		  "# Handling of foreign (ie CVS) identifiers.\n"
		  "#\n"
		  "[attr]foreign_ident -ident block_commit=Remove-foreign_ident-attribute-before-commit.\n"
		  "# Files containing CVS ids follow.\n"
		  "# Remove the corresponding line before committing\n"
		  "# changes to these files.\n";
	      }
	      data += "/" + fnquote(path) + " foreign_ident\n";
	    }
	  }
	  write("# Git attributes.\n"
		"M 100644 inline .gitattributes\n"
		"data %d\n"
		"%s\n",
		sizeof(data),
		data);
	}

	// End marker (compat with old fast-import).
	write("\n");
      }
      
      if (git_id) {
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

  class MergeCommit
  {
    inherit GitCommit;

    constant is_merge = 1;

    GitCommit _first_parent;

    array(GitCommit) ordered_parents()
    {
      if (!_first_parent) return ::ordered_parents();
      return ({ _first_parent }) + (::ordered_parents() - ({ _first_parent }));
    }

    GitCommit first_parent()
    {
      return _first_parent;
    }

    void hook_parent(GitCommit p)
    {
      if (!_first_parent) _first_parent = p;
      ::hook_parent(p);
    }

    void detach_parent(GitCommit p)
    {
      ::detach_parent(p);
      if (p == _first_parent) _first_parent = UNDEFINED;
      if ((sizeof(parents) < 2) && !sizeof(revisions)) {
	// This commit doesn't have a purpose if the merged
	// parents go away.
	_first_parent = UNDEFINED;
	commit_flags |= COMMIT_HIDE;
      }
    }

    void implode(mapping(string:mapping(string:int))|void dirty_commits)
    {
      // Detach from our parents and children.
      _first_parent = UNDEFINED;
      commit_flags |= COMMIT_HIDE;
      ::implode(dirty_commits);
    }

    array(string|Leafset) low_format_message(Leafset leaves)
    {
      if (leaves & heads) {
	leaves &= heads;
      }
      Leafset leaf = leaves & ~(leaves - 1);
      string l = leaf_lookup[leaf->digits(256)][..<1];
      if (has_prefix(l, "ROOTS/")) {
	sscanf(l, "ROOTS/%*d/%s", l);
      }
      return ({ "'" + l + "'", leaf });
    }

    string format_message()
    {
      if (sizeof(revisions)) return ::format_message();

      array(GitCommit) merges = ordered_parents()[1..];

      if (!sizeof(merges)) return ::format_message();
      string prefix = "Merge ";

      // Check if there's a common tag or branch for all the merges.
      Leafset missing = merges[0]->leaves;
      foreach(merges; int i; GitCommit merged_parent) {
	missing &= merged_parent->leaves ^ leaves;
      }

      string label;
      Leafset listed;
      if (missing) {
	// Yes.
	[label, listed] = low_format_message(missing);
	prefix += label;
      } else {
	// No. List a subset that covers them all.
	foreach(merges; int i; GitCommit merged_parent) {
	  Leafset missing = merged_parent->leaves ^ leaves;

	  if ((missing & listed) || !missing) continue;

	  Leafset l;
	  [label, l] = low_format_message(missing);

	  listed |= l;

	  if (i) prefix += ", ";
	  prefix += label;
	}
      }
      if (!message) return prefix + ".\n\n";
      return prefix + ": " + ::format_message();
    }

    //! @param mp
    //!   Merged parent (ie not the first parent).
    //! @param killed_leaves
    //!   This is a set of leaves that @[mp] has, that this commit
    //!   must not have.
    protected void create(GitCommit mp, Leafset killed_leaves)
    {
      ::create(mp->uuid, killed_leaves->digits(16));
      ::hook_parent(mp);
      if (mp->commit_flags & COMMIT_HIDE) {
	commit_flags |= COMMIT_HIDE;
      }
      message = mp->message;
      timestamp = mp->timestamp + 1;
      time_offset = mp->time_offset + 1;
      timestamp_low = mp->timestamp_low;
      author = mp->author;
      committer = mp->committer;
    }
  }

  //! Generate a @expr{rev_info@} string.
  //!
  //! @param mode
  //!   Mode bits for the file.
  //!   Mode @expr{0@} (zero) indicates a deletion.
  //!
  //! @param sha
  //!   SHA1 hash of the content for the file.
  //!
  //! @param rev
  //!   Display revision of the file.
  //!
  //! @param expand
  //!   RCS expansion flags for the file.
  //!
  //! @param display_path
  //!   Path to show in the commit message if different
  //!   from the gir repository path.
  //!
  string make_rev_info(int mode, string sha, string rev,
		       RevisionFlags|void expand, string|void display_path)
  {
    if (!mode) {
      if (!has_suffix(rev, "(DEAD)")) rev += "(DEAD)";
      sha = "\0"*20;
    } else if (mode & 0111) {
      mode = 0100755;
    } else {
      mode = 0100644;
    }
    if (display_path)
      return sprintf("%4c%s%1c%s\0%s", mode, sha, expand, rev, display_path);
    return sprintf("%4c%s%1c%s", mode, sha, expand, rev);
  }

  string make_rev_info_from_rev(RCSFile.Revision rev, int mode)
  {
    if (rev->state == "dead") {
      mode = 0;
      rev->revision_flags &= ~EXPAND_GOT_KEYWORD;
    }
    return make_rev_info(mode, rev->sha, rev->revision, rev->revision_flags,
			 rev->display_path);
  }

  string rev_from_rev_info(string rev_info)
  {
    return (rev_info[25..] / "\0")[0];
  }

  string path_from_rev_info(string rev_info)
  {
    array(string) a = (rev_info[25..] / "\0");
    return (sizeof(a) > 1) && a[1];
  }

  int mode_from_rev_info(string rev_info)
  {
    return array_sscanf(rev_info, "%4c")[0];
  }

  string sha_from_rev_info(string rev_info)
  {
    return rev_info[4..23];
  }

  RevisionFlags expand_from_rev_info(string rev_info)
  {
    RevisionFlags expand = rev_info[24];
    return expand;
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
  Leafset heads;
  Leafset vendor_heads;
#else
  Leafset root_commits = ([]);
  Leafset heads = ([]);
#endif

  string latest_master_branch = "heads/master";

  GitCommit ref_factory(string ref)
  {
    GitRepository.GitCommit r = git_refs[ref];
    if (!r) {
      r = git_refs[ref] = GitCommit(ref);
    }
    return r;
  }

  void set_master_branch(string master)
  {
    master_branch = master;
    master = remote + master;
    GitCommit m = ref_factory(master);
    heads |= m->is_leaf;
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
    latest_master_branch = master;
  }

  string add_root_commit(string git_id, int|void timestamp, string|void prev)
  {
    GitCommit root_commit =
      GitCommit("ROOTS/" + (num_roots++) + "/" + git_id);

    // This is somewhat magic...
    // Since the root commits are older than all existing commits,
    // and are compatible with all other leaves, they will automatically
    // be hooked as parents to the relevant nodes during the graphing.

    root_commit->git_id = git_id;
    root_commit->timestamp = -0x7fffffff;

    if (prev) {
      root_commit->hook_parent(git_commits[prev]);
    }

    if (GitCommit head = (git_refs[git_id] ||
			  git_refs[remote + git_id] ||
			  git_refs["heads/" + git_id])) {
      // Copy stuff from the existing branch (since it might move...).
      root_commit->timestamp = head->timestamp;
      foreach(map(indices(head->parents), git_commits), GitCommit p) {
	root_commit->hook_parent(p);
      }
    }

    if (!zero_type(timestamp)) {
      root_commit->timestamp = timestamp;
      root_commit->commit_flags |= COMMIT_TS;
    }

    root_commit->timestamp_low = root_commit->timestamp;

    if (master_branch) {
      // Make sure the root is compatible with the current master branch.
      GitCommit m = ref_factory(remote + master_branch);
      heads |= git_refs[remote + master_branch]->is_leaf;
      m->hook_parent(root_commit);
    }

    // Ensure that files aren't propagated between archives...
    root_commit->full_revision_set = ([]);
    // Ensure that the root commits won't be merged to each other...
    root_commits |= root_commit->is_leaf;
    root_commit->propagate_dead_leaves(root_commits & ~root_commit->leaves);

    // We don't want the root to show up as a node of its own in git.
    root_commit->commit_flags |= COMMIT_HIDE;
    return root_commit->uuid;
  }

  //! Find a commit with the proper content and history.
  //!
  //! @param rev
  //!   Revision to find.
  //!
  //! @param parent_uuid
  //!   Id of a parent.
  //!
  //! @returns
  //!   Returns the @[GitCommit] if found and @[UNDEFINED] otherwise.
  GitCommit find_commit(RCSFile.Revision rev, string parent_uuid)
  {
    string suffix = rev->is_fake_revision?rev->base_rev:rev->revision;
    if (rev->state == "dead") {
      suffix += "(DEAD)";
    }
    if (rev->display_path) {
      suffix += "\0" + rev->display_path;
    }
    int i;
    string key = sprintf("%s:%s", rev->path, rev->revision);
    do {
      GitCommit res = git_commits[key];
      if (!res) return UNDEFINED;
      key = sprintf("%s:%d:%s", rev->path, i++, rev->revision);
      if (!parent_uuid) {
	if (sizeof(res->parents) || sizeof(res->soft_parents)) {
	  continue;
	}
      } else {
	if (!res->parents[parent_uuid] && !res->soft_parents[parent_uuid]) {
	  continue;
	}
      }
      if (!has_suffix(res->revisions[rev->path]||"", suffix)) {
	continue;
      }
      if ((sha_from_rev_info(res->revisions[rev->path]||"") == rev->sha) &&
	  (res->message == rev->log) &&
	  (res->timestamp == rev->time->unix_time()) &&
	  (res->committer == rev->author)) {
	// Found.
	if (handler && handler->filter_commits) {
	  // Check if the handler wants to do something with it.
	  res = handler->filter_commits(this_object(), res, rev);
	}
	if (res) {
	  return res;
	}
      }
    } while (1);
  }

  GitCommit commit_factory(RCSFile.Revision rev, int|void mode)
  {
    string rev_info;

    if (rev->state == "dead") {
      mode = 0;
    } else {
      // Ensure a valid file mode for git.
      mode |= 0100644;
    }

    string revision = rev->is_fake_revision?rev->base_rev:rev->revision;

    rev_info = make_rev_info(mode, rev->sha, revision, rev->revision_flags,
			     rev->display_path);

    string uuid = rev->path + ":" + rev->revision;
    int cnt;
    while (git_commits[uuid]) {
      uuid = rev->path + ":" + cnt++ + ":" + rev->revision;
    }

    GitCommit commit = GitCommit(rev->path, rev->revision, uuid);

    commit->timestamp = commit->timestamp_low = rev->time->unix_time();
    commit->revisions[rev->path] = rev_info;
    commit->author = rev->actual_author || rev->author;
    commit->committer = rev->author;
    commit->message = rev->log;
    switch(rev->state) {
    case "dead":
      // The handler wants this revision dead.
      commit->commit_flags |= COMMIT_DEAD;
      break;
    case "fake":
      // The commit may have some of the parent's tags.
      commit->commit_flags |= COMMIT_FAKE;
    }

    return commit;
  }

  MergeCommit merge_factory(GitCommit parent, Leafset killed_leaves)
  {
    string uuid = parent->uuid + ":" + killed_leaves->digits(16);
    GitCommit m = git_commits[uuid];
    if (m) return m;
    return MergeCommit(parent, killed_leaves);
  }

  GitCommit get_commit(RCSFile rcs_file, mapping(string:GitCommit) rcs_commits,
		       string rev)
  {
    if (!rev) return UNDEFINED;
    GitCommit res = rcs_commits[rev];
    if (res) return res;
    RCSFile.Revision r = rcs_file->revisions[rev];
    return rcs_commits[rev] = get_commit(rcs_file, rcs_commits, r->ancestor);
  }

  void init_git_branch(string tag, GitCommit c)
  {
    if (!c) return;

    GitCommit tag_commit = ref_factory(tag);
    //werror("initing branch: %O %O %O %O\n", path, tag, branch_rev, rcs_rev);
    //werror("L:%O\n", prev_commit);

    tag_commit->hook_parent(c);
#ifdef GIT_VERIFY
    verify_git_commits(1);
#endif
  }

  //! Checks if leaves are attachable to branches, and attaches those that are.
  //!
  //! This ensures that partial tags won't accumulate excessive children.
  void check_attached_to_branch(Flags flags, GitCommit c, int|void show_compat)
  {
    if (c->leaves & heads) return;

    Leafset mask = heads;
    mask &= ~c->dead_leaves;
    if (mask) {
      Leafset leaves = mask;
      while(leaves) {
	Leafset leaf = leaves & ~(leaves - 1);
	GitCommit l = git_commits[leaf_lookup[leaf->digits(256)]];
	if (!l || (l->timestamp < c->timestamp) && !c->is_leaf) {
	  // Not actually compatible with the branch.
	  mask -= leaf;
	}
	leaves -= leaf;
      }
    }
    if (mask) {
      if (show_compat) {
	progress(flags,
		 "\t%s is compatible with the following branches:\n",
		 c->uuid);
	while(mask) {
	  Leafset leaf = mask & ~(mask - 1);
	  progress(flags, "\t\t%s\n",
		   leaf_lookup[leaf->digits(256)] || "NONE");
	  mask -= leaf;
	}
      } else if (c->is_leaf) {
	foreach(map(indices(c->parents), git_commits), GitCommit p) {
	  mask &= p->leaves;
	}
	while(mask) {
	  Leafset leaf = mask & ~(mask - 1);
	  mask -= leaf;
	  GitCommit l = git_commits[leaf_lookup[leaf->digits(256)]];
	  if (l) l->hook_parent(c);
	}
      }
    } else {
      progress(flags,
	       "\t%s does not belong to any branch!\n",
	       c->uuid);
      // Find the most popular branch for the tag.
      mapping(Leafset:int) leafset_histogram = ([]);
      foreach(map(indices(c->parents), git_commits), GitCommit p) {
	leafset_histogram[p->leaves & heads]++;
      }
      mapping(Leafset:int) branch_histogram = ([]);
      foreach(leafset_histogram; Leafset set; int cnt) {
	while (set) {
	  Leafset leaf = set & ~(set - 1);
	  set -= leaf;
	  branch_histogram[leaf] += cnt;
	}
      }
      if (sizeof(branch_histogram)) {
	array(Leafset) branches = indices(branch_histogram);
	sort(values(branch_histogram), branches);
	Leafset m = branches[-1];
	progress(flags,
		 "\tMost compatible with %s (%d/%d parents)\n"
		 "\tIncompatible parents are:\n",
		 (leaf_lookup[m->digits(256)] || "NONE:")[..<1],
		 branch_histogram[m], sizeof(c->parents));
	foreach(git_sort(map(indices(c->parents), git_commits)),
		GitCommit p) {
	  if (p->dead_leaves & m) {
	    progress(flags, "\t\t%s\n", p->uuid);
	  }
	}
      } else {
	progress(flags, "\nIts parents are incompatible with all branches!\n");
      }
    }
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
      if (c->leaves & c->dead_leaves) {
	werror("Intersecting leaves:\n");
	describe_leaves("\t", c->leaves & c->dead_leaves, "\n");
	error("The set of leaves and set of dead leaves for %O intersect.\n"
	      "%s\n",
	      uuid, pretty_git(c));
      }
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
    if (r->commit_flags & COMMIT_TS) return;
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

  //! Import a single RCS file.
  //!
  //! @param path
  //!   Default path in the git repository for the revisions.
  //!
  //! @param rcs_file
  //!   RCS file to import.
  //!
  //! @param mode
  //!   File mode bits for the RCS file.
  //!
  //! @param flags
  //!
  void add_rcs_file(string path, RCSFile rcs_file, int mode, Flags|void flags)
  {
    if (handler && handler->repair_rcs_file) {
      handler->repair_rcs_file(this_object(), path, rcs_file, flags);
    }

    // Scan the revisions in reverse order to reduce the amount of recursion.
    foreach(reverse(sort(indices(rcs_file->revisions))), string r) {
      RCSFile.Revision rev = rcs_file->revisions[r];

      lookup_contributor(rev);

      if ((rev->state == "dead") || (flags & FLAG_PRETEND)) {
	rev->sha = "\0"*20;
	continue;
      }

      string data = rcs_file->get_contents_for_revision(rev);
      if ((rev->revision_flags & EXPAND_TEXT) == EXPAND_CRLF) {
	// Force a normalization.
	// Note that this will be reversed on checkout by .gitattributes.
	data = replace(data, "\r\n", "\n");
	rev->sha = Crypto.SHA1()->update(data)->digest();
      }
      if (rev->revision_flags & EXPAND_KEYWORDS) {
	if (flags & FLAG_NO_KEYWORDS) {
	  data = rcs_file->expand_keywords_for_revision(rev, data, -1);
	} else {
	  data = rcs_file->expand_keywords_for_revision(rev, data);
	}
	rev->sha = Crypto.SHA1()->update(data)->digest();
      }
      if (!git_blobs[rev->sha]) {
	write("# %s\n"
	      "# %s:%s\n"
	      "blob\n"
	      "mark %s\n"
	      "data %d\n"
	      "%s\n",
	      rcs_file->rcs_file_name, rev->path || path, r,
	      git_blobs[rev->sha] = new_mark(),
	      sizeof(data), data);
      }
      if (rev->path && has_suffix("/" + rev->path, "/.cvsignore") &&
	  !file_contents[rev->sha]) {
	// Save .cvsignore content for later processing.
	file_contents[rev->sha] = data;
      }
    }
    // Cleanup the memory use...
    foreach(rcs_file->revisions; string r; RCSFile.Revision rev) {
      if (rev->revision == rcs_file->head) continue;
      rev->text = UNDEFINED;
    }

    mapping(string:GitCommit) rcs_commits = ([]);

    // Find the set of GitCommits, and chain them.
    ADT.Stack stack = ADT.Stack();
    foreach(rcs_file->revisions; ; RCSFile.Revision rev) {
      if (rcs_commits[rev->revision] || !rev->path) continue;
      stack->push(0);	// Sentinel.
      GitCommit prev_c;
      while (!(prev_c = rcs_commits[rev->revision])) {
	if (!rev->ancestor) {
	  prev_c = rcs_commits[rev->revision] =
	    find_commit(rev, UNDEFINED) || commit_factory(rev, mode);
	  if (rev->state == "dead") {
	    // A dead initial commit.
	    // Probably an automatic commit for a file
	    // that was initially added on a branch.
	    prev_c->commit_flags |= COMMIT_HIDE;
	  }
	  break;
	}
	if (rev->path) {
	  stack->push(rev);
	}
	rev = rcs_file->revisions[rev->ancestor];
      }
      RCSFile.Revision prev_rev = rev;
      while (rev = stack->pop()) {
	GitCommit c = find_commit(rev, prev_c->uuid);
	if (!c) {
	  c = commit_factory(rev, mode);
	  if (rev->revision_flags & REVISION_MERGE) {
	    // NB: No need to check for renames, since revisions
	    //     don't propagate over soft links.
	    c->hook_soft_parent(prev_c);
	  } else {
	    if ((prev_rev->path != rev->path) &&
		!(rev->revision_flags & REVISION_COPY)) {
	      // Rename. Add a deletion of the old name.
	      string revision =
		rev->is_fake_revision?rev->base_rev:rev->revision;
	      c->revisions[prev_rev->path] =
		make_rev_info(0, "", revision, prev_rev->revision_flags,
			      prev_rev->display_path);
	    }
	    c->hook_parent(prev_c);
	  }
	  if ((rev->revision == "1.1.1.1") &&
	      (rev->ancestor == "1.1") &&
	      (prev_c->message == "Initial revision\n") &&
	      (rev->rcs_text == "")) {
	    // Prev_c (aka 1.1) was the automatic commit from running cvs import.
	    // Attempt to hide it.
	    prev_c->commit_flags |= COMMIT_HIDE;
	  }
	}
	prev_c = rcs_commits[rev->revision] = c;
	prev_rev = rev;
      }
    }
    foreach(rcs_file->revisions; ; RCSFile.Revision rev) {
      GitCommit c = rcs_commits[rev->revision];
      if (!c) continue;
      if (rev->merges) {
	foreach(rev->merges, string merge_rev) {
	  GitCommit m = rcs_commits[merge_rev];
	  if (!m) continue;
	  c->hook_soft_parent(m);
	}
      }
    }

    if (!master_branch) {
      set_master_branch("master");
    }

    Leafset all_leaves;
    Leafset vendor_leaves;
#ifndef USE_BITMASKS
    all_leaves = ([]);
    vendor_leaves = ([]);
#endif

    init_git_branch(remote + master_branch,
		    get_commit(rcs_file, rcs_commits, rcs_file->head));

    all_leaves |= git_refs[remote + master_branch]->is_leaf;
    heads |= git_refs[remote + master_branch]->is_leaf;

    foreach(rcs_file->tags; string tag; string tag_rev) {
      tag = fix_cvs_tag(tag);

      if ((tag_rev == "0.0.0.0") || (tag_rev == "0.0")) {
	// Force the file to be incompatible with the branch or tag.
	if (tag_rev == "0.0.0.0") {
	  tag = remote + tag;
	} else {
	  tag = "tags/" + tag;
	}
	GitCommit t = ref_factory(tag);
	all_leaves |= t->is_leaf;
	if (tag_rev == "0.0.0.0") {
	  heads |= t->is_leaf;
	}
	continue;
      }

      if (tag_rev == "1.1.1.1") {
	// This might be the automatic vendor branch tag.
	// We handle it later, see below.
	if (!starters[tag]) {
	  starters[tag] = ([ rcs_commits["1.1.1.1"]->uuid:1 ]);
	} else {
	  starters[tag][rcs_commits["1.1.1.1"]->uuid] = 1;
	}
	continue;
      }

      array(string) splitted_tag = tag_rev/".";
      if (rcs_file->symbol_is_branch(tag_rev)) {
	// Note that there are such things as revision "3.0"
	// in some RCS files...
	splitted_tag = splitted_tag[..<2] + splitted_tag[<0..];
	tag_rev = splitted_tag * ".";
      }
      string rcs_rev;
      string ref = "tags/" + tag;
      if ((rcs_rev = rcs_file->branch_heads[tag_rev])) {
	ref = remote + tag;
	tag_rev = rcs_rev;
      }
      init_git_branch(ref, get_commit(rcs_file, rcs_commits, tag_rev));
      if ((sizeof(splitted_tag) > 2) && (splitted_tag[2][-1] & 1)) {
	// The tag is on something that has branched off a vendor branch.
	// Since the vendor branch may have been the main branch at
	// any time, we mustn't propagate dead leaves from it
	// to the main branch.
	//
	// NB: Tags on the main branch is not a problem, since
	//     we add merge links for any commits there.
	//vendor_leaves |= git_refs[ref]->is_leaf;
#ifdef JOIN_VENDOR_BRANCHES
	if (sizeof(splitted_tag) == 3) {
	  // A vendor branch.
	  vendor_heads |= git_refs[ref]->is_leaf;
	  continue;
	}
#else
#if 0
	if (sizeof(splitted_tag) != 3) {
	  // Branch or tag from a vendor branch.
	  // The branch point could potentially be merged into
	  // the main branch.
	  if (sizeof(splitted_tag) & 1) {
	    // A branch from the vendor branch.
	    vendor_heads |= git_refs[ref]->is_leaf;
	  }
	  continue;
	}
#endif
#endif
      }
      if (!has_prefix(ref, "tags/")) {
	heads |= git_refs[ref]->is_leaf;
      }
      all_leaves |= git_refs[ref]->is_leaf;
    }

    // Time to handle vendor branches.
    if (rcs_file->branch) {
      // A (vendor) branch is acting as the main branch.
      init_git_branch(remote + master_branch, 
		      get_commit(rcs_file, rcs_commits, 
				 rcs_file->branch_heads[rcs_file->branch]));
    }
    // Check if there are any vendor branches. We assume that the
    // first commit on the main branch after a commit on the vendor
    // branch merges the changes of both branches.
    foreach(rcs_file->tags; string tag; string tag_rev) {
      array(string) rev_nos = (tag_rev/".");
      if (rev_nos[-2] == "0") {
	// Note that there are such things as revision "3.0"
	// in some RCS files...
	rev_nos = rev_nos[..<2] + rev_nos[<0..];
      }
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

      string vendor_branch = rev_nos*".";

      string vendor_head = rcs_file->branch_heads[vendor_branch];

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
      RCSFile.Revision vendor_rev = rcs_file->revisions[vendor_head];

      while (vendor_rev && main_rev) {
	while (vendor_rev && rcs_file->revisions[vendor_rev->ancestor] &&
	       (rcs_file->revisions[vendor_rev->ancestor]->time >=
		main_rev->time)) {
	  vendor_rev = rcs_file->revisions[vendor_rev->ancestor];
	}
	if (!vendor_rev || (vendor_rev->revision == main_rev->revision)) break;
	if (vendor_rev->time > main_rev->time) {
#if 0
#ifndef JOIN_VENDOR_BRANCHES
	  if ((rcs_file->branch == vendor_branch) &&
	      (main_rev->revision == main_head))
#endif
	  {
	    // The vendor branch acts as the main branch.
	    // vendor_rev is the first revision on the vendor branch
	    // after the main_rev revision.
	    if (vendor_rev->time < main_rev->time) {
	      error("%s: BAD vendor commit order!\n"
		    "Main: %s, Vendor: %s\n",
		    path, main_rev->revision, vendor_rev->revision);
	    }
	    rcs_commits[vendor_rev->revision]->
	      hook_parent(rcs_commits[main_rev->revision]);
	  }
#endif
	  // Advance vendor_rev.
	  vendor_rev = rcs_file->revisions[vendor_rev->ancestor];
	}
	if (!vendor_rev || (vendor_rev->revision == main_rev->revision)) break;
	while (rcs_file->revisions[main_rev->ancestor] &&
	       (rcs_file->revisions[main_rev->ancestor]->time >
		vendor_rev->time)) {
	  main_rev = rcs_file->revisions[main_rev->ancestor];
	}
	if (!vendor_rev || (vendor_rev->revision == main_rev->revision)) break;
	if (main_rev->time < vendor_rev->time) {
	  error("%s: BAD main commit order!\n"
		"Main: %s, Vendor: %s\n",
		path, main_rev->revision, vendor_rev->revision);
	}
	rcs_commits[main_rev->revision]->
	  hook_parent(rcs_commits[vendor_rev->revision]);
	main_rev = rcs_file->revisions[main_rev->ancestor];
      }
    }

    // Update the dead leaves.
    // FIXME: Sort?
    foreach(rcs_file->revisions;; RCSFile.Revision rev) {
      // Skip fake nodes, since it isn't certain what leaves
      // they should have.
      if ((rev->state == "fake") || !rev->path) continue;
      GitCommit c = rcs_commits[rev->revision];
      if (!c) continue;
#ifdef USE_BITMASKS
      c->propagate_dead_leaves(all_leaves & ~(c->leaves));
#else
      c->propagate_dead_leaves(all_leaves - c->leaves);
#endif
#if 0
      if (vendor_leaves) {
	array(string) a = rev->revision/".";
	// NB: No branch revisions will show up here,
	//     so we don't need to care about the ".0.".
	if ((sizeof(a) > 2) && (a[2][-1] & 1)) {
	  // Revision that has branched off from a vendor branch.
	  c->propagate_dead_leaves(vendor_leaves & ~(c->leaves));
	}
      }
#endif
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
      if (ancestor->full_revision_set) {
	node->hook_parent(ancestor);
	foreach(ancestor->full_revision_set; string path; string rev_info) {
	  if (!rev_set[path] || (rev_set[path] < rev_info)) {
	    rev_set[path] = rev_info;
	  }
	}
	continue;
      }
      foreach(ancestor->revisions; string path; string short_rev_info) {
	string rev_info = sprintf("%4c%s", ancestor->timestamp, short_rev_info);
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

  //! Read and import a directory containing RCS files.
  //!
  //! @param repository
  //!   Filesystem path to the RCS file to read.
  //!
  //! @param flags
  //!
  //! @param path
  //!   Corresponding default path in the resulting git repository.
  //!   Defaults to @expr{""@} (ie the root).
  //!
  //! @param handler_state
  //!   Mapping containing state for use by the handlers.
  //!
  //! @param display_path
  //!   Path to display in the commit messages.
  //!   Defaults to @[path].
  void read_rcs_repository(string repository, Flags|void flags,
			   string|void path, mapping|void handler_state,
			   string|void display_path)
  {
    array(string) files = sort(get_dir(repository));
    path = path || "";
    display_path = display_path || path;
    string handler_path = path;
    handler_state = handler_state ? (handler_state + ([])) : ([]);
    if (handler && handler->enter_directory) {
      array(string|array(string)) a =
	handler->enter_directory(this_object(), handler_path, files, flags,
				 handler_state, display_path);
      if (sizeof(a) == 2) {
	[path, files] = a;
	display_path = path;
      } else {
	[path, files, display_path] = a;
      }
    }
    foreach(files, string fname) {
      string fpath = repository + "/" + fname;
      string subpath = path;
      string display_subpath = display_path;

      if (Stdio.is_dir(fpath)) {
	if ((fname != "Attic") && (fname != "RCS")) {
	  if (subpath != "")
	    subpath += "/" + fname;
	  else
	    subpath = fname;
	  if (display_subpath != "")
	    display_subpath += "/" + fname;
	  else
	    display_subpath = fname;
	}
	read_rcs_repository(fpath, flags, subpath, handler_state,
			    display_subpath);
      } else if (has_suffix(fname, ",v")) {
	fname = fname[..sizeof(fname)-3];
	if (subpath != "")
	  subpath += "/" + fname;
	else
	  subpath = fname;
	if (display_subpath != "")
	  display_subpath += "/" + fname;
	else
	  display_subpath = fname;
	progress(flags, "\r%d: %-65s ", sizeof(git_commits), subpath[<64..]);
	add_rcs_file(subpath, RCSFile(fpath, subpath, UNDEFINED,
				      display_subpath),
		     file_stat(fpath)->mode, flags);
      } else if (!has_suffix(fname, ",v~") && (fname != "core") &&
		 !has_prefix(fname, "#cvs.rfl.")) {
	progress(flags, "\n");
	werror("Warning: Skipping %s.\n", fpath);
      }
    }
    if (handler && handler->leave_directory) {
      handler->leave_directory(this_object(), handler_path, files, flags,
			       handler_state);
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

    // Ensure that root commits aren't inserted as waypoints in the graph.
    foreach(git_commits;; GitCommit c) {
      c->propagate_dead_leaves(root_commits & ~c->leaves);
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

    if (handler && handler->rake_leaves) {
      // Hook for custom handling of leaves and dead leaves.
      progress(flags, "Raking leaves some more...\n");
      handler->rake_leaves(this_object());
    }

    foreach(git_refs;; GitCommit r) {
      // Fix the timestamp for the ref.
      fix_git_ts(r, fuzz*16);
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

      // We attach dead leaves to the commits that lack them.
      foreach(git_sort(values(git_commits)), GitCommit c) {
	i++;
	if (!(cnt--)) {
	  cnt = 100;
	  progress(flags, "\r%d(%d): %-60s  ",
		   sizeof(git_commits) - i, sizeof(git_commits), c->uuid[<59..]);
	}
	if (c->is_leaf) continue;	// We want tags to tangle...
	if (!equal((c->leaves | c->dead_leaves) & mask, mask)) {
	  Leafset missing_dead = mask - (c->leaves & mask);
	  c->propagate_dead_leaves(missing_dead & ~c->leaves);
	}
      }
      progress(flags, "\n");
    }

    progress(flags, "Checking if leaves are attached to branches...\n");

    foreach(sort(indices(git_refs)), string ref) {
      if (has_prefix(ref, "tags/")) {
	GitCommit c = git_refs[ref];
	check_attached_to_branch(flags, c);
      }
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

    if (handler && handler->bump_timestamps) {
      handler->bump_timestamps(this_object(), flags);
    }

    int margin;

    int cnt;

    // Set of commits that may have timestamps before their parents.
    mapping(string:mixed) dirty = git_commits + ([]);

    while (sizeof(dirty)) {
      foreach(git_sort(map(indices(dirty), git_commits)), GitCommit r) {
	if (!(cnt--)) {
	  cnt = 100;
	  progress(flags, "\r%d: %-67s  ", sizeof(dirty), r->uuid[<66..]);
	}
	// Ensure that the commit timestamp order is valid.
	int ts = r->timestamp - 1;
	foreach(git_sort(map(indices(r->parents), git_commits)),
		GitCommit p) {
	  if (p->timestamp > ts) {
	    ts = p->timestamp;
	  }
	}
	foreach(git_sort(map(indices(r->soft_parents), git_commits)),
		GitCommit p) {
	  if (p->timestamp > ts) {
	    ts = p->timestamp;
	  }
	}
	if (ts >= r->timestamp) {
	  ts++;
	  r->time_offset += ts - r->timestamp;
	  r->timestamp = ts;
	  dirty |= r->children;
	}
	if (r->time_offset > margin) margin = r->time_offset;
	m_delete(dirty, r->uuid);
      }
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
      if (c->is_leaf) continue;	// Handle the leaves later.
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
    // Note: This is O(n�)*O(propagation) in the worst case! But that only
    //       happens if all commits are within the FUZZ timespan and aren't
    //       eligible for merging. Assuming the number of commits not eligible
    //       for merging in a FUZZ timespan is << n,
    //       this should be O(n)*O(propagation).
    // Note: We perform two passes, to avoid missing merges due to early
    //       termination.
    // Note: We might miss some merges since we terminate as soon as
    //       we reach one of our children/parents, but that is unlikely,
    //       and shouldn't matter much.
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
      if (!c->message) {
	// Don't merge tags, since they contain too little information
	// for reliable merging.
	continue;
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
	    (p->author == c->author) &&
	    (p->message == c->message)) {
	  // Close enough in time for merge...
	  // c isn't a child of p.
	  // and the relevant fields are compatible.

	  // Check that none of c->parents is a child to p,
	  // and that none of c->children is a parent to p.
	  // We hope that there aren't any larger commit loops...
	  // FIXME: Redundant?
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

    sorted_commits -= ({ 0 });

#if 0
    bump_timestamps(flags);

    sort(sorted_commits->timestamp, sorted_commits);
#endif

    progress(flags, "Merging some more...\n");

    for (i = sizeof(sorted_commits); i--;) {
      GitCommit p = sorted_commits[i];
      if (!p) {
	// Probably destructed by a forced merge.
	// Get rid of the object.
	sorted_commits[i] = 0;
	continue;
      }
#if 0
      if (p->time_offset) {
	// Undo the timestamp bumping.
	p->timestamp -= p->time_offset;
	p->time_offset = 0;
      }
#endif
      if (!p->message) {
	// Don't merge tags, since they contain too little information
	// for reliable merging.
	continue;
      }
      for (int j = i+1; j < sizeof(sorted_commits); j++) {
	GitCommit c = sorted_commits[j];
	if (!c) continue;
	if (p->timestamp + fuzz <= c->timestamp) {
	  if (p->timestamp + margin <= c->timestamp) {
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
		   i, sizeof(sorted_commits) - j,
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
	    (p->author == c->author) &&
	    (p->message == c->message)) {
	  // Close enough in time for merge...
	  // c isn't a child of p.
	  // and the relevant fields are compatible.

	  // Check that none of c->parents is a child to p,
	  // and that none of c->children is a parent to p.
	  // We hope that there aren't any larger commit loops...
	  // FIXME: Redundant?
	  if (!sizeof(c->parents & p->children) &&
	      !sizeof(c->children & p->parents)) {
	    c->merge(p);
	    sorted_commits[i] = 0;
	    p = c;
	  }
	}
      }
    }

    progress(flags, "\n");

    sorted_commits -= ({ 0 });

    progress(flags, "Checking if leaves are attached to branches...\n");

    foreach(sort(indices(git_refs)), string ref) {
      if (has_prefix(ref, "tags/")) {
	GitCommit c = git_refs[ref];
	check_attached_to_branch(flags, c);
      }
    }

    progress(flags, "Adjusting tags...\n");

    foreach(sorted_commits; int i; GitCommit r) {
      // Fix the timestamp for the ref.
      if (!r->message) {
	// Just a minimal margin needed now.
	fix_git_ts(r, 1);
      }
    }

    bump_timestamps(flags);

    // Note: Due to the merging and the changed commit timestamps,
    //       some of the commits may have come out of order.
    sort(sorted_commits->timestamp, sorted_commits);

    verify_sorted_commits(flags);
  }

  static void propagate_successor(int successor,
				  mapping(string:int) predecessors,
				  array(IntRanges) successor_sets,
				  array(IntRanges) all_successor_sets,
				  mapping(string:int) commit_id_lookup)
  {
    while (sizeof(predecessors)) {
      mapping(string:int) more_predecessors = ([]);
      foreach(map(indices(predecessors), git_commits), GitCommit p) {
	int p_id = commit_id_lookup[p->uuid];
	if (!zero_type(p_id)) {
	  IntRanges successors = successor_sets[p_id];
	  IntRanges all_successors = all_successor_sets[p_id];
	  if (all_successors) {
	    all_successors[successor] = 1;
	  }
	  if (successors) {
	    if (successors[successor]) continue;
	    successors[successor] = 1;
	  }
	}
	more_predecessors += p->parents;
      }
      predecessors = more_predecessors;
    }
  }

  static void repair_reordering(GitCommit c,
				array(IntRanges) successor_sets,
				array(IntRanges) all_successor_sets,
				mapping(string:int) commit_id_lookup)
  {
    while (sizeof(c->parents)) {
      int pos = commit_id_lookup[c->uuid];
      int new_pos = pos;
      mapping(string:int) parents = c->parents;
      while (sizeof(parents)) {
	mapping(string:int) more_parents = ([]);
	foreach(map(indices(parents), git_commits), GitCommit p) {
	  int ppos = commit_id_lookup[p->uuid];
	  if (zero_type(ppos)) {
	    more_parents |= p->parents;
	  } else if (ppos > new_pos) {
	    new_pos = ppos;
	  }
	}
	parents = more_parents;
      }
      if (new_pos == pos) return;

      // Swap with the node at new_pos.
      IntRanges successors = successor_sets[pos];
      IntRanges all_successors = all_successor_sets[pos];
      GitCommit p = sorted_commits[new_pos];
      sorted_commits[pos] = p;
      successor_sets[pos] = successor_sets[new_pos];
      all_successor_sets[pos] = all_successor_sets[new_pos];
      commit_id_lookup[p->uuid] = pos;
      sorted_commits[new_pos] = c;
      successor_sets[new_pos] = successors;
      all_successor_sets[new_pos] = all_successors;
      commit_id_lookup[c->uuid] = new_pos;

      // Propagate new_pos as a successor to all the parents.
      propagate_successor(new_pos, c->parents, successor_sets,
			  all_successor_sets, commit_id_lookup);

      // p might now need a new position.
      c = p;
    }
  }

  static void validate_graphing_invariants(int i,
					   mapping(string:int) dirty_commits,
					   array(GitCommit) sorted_commits,
					   array(IntRanges) successor_sets,
					   array(IntRanges) all_successor_sets,
					   mapping(string:int) commit_id_lookup)
  {
    /* Loop-invariants to validate:
     *
     * [ ] The successor_sets[i..] are complete.
     * [X] There are no transitive parent pointers from any of
     *     sorted_commits[i..] to any of sorted_commits[..i-1].
     * [X] The parent-child relation is bi-directional for all
     *     sorted_commits[i..].
     * [ ] Parents have a lower index in sorted_commits than their children.
     *
     */

    mapping(string:int) checked = ([]);

    while (sizeof(dirty_commits)) {
      mapping(string:int) commits = dirty_commits - checked;
      dirty_commits = ([]);
      foreach(map(indices(commits), git_commits), GitCommit c) {
	checked[c->uuid] = 1;
	foreach(indices(c->parents), string puuid) {
	  int id = commit_id_lookup[puuid];
	  if (zero_type(id)) {
	    dirty_commits[puuid] = 1;
	    continue;
	  }
	  // Check for invalid parent pointers.
	  if (id < i) {
	    error("Parent pointer %O(%d) passes low threshold %O(%d) for child %O.\n",
		  puuid, id, sorted_commits[i]->uuid, i, c->uuid);
	  }
	  // Check that all child pointers are bi-directional.
	  GitCommit p = git_commits[puuid];
	  if (!p->children[c->uuid]) {
	    error("Parent %O(%d) is missing child %O during graphing of %O(%d).\n",
		  puuid, id, c->uuid, sorted_commits[i]->uuid, i);
	  }
	}
	foreach(map(indices(c->children), git_commits), GitCommit cc) {
	  if (!cc->parents[c->uuid]) {
	    error("Child %O is missing parent %O during graphing of %O(%d).\n",
		  cc->uuid, c->uuid, sorted_commits[i]->uuid, i);
	  }
	}
      }
    }
  }

  // Attempt to unify as many commits as possible given
  // the following invariants:
  //
  //   * The set of reachable leaves from a commit containing a revision.
  //   * The commit order must be maintained (ie a node may not reparent
  //     one of its parents).
  //
  // Note: On entry bump_timestamps() has been run, and sorted_commits
  //       is up to date.
  void graph_git_commits(Flags|void flags)
  {
    unify_git_commits(flags);

    int cnt;
    int i;

    // Now we can generate a DAG by traversing from the leaves toward the root.
    // Note: This is O(n�)! But since we utilize information in the successor
    //       sets, it's usually quite fast.
    progress(flags, "Graphing...\n");
    array(IntRanges) successor_sets =
      allocate(sizeof(sorted_commits), IntRanges)();
    array(IntRanges) all_successor_sets =
      allocate(sizeof(sorted_commits), IntRanges)();
    mapping(string:int) commit_id_lookup =
      mkmapping(sorted_commits->uuid, indices(sorted_commits));
    // By looping on most recent first, it is possible to unify
    // the resurrection and the graphing passes of old.
    // Note however that this means that the reduction of tag
    // commits will have to be done later (currently at generate time).
    for (i = sizeof(sorted_commits); i--;) {
      GitCommit p = sorted_commits[i];
      if (!p) continue;
      mapping(string:int) orig_children = p->children;
      IntRanges successors = successor_sets[i];
      IntRanges all_successors = all_successor_sets[i];

      /* Loop-invariants used below:
       *
       * * The successor_sets[i+1..] are complete.
       * * There are no parent pointers from any of sorted_commits[i+1..]
       *   to any of sorted_commits[..i].
       * * The parent-child relation is bi-directional for all
       *   sorted_commits[i+1..].
       * * Parents have a lower index in sorted_commits than their children.
       *
       */
      // Set of commits that have been affected by this iteration.
      mapping(string:int) dirty_commits = orig_children + ([
	p->uuid:1,
      ]);

      if (p->time_offset) {
	// Undo any timestamp bumping.
	p->timestamp -= p->time_offset;
	p->time_offset = 0;
      }

      // Check if we should trace...
      int trace_mode = (p->commit_flags & COMMIT_TRACE)
#if 0
	|| (< "src/modules/Parser/xml.c:1.85",
      >)[p->uuid]
#endif
	;
      
      if (trace_mode) {
	werror("\nTRACE ON.\n");
	werror("%O\n", p);
	werror("Dead leaves: \n");
	describe_leaves("\t", p->dead_leaves, "\n");
      }

      mapping(string:int) reordered_parents = ([]);

      // We'll rebuild this...
      p->children = ([]);
      for (int j = i + 1; j < sizeof(sorted_commits); j++) {
	GitCommit c = sorted_commits[j];
	// if (!c) continue;
	if (!c /* || !p->message */) {
	  // Make sure leaves stay leaves...
	  // Attempt to make the range tighter.
	  successors[j] = 1;
	  all_successors[j] = 1;
	  continue;
	}
	if (successors[j]) {
	  // Accellerate by skipping past the range.
	  int t = successors->find(j);
	  j = successors->ranges[t]-1;
	  continue;
	}
	if (!(cnt--) || trace_mode) {
	  cnt = 99;
	  progress(flags, "\r%d:%d(%d): %-55s  ",
		   i, sizeof(sorted_commits)-j, sizeof(git_commits),
		   p->uuid[<54..]);
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
	  werror("Hooking %O(%d) as a parent to %O(%d)...\n"
		 "  successors: { %{[%d,%d), %}}\n"
		 "  other: { %{[%d,%d), %}}\n",
		 p, i, c, j, successors->ranges/2,
		 successor_sets[j]?successor_sets[j]->ranges/2:({}));
	}

	if (sizeof(c->parents)) {
	  // c already has another parent.
	  if (!(flags & FLAG_LINEAR)) {
	    // Just perform reordering.

	    mapping(string:int) potential_parents = c->parents;
	    while(sizeof(potential_parents)) {
	      mapping(string:int) more_potential_parents = ([]);
	      // Check if it's possible to reorder the commits.
	      foreach(map(indices(potential_parents), git_commits),
		      GitCommit cp) {
		if (!((p->leaves ^ cp->leaves) & heads) &&
		    !(p->leaves & (cp->dead_leaves | cp->is_leaf))) {
		  // cp isn't on a different branch,
		  // and is compatible with being a parent to p.
		  if (cp->timestamp < p->timestamp + fuzz) {
		    // cp is within the time range.
		    // Reorder possible.
		    // Note that only direct parents to c need to be detached.
		    c->detach_parent(cp);
		    p->hook_parent(cp);
		    reordered_parents[cp->uuid] = 1;
		    // Note: The successor sets are updated by
		    // repair_reordering() later.
		  } else {
		    // cp's parents are candidates for being
		    // parents to p.
		    more_potential_parents += cp->parents;
		  }
		}
	      }
	      potential_parents = more_potential_parents;
	    }
	  } else {
	    // Linear mode.

	    GitCommit cp;
	    // We need to scan backwards. Since the merge commits
	    // aren't members of the successor sets we may have
	    // skipped past some of them.
	    while ((cp = c->first_parent()) && !(cp->leaves & p->dead_leaves)) {
	      // cp is compatible with p.
	      c = cp;
	      if (p->children[c->uuid]) break;
	    }
	    // NOTE: If the successor sets are incomplete,
	    //       we may arrive back at one of our new children
	    //       during the pass for the second and later child.
	    while (cp && !p->children[c->uuid]) {
	      // c still has a parent.

	      // Is cp a potential parent to p?
	      if ((cp->timestamp < p->timestamp + fuzz) &&
		  !(cp->dead_leaves & p->leaves)) {
		// Yes.
		// Note that only direct parents to c need to be detached.
		c->detach_parent(cp);
		p->hook_parent(cp);
		reordered_parents[cp->uuid] = 1;
		// Note: The successor sets are updated by
		// repair_reordering() later.
		break;
	      }

	      // Create merge commits for all the parents on
	      // the first_parent chain.

	      GitCommit m = merge_factory(cp, cp->leaves & p->dead_leaves);
	      if (c->leaves & m->dead_leaves) {
		GitCommit mm = merge_factory(m, c->leaves & m->dead_leaves);
		foreach(map(indices(m->parents), git_commits), GitCommit mp) {
		  if (mp->dead_leaves & c->leaves) {
		    m->detach_parent(mp);
		    mm->hook_parent(mp);
		  }
		}
		m->dead_leaves &= ~(c->leaves & m->dead_leaves);
		foreach(map(indices(m->children), git_commits), GitCommit mc) {
		  if (mc == mm) continue;
		  mc->detach_parent(m);
		  mc->hook_parent(mm);
		}
	      }
	      c->hook_parent(m);

	      // Make sure m stays compatible with p.
	      m->propagate_dead_leaves(p->dead_leaves);

	      // Reparent any children to cp that are compatible with p.
	      foreach(map(indices(cp->children), git_commits), GitCommit cc) {
		if (!(cc->leaves & m->dead_leaves) && (cc != m)) {
		  cc->detach_parent(cp);
		  cc->hook_parent(m);
		}
	      }

	      c = m;
	      cp = cp->first_parent();
	    }
	  }
	}

	// Make c a child to p.
	c->hook_parent(p);
	// All of j's successors are successors to us.
	successors->union(successor_sets[j]);
	all_successors->union(all_successor_sets[j]);
	// And so is j as well.
	successors[j] = 1;
	all_successors[j] = 1;

	dirty_commits[c->uuid] = 1;

	if (trace_mode) {
	  werror("  joined: { %{[%d,%d), %}}\n", successors->ranges/2);
	}

	// If we have the same set of leaves as our (new) child, then we
	// won't find any further children that aren't already successors to c.
	if (equal(c->leaves, p->leaves - p->is_leaf)) {
	  if (trace_mode) {
	    werror("  Same set of leaves as parent ==> early termination.\n");
	  }
	  break;
	}
      }

      // Handle soft children as well.
      foreach(map(indices(p->soft_children), git_commits), GitCommit c) {
	int j = commit_id_lookup[c->uuid];
	// Is it already a successor to us?
	if (all_successors[j]) {
	  // Yes, no need for one more link. Detach.
	  c->detach_soft_parent(p);
	  continue;
	}
	// It's a successor now...
	all_successors->union(all_successor_sets[j]);
	all_successors[j] = 1;
      }

      if (!sizeof(p->children) &&
	  !has_prefix(p->uuid, "remotes/") &&
	  !has_prefix(p->uuid, "heads/")) {
	progress(flags, "\n%O is a suspect HEAD.\n", p->uuid);
	check_attached_to_branch(flags, p, 1);
      }

      // This will be rebuilt...
      // We've kept it around to make sure that leaves propagate properly.
      // Any parents we've added above due to reordering are kept.
      p->parents = reordered_parents;

      dirty_commits += reordered_parents;

      // Restore some obscured children.
      // FIXME: This is a kludge that hides some other bug.
      foreach(map(indices(orig_children), git_commits), GitCommit c) {
	if (c && c->parents[p->uuid] && !p->children[c->uuid]) {
	  p->children[c->uuid] = 1;
	}
      }

      // FIXME: Ensure that none of the parents is a successor to
      //        any of the other parents.
      // For this to happen requires a rather strange tagging pattern,
      // so I've skipped on it for now.

      // Repair the tables if any reordering of commits is needed.
      // At most all commits newer than p, but less than fuzz time
      // newer than p are affected.
      repair_reordering(p, successor_sets, all_successor_sets,
			commit_id_lookup);

      validate_graphing_invariants(i, dirty_commits, sorted_commits,
				   successor_sets, all_successor_sets,
				   commit_id_lookup);

#if 0
      if ((p->commit_flags & COMMIT_HIDE) && (!p->is_leaf)) {
	// Hide the commit.
	if (trace_mode) {
	  werror("Hiding commit %O.\n", p);
	}
	foreach(map(indices(p->children), git_commits), GitCommit c) {
	  c->detach_parent(p);
	}
	successor_sets[i] = 0;
	sorted_commits[i] = 0;
	m_delete(git_commits, p->uuid);
	destruct(p);
	continue;
      }
#endif

      foreach(map(indices(p->children), git_commits), GitCommit c) {
	// If we have the same set of leaves as our child,
	// then the algorithm will always select us before the child,
	// so there's no need to keep the childs successor set around
	// anymore. Unless the child has soft parents which haven't
	// been graphed yet.
	if (equal(c->leaves, p->leaves) && !sizeof(c->soft_parents)) {
	  if (trace_mode) {
	    werror("  zapped successors for %d (%O)\n",
		   commit_id_lookup[p->uuid], p);
	  }
	  int c_id = commit_id_lookup[c->uuid];
	  if (!zero_type(c_id)) {
	    successor_sets[c_id] = UNDEFINED;
	    all_successor_sets[c_id] = UNDEFINED;
	  }
	}
      }

      if (p->uuid == termination_uuid) {
	break;
      }
    }
    successor_sets = UNDEFINED;
    all_successor_sets = UNDEFINED;
    sorted_commits -= ({ 0 });

    progress(flags, "\nDone\n");

    verify_git_commits(1);

    foreach(sorted_commits, GitCommit c) {
      if (c->is_merge && (sizeof(c->parents) < 2)) {
	c->commit_flags |= COMMIT_HIDE;
      }
    }

    progress(flags, "Merging tags with commits...\n");
    bump_timestamps(flags);
    sorted_commits = values(git_commits);
    sort(sorted_commits->timestamp, sorted_commits);
    commit_id_lookup = mkmapping(sorted_commits->uuid, indices(sorted_commits));
    mapping(string:mapping(string:int)) dirty_commits = ([]);
    cnt = 0;

    // Here we loop in the other direction, and join tags with the
    // commits they tag if there's a real commit that matches the tag.
    for (i = 0; i < sizeof(sorted_commits); i++) {
      GitCommit c = sorted_commits[i];
      if (!c) continue;

      // Check if we should trace...
      int trace_mode = (c->commit_flags & COMMIT_TRACE);

      if (!(cnt--) || trace_mode) {
	cnt = 99;
	progress(flags, "\r%d(%d): %-60s  ",
		 sizeof(sorted_commits)-i, sizeof(git_commits),
		 c->uuid[<59..]);
	if (trace_mode) werror("\n");
      }

      if (dirty_commits[c->uuid]) {
	// Adjust the parents if needed.
	// We assume that the parents are close in the graph,
	// so we don't mess with creating predecessor sets.
	array(string) suspect_parents = indices(dirty_commits[c->uuid]);
	sort(map(suspect_parents, commit_id_lookup), suspect_parents);
	foreach(reverse(suspect_parents), string sp_uuid) {
	  int sp_id = commit_id_lookup[sp_uuid];
	  ADT.Heap heap = ADT.Heap();
	  foreach(indices(c->parents), string p_uuid) {
	    if (commit_id_lookup[p_uuid] < sp_id) continue;	// Cut
	    heap->push(-commit_id_lookup[p_uuid]);
	  }
	  int found;
	  while(sizeof(heap)) {
	    int p_id = -heap->pop();
	    GitCommit p = sorted_commits[p_id];
	    if (found = (p->parents[sp_uuid])) break;
	    foreach(indices(p->parents), string pp_uuid) {
	      if (commit_id_lookup[pp_uuid] < sp_id) continue;	// Cut
	      heap->push(-commit_id_lookup[pp_uuid]);
	    }
	    // Flush duplicates.
	    while (sizeof(heap) && (heap->peek() == -p_id)) {
	      heap->pop();
	    }
	  }
	  if (found) {
	    if (trace_mode) {
	      werror("Detaching %s from being a parent to %s.\n",
		     sp_uuid, c->uuid);
	    }
	    c->detach_parent(git_commits[sp_uuid]);
	  }
	}
      }

      if (c->message && !(c->commit_flags & COMMIT_HIDE)) {
	// Not a tag and not hidden.
	continue;
      }

      if (!c->message && sizeof(c->parents) != 1) continue; // Needs to exist.

      if (has_prefix(c->uuid, "ROOT")) continue;	// Magic.

      if (trace_mode) {
	werror("Imploding commit %s(0x%08x):\n"
	       "  %O"
	       "  %O\n",
	       c->uuid, c->flags, c->message, c);
      }

      // Hide any revisions that belonged to c.
      c->revisions = ([]);
      c->commit_flags &= ~COMMIT_HIDE;	// Don't propagate the hidden flag.

      c->implode(dirty_commits);
      sorted_commits[i] = 0;
      // FIXME: Update git_refs!
    }

    commit_id_lookup = UNDEFINED;

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

  void generate(Flags|void flags)
  {
    bump_timestamps(flags);

    progress(flags, "Committing...\n");

    // Loop over the commits oldest first to reduce recursion.
    foreach(git_sort(values(git_commits)); int i; GitCommit c) {
      if (!(i & 0x1f)) {
	progress(flags, "\r%d: %-70s ", sizeof(git_commits) - i, c->uuid[<69..]);
      }
      c->generate(flags);
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
    git_blobs = ([]);
#ifdef USE_BITMASKS
    next_leaf = 1;
    leaf_lookup = ([]);
    root_commits = 0;
    heads = 0;
#else
    root_commits = ([]);
    heads = ([]);
#endif
    num_roots = 0;
  }

  string dir;

  //! Process and flush the accumulated state to git.
  void flush(Flags flags)
  {
    rake_leaves(flags);

    // Unify and graph commits.
    graph_git_commits(flags);

    // werror("Git refs: %O\n", git->git_refs);

    final_check(flags);

    // return 0;

    // FIXME: Generate a git repository.

    if (!(flags & FLAG_PRETEND)) {
      generate(flags);

      if (dir) {
	// Update the HEAD
	// This is unfortunately not supported by git-fast-import.
	Process.run(({ "git", "--git-dir", dir, "symbolic-ref",
		       "HEAD", "refs/" + latest_master_branch }));

	if (need_pre_commit_hook && !file_stat(dir + "/hooks/pre-commit")) {
	  // We need to create a suitable pre-commit hook.
	  // This is another thing that is not supported by git-fast-import.
	  Stdio.write_file(dir + "/hooks/pre-commit",
                           #string "hooks/pre-commit");
	  chmod(dir + "/hooks/pre-commit", 0755);
	}
      }
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
  werror("%s\n"
	 "\t[-h | --help] [-p] [-q | --quiet] ([(-A | --authors) <authors>]\n"
	 "\t[(-C | --git-dir) <gitdir> [(-R | --root) <root-commitish>]]\n"
	 "\t[(-o | --branch) <branch>] [(-r | --remote) <remote>]\n"
	 "\t[(-c | --config) <config-file>] [--contributors <contributors>]\n"
	 "\t[(-Z | --timezone) <timezone>] [-z <fuzz>]\n"
	 "\t[-l | --linear] [-m]\n"
	 "\t[-k] [--disable-rev]\n"
	 "\t-d <repository>)*\n",
	 argv[0]);
}

int main(int argc, array(string) argv)
{
  GitRepository git = GitRepository();

  // Some constants for the benefit of the configuration files.
  add_constant("GitRepository", GitRepository);
  add_constant("GitHandler", git->GitHandler);
  add_constant("git_progress", progress);
  add_constant("RCSFile", RCSFile);
  add_constant("GitFlags", Flags);
  add_constant("GIT_FLAG_PRETEND", FLAG_PRETEND);
  add_constant("GIT_FLAG_DETECT_MERGES", FLAG_DETECT_MERGES);
  add_constant("GIT_FLAG_QUIET", FLAG_QUIET);
  add_constant("GIT_FLAG_NO_KEYWORDS", FLAG_NO_KEYWORDS);
  add_constant("git_progress", progress);
  add_constant("RevisionFlags", RevisionFlags);
  add_constant("GIT_EXPAND_BINARY", EXPAND_BINARY);
  add_constant("GIT_EXPAND_LF", EXPAND_LF);
  add_constant("GIT_EXPAND_CRLF", EXPAND_CRLF);
  add_constant("GIT_EXPAND_TEXT", EXPAND_TEXT);
  add_constant("GIT_EXPAND_KEYWORDS", EXPAND_KEYWORDS);
  add_constant("GIT_EXPAND_ALL", EXPAND_ALL);
  add_constant("GIT_EXPAND_GUESS", EXPAND_GUESS);
  add_constant("GIT_EXPAND_GOT_KEYWORD", EXPAND_GOT_KEYWORD);
  add_constant("GIT_REVISION_COPY", REVISION_COPY);
  add_constant("GIT_REVISION_MERGE", REVISION_MERGE);

  Flags flags;

  Process.Process fast_importer;

  array(string) initial_argv = argv + ({});

  foreach(Getopt.find_all_options(argv, ({
	   ({ "help",       Getopt.NO_ARG,  ({ "-h", "--help" }), 0, 0 }),
	   ({ "authors",    Getopt.HAS_ARG, ({ "-A", "--authors" }), 0, 0 }),
	   ({ "contrib",    Getopt.HAS_ARG, ({ "--contributors" }), 0, 0 }),
	   ({ "config",     Getopt.HAS_ARG, ({ "-c", "--config" }), 0, 0 }),
	   ({ "git-dir",    Getopt.HAS_ARG, ({ "-C", "--git-dir" }), 0, 0 }),
	   ({ "root",       Getopt.HAS_ARG, ({ "-R", "--root" }), 0, 0 }),
	   ({ "branch",     Getopt.HAS_ARG, ({ "-o", "--branch" }), 0, 0 }),
	   ({ "remote",     Getopt.HAS_ARG, ({ "-r", "--remote" }), 0, 0 }),
	   ({ "repository", Getopt.HAS_ARG, ({ "-d" }), 0, 0 }),
	   ({ "fuzz",       Getopt.HAS_ARG, ({ "-z" }), 0, 0 }),
	   ({ "timezone",   Getopt.HAS_ARG, ({ "-Z", "--timezone" }), 0, 0, }),
	   ({ "nokeywords", Getopt.NO_ARG,  ({ "-k" }), 0, 0 }),
	   ({ "linear",     Getopt.NO_ARG,  ({ "-l", "--linear" }), 0, 0 }),
	   ({ "merges",     Getopt.NO_ARG,  ({ "-m" }), 0, 0 }),
	   ({ "pretend",    Getopt.NO_ARG,  ({ "-p" }), 0, 0 }),
	   ({ "quiet",      Getopt.NO_ARG,  ({ "-q", "--quiet" }), 0, 0 }),
	   ({ "disable-rev",Getopt.NO_ARG,  ({ "--disable-rev" }), 0, 0 }),
				  })),
	  [string arg, string val]) {
    switch(arg) {
    case "help":
      usage(argv);
      exit(0);
    case "config":
      if (Stdio.is_file(val)) {
      } else if (!has_suffix(val, ".pcvs2git") &&
		 Stdio.is_file(val + ".pcvs2git")) {
	val = val + ".pcvs2git";
      } else if (!has_prefix(val, "/")) {
	string c = combine_path(__FILE__, "../config", val);
	if (Stdio.is_file(c)) {
	  val = c;
	} else if (!has_suffix(c, ".pcvs2git") &&
		   Stdio.is_file(c + ".pcvs2git")) {
	  val = c + ".pcvs2git";
	}
      }
      parse_config(git, val, flags);
      break;
    case "authors":
      git->merge_authors(git->read_authors_file(val));
      break;
    case "contrib":
      git->read_contributors_file(val);
      break;
    case "branch":
      git->set_master_branch(val);
      break;
    case "remote":
      if (val != "") {
	git->remote = "remotes/" + val + "/";
      } else {
	git->remote = "heads/";
      }
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
	git->dir = val;
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
    case "timezone":
      git->default_tz = Calendar.Timezone[val];
      if (!git->default_tz) {
	if ((sscanf(val, "%d%s", git->default_tz, string rest) != 2) ||
	    (rest != "")) {
	  werror("Unknown timezone %O.\n", val);
	  exit(1);
	}
      }
      break;
    case "fuzz":
      git->fuzz = (int)val;
      break;
    case "linear":
      flags |= FLAG_LINEAR;
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
    case "disable-rev":
      flags |= FLAG_DISABLE_REV;
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

  int ret;

  // Wait for the importer to finish.
  if (fast_importer) {
    Stdio.stdout->close();
    ret = fast_importer->wait();
  }

  if (!ret && !(flags & FLAG_PRETEND) && git->dir) {
    // Perform a gc to pack the repository.
    // This is unfortunately not supported by git-fast-import.
    werror("Garbage-collecting...\n");
    Process.run(({ "git", "--git-dir", git->dir, "gc", "--aggressive" }));
    werror("Done.\n");
  }

  return ret;
}
