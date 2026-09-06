//! Reading and writing bus content straight in the object database.
//!
//! Everything this crate reads from git history -- a stream's header and
//! segments, a roster epoch, the bus config -- is a handful of small blobs
//! at known paths in a known commit. `gitrepo.rs` originally served all of
//! it through `ensure_bus_worktree`: materialize a real working tree on
//! disk at that commit, read the files with ordinary filesystem calls,
//! leave the worktree behind as a cache. That works, but it pays for a few
//! kilobytes of JSON with a `git worktree add` (plus, on a stale cache, a
//! `git worktree remove`) -- measured at roughly 4.6 seconds per cycle on
//! the real fleet repo, which accumulates hundreds of registered worktrees
//! over time. A single `status --sync` reads one stream per active member,
//! so that cost multiplies: 60-75 seconds for a command whose entire
//! payload is a few hundred kilobytes already sitting in the odb.
//!
//! This module is the path that skips all of it, for reads
//! ([`ObjectReader`]) and equally for writes ([`ObjectWriter`],
//! [`RefStore`]). Each trait is stated in this crate's own vocabulary --
//! "the bytes recorded at this path in this commit", "the entries at the
//! root of this commit's tree", "point this ref at that commit, but only if
//! it still points where I last read" -- rather than as `git` argument
//! lists. Two things fall out of that shape:
//!
//!  - The backend is swappable. [`Libgit2Reader`] is the production
//!    implementation, but nothing above this line knows libgit2 exists.
//!  - It is mockable. `gitrepo::mock::MockGit` intercepts the `git`
//!    subprocess, so it has no purchase on an in-process library call;
//!    [`FixtureObjectReader`] replaces it for everything ported here,
//!    letting `storage`/`stream`/`registry` unit-test their blob-reading
//!    paths against known content with no repository on disk at all.
//!
//! Deliberately partial. Merges and all remote transport stay on
//! `gitrepo.rs`'s `git` subprocess, and that split is not incidental:
//!
//!  - The merge path is pinned to git's own ORT implementation for
//!    byte-identical cross-platform trees (AGENT_REVIEW.md section 7) and
//!    must not be reimplemented against libgit2's separate merge algorithm.
//!  - `git2` is built with `default-features = false`, which drops its
//!    HTTPS/SSH transports, so `fetch`/`push` keep going through the user's
//!    own credential helpers, SSH agent and `.netrc`.
//!
//! What is left on the subprocess is therefore exactly the set of calls that
//! talk to a network or must be byte-reproducible -- and nothing on the
//! local hot path.

use crate::error::{invalid, AbError, AbResult};
use crate::scalars::ObjectId;
use std::path::{Path, PathBuf};

/// Read-only access to content recorded in git history, addressed by commit
/// and path.
///
/// The two cases an implementation must keep distinct, because callers
/// depend on the difference:
///
///  - `commit` does not resolve to a commit in this repository at all. That
///    is a hard error (`AbError::Git`), mirroring how `gitrepo::rev_parse`
///    fails rather than reporting absence.
///  - `commit` resolves, but records nothing at `path`. That is `Ok(None)`
///    -- an ordinary, expected answer, mirroring `gitrepo::rev_parse_opt`.
pub trait ObjectReader {
    /// The bytes recorded at `path` (slash-separated, relative to the root
    /// of `commit`'s tree), or `None` if `commit` records no entry there.
    ///
    /// Errors if `commit` does not resolve, or if `path` names something
    /// that is not a file -- a directory or a submodule where a blob was
    /// expected is corruption, not absence, and must not be reported as a
    /// missing file.
    fn read_blob_at(&self, commit: &ObjectId, path: &str) -> AbResult<Option<Vec<u8>>>;

    /// The names of every entry directly at the root of `commit`'s tree,
    /// files and directories alike, one level deep only.
    ///
    /// One level is all this crate needs: a stream tree keeps its header
    /// and every `NNNNNN.jsonl` segment at its root (`storage.rs`), and the
    /// registry keeps `epoch.json`/`bus_config.json` at its own root
    /// (`registry.rs`). Directory names are included rather than filtered
    /// out so callers can *reject* an unexpected subdirectory instead of
    /// silently ignoring it.
    ///
    /// Errors if `commit` does not resolve.
    fn list_root_entries(&self, commit: &ObjectId) -> AbResult<Vec<String>>;
}

/// The production [`ObjectReader`]: libgit2, reading blobs directly out of
/// the object database with no working tree involved.
///
/// Opening one is the per-call setup cost (it locates and parses the
/// repository's configuration), so callers with more than one thing to read
/// -- `registry::read_epoch_chain` walking a lineage, `sync::reduce_local`
/// reading every member's stream -- should open a single reader and pass it
/// down rather than opening one per blob.
pub struct Libgit2Reader {
    repo: git2::Repository,
}

impl Libgit2Reader {
    /// Opens the repository containing `repo_dir`, searching upward from it
    /// the way `git -C <dir>` does, so this accepts exactly the paths
    /// `gitrepo::run` already accepts -- including a linked worktree, whose
    /// objects live in the shared common directory.
    pub fn open(repo_dir: &Path) -> AbResult<Self> {
        let repo = git2::Repository::discover(repo_dir).map_err(|e| {
            AbError::Git(format!(
                "cannot open a git repository at {}: {e}",
                repo_dir.display()
            ))
        })?;
        Ok(Libgit2Reader { repo })
    }

    fn tree_of(&self, commit: &ObjectId) -> AbResult<git2::Tree<'_>> {
        // `BusConfig::new`/`parse` (bootstrap.rs) already refuse to activate
        // or read a sha256 bus at all -- the vendored libgit2 this reader
        // uses only supports sha1 without its experimental sha256 build
        // flag, and `Repository::discover`/`open` itself fails outright on a
        // real sha256 repo ("unknown object format 'sha256'") before any
        // commit is ever looked up. So a parse failure reaching this point
        // means genuine corruption of the stored id, not a hash-algorithm
        // mismatch this reader could have anticipated.
        let oid = git2::Oid::from_str(commit.as_str()).map_err(|e| {
            AbError::Git(format!(
                "{commit} is not an object id this repository's hash algorithm can \
                 represent: {e}"
            ))
        })?;
        let found = self.repo.find_commit(oid).map_err(|e| {
            AbError::Git(format!("commit {commit} does not resolve to a commit: {e}"))
        })?;
        found
            .tree()
            .map_err(|e| AbError::Git(format!("commit {commit} has no readable tree: {e}")))
    }
}

impl ObjectReader for Libgit2Reader {
    fn read_blob_at(&self, commit: &ObjectId, path: &str) -> AbResult<Option<Vec<u8>>> {
        let tree = self.tree_of(commit)?;
        let entry = match tree.get_path(Path::new(path)) {
            Ok(entry) => entry,
            Err(e) if e.code() == git2::ErrorCode::NotFound => return Ok(None),
            Err(e) => {
                return Err(AbError::Git(format!(
                    "cannot look up {path} in commit {commit}: {e}"
                )))
            }
        };
        // Git stores a symlink's target text as an ordinary blob object --
        // only the tree entry's *mode* marks it as a link, not the object's
        // own kind -- so `object.as_blob()` below would silently succeed and
        // hand back the link *target string* as if it were the file's real
        // content. A worktree checkout would instead have followed the link
        // (possibly outside the tree entirely); neither behavior is "read
        // this file's content", so reject explicitly rather than accepting
        // either.
        if entry.filemode() == i32::from(git2::FileMode::Link) {
            return Err(invalid(format!(
                "{path} in commit {commit} is a symlink, not a file; expected file content"
            )));
        }
        let object = entry.to_object(&self.repo).map_err(|e| {
            AbError::Git(format!(
                "cannot read the object at {path} in commit {commit}: {e}"
            ))
        })?;
        let blob = object.as_blob().ok_or_else(|| {
            invalid(format!(
                "{path} in commit {commit} is not a file (it is a {}); expected file content",
                object
                    .kind()
                    .map(|k| k.str())
                    .unwrap_or("object of unknown type")
            ))
        })?;
        Ok(Some(blob.content().to_vec()))
    }

    fn list_root_entries(&self, commit: &ObjectId) -> AbResult<Vec<String>> {
        let tree = self.tree_of(commit)?;
        let mut names = Vec::with_capacity(tree.len());
        for entry in tree.iter() {
            // `git2` fails a name that is not valid UTF-8. Every path this
            // crate ever writes is ASCII, so this is junk that must be
            // surfaced rather than skipped -- silently dropping it would
            // let an unreadable entry masquerade as an absent one.
            let name = entry.name().map_err(|e| {
                invalid(format!(
                    "commit {commit} has a tree entry whose name is not valid UTF-8: {e}"
                ))
            })?;
            names.push(name.to_string());
        }
        Ok(names)
    }
}

// ------------------------------------------------------------- writing

/// Creating objects in the database, addressed the way this crate thinks
/// about them -- "a stream tree is its header plus its segment files" --
/// rather than as an index that gets staged and committed.
///
/// The write path this replaces goes through a working tree: check a commit
/// out, edit files on disk, `git add -A`, `git commit`. That is why
/// `registry.rs` and `stream.rs` still take a `worktree` argument. The shape
/// costs a `git worktree add` per write (~4.6s on the fleet repo), takes the
/// repository index lock, and serializes every concurrent writer on git's
/// shared `.git/worktrees` registration state -- the collisions `coord1:44`
/// reports, and the "missing but already registered worktree" failure two
/// agents hit live. None of it is needed to do what an append actually does,
/// which is rewrite one known blob at one known path in an otherwise
/// unchanged tree.
///
/// Building the tree directly also turns a retrospective check into a
/// structural one. `stream::append_to_stream` writes files, commits, and
/// *then* diffs the result to confirm it touched only segment paths; an
/// implementation of this trait cannot touch a path the caller did not name,
/// so there is nothing left to check after the fact.
pub trait ObjectWriter {
    /// Writes `content` as a blob, returning its id. Writing the same bytes
    /// twice is not an error and yields the same id -- git object storage is
    /// content-addressed, so this is idempotent by construction.
    fn write_blob(&self, content: &[u8]) -> AbResult<ObjectId>;

    /// Builds a tree from `base`'s tree with `edits` applied at the root,
    /// returning the new tree's id. `base` is a *commit* (the natural way
    /// every caller here thinks of it -- "the parent commit's tree, with
    /// this segment replaced"); `None` starts from an empty tree, which is
    /// what a stream or registry root commit needs.
    ///
    /// Every edit names a root-level file. This deliberately cannot express
    /// a nested path or a deletion: the bus writes neither, and a trait that
    /// could express them would need a policy for what happens to entries
    /// the caller did not mention.
    fn write_tree(&self, base: Option<&ObjectId>, edits: &[(&str, ObjectId)])
        -> AbResult<ObjectId>;

    /// Creates a commit with `parents` (empty for a root commit) and returns
    /// its id. Updates no reference -- publishing the commit is
    /// [`RefStore::compare_and_set`]'s job, kept separate so a caller can
    /// build a commit and still refuse to publish it.
    ///
    /// Identity is resolved exactly as `git commit` resolves it --
    /// environment first, then configuration; see
    /// [`Libgit2Reader::ambient_identity`]. Real stream commits on this fleet
    /// carry the operator's own name and email, not a synthetic one.
    /// The byte-reproducible identity that merge candidates need is a
    /// different concern with a different rule (AGENT_REVIEW.md section 7)
    /// and stays in `gitrepo::commit_tree_deterministic`.
    fn create_commit(
        &self,
        tree: &ObjectId,
        parents: &[&ObjectId],
        message: &str,
    ) -> AbResult<ObjectId>;
}

/// Reading and moving references.
///
/// The compare-and-swap in [`RefStore::compare_and_set`] is the point of
/// this trait rather than an extra. The write path it replaces ends in a
/// bare `git update-ref <ref> <commit>`, which overwrites whatever is there;
/// the staleness check that makes a losing writer stop
/// (`stream::append_to_stream`'s gate 6 half) happens earlier, against a tip
/// read before the commit was built. Between that read and that write sits
/// the whole of building a commit -- a window a second writer can land in.
/// Naming the expected value closes it in the one place that can actually
/// enforce it.
pub trait RefStore {
    /// The commit `refname` points at, or `None` if it does not exist.
    /// A reference that exists but does not resolve to a commit is an error,
    /// not absence.
    fn resolve(&self, refname: &str) -> AbResult<Option<ObjectId>>;

    /// Every reference whose name starts with `prefix`, as
    /// `(refname, commit)` pairs sorted by name.
    ///
    /// Only `#[cfg(test)]` code calls this today -- it is how the
    /// ref-shadowing regression tests in `stream.rs`/`registry.rs` inspect
    /// the *actual* ref set, which is the one question `resolve` cannot
    /// answer (a lookup that resolves tells you nothing about a
    /// wrongly-named ref sitting beside it). A plain build cannot see that
    /// cross-module test usage and reports it dead; the same
    /// `#[allow(dead_code)]`-with-a-reason treatment `GitOutput::ok`/`err`
    /// already carry in `gitrepo.rs`.
    #[allow(dead_code)]
    fn list(&self, prefix: &str) -> AbResult<Vec<(String, ObjectId)>>;

    /// Points `refname` at `new`, but only if it currently points at
    /// `expected` -- or, when `expected` is `None`, only if it does not
    /// exist at all. Fails rather than overwriting, so a caller that loses
    /// the race stops and resolves custody instead of clobbering the winner
    /// (AGENT_COORDINATION_EVOLUTION.md section 2.1).
    fn compare_and_set(
        &self,
        refname: &str,
        expected: Option<&ObjectId>,
        new: &ObjectId,
    ) -> AbResult<()>;
}

impl ObjectWriter for Libgit2Reader {
    fn write_blob(&self, content: &[u8]) -> AbResult<ObjectId> {
        let oid = self
            .repo
            .blob(content)
            .map_err(|e| AbError::Git(format!("cannot write a blob: {e}")))?;
        ObjectId::parse(oid.to_string())
    }

    fn write_tree(
        &self,
        base: Option<&ObjectId>,
        edits: &[(&str, ObjectId)],
    ) -> AbResult<ObjectId> {
        let base_tree = match base {
            Some(commit) => Some(self.tree_of(commit)?),
            None => None,
        };
        let mut builder = self
            .repo
            .treebuilder(base_tree.as_ref())
            .map_err(|e| AbError::Git(format!("cannot start building a tree: {e}")))?;
        for (name, blob) in edits {
            if name.is_empty() || name.contains('/') {
                return Err(invalid(format!(
                    "{name} is not a root-level file name; this writer builds flat trees only"
                )));
            }
            let oid = git2::Oid::from_str(blob.as_str())
                .map_err(|e| AbError::Git(format!("{blob} is not a usable object id: {e}")))?;
            builder
                .insert(name, oid, i32::from(git2::FileMode::Blob))
                .map_err(|e| AbError::Git(format!("cannot place {name} in the tree: {e}")))?;
        }
        let oid = builder
            .write()
            .map_err(|e| AbError::Git(format!("cannot write the tree: {e}")))?;
        ObjectId::parse(oid.to_string())
    }

    fn create_commit(
        &self,
        tree: &ObjectId,
        parents: &[&ObjectId],
        message: &str,
    ) -> AbResult<ObjectId> {
        let tree_oid = git2::Oid::from_str(tree.as_str())
            .map_err(|e| AbError::Git(format!("{tree} is not a usable object id: {e}")))?;
        let tree_obj = self
            .repo
            .find_tree(tree_oid)
            .map_err(|e| AbError::Git(format!("{tree} does not resolve to a tree: {e}")))?;

        let mut parent_commits = Vec::with_capacity(parents.len());
        for p in parents {
            let oid = git2::Oid::from_str(p.as_str())
                .map_err(|e| AbError::Git(format!("{p} is not a usable object id: {e}")))?;
            parent_commits.push(
                self.repo
                    .find_commit(oid)
                    .map_err(|e| AbError::Git(format!("parent {p} does not resolve: {e}")))?,
            );
        }
        let parent_refs: Vec<&git2::Commit<'_>> = parent_commits.iter().collect();

        let (author, committer) = self.ambient_identity()?;

        let oid = self
            .repo
            .commit(None, &author, &committer, message, &tree_obj, &parent_refs)
            .map_err(|e| AbError::Git(format!("cannot create the commit: {e}")))?;
        ObjectId::parse(oid.to_string())
    }
}

impl RefStore for Libgit2Reader {
    fn resolve(&self, refname: &str) -> AbResult<Option<ObjectId>> {
        let reference = match self.repo.find_reference(refname) {
            Ok(r) => r,
            Err(e) if e.code() == git2::ErrorCode::NotFound => return Ok(None),
            Err(e) => {
                return Err(AbError::Git(format!("cannot read {refname}: {e}")));
            }
        };
        let commit = reference.peel_to_commit().map_err(|e| {
            AbError::Git(format!(
                "{refname} exists but does not resolve to a commit: {e}"
            ))
        })?;
        Ok(Some(ObjectId::parse(commit.id().to_string())?))
    }

    fn list(&self, prefix: &str) -> AbResult<Vec<(String, ObjectId)>> {
        let refs = self
            .repo
            .references()
            .map_err(|e| AbError::Git(format!("cannot enumerate references: {e}")))?;
        let mut out = Vec::new();
        for r in refs {
            let r = r.map_err(|e| AbError::Git(format!("cannot read a reference: {e}")))?;
            // A name that is not valid UTF-8 is junk in a namespace this
            // crate wholly controls, but it is not necessarily *this*
            // namespace's junk -- skipping it keeps an unrelated broken ref
            // elsewhere in the repository from failing every bus command.
            let Ok(name) = r.name() else { continue };
            if !name.starts_with(prefix) {
                continue;
            }
            let commit = r.peel_to_commit().map_err(|e| {
                AbError::Git(format!(
                    "{name} exists but does not resolve to a commit: {e}"
                ))
            })?;
            out.push((name.to_string(), ObjectId::parse(commit.id().to_string())?));
        }
        out.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(out)
    }

    fn compare_and_set(
        &self,
        refname: &str,
        expected: Option<&ObjectId>,
        new: &ObjectId,
    ) -> AbResult<()> {
        let new_oid = git2::Oid::from_str(new.as_str())
            .map_err(|e| AbError::Git(format!("{new} is not a usable object id: {e}")))?;
        let reason = format!("agent-bus: set {refname}");

        match expected {
            // Creation, as an atomic create-if-absent.
            //
            // `Repository::reference(.., force = false, ..)` is NOT that, and
            // the difference is a real race rather than a theoretical one:
            // it calls `git_reference_create` with `old_id = NULL`, and
            // libgit2's `cmp_old_ref` treats NULL as "matches anything", so
            // the only existence check is `reference_path_available` --
            // which runs *before* the loose-ref lock is taken. Two writers
            // can both pass that check, serialize on the lock, and the loser
            // silently overwrites the winner.
            //
            // `reference_matching` with the zero oid expresses "must not
            // exist" as the expected *old value*, which libgit2 evaluates
            // under the lock, so the loser is refused. This is what makes
            // two hosts racing a stream root or the registry root resolve to
            // one winner (gates 6 and 19) rather than to whoever wrote last.
            None => {
                self.repo
                    .reference_matching(refname, new_oid, false, git2::Oid::ZERO_SHA1, &reason)
                    .map_err(|e| {
                        // Only `Exists` is the race. A directory/file
                        // collision (`refs/a` against an existing `refs/a/b`)
                        // or a `new` that names no object are configuration
                        // and caller bugs; telling the operator to "retry"
                        // would invite an unbounded loop against something
                        // retrying cannot fix.
                        if e.code() == git2::ErrorCode::Exists {
                            return invalid(format!(
                                "{refname} already exists, but was expected not to -- another                                  writer created it first; re-read the current tip and retry: {e}"
                            ));
                        }
                        invalid(format!(
                            "{refname} could not be created, and not because another writer won                              the race -- retrying will not help: {e}"
                        ))
                    })?;
            }
            Some(want) => {
                let mut reference = self.repo.find_reference(refname).map_err(|e| {
                    invalid(format!(
                        "{refname} was expected to point at {want} but does not exist -- it was \
                         deleted since it was read; re-read the current tip and retry: {e}"
                    ))
                })?;
                let actual = reference.peel_to_commit().map_err(|e| {
                    AbError::Git(format!(
                        "{refname} exists but does not resolve to a commit: {e}"
                    ))
                })?;
                if actual.id().to_string() != want.as_str() {
                    // Deliberately worded so it cannot be confused with a
                    // caller's own staleness pre-check. Those checks read the
                    // tip *before* building a commit; this one fires for a
                    // writer that landed in the window between. A test that
                    // cannot tell the two apart cannot tell whether the
                    // compare-and-swap is doing anything at all -- which is
                    // exactly how it went untested at every call site.
                    return Err(invalid(format!(
                        "{refname} changed after this write was prepared: expected {want}, found \
                         {} -- another writer published first; re-read the current tip and retry",
                        actual.id()
                    )));
                }
                // libgit2 re-checks the old value under its own reference
                // lock here, so this still fails closed against a writer that
                // landed between the comparison above and this call.
                reference.set_target(new_oid, &reason).map_err(|e| {
                    // A symbolic ref fails here too, and it is not a race:
                    // `git update-ref` would have followed the symref and
                    // moved its target instead. Refusing is right -- a bus ref
                    // must be direct -- but saying "another writer won" would
                    // send the operator after a race that never happened.
                    if e.code() == git2::ErrorCode::InvalidSpec || e.message().contains("symbolic")
                    {
                        return invalid(format!(
                            "{refname} is a symbolic reference, not a direct one; a bus ref must \
                             point straight at a commit -- repoint or remove it: {e}"
                        ));
                    }
                    invalid(format!(
                        "{refname} moved while it was being updated -- another writer won the \
                         race; re-read the current tip and retry: {e}"
                    ))
                })?;
            }
        }
        Ok(())
    }
}

// ------------------------------------------------------------- history

/// Reading commit history: resolving revisions, walking ancestry, comparing
/// trees, and reading a commit's own metadata.
///
/// Separate from [`ObjectReader`] because the questions are different in
/// kind -- that trait answers "what bytes are recorded at this path", this
/// one answers "how do these commits relate" -- and separate from
/// [`ObjectWriter`] because every method here is read-only.
///
/// [`Libgit2Reader`] is the only implementation. Unlike the blob-reading
/// traits, there is no fixture counterpart: every consumer of this trait
/// (`merge_candidate.rs`, `merge_ready.rs`, `audit_main.rs`) is testing a
/// property of real git history -- that a candidate has exactly one merge
/// base, that a range of commits carries the right trailers, that a diff
/// stays inside a reviewed scope -- and a hand-written fixture asserting
/// those against invented data would be testing the fixture. Those modules
/// build real repositories in their tests, and should.
pub trait HistoryReader {
    /// Resolve a git revision expression (`HEAD`, a branch, a raw object id,
    /// `<rev>^{tree}`) to the object it names, or `None` if it names
    /// nothing. Anything that resolves to a non-commit -- a tree, a blob --
    /// still resolves here; callers that require a commit say so themselves.
    fn resolve_rev(&self, spec: &str) -> AbResult<Option<ObjectId>>;

    /// `commit`'s parents, in order. Empty for a root commit.
    fn parents_of(&self, commit: &ObjectId) -> AbResult<Vec<ObjectId>>;

    /// `commit`'s committer-date unix timestamp in seconds. Deliberately the
    /// *committer* date, not the author date: `commit_tree_deterministic`
    /// derives a candidate's timestamp from its parents' committer dates.
    fn committer_timestamp(&self, commit: &ObjectId) -> AbResult<i64>;

    /// `commit`'s message.
    ///
    /// Two documented differences from `git show -s --format=%B`, both of
    /// which lose trailers rather than inventing them:
    ///
    ///  - libgit2 skips leading newlines; `%B` preserves them. A message that
    ///    begins with a blank line therefore has a *different* first
    ///    paragraph here, and since the trailer block can never be the first
    ///    paragraph, this can only ever make a trailer block disappear.
    ///  - `%B` transcodes through the commit's `encoding` header into UTF-8;
    ///    this returns the recorded bytes and rejects them if they are not
    ///    already UTF-8 (see below).
    ///
    /// Brute-forcing 375 message shapes through the real
    /// `git interpret-trailers` found 84 shapes where this path sees fewer
    /// trailers and none where it sees more, so every consumer
    /// (`verify_authorship`, `merge_ready`, `audit_main`) fails closed.
    fn commit_message(&self, commit: &ObjectId) -> AbResult<String>;

    /// How many merge bases `a` and `b` have. AGENT_REVIEW.md section 7
    /// requires exactly one, so the count -- not merely "is there one" -- is
    /// the answer callers need.
    fn merge_base_count(&self, a: &ObjectId, b: &ObjectId) -> AbResult<usize>;

    /// Commits reachable from `to` but not from `from_exclusive`, oldest
    /// first, following only first parents.
    fn first_parent_range(
        &self,
        from_exclusive: &ObjectId,
        to: &ObjectId,
    ) -> AbResult<Vec<ObjectId>>;

    /// Commits reachable from `to` but not from `from_exclusive`, following
    /// every parent, **newest first**.
    ///
    /// Precisely: **commit-date** order, which is what `git rev-list`
    /// without `--reverse` produces and what `Sort::NONE` asks libgit2 for.
    ///
    /// Not topological order. The two are *not* interchangeable, and the
    /// difference is reachable from histories this crate builds: for
    /// base->l1(t=100)->l2(t=400) and base->r1(t=200)->r2(t=300) merged at M,
    /// git gives `M l2 r2 r1 l1` while a topological walk gives
    /// `M r2 r1 l2 l1`. Using `Sort::TOPOLOGICAL` here was a real defect;
    /// `range_matches_git_rev_list_order_across_a_date_skewed_merge` is built
    /// on that exact shape and fails if it comes back.
    fn range(&self, from_exclusive: &ObjectId, to: &ObjectId) -> AbResult<Vec<ObjectId>>;

    /// Every path that differs between `from`'s tree and `to`'s tree, as
    /// `(status, path)`.
    ///
    /// Rename detection is deliberately **off**. `git diff --name-status`
    /// with detection on collapses a rename to one `R<score> old new` line,
    /// and this crate's two consumers -- `merge_ready::check_merge_ready`
    /// and `audit_main`'s post-hoc scope correlation -- read only the path
    /// and check it against a reviewed scope. Under detection, a file
    /// renamed *into* the reviewed scope from outside it reports only the
    /// new (in-scope) path, and the out-of-scope path it came from is never
    /// checked. With detection off the same change is a delete plus an add,
    /// so both paths are reported and both are scope-checked. Strictly more
    /// paths, never fewer, is the only safe direction for a gate whose job
    /// is to catch a change outside what was reviewed.
    fn diff_name_status(&self, from: &ObjectId, to: &ObjectId) -> AbResult<Vec<(String, String)>>;
}

impl Libgit2Reader {
    /// The working directory of the repository this reader opened.
    ///
    /// Equivalent to `git rev-parse --show-toplevel`, including from a
    /// linked worktree, where it is that worktree's own root.
    pub fn workdir(&self) -> AbResult<PathBuf> {
        self.repo
            .workdir()
            .map(|p| p.to_path_buf())
            .ok_or_else(|| AbError::Git("this repository has no working directory".into()))
    }

    /// The repository's single shared git directory, equivalent to `git
    /// rev-parse --git-common-dir`: the *main* checkout's git directory even
    /// when called from a linked worktree.
    pub fn common_dir(&self) -> PathBuf {
        self.repo.commondir().to_path_buf()
    }

    /// The author and committer `git commit` would use here.
    ///
    /// `Repository::signature` alone is not that. It reads *configuration
    /// only*, while git resolves each field from the environment first:
    /// `GIT_AUTHOR_NAME`/`GIT_AUTHOR_EMAIL` for the author,
    /// `GIT_COMMITTER_NAME`/`GIT_COMMITTER_EMAIL` for the committer, each
    /// falling back to `user.name`/`user.email`. Hosts that supply identity
    /// purely through the environment are ordinary -- CI containers, git
    /// hooks, anything invoked under `env` -- and on those, using
    /// configuration alone turns every bus write into a hard "cannot
    /// determine a commit identity" failure where `git commit` succeeded.
    ///
    /// `GIT_AUTHOR_DATE`/`GIT_COMMITTER_DATE` are deliberately *not* honored:
    /// a stream or registry commit is timestamped when it is written, and the
    /// one place a caller-chosen timestamp matters --- a reproducible merge
    /// candidate --- takes its identity and time explicitly through
    /// [`Libgit2Reader::commit_with_identity`] instead.
    fn ambient_identity(&self) -> AbResult<(git2::Signature<'_>, git2::Signature<'_>)> {
        let cfg = self.repo.config().and_then(|mut c| c.snapshot());
        let resolved = resolve_identity(
            |k| std::env::var(k).ok(),
            |k| {
                cfg.as_ref()
                    .ok()
                    .and_then(|c| c.get_str(k).ok().map(|v| v.to_string()))
            },
        )?;
        let author = git2::Signature::now(&resolved.author_name, &resolved.author_email)
            .map_err(|e| AbError::Git(format!("cannot build the author identity: {e}")))?;
        let committer =
            git2::Signature::now(&resolved.committer_name, &resolved.committer_email)
                .map_err(|e| AbError::Git(format!("cannot build the committer identity: {e}")))?;
        Ok((author, committer))
    }

    fn commit_at(&self, commit: &ObjectId) -> AbResult<git2::Commit<'_>> {
        let oid = git2::Oid::from_str(commit.as_str())
            .map_err(|e| AbError::Git(format!("{commit} is not a usable object id: {e}")))?;
        self.repo
            .find_commit(oid)
            .map_err(|e| AbError::Git(format!("commit {commit} does not resolve to a commit: {e}")))
    }

    fn walk(
        &self,
        from_exclusive: &ObjectId,
        to: &ObjectId,
        first_parent_only: bool,
        oldest_first: bool,
    ) -> AbResult<Vec<ObjectId>> {
        let from = git2::Oid::from_str(from_exclusive.as_str()).map_err(|e| {
            AbError::Git(format!("{from_exclusive} is not a usable object id: {e}"))
        })?;
        let to_oid = git2::Oid::from_str(to.as_str())
            .map_err(|e| AbError::Git(format!("{to} is not a usable object id: {e}")))?;
        // `git rev-list a..b` errors when either endpoint is unknown rather
        // than silently walking nothing, so resolve both first.
        self.commit_at(from_exclusive)?;
        self.commit_at(to)?;

        let mut walk = self
            .repo
            .revwalk()
            .map_err(|e| AbError::Git(format!("cannot start a revision walk: {e}")))?;
        // `git rev-list` is newest-first by default and oldest-first with
        // `--reverse`. Both orders are load-bearing here and they are not
        // interchangeable: `rev_list_first_parent` replaced a call that
        // passed `--reverse`, `range` replaced one that did not, and
        // `audit_main` renders the result into golden output.
        //
        // `Sort::NONE`, not `Sort::TOPOLOGICAL`. git's default is *commit
        // date* order, and the two differ on any range spanning a merge whose
        // sides have interleaved committer dates: for base->l1(t=100)->
        // l2(t=400) and base->r1(t=200)->r2(t=300) merged at M(t=500), git
        // gives `M l2 r2 r1 l1` and a topological walk gives `M r2 r1 l2 l1`.
        // `Sort::NONE` is libgit2's spelling of that same date ordering.
        let mut sorting = git2::Sort::NONE;
        if oldest_first {
            sorting |= git2::Sort::REVERSE;
        }
        walk.set_sorting(sorting)
            .map_err(|e| AbError::Git(format!("cannot set revision walk order: {e}")))?;
        if first_parent_only {
            walk.simplify_first_parent().map_err(|e| {
                AbError::Git(format!("cannot restrict the walk to first parents: {e}"))
            })?;
        }
        walk.push(to_oid)
            .map_err(|e| AbError::Git(format!("cannot walk from {to}: {e}")))?;
        walk.hide(from).map_err(|e| {
            AbError::Git(format!(
                "cannot exclude {from_exclusive} from the walk: {e}"
            ))
        })?;

        let mut out = Vec::new();
        for step in walk {
            let oid = step.map_err(|e| AbError::Git(format!("revision walk failed: {e}")))?;
            out.push(ObjectId::parse(oid.to_string())?);
        }
        Ok(out)
    }
}

/// The four fields `git commit` resolves before writing a commit.
#[derive(Debug, PartialEq, Eq)]
pub struct ResolvedIdentity {
    pub author_name: String,
    pub author_email: String,
    pub committer_name: String,
    pub committer_email: String,
}

/// Strip the characters git refuses to put in an ident.
///
/// `git` removes `<`, `>` and newlines from a name or email before writing a
/// commit; libgit2 rejects only the angle brackets and will happily write a
/// newline straight into the ident line, producing a commit object no parser
/// can read back. Removing them here keeps the in-process writer from
/// creating an object the subprocess half could never have created.
fn strip_ident_crud(v: String) -> String {
    v.chars()
        .filter(|c| *c != '<' && *c != '>' && !c.is_control())
        .collect()
}

/// git's identity precedence, as a pure function of two lookups.
///
/// Split out from [`Libgit2Reader::ambient_identity`] so the rule can be
/// tested without setting environment variables, which are process-global and
/// would leak into every other test running in parallel.
///
/// The order per field is git's: `GIT_AUTHOR_NAME` / `GIT_COMMITTER_NAME`
/// then `user.name`; `GIT_AUTHOR_EMAIL` / `GIT_COMMITTER_EMAIL`, then
/// `user.email`, then the plain **`EMAIL`** variable. `EMAIL` is a documented
/// git mechanism (git-commit-tree(1)) and omitting it is the same defect as
/// reading configuration only: a host with `user.name` set and `EMAIL`
/// exported -- an ordinary container setup -- commits happily under `git` and
/// would fail every bus write here.
///
/// Two deliberate divergences from git, both in the direction of writing a
/// valid commit rather than refusing or writing a broken one:
///
///  - An environment variable set to the *empty string* is treated as absent
///    and the next source is consulted. Real git instead dies with "empty
///    ident name" for an empty name, and writes a commit with an empty
///    `<>` email for an empty email. Neither is useful to a bus writer.
///  - Characters git strips from an ident are stripped here too (see
///    [`strip_ident_crud`]); libgit2 would otherwise let a newline through.
pub fn resolve_identity(
    env: impl Fn(&str) -> Option<String>,
    config: impl Fn(&str) -> Option<String>,
) -> AbResult<ResolvedIdentity> {
    let name = |env_key: &str| -> Option<String> {
        env(env_key)
            .filter(|v| !v.is_empty())
            .or_else(|| config("user.name"))
            .filter(|v| !v.is_empty())
            .map(strip_ident_crud)
            .filter(|v| !v.is_empty())
    };
    let email = |env_key: &str| -> Option<String> {
        env(env_key)
            .filter(|v| !v.is_empty())
            .or_else(|| config("user.email"))
            .or_else(|| env("EMAIL"))
            .filter(|v| !v.is_empty())
            .map(strip_ident_crud)
            .filter(|v| !v.is_empty())
    };
    let missing_name = |what: &str, env_key: &str| {
        AbError::Git(format!(
            "cannot determine a commit {what} name: set user.name, or {env_key}"
        ))
    };
    let missing_email = |what: &str, env_key: &str| {
        AbError::Git(format!(
            "cannot determine a commit {what} email: set user.email, or {env_key} or EMAIL"
        ))
    };

    Ok(ResolvedIdentity {
        author_name: name("GIT_AUTHOR_NAME")
            .ok_or_else(|| missing_name("author", "GIT_AUTHOR_NAME"))?,
        author_email: email("GIT_AUTHOR_EMAIL")
            .ok_or_else(|| missing_email("author", "GIT_AUTHOR_EMAIL"))?,
        committer_name: name("GIT_COMMITTER_NAME")
            .ok_or_else(|| missing_name("committer", "GIT_COMMITTER_NAME"))?,
        committer_email: email("GIT_COMMITTER_EMAIL")
            .ok_or_else(|| missing_email("committer", "GIT_COMMITTER_EMAIL"))?,
    })
}

impl Libgit2Reader {
    /// A commit whose identity and timestamp the caller fixes, rather than
    /// taking them from repository configuration and the clock.
    ///
    /// This is what makes a merge candidate reproducible: AGENT_REVIEW.md
    /// section 7 requires any agent to be able to reconstruct another
    /// agent's candidate and get the same object id, which is only true if
    /// every byte of the commit object is a function of its inputs. It
    /// produces exactly the bytes `git commit-tree` produces for the same
    /// inputs, including git's rule that a message not ending in a newline
    /// gains one -- asserted directly by
    /// `commit_with_identity_matches_git_commit_tree_byte_for_byte`, which
    /// builds the same commit both ways and compares the two object ids.
    ///
    /// No signature is ever written, regardless of ambient `commit.gpgsign`
    /// configuration: section 7 admits "no optional encoding, signature, or
    /// mergetag headers". libgit2 signs only when explicitly asked, so this
    /// needs no equivalent of the subprocess version's `-c
    /// commit.gpgsign=false`.
    pub fn commit_with_identity(
        &self,
        tree: &ObjectId,
        parents: &[&ObjectId],
        message: &str,
        name: &str,
        email: &str,
        unix_seconds: i64,
    ) -> AbResult<ObjectId> {
        let tree_oid = git2::Oid::from_str(tree.as_str())
            .map_err(|e| AbError::Git(format!("{tree} is not a usable object id: {e}")))?;
        let tree_obj = self
            .repo
            .find_tree(tree_oid)
            .map_err(|e| AbError::Git(format!("{tree} does not resolve to a tree: {e}")))?;

        let mut parent_commits = Vec::with_capacity(parents.len());
        for p in parents {
            parent_commits.push(self.commit_at(p)?);
        }
        let parent_refs: Vec<&git2::Commit<'_>> = parent_commits.iter().collect();

        // Offset zero: the subprocess version passed "<ts> +0000".
        let when = git2::Time::new(unix_seconds, 0);
        let who = git2::Signature::new(name, email, &when)
            .map_err(|e| AbError::Git(format!("cannot build the fixed commit identity: {e}")))?;

        // `git commit-tree` terminates a message with a newline; libgit2
        // writes exactly what it is given. Matching git here is the whole
        // point -- a missing byte changes the object id. An *empty* message
        // is the exception: `git commit-tree -m ""` writes no body at all, so
        // adding a newline there would make the two disagree by one byte.
        let message = if message.is_empty() || message.ends_with('\n') {
            message.to_string()
        } else {
            format!("{message}\n")
        };

        let oid = self
            .repo
            .commit(None, &who, &who, &message, &tree_obj, &parent_refs)
            .map_err(|e| AbError::Git(format!("cannot create the deterministic commit: {e}")))?;
        ObjectId::parse(oid.to_string())
    }
}

impl HistoryReader for Libgit2Reader {
    fn resolve_rev(&self, spec: &str) -> AbResult<Option<ObjectId>> {
        match self.repo.revparse_single(spec) {
            Ok(obj) => Ok(Some(ObjectId::parse(obj.id().to_string())?)),
            // Both "no such ref" and "no such object" are ordinary absence
            // here, matching `rev-parse --verify --quiet <rev>^{object}`,
            // whose whole purpose is to distinguish those from a malformed
            // expression. `InvalidSpec` stays an error: a caller that hands
            // this an unparseable expression has a bug, and silently
            // reporting "not found" would hide it.
            Err(e)
                if e.code() == git2::ErrorCode::NotFound
                    || e.class() == git2::ErrorClass::Reference =>
            {
                Ok(None)
            }
            Err(e) => Err(AbError::Git(format!("cannot resolve {spec:?}: {e}"))),
        }
    }

    fn parents_of(&self, commit: &ObjectId) -> AbResult<Vec<ObjectId>> {
        let c = self.commit_at(commit)?;
        c.parent_ids()
            .map(|id| ObjectId::parse(id.to_string()))
            .collect()
    }

    fn committer_timestamp(&self, commit: &ObjectId) -> AbResult<i64> {
        Ok(self.commit_at(commit)?.committer().when().seconds())
    }

    fn commit_message(&self, commit: &ObjectId) -> AbResult<String> {
        let c = self.commit_at(commit)?;
        // A message that is not valid UTF-8 is content this crate cannot
        // reason about; every trailer it looks for is ASCII.
        //
        // Note this is genuinely stricter than the `git show -s --format=%B`
        // it replaced, which *transcodes* through the commit's `encoding`
        // header rather than converting lossily -- a commit declaring
        // `encoding ISO-8859-1` used to read back as valid UTF-8 and now
        // errors here. Callers must therefore treat this as a finding about
        // one commit, not as a reason to abandon a whole history walk; see
        // `audit_main`, which does.
        std::str::from_utf8(c.message_bytes())
            .map(|s| s.to_string())
            .map_err(|e| {
                invalid(format!(
                    "commit {commit} has a message that is not valid UTF-8: {e}"
                ))
            })
    }

    fn merge_base_count(&self, a: &ObjectId, b: &ObjectId) -> AbResult<usize> {
        let a_oid = git2::Oid::from_str(a.as_str())
            .map_err(|e| AbError::Git(format!("{a} is not a usable object id: {e}")))?;
        let b_oid = git2::Oid::from_str(b.as_str())
            .map_err(|e| AbError::Git(format!("{b} is not a usable object id: {e}")))?;
        match self.repo.merge_bases(a_oid, b_oid) {
            Ok(bases) => Ok(bases.len()),
            // `git merge-base --all` exits non-zero with no output when the
            // two commits share no history at all; that is zero bases, not a
            // failure to compute them.
            Err(e) if e.code() == git2::ErrorCode::NotFound => Ok(0),
            Err(e) => Err(AbError::Git(format!(
                "cannot compute merge bases of {a} and {b}: {e}"
            ))),
        }
    }

    fn first_parent_range(
        &self,
        from_exclusive: &ObjectId,
        to: &ObjectId,
    ) -> AbResult<Vec<ObjectId>> {
        // The call this replaced passed `--reverse`.
        self.walk(from_exclusive, to, true, true)
    }

    fn range(&self, from_exclusive: &ObjectId, to: &ObjectId) -> AbResult<Vec<ObjectId>> {
        // The call this replaced did *not* pass `--reverse`, so this stays
        // newest-first.
        self.walk(from_exclusive, to, false, false)
    }

    fn diff_name_status(&self, from: &ObjectId, to: &ObjectId) -> AbResult<Vec<(String, String)>> {
        let from_tree = self.tree_of(from)?;
        let to_tree = self.tree_of(to)?;
        // No `find_similar` call: see the trait method's doc for why rename
        // detection stays off.
        let diff = self
            .repo
            .diff_tree_to_tree(Some(&from_tree), Some(&to_tree), None)
            .map_err(|e| AbError::Git(format!("cannot diff {from}..{to}: {e}")))?;

        let mut out = Vec::new();
        for delta in diff.deltas() {
            // The status letters `git diff --name-status` prints, so a
            // caller (and a golden test) sees the same vocabulary as before.
            let status = match delta.status() {
                git2::Delta::Added => "A",
                git2::Delta::Deleted => "D",
                git2::Delta::Modified => "M",
                git2::Delta::Renamed => "R",
                git2::Delta::Copied => "C",
                // Unreachable in practice: without
                // `GIT_DIFF_INCLUDE_TYPECHANGE`, libgit2 splits a typechange
                // into a delete plus an add of the same path rather than
                // emitting this. Kept so the arm exists if that option is
                // ever set, and because dropping it would make the catch-all
                // below reject a status git can name.
                git2::Delta::Typechange => "T",
                other => {
                    return Err(AbError::Git(format!(
                        "unexpected diff status {other:?} between {from} and {to}"
                    )))
                }
            };
            // A delete has no new path and an add has no old one; take
            // whichever side exists, preferring the new path so a
            // modification reports its current name.
            let path = delta
                .new_file()
                .path()
                .or_else(|| delta.old_file().path())
                .ok_or_else(|| {
                    AbError::Git(format!("a change between {from} and {to} names no path"))
                })?;
            let path = path.to_str().ok_or_else(|| {
                invalid(format!(
                    "a path changed between {from} and {to} is not valid UTF-8"
                ))
            })?;
            // Git records paths with forward slashes regardless of platform;
            // `Path::to_str` on Windows preserves them, but normalize
            // defensively so scope claims (which are always slash-separated)
            // compare correctly.
            //
            // Note these paths are *unquoted*. `git diff --name-status`
            // applies `core.quotePath`, which is on by default, so the old
            // subprocess returned the literal 16 characters `"caf\303\251.txt"`
            // for `café.txt` -- a form no `PathClaim` could ever match, so
            // every non-ASCII path silently failed the reviewed-scope check
            // instead of being checked. Reporting the real path is what makes
            // that gate work on non-ASCII trees at all.
            out.push((status.to_string(), path.replace('\\', "/")));
        }
        Ok(out)
    }
}

#[cfg(test)]
thread_local! {
    /// Armed by [`arm_competing_writer`], fired once by the next
    /// [`fire_competing_writer`] on this thread.
    static BEFORE_COMPARE_AND_SET: std::cell::RefCell<Option<Box<dyn FnOnce()>>> =
        const { std::cell::RefCell::new(None) };
}

/// Arrange for `f` to run once, at the next `fire_competing_writer` point.
///
/// The fire points sit in `stream.rs` and `registry.rs` immediately after
/// each writer's staleness pre-check and *before* it builds its commit --
/// which is exactly where a real competing writer lands, and the window the
/// compare-and-swap exists to close.
///
/// The placement is load-bearing. Firing this from inside `compare_and_set`
/// instead would run it after any value the call site reads, so a call site
/// that defeated the CAS by re-reading the tip and passing *that* as
/// `expected` would still appear to be refused. Mutation testing found
/// exactly that defect surviving the whole suite, so the seam has to be
/// upstream of the call site's own reads.
///
/// Firing once, and only once, is what makes it a competing writer rather
/// than an infinite loop.
#[cfg(test)]
pub(crate) fn arm_competing_writer(f: impl FnOnce() + 'static) {
    BEFORE_COMPARE_AND_SET.with(|h| *h.borrow_mut() = Some(Box::new(f)));
}

/// Run whatever [`arm_competing_writer`] armed, if anything.
#[cfg(test)]
pub(crate) fn fire_competing_writer() {
    let armed = BEFORE_COMPARE_AND_SET.with(|h| h.borrow_mut().take());
    if let Some(f) = armed {
        f();
    }
}

/// An in-memory [`ObjectReader`] over content supplied directly, for unit
/// tests of everything layered on the trait.
///
/// It exists because the crate's established test seam does not reach here:
/// `gitrepo::mock::MockGit` works by intercepting the `git` subprocess, and
/// [`Libgit2Reader`] never spawns one. Rather than force every test of
/// `storage`/`stream`/`registry`'s blob-reading paths to build a real
/// repository and make real commits (which `outer_tests` still does, once,
/// as the end-to-end proof), this lets them state the exact tree content
/// under test -- including content a real `append_to_stream` would refuse
/// to write, which is precisely what the rejection paths need.
///
/// Paths are stored flat and slash-separated; `list_root_entries` derives
/// the root listing from them the way a real tree would, reporting the
/// first component of a nested path once as a directory entry.
#[cfg(test)]
#[derive(Default)]
pub struct FixtureObjectReader {
    commits: std::collections::BTreeMap<String, std::collections::BTreeMap<String, Vec<u8>>>,
}

#[cfg(test)]
impl FixtureObjectReader {
    pub fn new() -> Self {
        Self::default()
    }

    /// Records `content` at `path` in `commit`, creating the commit if this
    /// is the first path given for it. A commit with no paths recorded is
    /// one that does not resolve at all, which is how the
    /// commit-missing error path gets exercised.
    pub fn with_blob(mut self, commit: &ObjectId, path: &str, content: impl AsRef<[u8]>) -> Self {
        self.commits
            .entry(commit.as_str().to_string())
            .or_default()
            .insert(path.to_string(), content.as_ref().to_vec());
        self
    }

    /// Records an entry that exists in the tree but is not a file, so
    /// callers' "expected a file, found something else" branches can be
    /// tested. Modeled as a nested path, exactly as a real tree would
    /// represent a directory.
    pub fn with_directory(self, commit: &ObjectId, name: &str) -> Self {
        self.with_blob(commit, &format!("{name}/placeholder"), b"x")
    }

    fn tree_of(&self, commit: &ObjectId) -> AbResult<&std::collections::BTreeMap<String, Vec<u8>>> {
        self.commits
            .get(commit.as_str())
            .ok_or_else(|| AbError::Git(format!("commit {commit} does not resolve to a commit")))
    }
}

#[cfg(test)]
impl ObjectReader for FixtureObjectReader {
    fn read_blob_at(&self, commit: &ObjectId, path: &str) -> AbResult<Option<Vec<u8>>> {
        let tree = self.tree_of(commit)?;
        if let Some(bytes) = tree.get(path) {
            return Ok(Some(bytes.clone()));
        }
        let as_dir = format!("{path}/");
        if tree.keys().any(|k| k.starts_with(&as_dir)) {
            return Err(invalid(format!(
                "{path} in commit {commit} is not a file (it is a tree); expected file content"
            )));
        }
        Ok(None)
    }

    fn list_root_entries(&self, commit: &ObjectId) -> AbResult<Vec<String>> {
        let tree = self.tree_of(commit)?;
        let mut names = std::collections::BTreeSet::new();
        for path in tree.keys() {
            let root = match path.split_once('/') {
                Some((first, _)) => first,
                None => path.as_str(),
            };
            names.insert(root.to_string());
        }
        Ok(names.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn oid(byte: u8) -> ObjectId {
        ObjectId::parse(format!("{byte:02x}").repeat(20)).unwrap()
    }

    // ------------------------------------------------ the fixture reader

    #[test]
    fn fixture_reads_back_recorded_content() {
        let c = oid(1);
        let r = FixtureObjectReader::new().with_blob(&c, "header.json", b"{\"a\":1}");
        assert_eq!(
            r.read_blob_at(&c, "header.json").unwrap(),
            Some(b"{\"a\":1}".to_vec())
        );
    }

    #[test]
    fn fixture_reports_an_absent_path_as_none() {
        let c = oid(1);
        let r = FixtureObjectReader::new().with_blob(&c, "header.json", b"{}");
        assert_eq!(r.read_blob_at(&c, "epoch.json").unwrap(), None);
    }

    #[test]
    fn fixture_reports_an_unresolvable_commit_as_an_error() {
        let r = FixtureObjectReader::new().with_blob(&oid(1), "header.json", b"{}");
        let err = r.read_blob_at(&oid(2), "header.json").unwrap_err();
        assert!(matches!(err, AbError::Git(_)), "got {err:?}");
        assert!(err.to_string().contains("does not resolve"));
    }

    #[test]
    fn fixture_rejects_reading_a_directory_as_a_file() {
        let c = oid(1);
        let r = FixtureObjectReader::new().with_directory(&c, "subdir");
        let err = r.read_blob_at(&c, "subdir").unwrap_err();
        assert!(err.to_string().contains("is not a file"));
    }

    #[test]
    fn fixture_lists_root_entries_including_directories_once() {
        let c = oid(1);
        let r = FixtureObjectReader::new()
            .with_blob(&c, "header.json", b"{}")
            .with_blob(&c, "000000.jsonl", b"{}\n")
            .with_blob(&c, "sub/a", b"a")
            .with_blob(&c, "sub/b", b"b");
        assert_eq!(
            r.list_root_entries(&c).unwrap(),
            vec![
                "000000.jsonl".to_string(),
                "header.json".to_string(),
                "sub".to_string()
            ]
        );
    }

    #[test]
    fn fixture_listing_an_unresolvable_commit_is_an_error() {
        let r = FixtureObjectReader::new();
        assert!(r.list_root_entries(&oid(9)).is_err());
    }

    // ------------------------------------------------- the libgit2 reader

    fn git(dir: &Path, args: &[&str]) {
        let status = std::process::Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .status()
            .unwrap();
        assert!(status.success(), "git {args:?} failed in {}", dir.display());
    }

    /// A real repository with one commit holding `README.md` at its root
    /// and `sub/nested.txt` one level down.
    fn init_repo() -> (tempfile::TempDir, ObjectId) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path();
        git(path, &["init", "--quiet", "-b", "main"]);
        git(path, &["config", "user.email", "test@example.com"]);
        git(path, &["config", "user.name", "Test"]);
        std::fs::write(path.join("README.md"), "hello\n").unwrap();
        std::fs::create_dir(path.join("sub")).unwrap();
        std::fs::write(path.join("sub").join("nested.txt"), "deep\n").unwrap();
        git(path, &["add", "-A"]);
        git(path, &["commit", "-q", "-m", "initial"]);
        let head = crate::gitrepo::rev_parse(path, "HEAD").unwrap();
        (dir, ObjectId::parse(head).unwrap())
    }

    // ------------------------------------------------- history and identity

    /// The claim `commit_with_identity` exists to make: for the same tree,
    /// parents, message, identity and timestamp, libgit2 writes byte-for-byte
    /// the commit object `git commit-tree` writes -- so the object id matches.
    ///
    /// This is load-bearing, not decorative. AGENT_REVIEW.md section 7 lets
    /// any agent reconstruct another agent's merge candidate and compare ids;
    /// if these two disagreed by a single byte, every candidate built before
    /// this change would become unreproducible after it.
    #[test]
    fn commit_with_identity_matches_git_commit_tree_byte_for_byte() {
        let (repo, head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();

        let tree = {
            let blob = g.write_blob(b"payload\n").unwrap();
            g.write_tree(None, &[("a.txt", blob)]).unwrap()
        };

        // Messages chosen to exercise git's own normalization: one without a
        // trailing newline (git appends one), one with, and one with a
        // trailer block, which is what real candidates carry.
        for message in [
            "candidate: no trailing newline",
            "candidate: trailing newline\n",
            "candidate: with trailers\n\nAgent-Bus-Agent: c-agent\nCo-Authored-By: X <x@y>\n",
        ] {
            let ts = 1_700_000_000_i64;
            let ours = g
                .commit_with_identity(
                    &tree,
                    &[&head],
                    message,
                    crate::gitrepo::DETERMINISTIC_COMMIT_NAME,
                    crate::gitrepo::DETERMINISTIC_COMMIT_EMAIL,
                    ts,
                )
                .unwrap();

            let date = format!("{ts} +0000");
            let out = std::process::Command::new("git")
                .arg("-C")
                .arg(repo.path())
                .args(["-c", "commit.gpgsign=false"])
                .args([
                    "commit-tree",
                    tree.as_str(),
                    "-p",
                    head.as_str(),
                    "-m",
                    message,
                ])
                .env("GIT_AUTHOR_NAME", crate::gitrepo::DETERMINISTIC_COMMIT_NAME)
                .env(
                    "GIT_AUTHOR_EMAIL",
                    crate::gitrepo::DETERMINISTIC_COMMIT_EMAIL,
                )
                .env("GIT_AUTHOR_DATE", &date)
                .env(
                    "GIT_COMMITTER_NAME",
                    crate::gitrepo::DETERMINISTIC_COMMIT_NAME,
                )
                .env(
                    "GIT_COMMITTER_EMAIL",
                    crate::gitrepo::DETERMINISTIC_COMMIT_EMAIL,
                )
                .env("GIT_COMMITTER_DATE", &date)
                .env_remove("GIT_CONFIG_COUNT")
                .output()
                .unwrap();
            assert!(
                out.status.success(),
                "git commit-tree failed: {}",
                String::from_utf8_lossy(&out.stderr)
            );
            let theirs = String::from_utf8_lossy(&out.stdout).trim().to_string();

            assert_eq!(
                ours.as_str(),
                theirs,
                "libgit2 and git commit-tree disagree for message {message:?}"
            );
        }
    }

    /// AGENT_REVIEW.md section 7 admits "no optional encoding, signature, or
    /// mergetag headers". The byte-identity test above passes git an explicit
    /// `-c commit.gpgsign=false`, which proves the two agree when signing is
    /// off but says nothing about ambient configuration. This pins the
    /// stronger property: with `commit.gpgsign = true` set in the repository,
    /// our object id is unchanged, so a signed-by-default host cannot produce
    /// a candidate no other agent can reconstruct.
    #[test]
    fn commit_with_identity_ignores_ambient_gpgsign_configuration() {
        let (repo, head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let blob = g.write_blob(b"payload\n").unwrap();
        let tree = g.write_tree(None, &[("a.txt", blob)]).unwrap();
        let ts = 1_700_000_000_i64;

        let before = g
            .commit_with_identity(
                &tree,
                &[&head],
                "candidate",
                crate::gitrepo::DETERMINISTIC_COMMIT_NAME,
                crate::gitrepo::DETERMINISTIC_COMMIT_EMAIL,
                ts,
            )
            .unwrap();

        git(repo.path(), &["config", "commit.gpgsign", "true"]);
        git(repo.path(), &["config", "user.signingkey", "DEADBEEF"]);

        let after = g
            .commit_with_identity(
                &tree,
                &[&head],
                "candidate",
                crate::gitrepo::DETERMINISTIC_COMMIT_NAME,
                crate::gitrepo::DETERMINISTIC_COMMIT_EMAIL,
                ts,
            )
            .unwrap();

        assert_eq!(
            before, after,
            "ambient commit.gpgsign must not change the candidate's object id"
        );
        // And the object really carries no signature header.
        let raw = git2::Repository::open(repo.path()).unwrap();
        let odb = raw.odb().unwrap();
        let obj = odb
            .read(git2::Oid::from_str(after.as_str()).unwrap())
            .unwrap();
        let body = String::from_utf8_lossy(obj.data()).to_string();
        assert!(
            !body.contains("gpgsig"),
            "commit carries a signature: {body}"
        );
    }

    /// Rename detection stays off, so a rename is reported as both the path
    /// it left and the path it arrived at. `merge_ready` and `audit_main`
    /// scope-check every path this returns, and a rename *into* a reviewed
    /// scope must not hide the out-of-scope path it came from.
    #[test]
    fn diff_name_status_reports_both_sides_of_a_rename() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();

        let blob = g.write_blob(b"same content, moved\n").unwrap();
        let before_tree = g
            .write_tree(None, &[("outside.txt", blob.clone())])
            .unwrap();
        let before = g.create_commit(&before_tree, &[], "before").unwrap();
        let after_tree = g.write_tree(None, &[("inside.txt", blob)]).unwrap();
        let after = g.create_commit(&after_tree, &[&before], "after").unwrap();

        let changed = g.diff_name_status(&before, &after).unwrap();
        let mut paths: Vec<&str> = changed.iter().map(|(_, p)| p.as_str()).collect();
        paths.sort_unstable();
        assert_eq!(
            paths,
            vec!["inside.txt", "outside.txt"],
            "both sides of a rename must be reported so both get scope-checked"
        );
    }

    #[test]
    fn history_walks_agree_with_the_shape_of_the_graph() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();

        let blob = g.write_blob(b"x").unwrap();
        let tree = g.write_tree(None, &[("a.txt", blob)]).unwrap();
        let root = g.create_commit(&tree, &[], "root").unwrap();
        let mid = g.create_commit(&tree, &[&root], "mid").unwrap();
        let tip = g.create_commit(&tree, &[&mid], "tip").unwrap();

        assert_eq!(g.parents_of(&tip).unwrap(), vec![mid.clone()]);
        assert!(g.parents_of(&root).unwrap().is_empty());
        assert_eq!(
            g.first_parent_range(&root, &tip).unwrap(),
            vec![mid.clone(), tip.clone()],
            "oldest first, exclusive of the start point"
        );
        assert_eq!(g.range(&root, &tip).unwrap().len(), 2);
        assert_eq!(g.merge_base_count(&mid, &tip).unwrap(), 1);
    }

    /// Two commits with no shared history have zero merge bases -- the state
    /// `git merge-base --all` signals by exiting non-zero with no output, and
    /// which `merge_candidate` treats as "not exactly one" rather than as an
    /// error to propagate.
    #[test]
    fn merge_base_count_is_zero_for_unrelated_histories() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let blob = g.write_blob(b"x").unwrap();
        let tree = g.write_tree(None, &[("a.txt", blob)]).unwrap();
        let a = g.create_commit(&tree, &[], "orphan a").unwrap();
        let b = g.create_commit(&tree, &[], "orphan b").unwrap();
        // Distinct commits (different messages), sharing no ancestry.
        assert_ne!(a, b);
        assert_eq!(g.merge_base_count(&a, &b).unwrap(), 0);
    }

    #[test]
    fn resolve_rev_handles_refs_ids_and_peel_suffixes() {
        let (repo, head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();

        assert_eq!(g.resolve_rev("HEAD").unwrap(), Some(head.clone()));
        assert_eq!(g.resolve_rev(head.as_str()).unwrap(), Some(head.clone()));
        assert!(g.resolve_rev("refs/heads/main").unwrap().is_some());
        // A peel suffix resolves to a different object than the commit.
        let tree = g.resolve_rev(&format!("{head}^{{tree}}")).unwrap().unwrap();
        assert_ne!(tree, head);
    }

    /// Falsification: a well-formed id that names nothing, and a ref that
    /// does not exist, are both absence -- not errors.
    #[test]
    fn resolve_rev_reports_unknown_objects_and_refs_as_none() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        assert_eq!(g.resolve_rev(oid(0x5a).as_str()).unwrap(), None);
        assert_eq!(g.resolve_rev("refs/heads/never-existed").unwrap(), None);
    }

    // --------------------------------- regressions from adversarial review

    /// `range` must reproduce `git rev-list`'s order, which is *commit date*
    /// order, not topological order. The two agree on every linear history --
    /// which is exactly why the earlier guard test, built on a linear side
    /// branch, could not falsify the claim it existed to pin.
    ///
    /// This builds the shape where they diverge: a merge whose two sides have
    /// interleaved committer dates. With `Sort::TOPOLOGICAL` the walk returns
    /// one side entirely before the other; git interleaves them by date.
    #[test]
    fn range_matches_git_rev_list_order_across_a_date_skewed_merge() {
        let (repo, _head) = init_repo();

        // Commit at an exact committer date so the skew is deterministic.
        // git needs the `@<unix>` raw form here; a bare number is rejected.
        let commit_at = |name: &str, ts: i64| -> String {
            std::fs::write(repo.path().join(format!("{name}.txt")), name).unwrap();
            git(repo.path(), &["add", "-A"]);
            let date = format!("@{ts} +0000");
            let out = std::process::Command::new("git")
                .arg("-C")
                .arg(repo.path())
                .args(["commit", "-q", "-m", name])
                .env("GIT_AUTHOR_DATE", &date)
                .env("GIT_COMMITTER_DATE", &date)
                .output()
                .unwrap();
            assert!(
                out.status.success(),
                "git commit failed: {}",
                String::from_utf8_lossy(&out.stderr)
            );
            crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap()
        };

        let base = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();

        // Left side: dates 100 then 400 (relative to a fixed epoch).
        git(repo.path(), &["checkout", "-q", "-b", "left"]);
        commit_at("l1", 1_700_000_100);
        let l2 = commit_at("l2", 1_700_000_400);

        // Right side off base: dates 200 then 300 -- interleaved with the
        // left side, which is the whole point.
        git(repo.path(), &["checkout", "-q", "-b", "right", &base]);
        commit_at("r1", 1_700_000_200);
        let r2 = commit_at("r2", 1_700_000_300);

        // Merge them without a working-tree merge.
        let tree = crate::gitrepo::rev_parse(repo.path(), &format!("{r2}^{{tree}}")).unwrap();
        let merge = crate::gitrepo::commit_tree_deterministic(
            repo.path(),
            &tree,
            &[l2.as_str(), r2.as_str()],
            "merge",
        )
        .unwrap();

        let g = Libgit2Reader::open(repo.path()).unwrap();
        let ours: Vec<String> = g
            .range(
                &ObjectId::parse(base.clone()).unwrap(),
                &ObjectId::parse(merge.clone()).unwrap(),
            )
            .unwrap()
            .into_iter()
            .map(|id| id.into_string())
            .collect();

        let theirs: Vec<String> =
            crate::gitrepo::run_ok(repo.path(), &["rev-list", &format!("{base}..{merge}")])
                .unwrap()
                .lines()
                .map(|l| l.to_string())
                .collect();

        assert_eq!(
            ours, theirs,
            "range must reproduce `git rev-list` order on a date-skewed merge"
        );
    }

    /// `git commit` resolves identity from the environment before
    /// configuration. A host that supplies only `GIT_AUTHOR_*`/
    /// `GIT_COMMITTER_*` -- a CI container, a git hook, anything under `env`
    /// -- is ordinary, and reading configuration alone turned every bus write
    /// on such a host into a hard failure.
    ///
    /// Tested through the pure rule rather than by setting real environment
    /// variables, which are process-global and would leak into every other
    /// test running in parallel.
    #[test]
    fn identity_takes_the_environment_before_configuration() {
        let env_only = |k: &str| match k {
            "GIT_AUTHOR_NAME" => Some("CI Bot".to_string()),
            "GIT_AUTHOR_EMAIL" => Some("ci@example.com".to_string()),
            "GIT_COMMITTER_NAME" => Some("CI Bot".to_string()),
            "GIT_COMMITTER_EMAIL" => Some("ci@example.com".to_string()),
            _ => None,
        };
        let got = resolve_identity(env_only, |_| None).unwrap();
        assert_eq!(got.author_name, "CI Bot");
        assert_eq!(got.committer_email, "ci@example.com");

        // Environment wins over configuration, per field.
        let got = resolve_identity(
            |k| (k == "GIT_COMMITTER_NAME").then(|| "Committer".to_string()),
            |k| match k {
                "user.name" => Some("Configured".to_string()),
                "user.email" => Some("cfg@example.com".to_string()),
                _ => None,
            },
        )
        .unwrap();
        assert_eq!(got.author_name, "Configured", "no GIT_AUTHOR_NAME set");
        assert_eq!(got.committer_name, "Committer", "environment wins");
        assert_eq!(got.author_email, "cfg@example.com");
    }

    /// The `EMAIL` fallback. git resolves an email as
    /// `GIT_AUTHOR_EMAIL` -> `user.email` -> `EMAIL`, and a host with
    /// `user.name` configured and `EMAIL` exported is an ordinary container
    /// setup. Stopping at `user.email` made every bus write fail there --
    /// the same defect as reading configuration only, via a different
    /// variable.
    #[test]
    fn identity_falls_back_to_the_plain_email_variable() {
        let got = resolve_identity(
            |k| (k == "EMAIL").then(|| "envonly@example.com".to_string()),
            |k| (k == "user.name").then(|| "Only Name".to_string()),
        )
        .unwrap();
        assert_eq!(got.author_email, "envonly@example.com");
        assert_eq!(got.committer_email, "envonly@example.com");
        assert_eq!(got.author_name, "Only Name");

        // ...but `user.email` still wins over it.
        let got = resolve_identity(
            |k| (k == "EMAIL").then(|| "envonly@example.com".to_string()),
            |k| match k {
                "user.name" => Some("Only Name".to_string()),
                "user.email" => Some("configured@example.com".to_string()),
                _ => None,
            },
        )
        .unwrap();
        assert_eq!(got.author_email, "configured@example.com");
    }

    /// A missing name and a missing email are different problems and must not
    /// share one message -- the old text told an operator to "set user.name
    /// and user.email" when `user.name` was already set.
    #[test]
    fn identity_errors_name_the_field_that_is_actually_missing() {
        let err = resolve_identity(|_| None, |k| (k == "user.name").then(|| "N".to_string()))
            .unwrap_err()
            .to_string();
        assert!(err.contains("email"), "{err}");
        assert!(
            err.contains("EMAIL"),
            "must mention the EMAIL fallback: {err}"
        );
        assert!(!err.contains("author name"), "the name is present: {err}");

        let err = resolve_identity(|_| None, |k| (k == "user.email").then(|| "e@x".to_string()))
            .unwrap_err()
            .to_string();
        assert!(err.contains("name"), "{err}");
    }

    /// git removes `<`, `>` and newlines from an ident before writing a
    /// commit; libgit2 rejects only the angle brackets and would write a
    /// newline straight into the ident line, producing a commit object no
    /// parser can read back.
    #[test]
    fn identity_strips_the_characters_git_strips() {
        let got = resolve_identity(
            |k| match k {
                "GIT_AUTHOR_NAME" => Some(
                    "Ali
ce <boss>"
                        .to_string(),
                ),
                "GIT_AUTHOR_EMAIL" => Some(
                    "a
@e.com"
                        .to_string(),
                ),
                _ => None,
            },
            |k| match k {
                "user.name" => Some("N".to_string()),
                "user.email" => Some("e@x".to_string()),
                _ => None,
            },
        )
        .unwrap();
        assert_eq!(got.author_name, "Alice boss");
        assert_eq!(got.author_email, "a@e.com");
    }

    /// An empty environment variable falls through to the next source.
    ///
    /// This is a deliberate divergence, not parity: real git *dies* with
    /// "empty ident name" for `GIT_AUTHOR_NAME=""`, and writes a commit with
    /// an empty `<>` email for `GIT_AUTHOR_EMAIL=""`. Neither is useful to a
    /// bus writer, so both fall through here.
    #[test]
    fn identity_treats_an_empty_environment_variable_as_absent() {
        let got = resolve_identity(
            |_| Some(String::new()),
            |k| match k {
                "user.name" => Some("Configured".to_string()),
                "user.email" => Some("cfg@example.com".to_string()),
                _ => None,
            },
        )
        .unwrap();
        assert_eq!(got.author_name, "Configured");

        // And with nothing anywhere, a clear failure naming both routes.
        let err = resolve_identity(|_| None, |_| None).unwrap_err();
        assert!(err.to_string().contains("user.name"), "{err}");
        assert!(err.to_string().contains("GIT_AUTHOR_NAME"), "{err}");
    }

    /// `git diff --name-status` applies `core.quotePath`, so the subprocess
    /// this replaced returned `"caf\303\251.txt"` -- a form no slash-separated
    /// `PathClaim` could ever match, meaning every non-ASCII path silently
    /// failed the reviewed-scope check instead of being checked. Reporting the
    /// real path is what makes that gate work on a non-ASCII tree.
    #[test]
    fn diff_name_status_reports_non_ascii_paths_unquoted() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();

        let blob = g.write_blob(b"content\n").unwrap();
        let before = g
            .create_commit(&g.write_tree(None, &[]).unwrap(), &[], "empty")
            .unwrap();
        let after_tree = g.write_tree(None, &[("café.txt", blob)]).unwrap();
        let after = g.create_commit(&after_tree, &[&before], "add").unwrap();

        let changed = g.diff_name_status(&before, &after).unwrap();
        assert_eq!(
            changed,
            vec![("A".to_string(), "café.txt".to_string())],
            "the path must be the real one, not a quoted escape sequence"
        );
        assert!(
            !changed[0].1.contains('\\'),
            "no octal escaping: {:?}",
            changed[0].1
        );
    }

    // --------------------------------- history: statuses and error paths

    /// `diff_name_status` had test coverage for additions and deletions only.
    /// Modification and typechange are both reachable, and both feed the same
    /// scope gate in `merge_ready`/`audit_main`, so both need pinning.
    #[test]
    fn diff_name_status_reports_modification_and_typechange() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();

        let before_blob = g.write_blob(b"one\n").unwrap();
        let before_tree = g.write_tree(None, &[("f.txt", before_blob)]).unwrap();
        let before = g.create_commit(&before_tree, &[], "before").unwrap();

        // Modified: same path, different content.
        let after_blob = g.write_blob(b"two\n").unwrap();
        let after_tree = g
            .write_tree(None, &[("f.txt", after_blob.clone())])
            .unwrap();
        let after = g.create_commit(&after_tree, &[&before], "after").unwrap();
        assert_eq!(
            g.diff_name_status(&before, &after).unwrap(),
            vec![("M".to_string(), "f.txt".to_string())]
        );

        // Typechange: same path and content, different file mode. Built with
        // git2 directly because `ObjectWriter::write_tree` deliberately only
        // ever writes a regular-file mode.
        let raw = git2::Repository::open(repo.path()).unwrap();
        let exec_tree = {
            let mut b = raw.treebuilder(None).unwrap();
            b.insert(
                "f.txt",
                git2::Oid::from_str(after_blob.as_str()).unwrap(),
                i32::from(git2::FileMode::BlobExecutable),
            )
            .unwrap();
            ObjectId::parse(b.write().unwrap().to_string()).unwrap()
        };
        let exec = g.create_commit(&exec_tree, &[&after], "chmod").unwrap();
        let changed = g.diff_name_status(&after, &exec).unwrap();
        assert_eq!(changed.len(), 1, "{changed:?}");
        assert_eq!(changed[0].1, "f.txt");
        // git reports a mode-only change as a modification; either letter is
        // a real answer, but it must not be silently dropped.
        assert!(
            changed[0].0 == "T" || changed[0].0 == "M",
            "unexpected status {:?}",
            changed[0].0
        );
    }

    /// Falsification: a commit message that is not valid UTF-8 must be
    /// rejected rather than lossily converted. A lossy conversion could
    /// invent or destroy a trailer, and trailers are the input to merge
    /// authorization.
    #[test]
    fn commit_message_rejects_a_message_that_is_not_valid_utf8() {
        let (repo, head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let raw = git2::Repository::open(repo.path()).unwrap();

        // Hand-build a commit object so the message can hold bytes `git2`'s
        // safe API (which takes &str) could never produce.
        let tree = raw
            .find_commit(git2::Oid::from_str(head.as_str()).unwrap())
            .unwrap()
            .tree_id();
        let mut body = Vec::new();
        body.extend_from_slice(format!("tree {tree}\n").as_bytes());
        body.extend_from_slice(b"author T <t@e> 1700000000 +0000\n");
        body.extend_from_slice(b"committer T <t@e> 1700000000 +0000\n\n");
        body.extend_from_slice(b"subject \xff\xfe not utf8\n");
        let oid = raw
            .odb()
            .unwrap()
            .write(git2::ObjectType::Commit, &body)
            .unwrap();
        let id = ObjectId::parse(oid.to_string()).unwrap();

        let err = g.commit_message(&id).unwrap_err();
        assert!(err.to_string().contains("not valid UTF-8"), "{err}");
    }

    /// The endpoint checks in the walk: `git rev-list a..b` fails when either
    /// end names nothing, rather than quietly walking an empty range, and so
    /// must this.
    #[test]
    fn history_walks_reject_endpoints_that_name_nothing() {
        let (repo, head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let missing = oid(0x7c);

        assert!(g.range(&missing, &head).is_err(), "unknown start accepted");
        assert!(g.range(&head, &missing).is_err(), "unknown end accepted");
        assert!(g.first_parent_range(&missing, &head).is_err());
        assert!(g.first_parent_range(&head, &missing).is_err());
        assert!(g.parents_of(&missing).is_err());
        assert!(g.committer_timestamp(&missing).is_err());
        assert!(g.commit_message(&missing).is_err());
        assert!(g.diff_name_status(&missing, &head).is_err());
    }

    /// `first_parent_range` must follow only first parents, which is the
    /// difference between "what this merge brought to main" and "every commit
    /// reachable from it". `range` follows both.
    #[test]
    fn first_parent_range_skips_the_second_parents_commits() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let blob = g.write_blob(b"x").unwrap();
        let tree = g.write_tree(None, &[("a.txt", blob)]).unwrap();

        let base = g.create_commit(&tree, &[], "base").unwrap();
        let side = g.create_commit(&tree, &[&base], "side").unwrap();
        let main = g.create_commit(&tree, &[&base], "main").unwrap();
        let merge = g.create_commit(&tree, &[&main, &side], "merge").unwrap();

        let first_parent = g.first_parent_range(&base, &merge).unwrap();
        assert_eq!(
            first_parent,
            vec![main.clone(), merge.clone()],
            "the second parent's commit must not appear"
        );

        let mut all = g.range(&base, &merge).unwrap();
        all.sort();
        let mut expected = vec![main, side, merge];
        expected.sort();
        assert_eq!(all, expected, "every parent is followed here");
    }

    /// A merge base count above one is what AGENT_REVIEW.md section 7's
    /// "requires one merge base" exists to reject, and it is not reachable
    /// from a linear history.
    #[test]
    fn merge_base_count_counts_multiple_bases() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let blob = g.write_blob(b"x").unwrap();
        let tree = g.write_tree(None, &[("a.txt", blob)]).unwrap();

        // A criss-cross: two roots, then two merges of both, giving the pair
        // of merges two independent merge bases.
        let a = g.create_commit(&tree, &[], "root a").unwrap();
        let b = g.create_commit(&tree, &[], "root b").unwrap();
        let m1 = g.create_commit(&tree, &[&a, &b], "merge one").unwrap();
        let m2 = g.create_commit(&tree, &[&b, &a], "merge two").unwrap();

        assert_eq!(g.merge_base_count(&m1, &m2).unwrap(), 2);
        assert_eq!(g.merge_base_count(&a, &m1).unwrap(), 1);
    }

    /// A syntactically impossible revision expression is a caller bug, not
    /// absence, and must not be reported as `None`.
    #[test]
    fn resolve_rev_errors_on_an_unparseable_expression() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let err = g.resolve_rev("HEAD^{bogus-peel-type}").unwrap_err();
        assert!(matches!(err, AbError::Git(_)), "{err:?}");
    }

    // ------------------------------------------- writing and moving refs

    /// The round trip the whole write path rests on: bytes in, a tree built
    /// from them, a commit naming that tree, a ref pointing at the commit --
    /// then read straight back through the read half of the same trait set.
    #[test]
    fn libgit2_writes_a_root_commit_and_reads_it_back() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();

        let blob = g.write_blob(b"{}\n").unwrap();
        let tree = g.write_tree(None, &[("header.json", blob)]).unwrap();
        let commit = g.create_commit(&tree, &[], "test: root").unwrap();

        assert_eq!(
            g.read_blob_at(&commit, "header.json").unwrap(),
            Some(b"{}\n".to_vec())
        );
        assert_eq!(g.list_root_entries(&commit).unwrap(), vec!["header.json"]);
    }

    /// Building on a parent must carry every entry the caller did *not*
    /// name through untouched. This is what makes `append_to_stream`'s
    /// "changes only its own segment paths" structural rather than a
    /// retrospective diff.
    #[test]
    fn libgit2_write_tree_carries_unnamed_entries_through() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();

        let header = g.write_blob(b"header-v1").unwrap();
        let seg = g.write_blob(b"line\n").unwrap();
        let base_tree = g
            .write_tree(None, &[("header.json", header), ("000000.jsonl", seg)])
            .unwrap();
        let base = g.create_commit(&base_tree, &[], "test: base").unwrap();

        // Name only the segment.
        let seg2 = g.write_blob(b"line\nline2\n").unwrap();
        let next_tree = g
            .write_tree(Some(&base), &[("000000.jsonl", seg2)])
            .unwrap();
        let next = g
            .create_commit(&next_tree, &[&base], "test: append")
            .unwrap();

        assert_eq!(
            g.read_blob_at(&next, "header.json").unwrap(),
            Some(b"header-v1".to_vec()),
            "an entry the caller did not name must survive unchanged"
        );
        assert_eq!(
            g.read_blob_at(&next, "000000.jsonl").unwrap(),
            Some(b"line\nline2\n".to_vec())
        );
    }

    /// Falsification: the trait builds flat trees only, so a nested path is
    /// a programming error rather than something silently accepted.
    #[test]
    fn libgit2_write_tree_rejects_a_nested_name() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let blob = g.write_blob(b"x").unwrap();
        let err = g.write_tree(None, &[("sub/deep.json", blob)]).unwrap_err();
        assert!(err.to_string().contains("root-level file name"), "{err}");
    }

    #[test]
    fn libgit2_write_tree_rejects_an_empty_name() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let blob = g.write_blob(b"x").unwrap();
        let err = g.write_tree(None, &[("", blob)]).unwrap_err();
        assert!(err.to_string().contains("root-level file name"), "{err}");
    }

    /// Falsification: a blob id that names nothing in this repository.
    #[test]
    fn libgit2_write_tree_rejects_an_unresolvable_blob() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let err = g.write_tree(None, &[("a.json", oid(0xab))]).unwrap_err();
        assert!(matches!(err, AbError::Git(_)), "got {err:?}");
    }

    #[test]
    fn libgit2_create_commit_rejects_an_unresolvable_tree() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let err = g.create_commit(&oid(0xcd), &[], "test").unwrap_err();
        assert!(
            err.to_string().contains("does not resolve to a tree"),
            "{err}"
        );
    }

    #[test]
    fn libgit2_create_commit_rejects_an_unresolvable_parent() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let blob = g.write_blob(b"x").unwrap();
        let tree = g.write_tree(None, &[("a.json", blob)]).unwrap();
        let err = g.create_commit(&tree, &[&oid(0xef)], "test").unwrap_err();
        assert!(err.to_string().contains("parent"), "{err}");
    }

    #[test]
    fn libgit2_resolve_reports_an_absent_ref_as_none() {
        let (repo, _head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        assert_eq!(g.resolve("refs/heads/nope").unwrap(), None);
    }

    #[test]
    fn libgit2_list_returns_only_the_requested_prefix_sorted() {
        let (repo, head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        g.compare_and_set("refs/heads/agent-events/b", None, &head)
            .unwrap();
        g.compare_and_set("refs/heads/agent-events/a", None, &head)
            .unwrap();

        let got = g.list("refs/heads/agent-events/").unwrap();
        let names: Vec<&str> = got.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(
            names,
            vec!["refs/heads/agent-events/a", "refs/heads/agent-events/b"],
            "sorted by name, and refs/heads/main excluded by the prefix"
        );
        assert!(got.iter().all(|(_, c)| *c == head));
    }

    /// Falsification of the creation case: `expected = None` means "only if
    /// this ref does not exist", so a second creation must lose rather than
    /// overwrite the first.
    #[test]
    fn libgit2_compare_and_set_refuses_to_create_over_an_existing_ref() {
        let (repo, head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        g.compare_and_set("refs/heads/once", None, &head).unwrap();
        let err = g
            .compare_and_set("refs/heads/once", None, &head)
            .unwrap_err();
        assert!(err.to_string().contains("already exists"), "{err}");
        assert!(
            err.to_string().contains("re-read"),
            "the message must tell the loser what to do next: {err}"
        );
    }

    /// Falsification of the update case: the whole point of naming the
    /// expected old value is that a writer whose read is stale is refused.
    #[test]
    fn libgit2_compare_and_set_refuses_when_the_ref_has_moved() {
        let (repo, head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();

        let blob = g.write_blob(b"x").unwrap();
        let tree = g.write_tree(None, &[("a.json", blob)]).unwrap();
        let other = g.create_commit(&tree, &[], "test: other").unwrap();

        g.compare_and_set("refs/heads/moving", None, &head).unwrap();
        // Someone else advanced it.
        g.compare_and_set("refs/heads/moving", Some(&head), &other)
            .unwrap();
        // Our stale view still names the old value.
        let err = g
            .compare_and_set("refs/heads/moving", Some(&head), &other)
            .unwrap_err();
        assert!(
            err.to_string()
                .contains("changed after this write was prepared"),
            "{err}"
        );
        assert!(
            err.to_string()
                .contains("re-read the current tip and retry"),
            "must name the operator action, not just the failure: {err}"
        );
    }

    /// Falsification: expecting a value on a ref that does not exist at all
    /// is a different failure from expecting the wrong value, and must say so.
    #[test]
    fn libgit2_compare_and_set_refuses_when_the_ref_was_deleted() {
        let (repo, head) = init_repo();
        let g = Libgit2Reader::open(repo.path()).unwrap();
        let err = g
            .compare_and_set("refs/heads/gone", Some(&head), &head)
            .unwrap_err();
        assert!(err.to_string().contains("does not exist"), "{err}");
    }

    #[test]
    fn libgit2_reads_a_blob_at_the_tree_root() {
        let (repo, head) = init_repo();
        let r = Libgit2Reader::open(repo.path()).unwrap();
        assert_eq!(
            r.read_blob_at(&head, "README.md").unwrap(),
            Some(b"hello\n".to_vec())
        );
    }

    #[test]
    fn libgit2_reads_a_blob_nested_below_the_tree_root() {
        let (repo, head) = init_repo();
        let r = Libgit2Reader::open(repo.path()).unwrap();
        assert_eq!(
            r.read_blob_at(&head, "sub/nested.txt").unwrap(),
            Some(b"deep\n".to_vec())
        );
    }

    /// The distinction the whole trait contract rests on: a path that is
    /// simply not there is `None`, not an error.
    #[test]
    fn libgit2_reports_an_absent_path_as_none() {
        let (repo, head) = init_repo();
        let r = Libgit2Reader::open(repo.path()).unwrap();
        assert_eq!(r.read_blob_at(&head, "nope.json").unwrap(), None);
        assert_eq!(r.read_blob_at(&head, "sub/nope.json").unwrap(), None);
        assert_eq!(r.read_blob_at(&head, "nope/deeper.json").unwrap(), None);
    }

    /// ...whereas a commit that does not exist at all is an error, so a
    /// caller can never mistake "this repository has not fetched that
    /// commit yet" for "that file was never written".
    #[test]
    fn libgit2_reports_an_unresolvable_commit_as_an_error() {
        let (repo, _head) = init_repo();
        let r = Libgit2Reader::open(repo.path()).unwrap();
        let missing = ObjectId::parse("0".repeat(40)).unwrap();
        let err = r.read_blob_at(&missing, "README.md").unwrap_err();
        assert!(matches!(err, AbError::Git(_)), "got {err:?}");
        assert!(err.to_string().contains("does not resolve to a commit"));
    }

    /// A blob's own id is a valid `ObjectId` but is not a commit; reading
    /// "at" it must fail rather than silently peeling to something.
    #[test]
    fn libgit2_reports_a_non_commit_object_id_as_an_error() {
        let (repo, head) = init_repo();
        let blob_id = crate::gitrepo::rev_parse(repo.path(), &format!("{head}:README.md")).unwrap();
        let r = Libgit2Reader::open(repo.path()).unwrap();
        let err = r
            .read_blob_at(&ObjectId::parse(blob_id).unwrap(), "README.md")
            .unwrap_err();
        assert!(err.to_string().contains("does not resolve to a commit"));
    }

    #[test]
    fn libgit2_rejects_reading_a_directory_as_a_file() {
        let (repo, head) = init_repo();
        let r = Libgit2Reader::open(repo.path()).unwrap();
        let err = r.read_blob_at(&head, "sub").unwrap_err();
        assert!(err.to_string().contains("is not a file"), "got {err}");
    }

    /// Git stores a symlink's target text as an ordinary blob object -- only
    /// the tree entry's mode (120000) marks it as a link -- so a naive
    /// `object.as_blob()` would silently succeed and hand back the link
    /// *target string* as if it were real file content. Constructed via raw
    /// plumbing (`update-index --add --cacheinfo 120000,...`) rather than an
    /// actual filesystem symlink, since the latter needs elevated privileges
    /// to create on Windows.
    #[test]
    fn libgit2_rejects_reading_a_symlink_as_a_file() {
        let (repo, _head) = init_repo();
        let path = repo.path();
        let blob_hash = {
            let out = std::process::Command::new("git")
                .arg("-C")
                .arg(path)
                .args(["hash-object", "-w", "--stdin"])
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .spawn()
                .and_then(|mut child| {
                    use std::io::Write;
                    child.stdin.take().unwrap().write_all(b"README.md").unwrap();
                    child.wait_with_output()
                })
                .unwrap();
            assert!(out.status.success());
            String::from_utf8(out.stdout).unwrap().trim().to_string()
        };
        git(
            path,
            &[
                "update-index",
                "--add",
                "--cacheinfo",
                &format!("120000,{blob_hash},link.json"),
            ],
        );
        git(path, &["commit", "-q", "-m", "add a symlink"]);
        let head = crate::gitrepo::rev_parse(path, "HEAD").unwrap();
        let head = ObjectId::parse(head).unwrap();

        let r = Libgit2Reader::open(path).unwrap();
        let err = r.read_blob_at(&head, "link.json").unwrap_err();
        assert!(err.to_string().contains("symlink"), "got {err}");
    }

    #[test]
    fn libgit2_lists_root_entries_including_directories() {
        let (repo, head) = init_repo();
        let r = Libgit2Reader::open(repo.path()).unwrap();
        let mut names = r.list_root_entries(&head).unwrap();
        names.sort();
        assert_eq!(names, vec!["README.md".to_string(), "sub".to_string()]);
    }

    #[test]
    fn libgit2_listing_an_unresolvable_commit_is_an_error() {
        let (repo, _head) = init_repo();
        let r = Libgit2Reader::open(repo.path()).unwrap();
        let missing = ObjectId::parse("0".repeat(40)).unwrap();
        assert!(r.list_root_entries(&missing).is_err());
    }

    /// Opening must search upward from a subdirectory, matching `git -C`,
    /// since callers pass whatever path they were handed.
    #[test]
    fn libgit2_opens_from_a_subdirectory_of_the_repository() {
        let (repo, head) = init_repo();
        let r = Libgit2Reader::open(&repo.path().join("sub")).unwrap();
        assert_eq!(
            r.read_blob_at(&head, "README.md").unwrap(),
            Some(b"hello\n".to_vec())
        );
    }

    #[test]
    fn libgit2_open_fails_outside_a_repository() {
        let dir = tempfile::tempdir().unwrap();
        // `Libgit2Reader` holds a `git2::Repository`, which is not `Debug`,
        // so `unwrap_err` is unavailable here.
        let err = match Libgit2Reader::open(dir.path()) {
            Ok(_) => panic!("opening a plain directory as a repository must fail"),
            Err(e) => e,
        };
        assert!(matches!(err, AbError::Git(_)), "got {err:?}");
        assert!(err.to_string().contains("cannot open a git repository"));
    }

    /// Blob content is returned exactly as recorded, with no line-ending
    /// translation: `read_blob_at` reads the odb, not a checkout, so the
    /// `core.autocrlf`/`.gitattributes` machinery that governs a working
    /// tree never runs. `storage.rs` rejects CR bytes outright, so this is
    /// load-bearing on Windows.
    #[test]
    fn libgit2_returns_blob_bytes_untranslated() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path();
        git(path, &["init", "--quiet", "-b", "main"]);
        git(path, &["config", "user.email", "test@example.com"]);
        git(path, &["config", "user.name", "Test"]);
        git(path, &["config", "core.autocrlf", "true"]);
        std::fs::write(path.join("lf.jsonl"), "{\"a\":1}\n{\"b\":2}\n").unwrap();
        git(path, &["add", "-A"]);
        git(path, &["commit", "-q", "-m", "initial"]);
        let head = ObjectId::parse(crate::gitrepo::rev_parse(path, "HEAD").unwrap()).unwrap();
        let r = Libgit2Reader::open(path).unwrap();
        let bytes = r.read_blob_at(&head, "lf.jsonl").unwrap().unwrap();
        assert!(!bytes.contains(&b'\r'), "blob bytes must not gain CRs");
        assert_eq!(bytes, b"{\"a\":1}\n{\"b\":2}\n".to_vec());
    }
}
