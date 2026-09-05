//! Reading committed bus content straight out of the object database.
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
//! This module is the read path that skips all of it. [`ObjectReader`] is
//! the interface the rest of the crate codes against, stated in this
//! crate's own vocabulary -- "the bytes recorded at this path in this
//! commit", "the entries at the root of this commit's tree" -- rather than
//! as `git` argument lists. Two things fall out of that shape:
//!
//!  - The backend is swappable. [`Libgit2Reader`] is the production
//!    implementation, but nothing above this line knows libgit2 exists.
//!  - It is mockable. `gitrepo::mock::MockGit` intercepts the `git`
//!    subprocess, so it has no purchase on an in-process library call;
//!    [`FixtureObjectReader`] replaces it for everything ported here,
//!    letting `storage`/`stream`/`registry` unit-test their blob-reading
//!    paths against known content with no repository on disk at all.
//!
//! Deliberately read-only, and deliberately partial: writes, merges,
//! rebases and all remote transport stay on `gitrepo.rs`'s `git`
//! subprocess. In particular the merge path is pinned to git's own ORT
//! implementation for byte-identical cross-platform trees (AGENT_REVIEW.md
//! section 7) and must not be reimplemented against libgit2's separate
//! merge algorithm.

use crate::error::{invalid, AbError, AbResult};
use crate::scalars::ObjectId;
use std::path::Path;

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
        // An `ObjectId` is already validated as 40 or 64 lowercase hex
        // digits, so a parse failure here means the repository's own hash
        // algorithm cannot represent it -- in practice, a sha256 id against
        // a libgit2 built without its experimental sha256 support. Say so,
        // rather than reporting it as a missing commit.
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
