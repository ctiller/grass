//! Shared test fixtures, built **in process** through libgit2.
//!
//! Every module that needs a real repository used to construct one by
//! spawning `git`: `init`, two `config` calls, `add`, `commit` -- five
//! processes per fixture, and several more per test for the working commits
//! on top. Measured on the CI-class Windows box this crate targets, a single
//! `git` spawn costs 170-650ms and `git init` alone costs ~360ms, so the unit
//! suite was spending the overwhelming majority of its wall clock waiting on
//! process creation: 117 pure-logic tests in `apply` finish in 20ms, while 52
//! repository-building tests across `coordinator`, `merge_ready`, `sync` and
//! `audit_main` took 72 seconds between them.
//!
//! These build the same objects with the same library the production code now
//! runs on, so the fixtures stay *real* -- genuine commits, trees and refs
//! that `git` itself reads back without complaint. That distinction is the
//! reason this is not a mock. An earlier version of this crate did mock the
//! `git` subprocess, and the mock's `interpret-trailers` accepted any line
//! containing `": "` -- far more permissive than git's actual trailer rules --
//! so a whole family of tests was validating against a parser that does not
//! exist. Speed bought that way is not worth having.
//!
//! What deliberately still spawns `git`: the differential tests that exist
//! precisely to check this crate against the real binary (`range` versus
//! `git rev-list`, `commit_with_identity` versus `git commit-tree`, the
//! `check-ref-format` corpus, and everything driving `merge-tree`). Making
//! those in-process would delete their entire purpose.

use std::path::Path;

/// A fixed, deterministic identity and timestamp for fixture commits.
///
/// Fixed rather than "now" so a fixture commit's object id depends only on
/// its content -- which keeps any golden or id-comparing test stable, and
/// means a rerun cannot produce a different history than the one a failure
/// was diagnosed against.
const FIXTURE_TIME: i64 = 1_700_000_000;

fn signature() -> git2::Signature<'static> {
    git2::Signature::new(
        "Test",
        "test@example.com",
        &git2::Time::new(FIXTURE_TIME, 0),
    )
    .expect("a valid fixture signature")
}

/// A real, non-bare repository on `main` with one commit -- the starting
/// point most repository tests want.
pub(crate) fn init_repo() -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("a temp dir");
    init_repo_at(dir.path());
    dir
}

/// [`init_repo`], into a caller-owned directory.
pub(crate) fn init_repo_at(path: &Path) {
    let mut opts = git2::RepositoryInitOptions::new();
    opts.initial_head("main");
    let repo = git2::Repository::init_opts(path, &opts).expect("init a fixture repository");
    {
        let mut config = repo.config().expect("fixture config");
        config.set_str("user.name", "Test").expect("set user.name");
        config
            .set_str("user.email", "test@example.com")
            .expect("set user.email");
        // Keep fixtures byte-stable across platforms: this crate's own tests
        // compare object ids, and CRLF translation would make them differ on
        // Windows only.
        config.set_bool("core.autocrlf", false).expect("autocrlf");
    }
    commit_file_in(&repo, path, "README.md", "hello\n", "initial");
}

/// A real bare repository standing in for a remote.
pub(crate) fn init_bare_origin() -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("a temp dir");
    let repo = git2::Repository::init_bare(dir.path()).expect("init a bare fixture");
    repo.set_head("refs/heads/main")
        .expect("point the bare HEAD at main");
    dir
}

/// Writes `name`, stages it, and commits it onto the current branch.
pub(crate) fn commit_file(dir: &Path, name: &str, contents: &str, message: &str) -> String {
    let repo = git2::Repository::open(dir).expect("open the fixture repository");
    commit_file_in(&repo, dir, name, contents, message)
}

fn commit_file_in(
    repo: &git2::Repository,
    workdir: &Path,
    name: &str,
    contents: &str,
    message: &str,
) -> String {
    let full = workdir.join(name);
    if let Some(parent) = full.parent() {
        std::fs::create_dir_all(parent).expect("fixture parent directory");
    }
    std::fs::write(&full, contents).expect("write the fixture file");

    let mut index = repo.index().expect("fixture index");
    index
        .add_path(Path::new(name))
        .expect("stage the fixture file");
    index.write().expect("write the fixture index");
    let tree_id = index.write_tree().expect("write the fixture tree");
    let tree = repo.find_tree(tree_id).expect("find the fixture tree");

    // Parent is whatever HEAD points at, or none for the root commit -- the
    // same shape `git commit` produces, without the process.
    let parents: Vec<git2::Commit> = match repo.head() {
        Ok(head) => vec![head.peel_to_commit().expect("HEAD resolves to a commit")],
        Err(_) => vec![],
    };
    let parent_refs: Vec<&git2::Commit> = parents.iter().collect();
    let sig = signature();
    let id = repo
        .commit(Some("HEAD"), &sig, &sig, message, &tree, &parent_refs)
        .expect("write the fixture commit");
    id.to_string()
}
