//! Thin wrapper around shelling out to `git`. The helper "uses ordinary Git
//! fetch, rebase, commit, and push operations" (AGENT_BUS.md section 1) rather
//! than reimplementing Git plumbing, so every operation here is a literal
//! `git` invocation.

use crate::error::{invalid, AbError, AbResult};
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Debug)]
pub struct GitOutput {
    pub success: bool,
    pub stdout: String,
    pub stderr: String,
}

// `ok`/`err` are mock-construction convenience constructors used from other
// modules' `#[cfg(test)]` test code; a plain (non-test) clippy/build pass
// can't see that cross-module usage and reports them dead.
#[allow(dead_code)]
impl GitOutput {
    pub fn ok(stdout: impl Into<String>) -> Self {
        GitOutput {
            success: true,
            stdout: stdout.into(),
            stderr: String::new(),
        }
    }

    pub fn err(stderr: impl Into<String>) -> Self {
        GitOutput {
            success: false,
            stdout: String::new(),
            stderr: stderr.into(),
        }
    }
}

/// Every git invocation in this crate funnels through `run` (a plain
/// argument list dispatch) or `run_stdin` (the one command, `interpret-
/// trailers`, that needs piped input) — so unit tests can substitute a
/// scripted [`mock::MockGit`] for the real `git` subprocess at exactly this
/// seam and exercise error/retry paths in `commands.rs`/`bus.rs`/
/// `review_cmds.rs`/`validate_cmd.rs`/`history.rs` without spawning real
/// processes or building real repositories. See the `mock` submodule.
pub fn run(dir: &Path, args: &[&str]) -> AbResult<GitOutput> {
    if let Some(out) = mock::intercept(dir, args, None) {
        return out;
    }
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .map_err(|e| AbError::Git(format!("failed to run git {args:?}: {e}")))?;
    Ok(GitOutput {
        success: out.status.success(),
        stdout: String::from_utf8_lossy(&out.stdout).trim_end().to_string(),
        stderr: String::from_utf8_lossy(&out.stderr).trim_end().to_string(),
    })
}

/// Run a git command and turn a nonzero exit into an error.
pub fn run_ok(dir: &Path, args: &[&str]) -> AbResult<String> {
    let out = run(dir, args)?;
    if !out.success {
        return Err(AbError::Git(format!("git {args:?} failed: {}", out.stderr)));
    }
    Ok(out.stdout)
}

pub fn version() -> AbResult<String> {
    let out = Command::new("git")
        .arg("--version")
        .output()
        .map_err(|e| AbError::Git(format!("failed to run git --version: {e}")))?;
    let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
    // "git version 2.53.0.windows.1" -> "2.53.0"
    let ver = s
        .strip_prefix("git version ")
        .unwrap_or(&s)
        .split(|c: char| !c.is_ascii_digit() && c != '.')
        .next()
        .unwrap_or("")
        .to_string();
    let parts: Vec<&str> = ver.split('.').collect();
    if parts.len() >= 3 {
        Ok(format!("{}.{}.{}", parts[0], parts[1], parts[2]))
    } else {
        Ok(ver)
    }
}

pub fn repo_root(start: &Path) -> AbResult<PathBuf> {
    let out = run_ok(start, &["rev-parse", "--show-toplevel"])?;
    Ok(PathBuf::from(out))
}

/// The repository's single shared git directory (AGENT_BUS.md section 2:
/// "Multiple agents sharing one clone use detached worktrees"). In a linked
/// worktree, `<repo_root>/.git` is a *file* pointing elsewhere, not a
/// directory — callers must not join onto it directly (`repo_root.join(
/// ".git")` breaks under a linked worktree with an OS "not a directory"
/// error). `--git-common-dir` (not `--git-dir`) deliberately resolves to the
/// *main* checkout's git directory even from a linked worktree, so agent-bus
/// staging worktrees and the cross-process lock are shared repo-wide rather
/// than fragmented per linked worktree.
pub fn common_dir(start: &Path) -> AbResult<PathBuf> {
    let out = run_ok(start, &["rev-parse", "--git-common-dir"])?;
    let dir = PathBuf::from(out);
    if dir.is_absolute() {
        Ok(dir)
    } else {
        Ok(start.join(dir))
    }
}

pub fn object_format(dir: &Path) -> AbResult<String> {
    let out = run(dir, &["rev-parse", "--show-object-format"])?;
    if out.success && !out.stdout.is_empty() {
        Ok(out.stdout)
    } else {
        Ok("sha1".to_string())
    }
}

pub fn rev_parse(dir: &Path, rev: &str) -> AbResult<String> {
    run_ok(dir, &["rev-parse", "--verify", rev])
}

pub fn rev_parse_opt(dir: &Path, rev: &str) -> AbResult<Option<String>> {
    // `rev-parse --verify` alone only checks that `rev` is *syntactically*
    // resolvable: for a full-length hex string it echoes the input back and
    // exits 0 even when no such object exists in the odb. Appending
    // `^{object}` forces git to actually dereference to an object, which
    // fails for both a nonexistent hash and a nonexistent ref.
    let target = format!("{rev}^{{object}}");
    let out = run(dir, &["rev-parse", "--verify", "--quiet", &target])?;
    if out.success && !out.stdout.is_empty() {
        Ok(Some(out.stdout))
    } else {
        Ok(None)
    }
}

pub fn check_ref_format(refname: &str) -> bool {
    Command::new("git")
        .args(["check-ref-format", refname])
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

pub fn push(dir: &Path, remote: &str, refspec: &str) -> AbResult<GitOutput> {
    run(dir, &["push", remote, refspec])
}

/// Push one or more explicit `<sha>:<refname>` refspecs, optionally as one
/// `--atomic` transaction. Without `--force`, each ref update is a real
/// remote-side compare-and-swap: the receiving `git` rejects any refspec
/// whose new value is not a fast-forward of what it currently holds (or,
/// for a ref that does not yet exist there, always accepts it -- the same
/// CAS the coordinator needs is therefore already the plain push behavior,
/// with no separate `--force-with-lease` bookkeeping required).
pub fn push_refspecs(
    dir: &Path,
    remote: &str,
    atomic: bool,
    refspecs: &[String],
) -> AbResult<GitOutput> {
    let mut args: Vec<String> = vec!["push".to_string()];
    if atomic {
        args.push("--atomic".to_string());
    }
    args.push(remote.to_string());
    args.extend(refspecs.iter().cloned());
    let arg_refs: Vec<&str> = args.iter().map(String::as_str).collect();
    run(dir, &arg_refs)
}

/// Ensure a detached worktree checked out at `origin/agent-bus` exists at
/// `worktree_path`, creating it if necessary (AGENT_BUS.md section 2: "Multiple
/// agents sharing one clone use detached worktrees").
pub fn ensure_bus_worktree(
    repo_dir: &Path,
    worktree_path: &Path,
    start_point: &str,
) -> AbResult<()> {
    if worktree_path.exists() {
        return Ok(());
    }
    if let Some(parent) = worktree_path.parent() {
        std::fs::create_dir_all(parent).map_err(|e| AbError::Io {
            path: parent.display().to_string(),
            source: e,
        })?;
    }
    run_ok(
        repo_dir,
        &[
            "worktree",
            "add",
            "--detach",
            &worktree_path.to_string_lossy(),
            start_point,
        ],
    )?;
    Ok(())
}

pub fn add_all(dir: &Path) -> AbResult<()> {
    run_ok(dir, &["add", "-A"])?;
    Ok(())
}

pub fn commit(dir: &Path, message: &str) -> AbResult<String> {
    run_ok(dir, &["commit", "-m", message])?;
    rev_parse(dir, "HEAD")
}

pub fn status_porcelain(dir: &Path) -> AbResult<String> {
    run_ok(dir, &["status", "--porcelain"])
}

pub fn checkout_detach(dir: &Path, rev: &str) -> AbResult<()> {
    run_ok(dir, &["checkout", "--detach", rev])?;
    Ok(())
}

/// Rebase the current (detached) HEAD onto `upstream`. Preserves each
/// commit's tree/message bytes exactly, only changing its parent — unlike
/// discarding and reconstructing the commit, this is what lets a retried
/// publish keep the event's original `observed` value.
pub fn rebase_onto(dir: &Path, upstream: &str) -> AbResult<GitOutput> {
    run(dir, &["rebase", upstream])
}

pub fn rebase_abort(dir: &Path) -> AbResult<()> {
    let _ = run(dir, &["rebase", "--abort"]);
    Ok(())
}

pub fn commit_message_trailers(dir: &Path, rev: &str) -> AbResult<Vec<(String, String)>> {
    let body = run_ok(dir, &["show", "-s", "--format=%B", rev])?;
    let out = run_stdin(dir, &["interpret-trailers", "--parse"], &body)?;
    if !out.success {
        return Err(AbError::Git(format!(
            "interpret-trailers failed: {}",
            out.stderr
        )));
    }
    let mut trailers = Vec::new();
    for line in out.stdout.split('\n') {
        if line.is_empty() {
            continue;
        }
        if let Some((k, v)) = line.split_once(':') {
            trailers.push((k.trim().to_string(), v.trim().to_string()));
        }
    }
    Ok(trailers)
}

pub fn run_stdin(dir: &Path, args: &[&str], stdin: &str) -> AbResult<GitOutput> {
    if let Some(out) = mock::intercept(dir, args, Some(stdin)) {
        return out;
    }
    use std::io::Write;
    let mut child = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| AbError::Git(format!("failed to run git {args:?}: {e}")))?;
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(stdin.as_bytes())
        .map_err(|e| AbError::Git(format!("failed to write stdin to git {args:?}: {e}")))?;
    let out = child
        .wait_with_output()
        .map_err(|e| AbError::Git(format!("failed to wait on git {args:?}: {e}")))?;
    Ok(GitOutput {
        success: out.status.success(),
        stdout: String::from_utf8_lossy(&out.stdout).trim_end().to_string(),
        stderr: String::from_utf8_lossy(&out.stderr).trim_end().to_string(),
    })
}

/// `git merge-tree --write-tree` a no-conflict ORT merge of `theirs` into
/// `ours`, without touching the working tree or index. Returns the resulting
/// tree object id, or `Err` if the merge is not clean.
/// AGENT_BUS_SCHEMA.md section 2 ("fixes all merge options") / AGENT_REVIEW.md
/// section 7 ("fixed helper-owned options and repository attributes...
/// Windows and Linux must produce the same tree"): pin every config knob that
/// could otherwise make the resulting tree depend on the ambient environment
/// rather than only on `ours`/`theirs`.
fn pinned_merge_config_args() -> Vec<&'static str> {
    vec![
        "-c",
        "core.autocrlf=false",
        "-c",
        "core.safecrlf=false",
        "-c",
        "core.symlinks=true",
        "-c",
        "merge.renormalize=false",
        "-c",
        "merge.renames=true",
        "-c",
        "diff.renameLimit=0",
    ]
}

pub fn merge_tree_write_tree(dir: &Path, ours: &str, theirs: &str) -> AbResult<String> {
    let mut args = pinned_merge_config_args();
    args.extend(["merge-tree", "--write-tree", "--name-only", ours, theirs]);
    let out = run(dir, &args)?;
    if !out.success {
        return Err(invalid(format!(
            "merge-tree could not cleanly merge {theirs} into {ours}: {}",
            if out.stderr.is_empty() {
                &out.stdout
            } else {
                &out.stderr
            }
        )));
    }
    let tree = out.stdout.lines().next().unwrap_or("").trim().to_string();
    if tree.is_empty() {
        return Err(invalid("merge-tree produced no tree id"));
    }
    Ok(tree)
}

/// Committer-date unix timestamp (seconds) of `rev`.
pub fn committer_timestamp(dir: &Path, rev: &str) -> AbResult<i64> {
    let out = run_ok(dir, &["show", "-s", "--format=%ct", rev])?;
    out.trim().parse().map_err(|e| {
        invalid(format!(
            "could not parse committer timestamp for {rev}: {e}"
        ))
    })
}

/// The exact number of merge bases between `a` and `b` (AGENT_REVIEW.md
/// section 7: "It requires one merge base").
pub fn merge_base_count(dir: &Path, a: &str, b: &str) -> AbResult<usize> {
    let out = run_ok(dir, &["merge-base", "--all", a, b])?;
    Ok(out.lines().filter(|l| !l.trim().is_empty()).count())
}

/// Construct a commit object with fully deterministic metadata
/// (AGENT_REVIEW.md section 7: fixed author/committer identity, one-second-
/// past-latest-parent UTC timestamp, no optional headers, exact message).
/// `parents` must be given in the exact intended order; no other option
/// varies it.
pub fn commit_tree_deterministic(
    dir: &Path,
    tree: &str,
    parents: &[&str],
    message: &str,
) -> AbResult<String> {
    let mut latest = i64::MIN;
    for p in parents {
        let t = committer_timestamp(dir, p)?;
        latest = latest.max(t);
    }
    let ts = latest
        .checked_add(1)
        .ok_or_else(|| invalid("candidate timestamp overflow"))?;
    let date = format!("{ts} +0000");

    let mut args: Vec<&str> = vec!["commit-tree", tree];
    for p in parents {
        args.push("-p");
        args.push(p);
    }
    args.push("-m");
    args.push(message);

    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        // Deterministic candidates never carry a signature, regardless of
        // ambient repo/global signing config (AGENT_REVIEW.md section 7: "no
        // optional encoding, signature, or mergetag headers").
        .args(["-c", "commit.gpgsign=false"])
        .args(&args)
        .env("GIT_AUTHOR_NAME", "Grass Agent Bus")
        .env("GIT_AUTHOR_EMAIL", "agent-bus@invalid")
        .env("GIT_AUTHOR_DATE", &date)
        .env("GIT_COMMITTER_NAME", "Grass Agent Bus")
        .env("GIT_COMMITTER_EMAIL", "agent-bus@invalid")
        .env("GIT_COMMITTER_DATE", &date)
        .env_remove("GIT_CONFIG_COUNT")
        .output()
        .map_err(|e| AbError::Git(format!("failed to run git commit-tree: {e}")))?;
    if !out.status.success() {
        return Err(AbError::Git(format!(
            "git commit-tree failed: {}",
            String::from_utf8_lossy(&out.stderr)
        )));
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

pub fn tag_lightweight(dir: &Path, name: &str, target: &str) -> AbResult<()> {
    run_ok(dir, &["tag", name, target])?;
    Ok(())
}

pub fn tag_exists_at(dir: &Path, name: &str, target: &str) -> AbResult<bool> {
    match rev_parse_opt(dir, &format!("refs/tags/{name}"))? {
        Some(id) => Ok(id == target),
        None => Ok(false),
    }
}

/// Whether `remote` actually has a tag named `name` pointing at `target` --
/// a real `ls-remote` network round trip, not a check against anything
/// already fetched into the local repository. `tag_exists_at` alone cannot
/// tell the difference between "this tag reached origin" and "this tag only
/// ever existed in the reviewer's own clone" (AGENT_BUS_SCHEMA.md's linked
/// validation, and every other agent, need the former).
pub fn remote_tag_matches(dir: &Path, remote: &str, name: &str, target: &str) -> AbResult<bool> {
    let refspec = format!("refs/tags/{name}");
    let out = run(dir, &["ls-remote", "--tags", remote, &refspec])?;
    if !out.success {
        return Ok(false);
    }
    // Lightweight tags (the only kind this crate creates) list the target
    // commit's own sha directly, one "<sha>\t<ref>" line per match.
    let sha = out
        .stdout
        .lines()
        .next()
        .and_then(|l| l.split_whitespace().next());
    Ok(sha == Some(target))
}

pub fn diff_name_status(dir: &Path, from: &str, to: &str) -> AbResult<Vec<(String, String)>> {
    let out = run_ok(dir, &["diff", "--name-status", &format!("{from}..{to}")])?;
    let mut result = Vec::new();
    for line in out.lines() {
        let mut parts = line.splitn(2, '\t');
        if let (Some(status), Some(path)) = (parts.next(), parts.next()) {
            result.push((status.to_string(), path.to_string()));
        }
    }
    Ok(result)
}

pub fn rev_list_first_parent(dir: &Path, from_exclusive: &str, to: &str) -> AbResult<Vec<String>> {
    let range = format!("{from_exclusive}..{to}");
    let out = run_ok(dir, &["rev-list", "--first-parent", "--reverse", &range])?;
    Ok(out.lines().map(|s| s.to_string()).collect())
}

pub fn parents_of(dir: &Path, rev: &str) -> AbResult<Vec<String>> {
    let out = run_ok(dir, &["show", "-s", "--format=%P", rev])?;
    Ok(out.split_whitespace().map(|s| s.to_string()).collect())
}

pub fn commits_between_first_parent_exclusive(
    dir: &Path,
    ancestor: &str,
    descendant_second_parent: &str,
) -> AbResult<Vec<String>> {
    // Commits introduced by the second parent relative to the first parent:
    // ancestor..second_parent
    let range = format!("{ancestor}..{descendant_second_parent}");
    let out = run_ok(dir, &["rev-list", &range])?;
    Ok(out.lines().map(|s| s.to_string()).collect())
}

pub fn is_ancestor(dir: &Path, ancestor: &str, descendant: &str) -> AbResult<bool> {
    let out = run(dir, &["merge-base", "--is-ancestor", ancestor, descendant])?;
    Ok(out.success)
}

/// A scriptable stand-in for the real `git` subprocess, installed for the
/// duration of one unit test. `gitrepo::run`/`run_stdin` are the sole two
/// dispatch points every other function in this module (and therefore every
/// git call made by `commands.rs`/`bus.rs`/`review_cmds.rs`/
/// `validate_cmd.rs`/`history.rs`/`bootstrap.rs`) ultimately funnels
/// through, so mocking here is enough to unit-test those modules' error and
/// retry branches without spawning real `git` processes or building real
/// repositories on disk — that remains `tests/cli_flow.rs`'s job, exercising
/// the real thing end to end.
pub mod mock {
    use super::{AbResult, GitOutput};
    use std::cell::RefCell;
    use std::path::Path;

    type Matcher = Box<dyn Fn(&Path, &[&str], Option<&str>) -> bool>;
    type Responder = Box<dyn Fn(&Path, &[&str], Option<&str>) -> AbResult<GitOutput>>;

    struct Rule {
        matcher: Matcher,
        responder: Responder,
    }

    thread_local! {
        static ACTIVE: RefCell<Option<MockGit>> = const { RefCell::new(None) };
    }

    /// Builds an ordered list of call-matching rules. Rules are tried in
    /// registration order; the first whose matcher accepts the call handles
    /// it. A call nothing matches panics with the full argument list, so a
    /// missing or wrong expectation fails loudly at the exact `git`
    /// invocation that was unexpected, rather than silently returning empty
    /// output that then fails some unrelated assertion downstream.
    ///
    /// The construction API below (`new`/`on`/`on_prefix`/`on_with`/
    /// `install`) is only ever called from other modules' `#[cfg(test)]`
    /// test code; a plain (non-test) clippy/build pass can't see that
    /// cross-module usage and reports it dead. `MockGit` the *type* stays
    /// unconditionally compiled (not `#[cfg(test)]`) because `ACTIVE`'s
    /// thread-local, used by `intercept` in every build, is typed with it.
    #[derive(Default)]
    pub struct MockGit {
        rules: Vec<Rule>,
    }

    #[allow(dead_code)]
    impl MockGit {
        pub fn new() -> Self {
            MockGit { rules: Vec::new() }
        }

        /// Match calls whose argument list is exactly `args` (any directory,
        /// no stdin check), always returning `output`.
        pub fn on(self, args: &[&str], output: GitOutput) -> Self {
            let expected: Vec<String> = args.iter().map(|s| s.to_string()).collect();
            self.on_with(
                move |_, a, _| {
                    a.len() == expected.len() && a.iter().zip(&expected).all(|(x, y)| x == y)
                },
                move |_, _, _| Ok(output.clone()),
            )
        }

        /// Match calls whose argument list starts with `prefix` — useful for
        /// commands with a variable tail (e.g. `diff --name-status a..b`
        /// where the range differs per test).
        pub fn on_prefix(self, prefix: &[&str], output: GitOutput) -> Self {
            let expected: Vec<String> = prefix.iter().map(|s| s.to_string()).collect();
            self.on_with(
                move |_, a, _| {
                    a.len() >= expected.len()
                        && a[..expected.len()]
                            .iter()
                            .zip(&expected)
                            .all(|(x, y)| x == y)
                },
                move |_, _, _| Ok(output.clone()),
            )
        }

        /// Fully custom matcher and responder, for a rule that needs to
        /// inspect the call directory, compute a response from the actual
        /// arguments, or return an `Err` (a failed git invocation, not just a
        /// nonzero-exit `GitOutput`).
        pub fn on_with(
            mut self,
            matcher: impl Fn(&Path, &[&str], Option<&str>) -> bool + 'static,
            responder: impl Fn(&Path, &[&str], Option<&str>) -> AbResult<GitOutput> + 'static,
        ) -> Self {
            self.rules.push(Rule {
                matcher: Box::new(matcher),
                responder: Box::new(responder),
            });
            self
        }

        /// Installs this mock for the current thread. Since `cargo test` runs
        /// tests on separate threads by default, this does not leak across
        /// tests; the returned guard uninstalls it when dropped (including on
        /// unwind, so a failing assertion mid-test still cleans up).
        #[must_use]
        pub fn install(self) -> MockGuard {
            ACTIVE.with(|a| *a.borrow_mut() = Some(self));
            MockGuard(())
        }
    }

    // Only ever constructed from other modules' `#[cfg(test)]` test code.
    #[allow(dead_code)]
    pub struct MockGuard(());

    impl Drop for MockGuard {
        fn drop(&mut self) {
            ACTIVE.with(|a| *a.borrow_mut() = None);
        }
    }

    pub(crate) fn intercept(
        dir: &Path,
        args: &[&str],
        stdin: Option<&str>,
    ) -> Option<AbResult<GitOutput>> {
        ACTIVE.with(|a| {
            let borrow = a.borrow();
            let mock = borrow.as_ref()?;
            for rule in &mock.rules {
                if (rule.matcher)(dir, args, stdin) {
                    return Some((rule.responder)(dir, args, stdin));
                }
            }
            panic!(
                "MockGit: no rule matched `git {}` in {}",
                args.join(" "),
                dir.display()
            );
        })
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::path::PathBuf;

        #[test]
        fn intercept_returns_none_with_no_mock_installed() {
            assert!(intercept(&PathBuf::from("."), &["status"], None).is_none());
        }

        #[test]
        fn on_matches_exact_args_and_ignores_dir() {
            let _guard = MockGit::new()
                .on(
                    &["rev-parse", "--verify", "HEAD"],
                    GitOutput::ok("deadbeef"),
                )
                .install();
            let out = crate::gitrepo::run(
                &PathBuf::from("/some/repo"),
                &["rev-parse", "--verify", "HEAD"],
            )
            .unwrap();
            assert!(out.success);
            assert_eq!(out.stdout, "deadbeef");
        }

        #[test]
        fn on_prefix_matches_a_variable_tail() {
            let _guard = MockGit::new()
                .on_prefix(
                    &["diff", "--name-status"],
                    GitOutput::ok("A\tfoo/bar.jsonl"),
                )
                .install();
            let out =
                crate::gitrepo::run(&PathBuf::from("."), &["diff", "--name-status", "aaa..bbb"])
                    .unwrap();
            assert_eq!(out.stdout, "A\tfoo/bar.jsonl");
        }

        #[test]
        fn guard_uninstalls_on_drop() {
            {
                let _guard = MockGit::new().on(&["status"], GitOutput::ok("")).install();
                assert!(intercept(&PathBuf::from("."), &["status"], None).is_some());
            }
            assert!(
                intercept(&PathBuf::from("."), &["status"], None).is_none(),
                "the mock must not leak past the guard's scope"
            );
        }

        #[test]
        #[should_panic(expected = "no rule matched")]
        fn unmatched_call_panics_loudly() {
            let _guard = MockGit::new().on(&["status"], GitOutput::ok("")).install();
            let _ = intercept(&PathBuf::from("."), &["log"], None);
        }

        #[test]
        fn on_with_can_return_an_error() {
            let _guard = MockGit::new()
                .on_with(
                    |_, a, _| a.first() == Some(&"push"),
                    |_, _, _| Err(crate::error::AbError::Git("denied".into())),
                )
                .install();
            let err = crate::gitrepo::run(&PathBuf::from("."), &["push", "origin", "agent-bus"])
                .unwrap_err();
            assert!(format!("{err}").contains("denied"));
        }
    }
}

#[cfg(test)]
mod outer_tests {
    use super::*;
    use crate::gitrepo::mock::MockGit;
    use std::path::PathBuf;

    /// `--git-common-dir` returning an already-absolute path (the common case
    /// from within a linked worktree, AGENT_BUS.md section 2) must be used
    /// as-is, not re-joined onto `start`.
    #[test]
    fn common_dir_returns_an_absolute_result_unchanged() {
        let abs = if cfg!(windows) {
            "C:\\repo\\.git"
        } else {
            "/repo/.git"
        };
        let _guard = MockGit::new()
            .on(&["rev-parse", "--git-common-dir"], GitOutput::ok(abs))
            .install();
        let got = common_dir(&PathBuf::from("/wherever")).unwrap();
        assert_eq!(got, PathBuf::from(abs));
    }

    /// A relative `--git-common-dir` result (the common case from within the
    /// main checkout, e.g. `.git`) must be resolved against `start`.
    #[test]
    fn common_dir_joins_a_relative_result_onto_start() {
        let _guard = MockGit::new()
            .on(&["rev-parse", "--git-common-dir"], GitOutput::ok(".git"))
            .install();
        let start = PathBuf::from("/repo/checkout");
        let got = common_dir(&start).unwrap();
        assert_eq!(got, start.join(".git"));
    }

    /// A failed (or empty-stdout) `--show-object-format` invocation must
    /// default to `"sha1"` rather than propagating an error — old `git`
    /// versions do not support the flag at all.
    #[test]
    fn object_format_defaults_to_sha1_when_the_command_fails() {
        let _guard = MockGit::new()
            .on(
                &["rev-parse", "--show-object-format"],
                GitOutput::err("unknown option"),
            )
            .install();
        let got = object_format(&PathBuf::from(".")).unwrap();
        assert_eq!(got, "sha1");
    }

    #[test]
    fn object_format_returns_the_reported_format_on_success() {
        let _guard = MockGit::new()
            .on(
                &["rev-parse", "--show-object-format"],
                GitOutput::ok("sha256"),
            )
            .install();
        let got = object_format(&PathBuf::from(".")).unwrap();
        assert_eq!(got, "sha256");
    }

    /// An already-existing worktree path is a no-op success — `ensure_bus_worktree`
    /// must not attempt to recreate (or shell out to git) at all.
    #[test]
    fn ensure_bus_worktree_is_a_noop_when_the_path_already_exists() {
        let dir = tempfile::tempdir().unwrap();
        // No MockGit installed at all: if this reached a git call, the mock
        // seam would panic with "no rule matched" since nothing is registered.
        ensure_bus_worktree(&PathBuf::from("/unused"), dir.path(), "origin/agent-bus").unwrap();
    }

    /// When the worktree path's parent cannot be created (here, because a
    /// path component is an ordinary file, not a directory), the IO error
    /// must be surfaced as `AbError::Io`, not panic or silently proceed.
    #[test]
    fn ensure_bus_worktree_reports_io_error_when_parent_cannot_be_created() {
        let dir = tempfile::tempdir().unwrap();
        let blocking_file = dir.path().join("not_a_dir");
        std::fs::write(&blocking_file, "x").unwrap();
        let worktree_path = blocking_file.join("nested").join("wt");
        let err = ensure_bus_worktree(
            &PathBuf::from("/unused"),
            &worktree_path,
            "origin/agent-bus",
        )
        .unwrap_err();
        assert!(matches!(err, AbError::Io { .. }), "{err:?}");
    }

    /// The ordinary path: the worktree does not yet exist, its parent can be
    /// created, and `git worktree add --detach <path> <start>` succeeds.
    #[test]
    fn ensure_bus_worktree_creates_a_new_worktree() {
        let dir = tempfile::tempdir().unwrap();
        let worktree_path = dir.path().join("nested").join("wt");
        let _guard = MockGit::new()
            .on_prefix(&["worktree", "add", "--detach"], GitOutput::ok(""))
            .install();
        ensure_bus_worktree(
            &PathBuf::from("/unused"),
            &worktree_path,
            "origin/agent-bus",
        )
        .unwrap();
    }

    /// A failing `git interpret-trailers --parse` invocation must surface as
    /// an error rather than an empty/garbage trailer list.
    #[test]
    fn commit_message_trailers_reports_interpret_trailers_failure() {
        let _guard = MockGit::new()
            .on_prefix(
                &["show", "-s", "--format=%B"],
                GitOutput::ok("subject\n\nAgent-Bus-Agent: alice"),
            )
            .on(
                &["interpret-trailers", "--parse"],
                GitOutput::err("bad format"),
            )
            .install();
        let err = commit_message_trailers(&PathBuf::from("."), "HEAD").unwrap_err();
        assert!(
            format!("{err}").contains("interpret-trailers failed"),
            "{err}"
        );
    }

    /// A non-clean `merge-tree --write-tree` (conflicting merge) must be
    /// reported as an `invalid` error naming both sides, not panic or return
    /// a bogus tree id.
    #[test]
    fn merge_tree_write_tree_reports_a_conflicting_merge() {
        let _guard = MockGit::new()
            .on_prefix(
                &["-c"],
                GitOutput::err("CONFLICT (content): merge conflict"),
            )
            .install();
        let err = merge_tree_write_tree(&PathBuf::from("."), "ours-sha", "theirs-sha").unwrap_err();
        assert!(err.to_string().contains("could not cleanly merge"), "{err}");
    }

    /// A "successful" `merge-tree` call that nonetheless produces no tree id
    /// on stdout must still be rejected rather than returning an empty tree.
    #[test]
    fn merge_tree_write_tree_reports_empty_output_as_an_error() {
        let _guard = MockGit::new()
            .on_prefix(&["-c"], GitOutput::ok(""))
            .install();
        let err = merge_tree_write_tree(&PathBuf::from("."), "ours-sha", "theirs-sha").unwrap_err();
        assert!(err.to_string().contains("produced no tree id"), "{err}");
    }

    /// `commit_tree_deterministic` shells out via a raw `std::process::Command`
    /// (not through the `gitrepo::run`/`MockGit` seam — see its own doc
    /// comment for why: it needs custom env vars for deterministic
    /// author/committer identity), so exercising its failure branch needs a
    /// real repository and a real (invalid) tree object id.
    #[test]
    fn commit_tree_deterministic_reports_a_real_git_failure() {
        fn init_repo() -> tempfile::TempDir {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path();
            std::process::Command::new("git")
                .args(["init", "--quiet", "-b", "main"])
                .arg(path)
                .status()
                .unwrap();
            std::process::Command::new("git")
                .arg("-C")
                .arg(path)
                .args(["config", "user.email", "test@example.com"])
                .status()
                .unwrap();
            std::process::Command::new("git")
                .arg("-C")
                .arg(path)
                .args(["config", "user.name", "Test"])
                .status()
                .unwrap();
            std::fs::write(path.join("README.md"), "hello\n").unwrap();
            std::process::Command::new("git")
                .arg("-C")
                .arg(path)
                .args(["add", "README.md"])
                .status()
                .unwrap();
            std::process::Command::new("git")
                .arg("-C")
                .arg(path)
                .args(["commit", "-q", "-m", "initial"])
                .status()
                .unwrap();
            dir
        }
        let repo = init_repo();
        let err = commit_tree_deterministic(
            repo.path(),
            "0000000000000000000000000000000000000000",
            &[],
            "msg",
        )
        .unwrap_err();
        assert!(format!("{err}").contains("commit-tree failed"), "{err}");
    }
}
