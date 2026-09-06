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

/// The repository's single shared git directory. Agents share one clone and
/// work in linked worktrees (AGENT_BUS.md section 2), and in a linked
/// worktree `<repo_root>/.git` is a *file* pointing elsewhere, not a
/// directory — callers must not join onto it directly (`repo_root.join(
/// ".git")` breaks under a linked worktree with an OS "not a directory"
/// error). `--git-common-dir` (not `--git-dir`) deliberately resolves to the
/// *main* checkout's git directory even from a linked worktree, so every
/// agent's outbox lands in one repo-wide location rather than being
/// fragmented per linked worktree. (This crate no longer stages anything in
/// worktrees of its own; the outbox is what still needs a shared home.)
pub fn common_dir(start: &Path) -> AbResult<PathBuf> {
    let out = run_ok(start, &["rev-parse", "--git-common-dir"])?;
    let dir = PathBuf::from(out);
    if dir.is_absolute() {
        Ok(dir)
    } else {
        Ok(start.join(dir))
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

#[cfg(test)]
pub fn check_ref_format(refname: &str) -> bool {
    // Memoized, because this sits on the hot read path and costs a process.
    // `Branch::parse` runs it, `Branch` deserializes through `parse`, and
    // every review event names two branches -- so reducing the fleet's own
    // bus spawned hundreds of `git check-ref-format` processes per command,
    // measured at 2.5 seconds of a 6-second `status`. The set of distinct
    // ref names across a whole reduction is tiny (`refs/heads/main` and one
    // branch per nomination) and git's answer for a given name is a pure
    // function of that name, so the second and later asks are free.
    static SEEN: std::sync::LazyLock<std::sync::Mutex<std::collections::HashMap<String, bool>>> =
        std::sync::LazyLock::new(|| std::sync::Mutex::new(std::collections::HashMap::new()));

    // A poisoned lock means another thread panicked mid-insert. The map is
    // a pure cache, so recovering the guard and carrying on is correct --
    // there is no invariant a panic could have left half-established.
    let mut cache = SEEN.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(known) = cache.get(refname) {
        return *known;
    }
    let answer = Command::new("git")
        .args(["check-ref-format", refname])
        .status()
        .map(|s| s.success())
        .unwrap_or(false);
    cache.insert(refname.to_string(), answer);
    answer
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

/// Fetch one or more explicit `<remote-ref>:<local-ref>` refspecs. Without
/// `--force`, this refuses to move a local branch ref except as a fast-
/// forward -- exactly the property a read-only fetch of another agent's
/// stream wants: an unexpected rewrite on the remote surfaces as a failed
/// fetch here rather than silently overwriting local history (AGENT_
/// COORDINATION_EVOLUTION.md section 1: "force pushes... are prohibited").
///
/// Returns the raw `GitOutput` -- a failed fetch (network error, rejected
/// non-fast-forward, unresolvable refspec) is reported via `success: false`,
/// *not* an `Err`, exactly like [`run`]. Most callers want a fetch failure to
/// be a hard error unconditionally; use [`fetch_refspecs_ok`] for that
/// (round-6 adversarial review: `sync::synced_snapshot` used to `?`-propagate
/// this function's `Result` directly, which only catches a failure to spawn
/// `git` at all -- a genuinely rejected fetch was silently swallowed, so a
/// snapshot reduced from stale local state was reported as `Freshness::
/// CurrentAsOfRemoteProbe` with a fresh `last_synced`, undermining gate 17's
/// entire "fail closed on staleness" guarantee for every currency-sensitive
/// caller). Call this raw form directly only when the caller needs the exact
/// `GitOutput` for its own error message, or genuinely wants to distinguish
/// "some refspecs don't exist on the remote" from "network/spawn failure" by
/// inspecting `stderr` itself.
pub fn fetch_refspecs(dir: &Path, remote: &str, refspecs: &[String]) -> AbResult<GitOutput> {
    let mut args: Vec<String> = vec!["fetch".to_string(), remote.to_string()];
    args.extend(refspecs.iter().cloned());
    let arg_refs: Vec<&str> = args.iter().map(String::as_str).collect();
    run(dir, &arg_refs)
}

/// [`fetch_refspecs`], but a failed fetch (as well as a failure to spawn
/// `git` at all) is a hard `Err` -- the safe default for the common case
/// where a caller has no graceful fallback for a rejected or failed fetch.
pub fn fetch_refspecs_ok(dir: &Path, remote: &str, refspecs: &[String]) -> AbResult<()> {
    let out = fetch_refspecs(dir, remote, refspecs)?;
    if !out.success {
        return Err(AbError::Git(format!(
            "git fetch {remote} {refspecs:?} failed: {}",
            out.stderr
        )));
    }
    Ok(())
}

/// Which of `refnames` actually exist on `remote` right now, checked with
/// one `ls-remote` round trip rather than one call per ref. A single
/// unresolvable refspec fails a `git fetch` *in its entirety* -- nothing
/// gets fetched, not even the refs that do exist (verified empirically: a
/// two-refspec fetch where only one ref is missing exits nonzero and
/// fetches neither) -- so a caller fetching a set of refs it cannot fully
/// guarantee all exist (e.g. every currently active roster member, some of
/// which may be registered but not yet have published a stream) should
/// filter against this first rather than let the whole fetch fail closed.
pub fn remote_refs_existing(
    dir: &Path,
    remote: &str,
    refnames: &[String],
) -> AbResult<std::collections::BTreeSet<String>> {
    if refnames.is_empty() {
        return Ok(std::collections::BTreeSet::new());
    }
    let mut args: Vec<&str> = vec!["ls-remote", "--heads", remote];
    args.extend(refnames.iter().map(String::as_str));
    let out = run(dir, &args)?;
    if !out.success {
        return Err(AbError::Git(format!(
            "git ls-remote failed: {}",
            out.stderr
        )));
    }
    let mut existing = std::collections::BTreeSet::new();
    for line in out.stdout.lines() {
        if let Some((_, refname)) = line.split_once('\t') {
            existing.insert(refname.to_string());
        }
    }
    Ok(existing)
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

/// Whether `remote` actually has a tag named `name` pointing at `target` --
/// a real `ls-remote` network round trip, not a check against anything
/// already fetched into the local repository. A local-only existence check
/// alone cannot tell the difference between "this tag reached origin" and
/// "this tag only ever existed in the reviewer's own clone" (AGENT_BUS_
/// SCHEMA.md's linked validation, and every other agent, need the former) --
/// and it also cannot be a *precondition* for validation to even start,
/// since the checkout doing the validating may not be the one that pushed
/// the tag (`coordinator::verify_review_merge_authorized` relies on this
/// function alone for exactly that reason).
pub fn remote_tag_matches(dir: &Path, remote: &str, name: &str, target: &str) -> AbResult<bool> {
    let refspec = format!("refs/tags/{name}");
    let out = run(dir, &["ls-remote", "--tags", remote, &refspec])?;
    if !out.success {
        // `ls-remote` exits 0 with empty stdout when the refspec simply
        // matches nothing (that case is handled below, by `sha == None`) --
        // a nonzero exit here means the remote itself couldn't be reached
        // or queried at all, a materially different problem from "no such
        // tag" that deserves its own loud error rather than collapsing into
        // a plain `false` (round-7 adversarial review: the caller's own
        // rejection message, "candidate tag ... is not fetchable from
        // {remote}", pointed a caller at re-tagging when the real cause was
        // connectivity).
        return Err(AbError::Git(format!(
            "git ls-remote {remote} {refspec} failed: {}",
            out.stderr
        )));
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

/// `(status, path)` per changed path between `from` and `to`. A rename or
/// copy line (`R100`/`C75`/...) carries *two* tab-separated path fields (old,
/// new) rather than one -- `path` here is always the second/final one, the
/// path that actually exists in `to`'s tree, since every caller cares about
/// "what changed in the resulting tree," not "what it used to be called."
/// (Previously mis-parsed via a 2-way split, which folded a rename's two
/// paths into one string with a literal embedded tab -- round-6 adversarial
/// review, reproduced directly: `merge_ready::check_merge_ready`'s scope
/// check rejected every renamed file regardless of whether it was in scope,
/// even though renames are deliberately supported elsewhere in this exact
/// crate, `merge.renames=true` pinned for candidate construction.)
pub fn diff_name_status(dir: &Path, from: &str, to: &str) -> AbResult<Vec<(String, String)>> {
    let out = run_ok(dir, &["diff", "--name-status", &format!("{from}..{to}")])?;
    let mut result = Vec::new();
    for line in out.lines() {
        let mut parts = line.split('\t');
        let (Some(status), Some(first_path)) = (parts.next(), parts.next()) else {
            continue;
        };
        let path = parts.next().unwrap_or(first_path);
        result.push((status.to_string(), path.to_string()));
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

    /// Run a real `git` subcommand and assert it succeeded -- for test setup
    /// only, never for the behavior under test itself. Mirrors the pattern
    /// already established in `sync.rs`'s test module.
    fn git(dir: &Path, args: &[&str]) {
        let status = std::process::Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .status()
            .unwrap();
        assert!(status.success(), "git {args:?} failed in {}", dir.display());
    }

    /// A real, non-bare repository with one commit on `main` -- the common
    /// starting point for tests that exercise real `git` subprocess
    /// behavior (as opposed to the `MockGit` seam used above).
    fn init_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path();
        git(path, &["init", "--quiet", "-b", "main"]);
        git(path, &["config", "user.email", "test@example.com"]);
        git(path, &["config", "user.name", "Test"]);
        std::fs::write(path.join("README.md"), "hello\n").unwrap();
        git(path, &["add", "README.md"]);
        git(path, &["commit", "-q", "-m", "initial"]);
        dir
    }

    /// A real bare repository, standing in for a remote (as in `sync.rs`'s
    /// `init_bare_origin`).
    fn init_bare_origin() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        git(dir.path(), &["init", "--quiet", "--bare", "-b", "main"]);
        dir
    }

    /// Write `name` with `contents`, stage it, and commit it with `message`
    /// -- the common "add one more real commit" step used by several tests
    /// below to build up branch/merge history.
    fn commit_file(dir: &Path, name: &str, contents: &str, message: &str) {
        std::fs::write(dir.join(name), contents).unwrap();
        git(dir, &["add", name]);
        git(dir, &["commit", "-q", "-m", message]);
    }

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

    /// The success path: given a real parent and its real tree, the
    /// resulting commit's metadata must be exactly what the function's own
    /// doc comment promises -- fixed author/committer identity, a timestamp
    /// exactly one second past the (sole) parent's, no extra headers, and
    /// the exact given message and parent list.
    #[test]
    fn commit_tree_deterministic_produces_a_real_deterministic_commit() {
        let repo = init_repo();
        let parent = rev_parse(repo.path(), "HEAD").unwrap();
        let parent_ts = committer_timestamp(repo.path(), &parent).unwrap();
        let tree = run_ok(repo.path(), &["rev-parse", "HEAD^{tree}"])
            .unwrap()
            .trim()
            .to_string();

        let commit_id =
            commit_tree_deterministic(repo.path(), &tree, &[&parent], "deterministic message")
                .unwrap();

        let got_ts = committer_timestamp(repo.path(), &commit_id).unwrap();
        assert_eq!(got_ts, parent_ts + 1);

        let author = run_ok(
            repo.path(),
            &["show", "-s", "--format=%an <%ae>", &commit_id],
        )
        .unwrap();
        assert_eq!(author.trim(), "Grass Agent Bus <agent-bus@invalid>");

        let subject = run_ok(repo.path(), &["show", "-s", "--format=%s", &commit_id]).unwrap();
        assert_eq!(subject.trim(), "deterministic message");

        let parents = run_ok(repo.path(), &["show", "-s", "--format=%P", &commit_id]).unwrap();
        assert_eq!(parents.trim(), parent);
    }

    /// The success path, parsing real `interpret-trailers` output for a
    /// commit that actually has trailers.
    #[test]
    fn commit_message_trailers_parses_real_trailers_from_a_commit() {
        let repo = init_repo();
        git(
            repo.path(),
            &[
                "commit",
                "--allow-empty",
                "-q",
                "-m",
                "subject line\n\nAgent-Bus-Agent: alice\nAgent-Bus-Seq: 3",
            ],
        );
        let trailers = commit_message_trailers(repo.path(), "HEAD").unwrap();
        assert_eq!(
            trailers,
            vec![
                ("Agent-Bus-Agent".to_string(), "alice".to_string()),
                ("Agent-Bus-Seq".to_string(), "3".to_string()),
            ]
        );
    }

    /// A commit with no trailers at all must report an empty list, not an
    /// error.
    #[test]
    fn commit_message_trailers_is_empty_for_a_commit_with_no_trailers() {
        let repo = init_repo();
        let trailers = commit_message_trailers(repo.path(), "HEAD").unwrap();
        assert!(trailers.is_empty(), "{trailers:?}");
    }

    /// `run_stdin`'s own real (non-mocked) subprocess path: stdin actually
    /// reaches the spawned `git` process and its stdout comes back.
    #[test]
    fn run_stdin_pipes_input_to_a_real_git_process() {
        let repo = init_repo();
        let out = run_stdin(
            repo.path(),
            &["interpret-trailers", "--parse"],
            "subject\n\nSigned-off-by: Alice <alice@example.com>",
        )
        .unwrap();
        assert!(out.success, "{out:?}");
        assert!(
            out.stdout
                .contains("Signed-off-by: Alice <alice@example.com>"),
            "{}",
            out.stdout
        );
    }

    /// A real (non-mocked) git failure reached through `run_stdin` must
    /// come back as `success == false` with real stderr, not an `Err` or a
    /// panic.
    #[test]
    fn run_stdin_reports_a_real_git_failure() {
        let repo = init_repo();
        let out = run_stdin(
            repo.path(),
            &["hash-object", "--stdin", "-t", "bogus-type"],
            "data",
        )
        .unwrap();
        assert!(!out.success, "{out:?}");
        assert!(!out.stderr.is_empty(), "{out:?}");
    }

    /// The success path: a real, cleanly-mergeable pair of branches must
    /// produce a real, resolvable tree object containing both sides'
    /// changes.
    #[test]
    fn merge_tree_write_tree_produces_a_real_clean_merge() {
        let repo = init_repo();
        git(repo.path(), &["checkout", "-q", "-b", "theirs"]);
        commit_file(repo.path(), "theirs.txt", "theirs\n", "add theirs.txt");
        let theirs_tip = rev_parse(repo.path(), "HEAD").unwrap();

        git(repo.path(), &["checkout", "-q", "main"]);
        commit_file(repo.path(), "ours.txt", "ours\n", "add ours.txt");
        let ours_tip = rev_parse(repo.path(), "HEAD").unwrap();

        let tree = merge_tree_write_tree(repo.path(), &ours_tip, &theirs_tip).unwrap();
        let listing = run_ok(repo.path(), &["ls-tree", "--name-only", &tree]).unwrap();
        assert!(listing.contains("ours.txt"), "{listing}");
        assert!(listing.contains("theirs.txt"), "{listing}");
        assert!(listing.contains("README.md"), "{listing}");
    }

    /// A real (non-mocked) conflicting merge: `git merge-tree --write-tree`
    /// reports the conflict on stdout with an *empty* stderr, so this
    /// exercises the branch the existing mocked conflict test (which always
    /// supplies stderr) cannot reach.
    #[test]
    fn merge_tree_write_tree_reports_a_real_conflicting_merge() {
        let repo = init_repo();
        git(repo.path(), &["checkout", "-q", "-b", "theirs"]);
        commit_file(
            repo.path(),
            "README.md",
            "theirs change\n",
            "theirs edits readme",
        );
        let theirs_tip = rev_parse(repo.path(), "HEAD").unwrap();

        git(repo.path(), &["checkout", "-q", "main"]);
        commit_file(
            repo.path(),
            "README.md",
            "ours change\n",
            "ours edits readme",
        );
        let ours_tip = rev_parse(repo.path(), "HEAD").unwrap();

        let err = merge_tree_write_tree(repo.path(), &ours_tip, &theirs_tip).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("could not cleanly merge"), "{msg}");
        assert!(msg.to_lowercase().contains("conflict"), "{msg}");
    }

    /// A real commit's committer timestamp must match exactly what `git
    /// show --format=%ct` itself reports.
    #[test]
    fn committer_timestamp_reads_a_real_commits_committer_date() {
        let repo = init_repo();
        let head = rev_parse(repo.path(), "HEAD").unwrap();
        let ts = committer_timestamp(repo.path(), &head).unwrap();
        let expected: i64 = run_ok(repo.path(), &["show", "-s", "--format=%ct", &head])
            .unwrap()
            .trim()
            .parse()
            .unwrap();
        assert_eq!(ts, expected);
        assert!(ts > 0, "expected a real unix timestamp, got {ts}");
    }

    /// A nonexistent revision is a real, realistic failure path (`git show`
    /// itself fails) rather than the unreachable-in-practice parse-error
    /// branch.
    #[test]
    fn committer_timestamp_fails_for_a_nonexistent_revision() {
        let repo = init_repo();
        let err = committer_timestamp(repo.path(), "not-a-real-rev").unwrap_err();
        assert!(matches!(err, AbError::Git(_)), "{err:?}");
    }

    /// Two branches with exactly one common ancestor must report a count of
    /// exactly one.
    #[test]
    fn merge_base_count_finds_the_single_common_ancestor() {
        let repo = init_repo();
        git(repo.path(), &["checkout", "-q", "-b", "a"]);
        commit_file(repo.path(), "a.txt", "a\n", "a work");
        let a_tip = rev_parse(repo.path(), "HEAD").unwrap();

        git(repo.path(), &["checkout", "-q", "main"]);
        commit_file(repo.path(), "b.txt", "b\n", "b work");
        let b_tip = rev_parse(repo.path(), "HEAD").unwrap();

        let count = merge_base_count(repo.path(), &a_tip, &b_tip).unwrap();
        assert_eq!(count, 1);
    }

    /// Genuinely unrelated (orphan) histories share no merge base at all.
    /// NOTE: this is a real, observed quirk of `merge_base_count`'s current
    /// implementation, not a design choice this test is merely confirming:
    /// `git merge-base --all` on unrelated histories exits nonzero with no
    /// output ("no common commits"), and `merge_base_count` calls it via
    /// `run_ok`, which turns *any* nonzero exit into an `Err` -- so the
    /// "genuinely unrelated" case a caller most likely wants distinguished
    /// as `Ok(0)` instead surfaces as an opaque `AbError::Git` with an empty
    /// message, indistinguishable from a real usage error (e.g. a bad
    /// revision). See this function's report note.
    #[test]
    fn merge_base_count_errs_for_unrelated_orphan_histories() {
        let repo = init_repo();
        let main_tip = rev_parse(repo.path(), "HEAD").unwrap();

        git(repo.path(), &["checkout", "-q", "--orphan", "unrelated"]);
        git(repo.path(), &["rm", "-rf", "-q", "."]);
        commit_file(repo.path(), "other.txt", "other\n", "unrelated root");
        let orphan_tip = rev_parse(repo.path(), "HEAD").unwrap();

        let err = merge_base_count(repo.path(), &main_tip, &orphan_tip).unwrap_err();
        assert!(matches!(err, AbError::Git(_)), "{err:?}");
    }

    /// The ordinary path: a lightweight tag must resolve back to exactly
    /// the target it was created at.
    #[test]
    fn tag_lightweight_creates_a_real_tag_pointing_at_the_target() {
        let repo = init_repo();
        let head = rev_parse(repo.path(), "HEAD").unwrap();
        tag_lightweight(repo.path(), "v-test", &head).unwrap();
        let resolved = run_ok(repo.path(), &["rev-parse", "refs/tags/v-test"])
            .unwrap()
            .trim()
            .to_string();
        assert_eq!(resolved, head);
    }

    /// Against a real bare "remote": covers a tag that reached the remote
    /// and matches, one that reached the remote but points elsewhere there,
    /// and one that never reached the remote at all (a purely local tag
    /// must not be confused with a published one).
    #[test]
    fn remote_tag_matches_covers_matching_mismatching_and_missing_remote_tags() {
        let origin = init_bare_origin();
        let origin_url = origin.path().to_string_lossy().to_string();
        let repo = init_repo();
        let head = rev_parse(repo.path(), "HEAD").unwrap();
        commit_file(repo.path(), "second.txt", "x\n", "second commit");
        let second = rev_parse(repo.path(), "HEAD").unwrap();

        push_refspecs(
            repo.path(),
            &origin_url,
            false,
            &["HEAD:refs/heads/main".to_string()],
        )
        .unwrap();
        tag_lightweight(repo.path(), "v1", &head).unwrap();
        push_refspecs(
            repo.path(),
            &origin_url,
            false,
            &["refs/tags/v1:refs/tags/v1".to_string()],
        )
        .unwrap();
        // a second, purely local tag that is never pushed at all.
        tag_lightweight(repo.path(), "local-only", &second).unwrap();

        assert!(remote_tag_matches(repo.path(), &origin_url, "v1", &head).unwrap());
        assert!(!remote_tag_matches(repo.path(), &origin_url, "v1", &second).unwrap());
        assert!(!remote_tag_matches(repo.path(), &origin_url, "no-such-tag", &head).unwrap());
        assert!(!remote_tag_matches(repo.path(), &origin_url, "local-only", &second).unwrap());
    }

    /// Round-7 adversarial review: a genuinely unreachable remote must be a
    /// hard `Err`, distinct from an ordinary "no such tag" negative --
    /// `ls-remote` itself only ever exits nonzero for a real connectivity/
    /// access failure (an unmatched refspec pattern is a normal, zero-exit,
    /// empty-stdout result, already covered by the "no-such-tag" case
    /// above), so collapsing a nonzero exit into a plain `false` here would
    /// misdirect a caller into thinking the tag itself is the problem.
    #[test]
    fn remote_tag_matches_reports_a_genuine_connectivity_failure_as_an_error() {
        let repo = init_repo();
        let head = rev_parse(repo.path(), "HEAD").unwrap();
        let bogus_remote = repo.path().join("no-such-remote-at-all");
        let err = remote_tag_matches(repo.path(), &bogus_remote.to_string_lossy(), "v1", &head)
            .unwrap_err();
        assert!(err.to_string().contains("ls-remote"), "{err}");
    }

    /// A merge commit's first-parent history must list the mainline
    /// commits (including the merge commit itself) in oldest-first order,
    /// and must exclude commits reachable only via the merge's second
    /// parent.
    #[test]
    fn rev_list_first_parent_lists_only_first_parent_commits_in_order() {
        let repo = init_repo();
        let base = rev_parse(repo.path(), "HEAD").unwrap();

        git(repo.path(), &["checkout", "-q", "-b", "side"]);
        commit_file(repo.path(), "side.txt", "side\n", "side work");
        let side_tip = rev_parse(repo.path(), "HEAD").unwrap();

        git(repo.path(), &["checkout", "-q", "main"]);
        commit_file(repo.path(), "main2.txt", "main2\n", "main work");

        git(
            repo.path(),
            &["merge", "-q", "--no-ff", "-m", "merge side", "side"],
        );
        let merge_commit = rev_parse(repo.path(), "HEAD").unwrap();
        commit_file(repo.path(), "main3.txt", "main3\n", "more main work");
        let final_tip = rev_parse(repo.path(), "HEAD").unwrap();

        let commits = rev_list_first_parent(repo.path(), &base, &final_tip).unwrap();
        assert_eq!(commits.len(), 3, "{commits:?}");
        assert_eq!(commits[1], merge_commit);
        assert_eq!(*commits.last().unwrap(), final_tip);
        assert!(!commits.contains(&side_tip));
    }

    /// The commits a merge's second parent actually introduced, relative to
    /// the first-parent ancestor -- newest first, per plain `git rev-list`
    /// ordering.
    #[test]
    fn commits_between_first_parent_exclusive_lists_the_second_parents_new_commits() {
        let repo = init_repo();
        let base = rev_parse(repo.path(), "HEAD").unwrap();

        git(repo.path(), &["checkout", "-q", "-b", "side"]);
        commit_file(repo.path(), "side1.txt", "1\n", "side commit 1");
        commit_file(repo.path(), "side2.txt", "2\n", "side commit 2");
        let side_tip = rev_parse(repo.path(), "HEAD").unwrap();

        git(repo.path(), &["checkout", "-q", "main"]);
        git(
            repo.path(),
            &["merge", "-q", "--no-ff", "-m", "merge side", "side"],
        );

        let commits =
            commits_between_first_parent_exclusive(repo.path(), &base, &side_tip).unwrap();
        assert_eq!(commits.len(), 2, "{commits:?}");
        let subjects: Vec<String> = commits
            .iter()
            .map(|c| {
                run_ok(repo.path(), &["show", "-s", "--format=%s", c])
                    .unwrap()
                    .trim()
                    .to_string()
            })
            .collect();
        assert_eq!(
            subjects,
            vec!["side commit 2".to_string(), "side commit 1".to_string()]
        );
    }

    /// Round-6 adversarial review, reproduced directly: a rename line from
    /// `git diff --name-status` carries two tab-separated path fields (old,
    /// new), which a naive 2-way split folds into one string with a literal
    /// embedded tab -- `merge_ready::check_merge_ready`'s scope check then
    /// rejected every renamed file outright, in-scope or not.
    #[test]
    fn diff_name_status_reports_the_new_path_for_a_rename_not_a_tab_mangled_string() {
        let repo = init_repo();
        commit_file(repo.path(), "old.txt", "unchanged content\n", "add old.txt");
        let from = rev_parse(repo.path(), "HEAD").unwrap();
        git(repo.path(), &["mv", "old.txt", "new.txt"]);
        git(
            repo.path(),
            &["commit", "-q", "-m", "rename old.txt to new.txt"],
        );
        let to = rev_parse(repo.path(), "HEAD").unwrap();

        let changed = diff_name_status(repo.path(), &from, &to).unwrap();
        assert_eq!(changed.len(), 1, "{changed:?}");
        let (status, path) = &changed[0];
        assert!(status.starts_with('R'), "{status}");
        assert_eq!(path, "new.txt");
        assert!(!path.contains('\t'), "{path}");
    }
}
