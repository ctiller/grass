//! What is left of shelling out to `git`.
//!
//! This module was once every git operation in the crate. It is now only the
//! ones that must stay a subprocess, plus thin wrappers whose bodies moved
//! in-process to `gitobjects.rs` but whose signatures many callers still use:
//!
//!  - **Remote transport** -- `fetch`, `push`, `ls-remote`. `git2` is built
//!    with `default-features = false`, dropping its own HTTPS/SSH backends,
//!    so these keep going through the user's credential helpers, SSH agent
//!    and `.netrc`. Reimplementing them would mean acquiring OpenSSL and
//!    libssh2 as build dependencies and reimplementing credential discovery.
//!  - **`merge-tree --write-tree`** -- pinned to git's own ORT
//!    implementation because AGENT_REVIEW.md section 7 requires every host to
//!    produce a byte-identical tree, which libgit2's separate merge algorithm
//!    would not.
//!  - **`interpret-trailers --parse`** -- see `commit_message_trailers` for
//!    why this one is deliberately not reimplemented.
//!  - **`git --version`** -- the merge-engine pin check, which is a question
//!    about the `git` binary itself.
//!
//! Everything here runs under a deadline with a process-tree kill
//! (`run_with_deadline`), because the remote operations above are exactly the
//! ones that can otherwise block forever.

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

/// How long any `git` subprocess may run before it is killed.
///
/// Every surviving subprocess in this crate either talks to a remote
/// (`fetch`, `push`, `ls-remote`) or is `merge-tree`/`interpret-trailers`;
/// the remote ones are the ones that can block forever. `g-reviewer:29`
/// reported exactly that -- an unreachable or hanging remote wedges every
/// agent-bus command with no deadline and no way out -- and this is the
/// deadline that answers it.
///
/// Generous on purpose. The bus fetches and pushes a handful of small refs,
/// so a healthy operation is a second or two; two minutes distinguishes
/// "hung" from "slow network" without ever being the thing that fails a real
/// operation. Override with `AGENT_BUS_GIT_TIMEOUT_SECS` for an unusually
/// slow link, or to tighten it in a test.
/// The one place this variable's name is written.
///
/// Both the lookup and the timeout error message derive from it, so the
/// failure mode a mutation exposed -- the message telling an operator to set
/// a variable the code no longer reads -- cannot recur by drift.
pub(crate) const TIMEOUT_VAR: &str = "AGENT_BUS_GIT_TIMEOUT_SECS";

fn git_timeout() -> std::time::Duration {
    git_timeout_from(|k| std::env::var(k).ok())
}

/// [`git_timeout`] against a supplied lookup.
///
/// Parameterized for the same reason `gitobjects::resolve_identity` is:
/// testing only the parse rule leaves the *wiring* -- that anything reads
/// [`TIMEOUT_VAR`] at all -- unproven, and mutation testing showed exactly
/// that gap here. Environment variables are process-global, so a test cannot
/// set one without leaking into every test running beside it.
fn git_timeout_from(env: impl Fn(&str) -> Option<String>) -> std::time::Duration {
    std::time::Duration::from_secs(parse_timeout_secs(env(TIMEOUT_VAR).as_deref()))
}

/// The override's parse rule, separated from reading the environment so a
/// test can exercise it directly.
///
/// A test that re-implements this rule locally and asserts against its own
/// copy proves nothing about the code that ships -- which is exactly what the
/// test here used to do.
///
/// Zero is treated as absent rather than as "no deadline": a deadline an
/// environment variable can switch off is not a deadline, and always having
/// one is the whole point (g-reviewer:29).
fn parse_timeout_secs(raw: Option<&str>) -> u64 {
    const DEFAULT_SECS: u64 = 120;
    raw.and_then(|v| v.parse::<u64>().ok())
        .filter(|v| *v > 0)
        .unwrap_or(DEFAULT_SECS)
}

#[cfg(test)]
thread_local! {
    /// Counts calls to [`kill_process_tree`] *on this thread*, so a test can
    /// prove the deadline invoked it rather than only that it reported a
    /// timeout.
    ///
    /// Thread-local, not a process-global atomic. `cargo test` runs tests in
    /// parallel threads, and a shared counter would let a *sibling* test's
    /// kill satisfy this test's assertion while its own deadline never fired
    /// -- a green test proving nothing, which is the exact class of defect
    /// this counter exists to rule out. `kill_process_tree` is called from
    /// the timing-out caller's own thread, so a thread-local is both correct
    /// and isolated.
    pub(crate) static KILLS_REQUESTED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Kill `pid` and everything it spawned.
///
/// A bare `Child::kill` reaps only the process we started. `git fetch` and
/// `git push` delegate the actual transport to a child of their own (`ssh`,
/// `git-remote-https`, a credential helper), and it is normally *that*
/// process which is blocked -- on a dead TCP connection, or on a credential
/// prompt reading a terminal that is not there. Killing only the parent
/// leaves the real culprit running and holding the pipe, so the wait never
/// ends.
fn kill_process_tree(pid: u32) {
    #[cfg(test)]
    KILLS_REQUESTED.with(|c| c.set(c.get() + 1));

    #[cfg(windows)]
    {
        // `taskkill /T` walks the tree; `/F` is required because a blocked
        // child will not process a polite close request.
        //
        // Spawned and deliberately not waited on. Waiting here would put an
        // unbounded wait on the error path of the very mechanism that exists
        // to bound waits -- a hung `taskkill` would wedge the caller exactly
        // as the hung `git` did. The OS reaps the tree whether or not we
        // watch, and the caller needs the timeout error more than it needs
        // confirmation that the kill completed.
        let _ = Command::new("taskkill")
            .args(["/T", "/F", "/PID", &pid.to_string()])
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn();
    }
    #[cfg(unix)]
    {
        // The child was put in its own process group (see `spawn_git`), so a
        // negative pid signals the whole group in one call.
        unsafe {
            libc_kill(-(pid as i32), 9);
        }
    }
}

#[cfg(unix)]
extern "C" {
    #[link_name = "kill"]
    fn libc_kill(pid: i32, sig: i32) -> i32;
}

/// Run `command`, returning its output, or killing its whole process tree and
/// failing if it outruns [`git_timeout`].
///
/// The wait happens on a separate thread rather than by polling
/// Which ambient git configuration a subprocess is allowed to see.
///
/// The distinction is load-bearing, and an earlier revision of this function
/// got it wrong in the permissive-looking direction: it stripped every
/// `GIT_CONFIG_*` variable for *all* subprocesses, which silently disarmed
/// the standard mechanisms for giving a push its credentials --
/// `GIT_CONFIG_COUNT` carrying `credential.helper` or `http.*.extraheader`
/// (how CI injects a token) and `GIT_CONFIG_GLOBAL` pointing at a config
/// outside an unwritable `$HOME`. Publication is the coordinator's sole job
/// (AGENT_COORDINATION_EVOLUTION.md section 2.3), so a host that cannot push
/// stalls the whole bus.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ConfigPolicy {
    /// The operator's configuration is *wanted*: credential helpers,
    /// `url.<base>.insteadOf`, proxies, `http.*`. Everything transport needs
    /// to reach a remote at all.
    Inherit,
    /// The operator's configuration is a *hazard*, because the command's
    /// output must depend only on its inputs: AGENT_REVIEW.md section 7
    /// requires a merge candidate to be byte-identically reconstructible on
    /// another host, and `interpret-trailers --parse` decides which commits
    /// carry an `Agent-Bus-Agent` trailer at all.
    ///
    /// Removing the variables is not sufficient, which is why this forces
    /// values rather than only unsetting: the ambient `~/.gitconfig` is read
    /// precisely when `GIT_CONFIG_GLOBAL` is *absent*. Measured against a
    /// global config defining a `merge.<driver>.driver` and a
    /// `core.attributesFile` selecting it, removal alone still produced a
    /// different tree for the same two commits; forcing produced the clean
    /// one.
    Hermetic,
}

// The policy the most recent `spawn_and_wait` on *this thread* ran under.
//
// A test seam, for a gap unit tests could not otherwise reach: asserting what
// `ConfigPolicy::Hermetic` does proves nothing about whether a given call
// site uses it, and mutation testing showed exactly that -- switching
// `merge_tree_write_tree` back to the inheriting `run` left the whole suite
// green. Observing it directly is the only honest alternative to setting a
// hostile `XDG_CONFIG_HOME` in the test process, which is global to every
// test running beside it.
//
// Thread-local rather than global for that same reason: the call under test
// and the assertion happen on one thread, so a sibling test cannot satisfy
// or clobber it.
#[cfg(test)]
thread_local! {
    static LAST_POLICY: std::cell::Cell<Option<ConfigPolicy>> =
        const { std::cell::Cell::new(None) };
}

#[cfg(test)]
pub(crate) fn last_config_policy() -> Option<ConfigPolicy> {
    LAST_POLICY.with(|p| p.get())
}

impl ConfigPolicy {
    fn apply(self, command: &mut Command) {
        #[cfg(test)]
        LAST_POLICY.with(|p| p.set(Some(self)));
        match self {
            ConfigPolicy::Inherit => {}
            ConfigPolicy::Hermetic => {
                // Injection at `-c` precedence, which libgit2 never sees.
                // Dropping `GIT_CONFIG_COUNT` neutralizes the indexed
                // `_KEY_<n>`/`_VALUE_<n>` pairs, which git reads only
                // through it. This half is not redundant with the forcing
                // below: with the count still set, an injected
                // `trailer.separators` was measured to survive
                // `GIT_CONFIG_GLOBAL=/dev/null` and make every trailer in a
                // commit message vanish from `--parse`.
                command.env_remove("GIT_CONFIG_PARAMETERS");
                command.env_remove("GIT_CONFIG_COUNT");
                // `/dev/null` is git's own documented spelling of "no such
                // config file", honored by git-for-windows too.
                command.env("GIT_CONFIG_GLOBAL", "/dev/null");
                command.env("GIT_CONFIG_SYSTEM", "/dev/null");
                command.env("GIT_CONFIG_NOSYSTEM", "1");
                // The system *attributes* file is reachable through no
                // `GIT_CONFIG_*` variable at all and needs its own switch.
                command.env("GIT_ATTR_NOSYSTEM", "1");
            }
        }
    }
}

/// `try_wait` in a loop. Polling costs either latency (a sleep between
/// checks, paid by every fast call) or CPU (a tight spin); a blocking wait
/// on a thread costs neither, and `recv_timeout` gives the deadline for
/// free. That matters here because these are the calls left on the hot
/// publication path.
fn run_with_deadline(
    mut command: Command,
    what: &str,
    policy: ConfigPolicy,
) -> AbResult<GitOutput> {
    command
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    spawn_and_wait(command, what, None, git_timeout(), policy)
}

/// [`run_with_deadline`], but writing `stdin_text` to the child first.
fn run_with_deadline_stdin(
    mut command: Command,
    what: &str,
    stdin_text: &str,
    policy: ConfigPolicy,
) -> AbResult<GitOutput> {
    command
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    spawn_and_wait(command, what, Some(stdin_text), git_timeout(), policy)
}

/// `timeout` is a parameter rather than read from [`git_timeout`] here so a
/// test can exercise the expiry path with a short deadline without setting a
/// process-global environment variable that every other test running in
/// parallel would also see.
fn spawn_and_wait(
    mut command: Command,
    what: &str,
    stdin_text: Option<&str>,
    timeout: std::time::Duration,
    policy: ConfigPolicy,
) -> AbResult<GitOutput> {
    // The two halves of this crate must agree on which repository they are
    // talking about. `git` honors `GIT_DIR`/`GIT_WORK_TREE` in preference to
    // the `-C <dir>` we pass; libgit2's `Repository::discover` ignores them
    // entirely and uses the path. With one of those set to another
    // repository the halves diverge -- `merge_tree_write_tree` would write a
    // tree into one object database while `commit_tree_deterministic` looked
    // for it in another, and a push would run against the wrong repository.
    // Before the in-process move there was only one half and no such split.
    //
    // Removing them makes the explicit path authoritative for both, which is
    // what every caller here means: each passes a repository path it
    // resolved itself.
    //
    // `GIT_DIR`/`GIT_WORK_TREE` alone do not close it. `git` also honors
    // `GIT_OBJECT_DIRECTORY`, `GIT_ALTERNATE_OBJECT_DIRECTORIES`,
    // `GIT_COMMON_DIR`, `GIT_INDEX_FILE` and `GIT_NAMESPACE` over `-C <dir>`,
    // and `Repository::discover` honors none of them. The object-directory
    // ones reach exactly the split named above: with `GIT_OBJECT_DIRECTORY`
    // set, `merge-tree --write-tree` writes its tree into that directory and
    // the in-process `commit_with_identity` cannot find it.
    //
    // Repository *location* is stripped unconditionally, for every caller:
    // it is the one class where the two halves of this crate would disagree
    // about which repository they are talking about. Ambient *configuration*
    // is not a single question with a single answer -- see [`ConfigPolicy`],
    // applied below -- because transport needs the operator's configuration
    // and candidate construction must be insulated from it.
    //
    // Nothing transport needs is touched here: `GIT_SSH_COMMAND`,
    // `GIT_ASKPASS`, `GIT_TERMINAL_PROMPT`, `GIT_SSL_*`, `GIT_PROXY_COMMAND`
    // and the credential-helper configuration all survive both policies.
    for var in [
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_COMMON_DIR",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_INDEX_FILE",
        "GIT_NAMESPACE",
        "GIT_CEILING_DIRECTORIES",
        "GIT_DISCOVERY_ACROSS_FILESYSTEM",
    ] {
        command.env_remove(var);
    }

    policy.apply(&mut command);

    #[cfg(unix)]
    {
        // Own process group, so `kill_process_tree` can signal the transport
        // children too.
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }

    let mut child = command
        .spawn()
        .map_err(|e| AbError::Git(format!("failed to run git {what}: {e}")))?;
    let pid = child.id();

    if let Some(text) = stdin_text {
        use std::io::Write;
        let mut pipe = child
            .stdin
            .take()
            .ok_or_else(|| AbError::Git(format!("git {what}: stdin pipe unavailable")))?;
        // A child that dies before reading everything makes this fail with a
        // broken pipe; that is not itself the error worth reporting, since
        // the exit status and stderr below say what actually went wrong.
        let _ = pipe.write_all(text.as_bytes());
        drop(pipe);
    }

    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(child.wait_with_output());
    });

    match rx.recv_timeout(timeout) {
        Ok(Ok(out)) => Ok(GitOutput {
            success: out.status.success(),
            stdout: String::from_utf8_lossy(&out.stdout).trim_end().to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).trim_end().to_string(),
        }),
        Ok(Err(e)) => Err(AbError::Git(format!("failed to run git {what}: {e}"))),
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            kill_process_tree(pid);
            Err(AbError::Git(format!(
                "git {what} did not finish within {}s and was killed. If this was a fetch or \
                 push, the remote is unreachable or is waiting on a credential prompt that \
                 cannot be answered here -- check the remote and your credential helper, then \
                 retry. Set {TIMEOUT_VAR} to allow longer.",
                timeout.as_secs()
            )))
        }
        // The waiting thread cannot drop the sender without sending, so this
        // is unreachable in practice; report it rather than panicking.
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => Err(AbError::Git(format!(
            "git {what}: the process wait ended unexpectedly"
        ))),
    }
}

/// Dispatch for a `git` subprocess that takes no stdin, with
/// [`mock::MockGit`] able to intercept it.
///
/// This used to be the seam through which *every* git operation in the crate
/// passed. It is not any more, and a test that assumes otherwise will mock a
/// call nobody makes: the whole local surface moved in-process to
/// `gitobjects.rs`, and `version` and `check_ref_format` spawn directly
/// without consulting the mock. What still arrives here is remote transport
/// (`fetch`, `push`, `ls-remote`) and `merge-tree`.
pub fn run(dir: &Path, args: &[&str]) -> AbResult<GitOutput> {
    if let Some(out) = mock::intercept(dir, args, None) {
        return out;
    }
    let mut command = Command::new("git");
    command.arg("-C").arg(dir).args(args);
    run_with_deadline(command, &format!("{args:?}"), ConfigPolicy::Inherit)
}

/// [`run`], but insulated from the operator's git configuration.
///
/// Only for commands whose output must depend on nothing but their inputs.
/// Using this for transport would break pushing on any host that supplies
/// credentials through configuration, which is most CI.
fn run_hermetic(dir: &Path, args: &[&str]) -> AbResult<GitOutput> {
    if let Some(out) = mock::intercept(dir, args, None) {
        return out;
    }
    let mut command = Command::new("git");
    command.arg("-C").arg(dir).args(args);
    run_with_deadline(command, &format!("{args:?}"), ConfigPolicy::Hermetic)
}

/// Run a git command and turn a nonzero exit into an error.
/// Only test code calls this now: every production caller either went
/// in-process or needs `run`'s untranslated output. Kept because the tests
/// that build real repositories still find it the clearest way to ask git a
/// question directly.
#[cfg(test)]
pub fn run_ok(dir: &Path, args: &[&str]) -> AbResult<String> {
    let out = run(dir, args)?;
    if !out.success {
        return Err(AbError::Git(format!("git {args:?} failed: {}", out.stderr)));
    }
    Ok(out.stdout)
}

pub fn version() -> AbResult<String> {
    let mut command = Command::new("git");
    command.arg("--version");
    let out = run_with_deadline(command, "--version", ConfigPolicy::Inherit)?;
    // A nonzero exit here is not a version. A malformed `~/.gitconfig` makes
    // `git --version` die with an empty stdout, and returning `Ok("")` sent
    // that straight into the pinned-engine comparison, which then reported
    // "installed git  is not the merge engine version this bus selects" --
    // a confident, wrong diagnosis for a broken config file.
    if !out.success {
        return Err(AbError::Git(format!(
            "git --version failed: {}",
            if out.stderr.trim().is_empty() {
                "(no output)"
            } else {
                out.stderr.trim()
            }
        )));
    }
    let s = out.stdout.trim().to_string();
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
    crate::gitobjects::Libgit2Reader::open(start)?.workdir()
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
    // libgit2 always reports this absolute, so the relative-path join the
    // `rev-parse --git-common-dir` version needed is gone.
    Ok(crate::gitobjects::Libgit2Reader::open(start)?.common_dir())
}

/// Resolve a revision expression against an already-open reader, failing
/// rather than reporting absence. The `gitrepo` wrappers below all accept
/// arbitrary revision strings (`HEAD`, a branch, a raw id) because their
/// `git` predecessors did, so each one resolves before calling the
/// object-id-typed methods on the reader.
fn resolve_required(
    g: &crate::gitobjects::Libgit2Reader,
    rev: &str,
) -> AbResult<crate::scalars::ObjectId> {
    crate::gitobjects::HistoryReader::resolve_rev(g, rev)?
        .ok_or_else(|| AbError::Git(format!("{rev} does not name an object in this repository")))
}

pub fn rev_parse(dir: &Path, rev: &str) -> AbResult<String> {
    rev_parse_opt(dir, rev)?
        .ok_or_else(|| AbError::Git(format!("{rev} does not name an object in this repository")))
}

pub fn rev_parse_opt(dir: &Path, rev: &str) -> AbResult<Option<String>> {
    // The subprocess version had to spell this as `<rev>^{object}`, because
    // `rev-parse --verify` alone accepts a full-length hex string
    // syntactically and echoes it back even when no such object exists.
    // `revparse_single` always dereferences to a real object, so the
    // workaround is unnecessary here -- but it is still *accepted*, since
    // callers may pass an explicit peel suffix of their own.
    crate::gitobjects::HistoryReader::resolve_rev(
        &crate::gitobjects::Libgit2Reader::open(dir)?,
        rev,
    )
    .map(|o| o.map(|id| id.into_string()))
}

#[cfg(test)]
pub fn check_ref_format(refname: &str) -> bool {
    // Test-only, and memoized because the differential corpus asks about the
    // same handful of names repeatedly.
    //
    // This was once on the hot read path: `Branch::parse` called it, `Branch`
    // deserializes through `parse`, and every review event names two
    // branches, so reducing the fleet's bus spawned hundreds of these -- 2.5
    // seconds of a 6-second `status`. `Branch::parse` now decides for itself
    // and this survives only as the oracle
    // `branch_parse_agrees_with_real_git_check_ref_format` measures it
    // against. Note it deliberately does not go through `run`, so it gets
    // neither the deadline nor the environment strip; nothing in a release
    // build calls it.
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

/// The trailers in `rev`'s commit message.
///
/// The message is read in-process; the *parse* deliberately stays on `git
/// interpret-trailers`, which is the one local git operation this crate does
/// not reimplement. That is a considered exception, not an oversight:
///
///  - It is a security boundary. `merge_candidate.rs` decides who authored a
///    candidate's commits from `Agent-Bus-Agent` trailers, and `merge_ready.
///    rs`/`audit_main.rs` decide who reviewed it from `Agent-Bus-Reviewer`.
///    A parser that saw a trailer git would not see would let a crafted
///    message claim an authorship or a review it never had.
///  - Git's real rule is not the one its manual documents. The 25%
///    non-trailer tolerance described there is not what the pinned binary
///    does: one prose line voids a block of eight trailers. Enumerating every
///    three-line block over {trailer, prose, cherry-pick, continuation}
///    against the real binary produces a rule that fits all sixty-four cases
///    only if you also encode that the presence of a `(cherry picked from
///    commit ...)` line silently relaxes the strictness -- an implementation
///    accident of `trailer.c`, not a principle, and not something to freeze
///    into an authorization check.
///  - There is nothing to gain. This is not on any hot path: `status`,
///    `tail`, `outbox`, `submit` and `coordinate` never call it. Only
///    `audit-main` and the merge path do, a handful of commits at a time.
///
/// What *was* worth taking off the subprocess is the message read, which is
/// not security-critical and used to be a second `git show` per commit. So
/// this costs one process per commit now instead of two.
pub fn commit_message_trailers(dir: &Path, rev: &str) -> AbResult<Vec<(String, String)>> {
    let g = crate::gitobjects::Libgit2Reader::open(dir)?;
    let body = crate::gitobjects::HistoryReader::commit_message(&g, &resolve_required(&g, rev)?)?;
    // `trailer.separators` is repository-local configuration that
    // `ConfigPolicy::Hermetic` does not reach, and it decides what counts as
    // a trailer at all: measured, `separators=%` makes every trailer in a
    // well-formed message vanish from `--parse`, which would report a
    // properly attributed commit as unattributed and refuse an honest merge.
    // Pinned to git's default, so behavior is unchanged where nobody set it.
    let out = run_stdin(
        dir,
        &[
            "-c",
            "trailer.separators=:",
            "interpret-trailers",
            "--parse",
        ],
        &body,
    )?;
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

/// Runs a git subcommand with `stdin`, **hermetically** -- see
/// [`ConfigPolicy::Hermetic`]. The name says `stdin`, so the policy is said
/// here instead: a caller that needs the operator's configuration (anything
/// touching a remote) must not reach for this one.
pub(crate) fn run_stdin(dir: &Path, args: &[&str], stdin: &str) -> AbResult<GitOutput> {
    if let Some(out) = mock::intercept(dir, args, Some(stdin)) {
        return out;
    }
    let mut command = Command::new("git");
    command.arg("-C").arg(dir).args(args);
    // Hermetic: the sole production caller is `interpret-trailers --parse`,
    // which decides which commits carry an `Agent-Bus-Agent` trailer and so
    // gates merge authorization. An ambient `trailer.separators` was measured
    // to make every trailer in a well-formed message vanish from `--parse`,
    // which would report a properly-attributed commit as unattributed.
    run_with_deadline_stdin(command, &format!("{args:?}"), stdin, ConfigPolicy::Hermetic)
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
        // Measured: same two commits, a directory renamed on one side and a
        // file added into the old directory on the other, produced three
        // different answers -- unset conflicts, `false` and `true` each
        // yield a *different* clean tree. It is per-clone `.git/config`, so
        // unlike a committed `.gitattributes` it is not repository content
        // every host shares. Pinned to git's own default so behavior is
        // unchanged where nobody set it.
        "-c",
        "merge.directoryRenames=conflict",
        // Measured, not assumed. `core.attributesFile` *defaults* to
        // `$XDG_CONFIG_HOME/git/attributes`, which git reads when the key is
        // unset -- so it is reached through neither `GIT_CONFIG_GLOBAL` nor
        // `GIT_CONFIG_COUNT` and survives every neutralization in
        // [`ConfigPolicy::Hermetic`]. With a `* merge=<driver>` line in that
        // file, `merge-tree` produced a different tree for the same two
        // commits; pinning the key produced the clean one. Without this,
        // section 7's "Windows and Linux must produce the same tree" is
        // contingent on the operator's home directory.
        "-c",
        "core.attributesFile=/dev/null",
    ]
}

/// Refuse to construct a candidate in a repository carrying an
/// `info/attributes` file.
///
/// `--attr-source` overrides the working tree and the index, and
/// `core.attributesFile` is pinned, but `$GIT_COMMON_DIR/info/attributes` is
/// consulted regardless of all three -- measured, and there is no git switch
/// that suppresses it. It is also per-clone rather than repository content,
/// so a candidate built under it is one no other host can reproduce, which is
/// exactly what section 7 forbids.
///
/// Failing closed is the only honest option: the alternative is to build a
/// tree that looks fine locally and cannot be reconstructed anywhere else,
/// and the coordinator would then reject the reviewer's honest authorization
/// with a mismatch it cannot explain.
fn refuse_ambient_attributes(dir: &Path) -> AbResult<()> {
    // Measured with `GIT_TRACE=1`: on a partial clone, `merge-tree` reading a
    // blob it does not have runs a fetch underneath -- object count went up
    // mid-merge. That fetch inherits this command's environment, and
    // candidate construction is deliberately hermetic, so it runs with no
    // credential helper, no `url.<base>.insteadOf`, no proxy, and with stdin
    // closed so no prompt can be answered. Against a private remote it fails
    // and surfaces as "could not cleanly merge", blaming the merge for a
    // credentials problem.
    //
    // Refused rather than papered over. Making the merge inherit
    // configuration would reopen the reproducibility hole this policy exists
    // to close, and pre-hydrating the objects is real work with its own
    // failure modes; neither belongs behind a silent fallback.
    if crate::gitobjects::Libgit2Reader::open(dir)?.is_partial_clone() {
        return Err(invalid(
            "this repository is a partial clone, and candidate construction refuses to run in              one: the merge reads blob content, which makes git fetch missing objects              mid-merge, and that fetch cannot authenticate because construction is              deliberately insulated from the operator's git configuration. Use a full clone              for the host that prepares merges, or hydrate it first with `git fetch              --refetch --filter=`."
                .to_string(),
        ));
    }
    let path = common_dir(dir)?.join("info").join("attributes");
    if path.exists() {
        return Err(invalid(format!(
            "{} exists; candidate construction refuses to run because git consults it no matter what this helper pins, so the resulting tree would depend on this clone rather than only on the commits being merged (AGENT_REVIEW.md section 7). Move the file aside, or commit those attributes so every host shares them.",
            path.display()
        )));
    }
    Ok(())
}

pub fn merge_tree_write_tree(dir: &Path, ours: &str, theirs: &str) -> AbResult<String> {
    // AGENT_REVIEW.md section 7 asks for "repository attributes from
    // `previous_main`", and without this the merge read them from whatever
    // happens to be checked out. Measured: an *untracked* `.gitattributes` in
    // the working tree changed the resulting tree for the same two commits.
    // `ConfigPolicy::Hermetic` cannot reach this -- the file is repository
    // content, not configuration -- and in the deployment AGENT_BUS.md
    // specifies, many agents share one clone, so one stray file would move
    // every candidate built on that host.
    refuse_ambient_attributes(dir)?;
    let attr_source = format!("--attr-source={ours}");
    let mut args = pinned_merge_config_args();
    args.push(&attr_source);
    args.extend(["merge-tree", "--write-tree", "--name-only", ours, theirs]);
    let out = run_hermetic(dir, &args)?;
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
    let g = crate::gitobjects::Libgit2Reader::open(dir)?;
    crate::gitobjects::HistoryReader::committer_timestamp(&g, &resolve_required(&g, rev)?)
}

/// The exact number of merge bases between `a` and `b` (AGENT_REVIEW.md
/// section 7: "It requires one merge base").
pub fn merge_base_count(dir: &Path, a: &str, b: &str) -> AbResult<usize> {
    let g = crate::gitobjects::Libgit2Reader::open(dir)?;
    crate::gitobjects::HistoryReader::merge_base_count(
        &g,
        &resolve_required(&g, a)?,
        &resolve_required(&g, b)?,
    )
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
    let g = crate::gitobjects::Libgit2Reader::open(dir)?;

    let mut resolved = Vec::with_capacity(parents.len());
    for p in parents {
        resolved.push(resolve_required(&g, p)?);
    }
    let mut latest = i64::MIN;
    for p in parents {
        latest = latest.max(committer_timestamp(dir, p)?);
    }
    let ts = latest
        .checked_add(1)
        .ok_or_else(|| invalid("candidate timestamp overflow"))?;

    let tree = resolve_required(&g, tree)?;
    let parent_refs: Vec<&crate::scalars::ObjectId> = resolved.iter().collect();
    let id = g.commit_with_identity(
        &tree,
        &parent_refs,
        message,
        DETERMINISTIC_COMMIT_NAME,
        DETERMINISTIC_COMMIT_EMAIL,
        ts,
    )?;
    Ok(id.into_string())
}

/// The fixed identity every reproducible candidate commit carries. Any
/// change here changes every future candidate's object id, so it is named
/// once rather than spelled out at the point of use.
pub const DETERMINISTIC_COMMIT_NAME: &str = "Grass Agent Bus";
pub const DETERMINISTIC_COMMIT_EMAIL: &str = "agent-bus@invalid";

pub fn tag_lightweight(dir: &Path, name: &str, target: &str) -> AbResult<()> {
    // `git tag` validates the name it is given; `Branch::parse` is this
    // crate's equivalent, cross-checked against real `git check-ref-format`
    // by `scalars::ref_format_tests`.
    //
    // `git tag` refuses two names `check-ref-format` accepts, so
    // `Branch::parse` cannot know about them: a tag literally named `HEAD`,
    // and one starting with `-` (which would be read as an option). Neither
    // is reachable from `candidate_tag_name`, but a tag name is caller input
    // and this function should not be the place that stops matching `git
    // tag`.
    if name == "HEAD" || name.starts_with('-') {
        return Err(invalid(format!(
            "{name} is not a usable tag name: git refuses a tag named HEAD or one starting with \
             a hyphen"
        )));
    }
    let refname = crate::scalars::Branch::parse(format!("refs/tags/{name}"))
        .map_err(|e| invalid(format!("{name} is not a usable tag name: {e}")))?;
    let g = crate::gitobjects::Libgit2Reader::open(dir)?;
    let target = resolve_required(&g, target)?;
    // Re-tagging the *same* target is a no-op, not a violation.
    //
    // AGENT_REVIEW.md section 7 makes the candidate tag immutable, and
    // `compare_and_set(.., None, ..)` enforces that -- but it also made
    // `prepare-merge` non-idempotent, and both the tag name and the target
    // are deterministic functions of `(previous_main, reviewed_commit,
    // reviewer)`. So a reviewer whose tag was created locally and whose push
    // then failed (network, credentials) could never retry: the second run
    // died at this call with "already exists ... another writer created it
    // first; re-read the current tip and retry", which is false -- it was
    // themselves -- and unactionable, since retrying cannot help. Meanwhile
    // the authorization stays unverifiable forever, because the tag never
    // reached the remote. Recovery required a manual `git tag -d`.
    //
    // Immutability is unaffected: a *different* target under the same name is
    // still refused below, which is the case the rule is actually about.
    if let Some(existing) = crate::gitobjects::RefStore::resolve(&g, refname.as_str())? {
        if existing == target {
            return Ok(());
        }
    }
    crate::gitobjects::RefStore::compare_and_set(&g, refname.as_str(), None, &target)
}

/// Whether `remote` actually has a tag named `name` pointing at `target` --
/// a real `ls-remote` network round trip, not a check against anything
/// already fetched into the local repository.
///
/// One limit worth stating, because a caller could otherwise over-trust this:
/// the remote spec is resolved by `git`, under the operator's configuration,
/// which transport deliberately inherits. A host with a `url.<base>.insteadOf`
/// rule can therefore have `remote` resolve somewhere other than where the
/// name suggests. That is inherent to letting transport keep its
/// configuration -- the same rule is what makes credentialed pushes work at
/// all -- so this answers "the tag is fetchable from the remote this host
/// resolves that name to", not "from the remote everyone else means". A local-only existence check
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

/// Every path that differs between `from` and `to`, as `(status, path)`.
///
/// Rename detection is off, so a rename is reported as a delete of the old
/// path plus an add of the new one rather than as a single `R<score>` entry
/// naming only the destination. Both consumers -- `merge_ready::
/// check_merge_ready` and `audit_main`'s post-hoc correlation -- check every
/// path returned against a reviewed scope, and reporting both sides is what
/// stops a rename *into* the reviewed scope from hiding the out-of-scope path
/// it came from. See `gitobjects::HistoryReader::diff_name_status`.
pub fn diff_name_status(dir: &Path, from: &str, to: &str) -> AbResult<Vec<(String, String)>> {
    let g = crate::gitobjects::Libgit2Reader::open(dir)?;
    crate::gitobjects::HistoryReader::diff_name_status(
        &g,
        &resolve_required(&g, from)?,
        &resolve_required(&g, to)?,
    )
}

pub fn rev_list_first_parent(dir: &Path, from_exclusive: &str, to: &str) -> AbResult<Vec<String>> {
    let g = crate::gitobjects::Libgit2Reader::open(dir)?;
    let out = crate::gitobjects::HistoryReader::first_parent_range(
        &g,
        &resolve_required(&g, from_exclusive)?,
        &resolve_required(&g, to)?,
    )?;
    Ok(out.into_iter().map(|id| id.into_string()).collect())
}

pub fn parents_of(dir: &Path, rev: &str) -> AbResult<Vec<String>> {
    let g = crate::gitobjects::Libgit2Reader::open(dir)?;
    let out = crate::gitobjects::HistoryReader::parents_of(&g, &resolve_required(&g, rev)?)?;
    Ok(out.into_iter().map(|id| id.into_string()).collect())
}

pub fn commits_between_first_parent_exclusive(
    dir: &Path,
    ancestor: &str,
    descendant_second_parent: &str,
) -> AbResult<Vec<String>> {
    // Commits introduced by the second parent relative to the first parent:
    // ancestor..second_parent
    let g = crate::gitobjects::Libgit2Reader::open(dir)?;
    let out = crate::gitobjects::HistoryReader::range(
        &g,
        &resolve_required(&g, ancestor)?,
        &resolve_required(&g, descendant_second_parent)?,
    )?;
    Ok(out.into_iter().map(|id| id.into_string()).collect())
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

    // ----------------------------------------------- the subprocess deadline

    /// A command that blocks far longer than any deadline in these tests.
    /// Neither program is `git`, which is the point: the deadline is a
    /// property of how this module runs a child, and a program that reliably
    /// hangs makes the expiry path deterministic instead of needing an
    /// unreachable remote.
    fn blocking_command() -> Command {
        if cfg!(windows) {
            let mut c = Command::new("cmd");
            // `ping -n N 127.0.0.1` is the portable Windows sleep.
            c.args(["/c", "ping -n 30 127.0.0.1 >nul"]);
            c
        } else {
            let mut c = Command::new("sh");
            c.args(["-c", "sleep 30"]);
            c
        }
    }

    /// The killer must actually terminate the process, not merely be called.
    ///
    /// This is half of what `g-reviewer:29` needs; the other half (that the
    /// deadline *invokes* it) is the test below. Splitting them is deliberate:
    /// an earlier single test asserted only the error text and a bounded wall
    /// clock, both of which stay true when the kill does nothing at all.
    #[test]
    fn kill_process_tree_actually_terminates_the_child() {
        let mut child = blocking_command()
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();

        // It is running, and stays running on its own.
        std::thread::sleep(std::time::Duration::from_millis(200));
        assert!(
            child.try_wait().unwrap().is_none(),
            "the fixture exited on its own; it cannot demonstrate a kill"
        );

        kill_process_tree(child.id());

        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
        loop {
            if child.try_wait().unwrap().is_some() {
                break;
            }
            assert!(
                std::time::Instant::now() < deadline,
                "the child was still running 10s after kill_process_tree"
            );
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
    }

    /// `g-reviewer:29`: an unbounded subprocess can hang every agent-bus
    /// command. On expiry the deadline must report *and* kill -- reporting
    /// alone leaves the process running and the pipe held.
    #[test]
    fn a_command_that_outruns_its_deadline_is_reported_and_its_tree_killed() {
        let before = KILLS_REQUESTED.with(|c| c.get());

        let mut command = blocking_command();
        command
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());

        let started = std::time::Instant::now();
        let err = spawn_and_wait(
            command,
            "test-hang",
            None,
            std::time::Duration::from_millis(300),
            ConfigPolicy::Inherit,
        )
        .unwrap_err();
        let elapsed = started.elapsed();

        assert!(
            err.to_string().contains("did not finish within"),
            "expected a timeout error, got: {err}"
        );
        // The deadline must bound the wait, not merely be reported after the
        // child finished on its own.
        assert!(
            elapsed < std::time::Duration::from_secs(15),
            "waited {elapsed:?}, so the deadline did not bound the wait"
        );
        // ...and it must have asked for the kill. Without this the test stays
        // green when the kill is removed entirely.
        assert!(
            KILLS_REQUESTED.with(|c| c.get()) > before,
            "the deadline expired without requesting a process-tree kill"
        );
    }

    /// This CLI's callers are other agents with no human in the loop, so a
    /// failure has to say what to do next, not only that it failed.
    #[test]
    fn the_timeout_error_names_the_operator_action() {
        let mut command = blocking_command();
        command
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());
        let err = spawn_and_wait(
            command,
            "test-hang",
            None,
            std::time::Duration::from_millis(300),
            ConfigPolicy::Inherit,
        )
        .unwrap_err()
        .to_string();
        assert!(err.contains("credential"), "{err}");
        assert!(err.contains("retry"), "{err}");
        assert!(err.contains("AGENT_BUS_GIT_TIMEOUT_SECS"), "{err}");
    }

    /// A command that finishes well inside the deadline must not be delayed
    /// by it. This is why the wait is a blocking wait on a thread rather than
    /// a poll loop with a sleep: a poll interval would be paid by every call.
    #[test]
    fn a_fast_command_is_not_delayed_by_the_deadline() {
        let repo = init_repo();
        let started = std::time::Instant::now();
        let out = run(repo.path(), &["rev-parse", "HEAD"]).unwrap();
        assert!(out.success, "{out:?}");
        assert!(
            started.elapsed() < std::time::Duration::from_secs(5),
            "a trivial git call took {:?}",
            started.elapsed()
        );
    }

    /// The override's parse rule, exercised against the shipped function
    /// rather than a copy of it re-implemented in the test. The previous
    /// version defined a local closure with the same logic and asserted
    /// against that, which proved nothing about the code that ships.
    /// The wiring, not only the rule: something must actually read
    /// [`TIMEOUT_VAR`], and it must be that name.
    ///
    /// Mutating `git_timeout` to read a variable that is never set left the
    /// whole suite green, because every other test either calls
    /// `parse_timeout_secs` directly or passes `spawn_and_wait` an explicit
    /// duration. The escape hatch the error message advertises was therefore
    /// unreachable and nothing noticed.
    #[test]
    fn the_deadline_reads_the_documented_environment_variable() {
        let seen = std::cell::RefCell::new(Vec::new());
        let got = git_timeout_from(|k| {
            seen.borrow_mut().push(k.to_string());
            (k == "AGENT_BUS_GIT_TIMEOUT_SECS").then(|| "7".to_string())
        });
        assert_eq!(got, std::time::Duration::from_secs(7));
        assert_eq!(
            seen.into_inner(),
            vec!["AGENT_BUS_GIT_TIMEOUT_SECS".to_string()],
            "the lookup must ask for exactly the documented variable"
        );

        // Unset falls back to the default.
        assert_eq!(
            git_timeout_from(|_| None),
            std::time::Duration::from_secs(120)
        );
        // And the constant the message advertises is the one that is read.
        assert_eq!(TIMEOUT_VAR, "AGENT_BUS_GIT_TIMEOUT_SECS");
    }

    #[test]
    fn the_deadline_default_is_used_when_the_override_is_unusable() {
        assert_eq!(parse_timeout_secs(None), 120);
        assert_eq!(parse_timeout_secs(Some("")), 120);
        assert_eq!(
            parse_timeout_secs(Some("0")),
            120,
            "zero must not disable the deadline"
        );
        assert_eq!(parse_timeout_secs(Some("not-a-number")), 120);
        assert_eq!(parse_timeout_secs(Some("-5")), 120);
        assert_eq!(parse_timeout_secs(Some("5")), 5);
        assert_eq!(parse_timeout_secs(Some("3600")), 3600);
    }
    use super::*;
    use crate::gitrepo::mock::MockGit;
    use std::path::PathBuf;

    // ------------------------------------------- ambient configuration

    /// The mechanism, asserted exactly: `Hermetic` must both *remove* the
    /// `-c`-precedence injection variables and *force* the file-location
    /// ones. Removing alone is insufficient -- git reads the operator's
    /// `~/.gitconfig` precisely when `GIT_CONFIG_GLOBAL` is absent -- and
    /// forcing alone is insufficient, because `GIT_CONFIG_COUNT` injection
    /// is honored independently of it. Both halves were measured against
    /// real git before being written down here.
    #[test]
    fn the_hermetic_policy_both_removes_and_forces_the_configuration_channels() {
        let mut command = Command::new("git");
        ConfigPolicy::Hermetic.apply(&mut command);
        let seen: std::collections::BTreeMap<String, Option<String>> = command
            .get_envs()
            .map(|(k, v)| {
                (
                    k.to_string_lossy().into_owned(),
                    v.map(|v| v.to_string_lossy().into_owned()),
                )
            })
            .collect();

        // Removed (`None` == `env_remove`).
        assert_eq!(seen.get("GIT_CONFIG_PARAMETERS"), Some(&None));
        assert_eq!(seen.get("GIT_CONFIG_COUNT"), Some(&None));
        // Forced.
        assert_eq!(
            seen.get("GIT_CONFIG_GLOBAL"),
            Some(&Some("/dev/null".to_string()))
        );
        assert_eq!(
            seen.get("GIT_CONFIG_SYSTEM"),
            Some(&Some("/dev/null".to_string()))
        );
        assert_eq!(
            seen.get("GIT_CONFIG_NOSYSTEM"),
            Some(&Some("1".to_string()))
        );
        assert_eq!(seen.get("GIT_ATTR_NOSYSTEM"), Some(&Some("1".to_string())));
    }

    /// The other half of the contract, and the one whose absence broke
    /// pushing: transport must see the operator's configuration untouched.
    #[test]
    fn the_inherit_policy_changes_no_configuration_at_all() {
        let mut command = Command::new("git");
        ConfigPolicy::Inherit.apply(&mut command);
        assert_eq!(
            command.get_envs().count(),
            0,
            "Inherit must not add, remove or override any environment variable"
        );
    }

    /// `core.attributesFile` needs its own pin because its *default* --
    /// `$XDG_CONFIG_HOME/git/attributes` -- is read when the key is unset,
    /// and is therefore reachable through no `GIT_CONFIG_*` variable at all.
    ///
    /// This drives real `git merge-tree` three ways over the same two
    /// commits: with a hostile attributes file plus the driver it names,
    /// unpinned (the tree changes); pinned (the tree is the clean one); and
    /// with no hostile configuration at all (establishing what "clean"
    /// means). Without the middle case a reader cannot tell whether the pin
    /// does anything, and without the first the test would pass even if the
    /// channel did not exist.
    #[test]
    fn the_attributes_file_pin_closes_a_channel_no_environment_variable_reaches() {
        let repo = init_repo();
        let path = repo.path();
        std::fs::write(path.join("f.txt"), "line1\nline2\n").unwrap();
        git(path, &["add", "f.txt"]);
        git(path, &["commit", "-q", "-m", "base"]);
        git(path, &["checkout", "-q", "-b", "left"]);
        commit_file(path, "f.txt", "LEFT\nline2\n", "left");
        git(path, &["checkout", "-q", "main"]);
        git(path, &["checkout", "-q", "-b", "right"]);
        commit_file(path, "f.txt", "RIGHT\nline2\n", "right");

        // A hostile "home": an attributes file selecting a merge driver that
        // resolves the conflict instead of leaving markers.
        let home = tempfile::tempdir().unwrap();
        std::fs::create_dir_all(home.path().join("git")).unwrap();
        std::fs::write(home.path().join("git/attributes"), "* merge=takeours\n").unwrap();

        let merge = |pin_attrs: bool, hostile: bool| -> String {
            let mut c = Command::new("git");
            c.arg("-C").arg(path);
            for a in [
                "-c",
                "merge.conflictStyle=merge",
                "-c",
                "core.autocrlf=false",
            ] {
                c.arg(a);
            }
            if pin_attrs {
                c.args(["-c", "core.attributesFile=/dev/null"]);
            }
            if hostile {
                c.env("XDG_CONFIG_HOME", home.path());
                // The driver definition itself may arrive by any route; what
                // matters is that the *attributes* half is unreachable by
                // environment.
                c.env("GIT_CONFIG_COUNT", "1");
                c.env("GIT_CONFIG_KEY_0", "merge.takeours.driver");
                c.env("GIT_CONFIG_VALUE_0", "cp %B %A");
            } else {
                c.env("GIT_CONFIG_GLOBAL", "/dev/null");
                c.env("GIT_CONFIG_NOSYSTEM", "1");
            }
            c.args(["merge-tree", "--write-tree", "--name-only", "left", "right"]);
            let out = c.output().unwrap();
            String::from_utf8_lossy(&out.stdout)
                .lines()
                .next()
                .unwrap_or_default()
                .to_string()
        };

        let clean = merge(false, false);
        assert!(
            !clean.is_empty(),
            "fixture: the clean merge must produce a tree"
        );
        assert_ne!(
            merge(false, true),
            clean,
            "fixture is not proving anything unless the ambient attributes file \
             actually changes the merge result"
        );
        assert_eq!(
            merge(true, true),
            clean,
            "pinning core.attributesFile must make the merge independent of the \
             operator's home directory (AGENT_REVIEW.md section 7)"
        );
        assert!(
            pinned_merge_config_args()
                .windows(2)
                .any(|w| { w[0] == "-c" && w[1] == "core.attributesFile=/dev/null" }),
            "the pin this test justifies must actually be in the pinned set"
        );
    }

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
    /// `common_dir` must report an absolute path to the repository's shared
    /// git directory, and must agree with `git rev-parse --git-common-dir`,
    /// which is what it replaced.
    ///
    /// The two tests this supersedes scripted a `MockGit` answer and checked
    /// the relative-path join that answer needed. libgit2 reports this
    /// absolute already, so there is no join left to test -- and a mock
    /// cannot intercept an in-process call in any case. Comparing against
    /// real git is a stronger claim than the one that was lost.
    #[test]
    fn common_dir_matches_git_and_is_absolute() {
        let repo = init_repo();
        let got = common_dir(repo.path()).unwrap();
        assert!(got.is_absolute(), "expected an absolute path, got {got:?}");

        let expected = run_ok(
            repo.path(),
            &["rev-parse", "--path-format=absolute", "--git-common-dir"],
        )
        .unwrap();
        assert_eq!(
            std::fs::canonicalize(&got).unwrap(),
            std::fs::canonicalize(PathBuf::from(expected.trim())).unwrap()
        );
    }

    /// A failing `git interpret-trailers --parse` invocation must surface as
    /// an error rather than an empty/garbage trailer list.
    #[test]
    fn commit_message_trailers_reports_interpret_trailers_failure() {
        // A real repository, not `PathBuf::from(".")`. The message is now
        // read in-process, so the old `show -s --format=%B` mock rule is
        // never consulted and the call needs a repository it can actually
        // open -- relying on the process working directory happening to be
        // one is exactly the accidental coupling this avoids. Only the
        // `interpret-trailers` rule still intercepts anything.
        let repo = init_repo();
        let _guard = MockGit::new()
            .on(
                &[
                    "-c",
                    "trailer.separators=:",
                    "interpret-trailers",
                    "--parse",
                ],
                GitOutput::err("bad format"),
            )
            .install();
        let err = commit_message_trailers(repo.path(), "HEAD").unwrap_err();
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
        // The all-zero id names no object; the failure now comes from
        // resolving it rather than from `git commit-tree`'s exit status.
        assert!(
            format!("{err}").contains("does not name an object"),
            "{err}"
        );
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
            &[
                "-c",
                "trailer.separators=:",
                "interpret-trailers",
                "--parse",
            ],
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

    /// The *wiring*, not the mechanism.
    ///
    /// `the_hermetic_policy_both_removes_and_forces_the_configuration_channels`
    /// proves what `ConfigPolicy::Hermetic` does; it says nothing about
    /// whether candidate construction uses it. Mutation testing showed the
    /// difference mattered: switching this call back to the inheriting `run`
    /// left all 549 tests green, which would have silently reopened
    /// AGENT_REVIEW.md section 7's reproducibility requirement.
    ///
    /// Transport is asserted in the same test, because the two halves of the
    /// split only mean anything together -- an implementation that made
    /// everything hermetic would satisfy the first assertion alone.
    /// The success path: a real, cleanly-mergeable pair of branches must
    /// produce a real, resolvable tree object containing both sides'
    /// changes.
    #[test]
    fn candidate_construction_runs_hermetic_while_transport_still_inherits() {
        let repo = init_repo();
        git(repo.path(), &["checkout", "-q", "-b", "theirs"]);
        commit_file(
            repo.path(),
            "theirs.txt",
            "theirs
",
            "add theirs.txt",
        );
        let theirs_tip = rev_parse(repo.path(), "HEAD").unwrap();
        git(repo.path(), &["checkout", "-q", "main"]);
        commit_file(
            repo.path(),
            "ours.txt",
            "ours
",
            "add ours.txt",
        );
        let ours_tip = rev_parse(repo.path(), "HEAD").unwrap();

        merge_tree_write_tree(repo.path(), &ours_tip, &theirs_tip).unwrap();
        assert_eq!(
            last_config_policy(),
            Some(ConfigPolicy::Hermetic),
            "merge-tree must not see the operator's configuration"
        );

        // A remote operation, which must keep it.
        let origin = init_bare_origin();
        let remote = origin.path().display().to_string();
        let _ = remote_refs_existing(repo.path(), &remote, &["refs/heads/main".to_string()]);
        assert_eq!(
            last_config_policy(),
            Some(ConfigPolicy::Inherit),
            "transport must still see credential helpers and url rewrites"
        );
    }

    /// The trailer parse decides which commits carry an `Agent-Bus-Agent`
    /// trailer, so it gates merge authorization; an ambient
    /// `trailer.separators` was measured to make every trailer in a
    /// well-formed message vanish from `--parse`.
    #[test]
    fn the_trailer_parse_runs_hermetic() {
        let repo = init_repo();
        commit_file(
            repo.path(),
            "x.txt",
            "x
",
            "subject

Agent-Bus-Agent: alice",
        );
        let head = rev_parse(repo.path(), "HEAD").unwrap();
        let trailers = commit_message_trailers(repo.path(), &head).unwrap();
        assert!(
            trailers
                .iter()
                .any(|(k, v)| k == "Agent-Bus-Agent" && v == "alice"),
            "fixture must produce a real trailer: {trailers:?}"
        );
        assert_eq!(last_config_policy(), Some(ConfigPolicy::Hermetic));
    }

    /// Builds two branches that merge cleanly, and returns `(repo, ours,
    /// theirs)`. They touch opposite ends of one file, so a merge driver or
    /// an `-merge` attribute changes the result while an honest merge does
    /// not -- which is what makes the attribute tests below falsifiable.
    fn cleanly_mergeable_repo() -> (tempfile::TempDir, String, String) {
        let repo = init_repo();
        let p = repo.path();
        std::fs::write(
            p.join("f.txt"),
            "l1
l2
l3
l4
l5
",
        )
        .unwrap();
        git(p, &["add", "f.txt"]);
        git(p, &["commit", "-q", "-m", "base"]);
        git(p, &["checkout", "-q", "-b", "ours"]);
        commit_file(
            p,
            "f.txt",
            "OURS
l2
l3
l4
l5
",
            "ours",
        );
        let ours = rev_parse(p, "HEAD").unwrap();
        git(p, &["checkout", "-q", "main"]);
        git(p, &["checkout", "-q", "-b", "theirs"]);
        commit_file(
            p,
            "f.txt",
            "l1
l2
l3
l4
THEIRS
",
            "theirs",
        );
        let theirs = rev_parse(p, "HEAD").unwrap();
        git(p, &["checkout", "-q", "main"]);
        (repo, ours, theirs)
    }

    /// AGENT_REVIEW.md section 7: "repository attributes from
    /// `previous_main`". Before `--attr-source`, the merge read them from
    /// whatever was checked out -- so an *untracked* file, which is not
    /// repository content at all and which no other host has, moved the
    /// candidate.
    ///
    /// Non-vacuous by construction: the same poison is shown to change the
    /// answer when the attribute source is the working tree, so the test
    /// fails both if the poison stops working and if the pin stops working.
    #[test]
    fn candidate_attributes_come_from_previous_main_not_the_working_tree() {
        let (repo, ours, theirs) = cleanly_mergeable_repo();
        let clean = merge_tree_write_tree(repo.path(), &ours, &theirs).unwrap();

        std::fs::write(
            repo.path().join(".gitattributes"),
            "* -merge
",
        )
        .unwrap();

        // The poison is real: pointed at the working tree, git refuses the
        // same merge outright.
        let poisoned = std::process::Command::new("git")
            .arg("-C")
            .arg(repo.path())
            .args(pinned_merge_config_args())
            .args(["merge-tree", "--write-tree", "--name-only", &ours, &theirs])
            .output()
            .unwrap();
        assert!(
            !poisoned.status.success(),
            "fixture proves nothing unless the untracked file changes the merge"
        );

        // Taken from `previous_main`, it is invisible.
        let with_pin = merge_tree_write_tree(repo.path(), &ours, &theirs).unwrap();
        assert_eq!(
            with_pin, clean,
            "an untracked .gitattributes must not move the candidate"
        );
    }

    /// The one attribute channel no git switch closes: `--attr-source`
    /// overrides the worktree and index, `core.attributesFile` is pinned, and
    /// `$GIT_COMMON_DIR/info/attributes` is still consulted over all three.
    /// It is per-clone, so a candidate built under it is one no other host
    /// can reproduce -- refused rather than silently host-dependent.
    #[test]
    fn candidate_construction_refuses_a_clone_carrying_info_attributes() {
        let (repo, ours, theirs) = cleanly_mergeable_repo();
        merge_tree_write_tree(repo.path(), &ours, &theirs)
            .expect("fixture must merge cleanly before the file exists");

        let info = common_dir(repo.path()).unwrap().join("info");
        std::fs::create_dir_all(&info).unwrap();
        std::fs::write(
            info.join("attributes"),
            "* -merge
",
        )
        .unwrap();

        let err = merge_tree_write_tree(repo.path(), &ours, &theirs)
            .expect_err("info/attributes must be refused, not silently honored");
        assert!(
            err.to_string()
                .contains("candidate construction refuses to run"),
            "expected the ambient-attributes refusal, got: {err}"
        );
    }

    /// `trailer.separators` is repository-local configuration, which the
    /// hermetic policy does not reach, and it decides what counts as a
    /// trailer at all -- so an unpinned parse would report a properly
    /// attributed commit as unattributed and refuse an honest merge.
    #[test]
    fn the_trailer_parse_is_pinned_against_repository_local_configuration() {
        let repo = init_repo();
        commit_file(
            repo.path(),
            "x.txt",
            "x
",
            "subject

Agent-Bus-Agent: alice",
        );
        let head = rev_parse(repo.path(), "HEAD").unwrap();

        // The poison is real: unpinned, this suppresses every trailer.
        git(repo.path(), &["config", "trailer.separators", "%"]);
        let unpinned = std::process::Command::new("git")
            .arg("-C")
            .arg(repo.path())
            .args(["interpret-trailers", "--parse"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .and_then(|mut c| {
                use std::io::Write;
                c.stdin.take().unwrap().write_all(
                    b"subject

Agent-Bus-Agent: alice
",
                )?;
                c.wait_with_output()
            })
            .unwrap();
        assert!(
            String::from_utf8_lossy(&unpinned.stdout).trim().is_empty(),
            "fixture proves nothing unless the local config suppresses trailers"
        );

        let trailers = commit_message_trailers(repo.path(), &head).unwrap();
        assert!(
            trailers
                .iter()
                .any(|(k, v)| k == "Agent-Bus-Agent" && v == "alice"),
            "the pinned parse must still see the trailer: {trailers:?}"
        );
    }

    /// `merge.directoryRenames` is repository-local configuration, which the
    /// hermetic policy does not reach, and it genuinely moves the answer:
    /// with a directory renamed on one side and a file added into the old
    /// directory on the other, `false` produces a *different clean tree* from
    /// git's default. Per-clone configuration deciding candidate content is
    /// exactly what section 7's "Windows and Linux must produce the same
    /// tree" forbids, so it is pinned to the default.
    #[test]
    fn candidate_construction_is_pinned_against_local_directory_rename_configuration() {
        let repo = init_repo();
        let p = repo.path();
        std::fs::create_dir_all(p.join("old")).unwrap();
        for i in 0..5 {
            std::fs::write(
                p.join("old").join(format!("f{i}.txt")),
                format!(
                    "c{i}
"
                ),
            )
            .unwrap();
        }
        git(p, &["add", "-A"]);
        git(p, &["commit", "-q", "-m", "base"]);
        git(p, &["checkout", "-q", "-b", "ours"]);
        git(p, &["mv", "old", "new"]);
        git(p, &["commit", "-q", "-m", "rename the directory"]);
        git(p, &["checkout", "-q", "main"]);
        git(p, &["checkout", "-q", "-b", "theirs"]);
        std::fs::write(
            p.join("old").join("added.txt"),
            "added
",
        )
        .unwrap();
        git(p, &["add", "-A"]);
        git(p, &["commit", "-q", "-m", "add into the old directory"]);
        git(p, &["checkout", "-q", "main"]);
        let ours = rev_parse(p, "ours").unwrap();
        let theirs = rev_parse(p, "theirs").unwrap();

        // Pinned to git's default, this is a genuine conflict: content was
        // added into a directory the other side renamed, and only a human
        // can say where it belongs.
        let err = merge_tree_write_tree(p, &ours, &theirs)
            .expect_err("the default treats this as a conflict");
        assert!(
            err.to_string().contains("could not cleanly merge"),
            "unexpected error: {err}"
        );

        // The poison is real, and it is the dangerous direction: local
        // configuration turns that refusal into a silent clean merge that
        // relocates the file.
        git(p, &["config", "merge.directoryRenames", "false"]);
        let unpinned = std::process::Command::new("git")
            .arg("-C")
            .arg(p)
            .args([
                "-c",
                "core.autocrlf=false",
                "-c",
                "merge.conflictStyle=merge",
                "-c",
                "merge.renames=true",
                "-c",
                "diff.renameLimit=0",
            ])
            .args(["merge-tree", "--write-tree", "--name-only", &ours, &theirs])
            .output()
            .unwrap();
        assert!(
            unpinned.status.success(),
            "fixture proves nothing unless local configuration makes this merge cleanly"
        );

        // Pinned, the same local configuration is invisible and the merge is
        // still refused.
        let still = merge_tree_write_tree(p, &ours, &theirs)
            .expect_err("merge.directoryRenames must be pinned, not taken from this clone");
        assert!(
            still.to_string().contains("could not cleanly merge"),
            "unexpected error: {still}"
        );
    }

    /// A partial clone is refused, with the real thing: an actual
    /// `--filter=blob:none` clone, not a hand-written config key, so the test
    /// fails if git ever stops recording the promisor remote the way this
    /// detection expects.
    #[test]
    fn candidate_construction_refuses_a_partial_clone() {
        let (source, ours, theirs) = cleanly_mergeable_repo();
        merge_tree_write_tree(source.path(), &ours, &theirs)
            .expect("the full clone must merge cleanly");

        let dest = tempfile::tempdir().unwrap();
        let target = dest.path().join("partial");
        let status = std::process::Command::new("git")
            .args(["clone", "--quiet", "--filter=blob:none", "--no-checkout"])
            .arg(source.path())
            .arg(&target)
            .status()
            .unwrap();
        assert!(status.success(), "fixture clone failed");

        let g = crate::gitobjects::Libgit2Reader::open(&target).unwrap();
        assert!(
            g.is_partial_clone(),
            "fixture proves nothing unless git actually recorded a promisor remote"
        );

        let err = merge_tree_write_tree(&target, &ours, &theirs)
            .expect_err("a partial clone must be refused, not silently merged");
        assert!(
            err.to_string().contains("partial clone"),
            "expected the partial-clone refusal, got: {err}"
        );
    }

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
    fn merge_base_count_is_zero_for_unrelated_orphan_histories() {
        let repo = init_repo();
        let main_tip = rev_parse(repo.path(), "HEAD").unwrap();

        git(repo.path(), &["checkout", "-q", "--orphan", "unrelated"]);
        git(repo.path(), &["rm", "-rf", "-q", "."]);
        commit_file(repo.path(), "other.txt", "other\n", "unrelated root");
        let orphan_tip = rev_parse(repo.path(), "HEAD").unwrap();

        // Two histories with no common ancestor have zero merge bases. The
        // subprocess version reported this as an error, because `git
        // merge-base --all` signals it by exiting non-zero with no output --
        // which meant `merge_candidate` surfaced a raw git error instead of
        // its own "do not have exactly one merge base". Zero is the honest
        // answer and produces the domain error the caller means.
        assert_eq!(
            merge_base_count(repo.path(), &main_tip, &orphan_tip).unwrap(),
            0
        );
    }

    /// `prepare-merge` must be retryable after a failed push, and must still
    /// refuse to move an existing candidate tag.
    ///
    /// The tag name and target are both deterministic functions of
    /// `(previous_main, reviewed_commit, reviewer)`, so re-running the same
    /// `prepare-merge` asks for the identical tag. Before this, the second
    /// run died claiming another writer had created it -- false, and
    /// unactionable -- while the candidate stayed unverifiable forever
    /// because the tag had never reached the remote.
    /// The ordinary path: a lightweight tag must resolve back to exactly
    /// the target it was created at.
    #[test]
    fn retagging_the_same_candidate_is_idempotent_but_moving_it_is_still_refused() {
        let repo = init_repo();
        let first = rev_parse(repo.path(), "HEAD").unwrap();
        commit_file(
            repo.path(),
            "other.txt",
            "other
",
            "another commit",
        );
        let second = rev_parse(repo.path(), "HEAD").unwrap();
        assert_ne!(first, second);

        tag_lightweight(repo.path(), "agent-candidate/bob/x", &first).unwrap();
        // The retry after a failed push: same name, same target.
        tag_lightweight(repo.path(), "agent-candidate/bob/x", &first)
            .expect("re-tagging the same target must be a no-op, not a conflict");
        assert_eq!(
            rev_parse(repo.path(), "refs/tags/agent-candidate/bob/x").unwrap(),
            first,
            "the tag must still point where it did"
        );

        // Immutability is untouched: a different target is still refused.
        let err = tag_lightweight(repo.path(), "agent-candidate/bob/x", &second)
            .expect_err("moving an existing candidate tag must be refused");
        assert!(
            err.to_string().contains("already exists"),
            "unexpected error: {err}"
        );
    }

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
    fn diff_name_status_reports_both_sides_of_a_rename_untangled() {
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
        let mut paths: Vec<&str> = changed.iter().map(|(_, p)| p.as_str()).collect();
        paths.sort_unstable();
        // Rename detection is deliberately off, so this is a delete plus an
        // add rather than one `R<score> old new` line. Both consumers
        // (`merge_ready`, `audit_main`) scope-check every path returned, and
        // a rename *into* a reviewed scope must not hide the out-of-scope
        // path it came from -- see `HistoryReader::diff_name_status`.
        assert_eq!(paths, vec!["new.txt", "old.txt"], "{changed:?}");
        // The original defect this guards: a tab-separated `old\tnew` pair
        // returned as one mangled path.
        assert!(
            changed.iter().all(|(_, p)| !p.contains('\t')),
            "{changed:?}"
        );
    }
}
