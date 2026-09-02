//! Repository-level context: locating the product repo, the `agent-bus`
//! branch, per-agent detached worktrees, and the fetch/rebase/push sync loop
//! (AGENT_BUS.md sections 2 and 10).

use crate::bootstrap::BusJson;
use crate::envelope::Envelope;
use crate::error::{invalid, AbResult};
use crate::events::EventData;
use crate::gitrepo;
use crate::lock::BusLock;
use crate::scalars::{Agent, ObjectId};
use crate::state::BusState;
use crate::{apply, history, storage};
use std::path::{Path, PathBuf};

pub const BUS_BRANCH: &str = "refs/heads/agent-bus";
pub const BUS_BRANCH_SHORT: &str = "agent-bus";

pub struct BusCtx {
    pub repo_root: PathBuf,
    pub has_origin: bool,
}

impl BusCtx {
    pub fn discover(repo_arg: Option<&str>) -> AbResult<BusCtx> {
        let start = match repo_arg {
            Some(p) => PathBuf::from(p),
            None => std::env::current_dir().map_err(|e| crate::error::AbError::Io {
                path: ".".to_string(),
                source: e,
            })?,
        };
        let repo_root = gitrepo::repo_root(&start)?;
        let remotes = gitrepo::run_ok(&repo_root, &["remote"])?;
        let has_origin = remotes.lines().any(|l| l.trim() == "origin");
        Ok(BusCtx { repo_root, has_origin })
    }

    pub fn worktrees_root(&self) -> AbResult<PathBuf> {
        Ok(gitrepo::common_dir(&self.repo_root)?.join("agent-bus-worktrees"))
    }

    pub fn worktree_path(&self, agent: &Agent) -> AbResult<PathBuf> {
        Ok(self.worktrees_root()?.join(agent.as_str()))
    }

    pub fn lock(&self) -> AbResult<BusLock> {
        BusLock::acquire(&gitrepo::common_dir(&self.repo_root)?)
    }

    pub fn bus_ref_exists(&self) -> AbResult<bool> {
        Ok(gitrepo::rev_parse_opt(&self.repo_root, BUS_BRANCH)?.is_some())
    }

    /// Fetch `origin/agent-bus` (if a remote is configured) into the local
    /// `agent-bus` branch ref when the local branch fast-forwards, else
    /// leaves local history and lets the caller's own rebase logic reconcile.
    pub fn fetch_remote(&self) -> AbResult<()> {
        if !self.has_origin {
            return Ok(());
        }
        // `origin` legitimately may not have `agent-bus` yet (freshly
        // bootstrapped and not yet pushed, or a brand-new clone before
        // anyone has published) -- that is not a fetch failure, it just
        // means there is nothing to reconcile against. Only a *transport*
        // failure (no network, auth, bad remote URL, ...) should be a hard
        // error; a missing ref specifically must not block every other bus
        // command from working purely off local state.
        let out = gitrepo::run(&self.repo_root, &["fetch", "origin", "refs/heads/agent-bus:refs/remotes/origin/agent-bus"])?;
        if !out.success && !out.stderr.contains("couldn't find remote ref") {
            return Err(crate::error::AbError::Git(format!(
                "git fetch origin refs/heads/agent-bus failed: {}",
                out.stderr
            )));
        }
        let local = gitrepo::rev_parse_opt(&self.repo_root, BUS_BRANCH)?;
        let remote = gitrepo::rev_parse_opt(&self.repo_root, "refs/remotes/origin/agent-bus")?;
        match (local, remote) {
            (None, Some(r)) => {
                gitrepo::run_ok(&self.repo_root, &["update-ref", BUS_BRANCH, &r])?;
            }
            (Some(l), Some(r)) if l != r => {
                if gitrepo::is_ancestor(&self.repo_root, &l, &r)? {
                    gitrepo::run_ok(&self.repo_root, &["update-ref", BUS_BRANCH, &r])?;
                }
                // else: local has unpublished commits ahead; leave as-is, the
                // per-agent worktree rebase handles reconciliation on push.
            }
            _ => {}
        }
        Ok(())
    }

    pub fn ensure_worktree(&self, agent: &Agent) -> AbResult<PathBuf> {
        let wt = self.worktree_path(agent)?;
        if !wt.exists() {
            gitrepo::ensure_bus_worktree(&self.repo_root, &wt, BUS_BRANCH)?;
        }
        Ok(wt)
    }

    pub fn bus_json(&self) -> AbResult<BusJson> {
        let bytes = std::process::Command::new("git")
            .arg("-C")
            .arg(&self.repo_root)
            .args(["cat-file", "-p", &format!("{BUS_BRANCH}:_bus/BUS.json")])
            .output()
            .map_err(|e| crate::error::AbError::Git(format!("{e}")))?;
        if !bytes.status.success() {
            return Err(invalid("_bus/BUS.json not found on agent-bus"));
        }
        BusJson::parse(&bytes.stdout)
    }

    pub fn load_state(&self) -> AbResult<BusState> {
        let walk = history::walk_full(&self.repo_root, BUS_BRANCH)?;
        apply::replay(&walk)
    }

    pub fn load_state_at(&self, tip: &str) -> AbResult<BusState> {
        let walk = history::walk_full(&self.repo_root, tip)?;
        apply::replay(&walk)
    }

    /// Fetch, ensure a rebased local worktree, and push. Returns the new
    /// `agent-bus` tip.
    pub fn sync(&self, agent: &Agent) -> AbResult<String> {
        let _lock = self.lock()?;
        self.fetch_remote()?;
        let wt = self.ensure_worktree(agent)?;
        let status = gitrepo::status_porcelain(&wt)?;
        for line in status.lines() {
            let path = line[3..].trim();
            if !path.starts_with(agent.as_str()) {
                return Err(invalid(format!(
                    "bus worktree for {agent} has changes outside its own directory: {path}"
                )));
            }
        }
        let mut attempts = 0;
        loop {
            attempts += 1;
            let target = gitrepo::rev_parse(&self.repo_root, BUS_BRANCH)?;
            let head = gitrepo::rev_parse(&wt, "HEAD")?;
            if head == target {
                // Nothing local and unpublished; already caught up.
                return Ok(target);
            }
            if gitrepo::is_ancestor(&wt, &head, &target)? {
                // The worktree is simply behind (no local unpublished work).
                gitrepo::checkout_detach(&wt, &target)?;
                return Ok(target);
            }
            // Local unpublished commit(s): rebase them (preserving content,
            // hence `observed`) onto the fetched tip rather than discarding
            // them, then attempt to publish.
            let rebase = gitrepo::rebase_onto(&wt, &target)?;
            if !rebase.success {
                gitrepo::rebase_abort(&wt)?;
                return Err(invalid(format!(
                    "rebasing {agent}'s local bus commits onto {target} conflicted: {}",
                    rebase.stderr
                )));
            }
            let push = gitrepo::push(&wt, ".", &format!("HEAD:{BUS_BRANCH}"))?;
            if push.success {
                self.push_remote()?;
                return gitrepo::rev_parse(&self.repo_root, BUS_BRANCH);
            }
            if attempts >= 10 {
                return Err(invalid(format!("push to {BUS_BRANCH} failed after {attempts} attempts: {}", push.stderr)));
            }
            self.fetch_remote()?;
        }
    }

    /// Publish a worktree's local commits to `origin` as well, best-effort.
    pub fn push_remote(&self) -> AbResult<()> {
        if !self.has_origin {
            return Ok(());
        }
        let local = gitrepo::rev_parse(&self.repo_root, BUS_BRANCH)?;
        gitrepo::run_ok(&self.repo_root, &["push", "origin", &format!("{local}:{BUS_BRANCH}")])?;
        Ok(())
    }
}

/// Append one event for `agent`, commit it in the agent's worktree, and push
/// it onto the shared `agent-bus` branch.
///
/// The event's `observed` is fixed once, at construction, to whatever bus
/// head was actually fetched — never refreshed on a later retry. A
/// non-fast-forward push means some other agent's unrelated-directory commit
/// landed first; recovery is a plain `git rebase` of this *already-built*
/// commit onto the new tip (same JSON bytes, new parent), not reconstructing
/// the event against fresher state. This is what AGENT_BUS.md section 5 means
/// by "synchronization rebases commits while event causality stays in
/// sequence IDs rather than transient local commit IDs" — and it's what lets
/// two events genuinely retain the *same* `observed` even though one ends up
/// published causally after the other, which is exactly the input the
/// concurrent-vs-causally-later distinction in section 10 is built to handle.
pub fn publish_event(ctx: &BusCtx, agent: &Agent, data: EventData, extra_refs: Vec<crate::scalars::EventId>) -> AbResult<Envelope> {
    let _lock = ctx.lock()?;
    ctx.fetch_remote()?;
    let wt = ctx.ensure_worktree(agent)?;

    let target = gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH)?;
    let head = gitrepo::rev_parse(&wt, "HEAD")?;
    if head != target {
        gitrepo::checkout_detach(&wt, &target)?;
    }
    let state = ctx.load_state_at(&target)?;
    let ag = state
        .agents
        .get(agent)
        .ok_or_else(|| invalid(format!("{agent} is not registered")))?;
    let observed = Some(ObjectId::parse(target.clone())?);
    let env = Envelope::new(agent, ag.next_seq, observed, &data, extra_refs);
    apply::dry_run(&state, &env)?;
    storage::append_event(&wt, &env)?;
    gitrepo::add_all(&wt)?;
    gitrepo::commit(&wt, &format!("agent-bus: {agent} {}#{}", env.kind, env.seq))?;

    let mut attempts = 0;
    loop {
        attempts += 1;
        let push = gitrepo::push(&wt, ".", &format!("HEAD:{BUS_BRANCH}"))?;
        if push.success {
            ctx.push_remote()?;
            return Ok(env);
        }
        if attempts >= 10 {
            return Err(invalid(format!("push to {BUS_BRANCH} failed after {attempts} attempts: {}", push.stderr)));
        }
        ctx.fetch_remote()?;
        let new_target = gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH)?;
        let rebase = gitrepo::rebase_onto(&wt, &new_target)?;
        if !rebase.success {
            gitrepo::rebase_abort(&wt)?;
            return Err(invalid(format!(
                "rebasing {}'s commit onto {new_target} conflicted (a concurrent writer under the same name?): {}",
                agent, rebase.stderr
            )));
        }
    }
}

pub fn bootstrap_init(
    ctx: &BusCtx,
    coordinators: &[Agent],
    product_review_from: &ObjectId,
) -> AbResult<()> {
    if ctx.bus_ref_exists()? {
        return Err(invalid("agent-bus branch already exists"));
    }
    let object_format = gitrepo::object_format(&ctx.repo_root)?;
    let bus_json = BusJson::new(object_format, coordinators.to_vec(), product_review_from.clone())?;

    let staging = ctx.worktrees_root()?.join("_bootstrap");
    if staging.exists() {
        std::fs::remove_dir_all(&staging).map_err(|e| crate::error::AbError::Io {
            path: staging.display().to_string(),
            source: e,
        })?;
    }
    std::fs::create_dir_all(&staging).map_err(|e| crate::error::AbError::Io {
        path: staging.display().to_string(),
        source: e,
    })?;
    gitrepo::run_ok(&staging, &["init", "--quiet"])?;

    std::fs::create_dir_all(staging.join("_bus")).ok();
    storage::atomic_write(&staging.join("_bus/BUS.json"), &bus_json.to_canonical_bytes())?;
    storage::atomic_write(
        &staging.join(".gitattributes"),
        crate::bootstrap::GITATTRIBUTES_CONTENTS.as_bytes(),
    )?;

    for c in coordinators {
        let data = EventData::AgentRegistered(crate::events::AgentRegistered {
            display_name: crate::scalars::Short::parse(c.as_str().to_string())?,
            primary_role: crate::events::Role::Coordinator,
            purpose: crate::scalars::Text::parse("bootstrap coordinator".to_string())?,
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        let env = Envelope {
            v: crate::envelope::SCHEMA_VERSION,
            id: crate::scalars::EventId::new(c, 0),
            agent: c.clone(),
            seq: 0,
            time: crate::scalars::Timestamp::now_utc(),
            observed: None,
            kind: data.kind().to_string(),
            refs: crate::scalars::StringSet::from_iter(std::iter::empty()),
            data: data.to_value(),
        };
        storage::append_event(&staging, &env)?;
    }

    gitrepo::add_all(&staging)?;
    gitrepo::run_ok(
        &staging,
        &["commit", "-m", "agent-bus: bootstrap root"],
    )?;
    let root_commit = gitrepo::rev_parse(&staging, "HEAD")?;
    gitrepo::run_ok(&staging, &["branch", "-f", BUS_BRANCH_SHORT, &root_commit])?;
    gitrepo::run_ok(
        &ctx.repo_root,
        &["fetch", staging.to_string_lossy().as_ref(), &format!("{BUS_BRANCH}:{BUS_BRANCH}")],
    )?;
    std::fs::remove_dir_all(&staging).ok();
    Ok(())
}

pub fn read_json_file(path: &Path) -> AbResult<serde_json::Value> {
    let bytes = std::fs::read(path).map_err(|e| crate::error::AbError::Io {
        path: path.display().to_string(),
        source: e,
    })?;
    Ok(serde_json::from_slice(&bytes)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::{AgentStatusEvent, LifecycleStatus};
    use crate::gitrepo::mock::MockGit;
    use crate::gitrepo::GitOutput;
    use crate::scalars::Text;
    use std::process::Command;

    // ---------------------------------------------------------------
    // Real-git test fixtures. No mock is installed for setup: without an
    // installed `MockGit`, `gitrepo::run`/`run_stdin` fall through to the
    // real subprocess (see `gitrepo::mock::intercept`), so calling the
    // crate's own `bootstrap_init`/`publish_event` here builds a genuine,
    // valid bus branch on disk exactly the way the CLI would. A `MockGit`
    // is installed later, only around the specific call a given test wants
    // to script (almost always just `push`), with a catch-all passthrough
    // rule for every other call so the rest of the flow still runs for
    // real. This is what lets these tests provoke an actual, real
    // non-fast-forward push rejection and a real, unresolved rebase
    // conflict rather than merely asserting that bus.rs *would* call the
    // right functions.
    // ---------------------------------------------------------------

    fn run_setup_git(dir: &Path, args: &[&str]) -> String {
        let out = Command::new("git").arg("-C").arg(dir).args(args).output().expect("failed to run git");
        assert!(out.status.success(), "git {args:?} failed: {}", String::from_utf8_lossy(&out.stderr));
        String::from_utf8_lossy(&out.stdout).trim().to_string()
    }

    fn init_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        run_setup_git(dir.path(), &["init", "--quiet"]);
        run_setup_git(dir.path(), &["config", "user.email", "test@example.com"]);
        run_setup_git(dir.path(), &["config", "user.name", "Test"]);
        dir
    }

    fn bare_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        run_setup_git(dir.path(), &["init", "--quiet", "--bare"]);
        dir
    }

    fn agent(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn some_object_id() -> ObjectId {
        ObjectId::parse("a".repeat(40)).unwrap()
    }

    /// Bootstrap a fresh `agent-bus` branch (real git, no mock) with the
    /// given coordinators already registered.
    fn bootstrap(dir: &Path, agents: &[&str]) -> BusCtx {
        let ctx = BusCtx { repo_root: dir.to_path_buf(), has_origin: false };
        let agents: Vec<Agent> = agents.iter().map(|a| agent(a)).collect();
        bootstrap_init(&ctx, &agents, &some_object_id()).unwrap();
        ctx
    }

    fn status_event(note: &str) -> EventData {
        EventData::AgentStatus(AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: Text::parse(note.to_string()).unwrap(),
            product_branch: None,
            product_commit: None,
        })
    }

    /// Real subprocess implementation identical to `gitrepo::run`/
    /// `run_stdin`'s own bodies, callable from inside a `MockGit` responder
    /// (which cannot recurse into `gitrepo::run` for "the real behavior"
    /// since that would just hit the mock again).
    fn real_git_output(dir: &Path, args: &[&str], stdin: Option<&str>) -> AbResult<GitOutput> {
        use std::io::Write as _;
        use std::process::Stdio;
        if let Some(input) = stdin {
            let mut child = Command::new("git")
                .arg("-C")
                .arg(dir)
                .args(args)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .map_err(|e| crate::error::AbError::Git(format!("failed to run git {args:?}: {e}")))?;
            child
                .stdin
                .as_mut()
                .unwrap()
                .write_all(input.as_bytes())
                .map_err(|e| crate::error::AbError::Git(format!("failed to write stdin to git {args:?}: {e}")))?;
            let out = child
                .wait_with_output()
                .map_err(|e| crate::error::AbError::Git(format!("failed to wait on git {args:?}: {e}")))?;
            Ok(GitOutput {
                success: out.status.success(),
                stdout: String::from_utf8_lossy(&out.stdout).trim_end().to_string(),
                stderr: String::from_utf8_lossy(&out.stderr).trim_end().to_string(),
            })
        } else {
            let out = Command::new("git")
                .arg("-C")
                .arg(dir)
                .args(args)
                .output()
                .map_err(|e| crate::error::AbError::Git(format!("failed to run git {args:?}: {e}")))?;
            Ok(GitOutput {
                success: out.status.success(),
                stdout: String::from_utf8_lossy(&out.stdout).trim_end().to_string(),
                stderr: String::from_utf8_lossy(&out.stderr).trim_end().to_string(),
            })
        }
    }

    /// Appends a catch-all rule that forwards any unmatched call to the
    /// real `git` subprocess, so a `MockGit` built with a few specific
    /// overrides otherwise behaves exactly like no mock were installed.
    fn passthrough(m: MockGit) -> MockGit {
        m.on_with(|_, _, _| true, |dir, args, stdin| real_git_output(dir, args, stdin))
    }

    /// Simulates another agent's unrelated, concurrent publish landing on
    /// `agent-bus` first: adds/overwrites `file_rel_path` in a throwaway
    /// detached worktree and force-updates the branch ref directly (a
    /// plumbing `update-ref`, not a push, so it can't hit
    /// `receive.denyCurrentBranch`). Returns the new tip.
    fn inject_commit(repo_root: &Path, file_rel_path: &str, contents: &str) -> String {
        let tmp = tempfile::tempdir().unwrap();
        run_setup_git(repo_root, &["worktree", "add", "--detach", &tmp.path().to_string_lossy(), BUS_BRANCH]);
        let file_path = tmp.path().join(file_rel_path);
        if let Some(parent) = file_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&file_path, contents).unwrap();
        run_setup_git(tmp.path(), &["add", "-A"]);
        run_setup_git(tmp.path(), &["commit", "-m", "agent-bus: concurrent write"]);
        let sha = run_setup_git(tmp.path(), &["rev-parse", "HEAD"]);
        run_setup_git(repo_root, &["update-ref", BUS_BRANCH, &sha]);
        run_setup_git(repo_root, &["worktree", "remove", "--force", &tmp.path().to_string_lossy()]);
        sha
    }

    /// Simulates a concurrent, *structurally valid* publish by a brand-new
    /// agent (a real `agent.registered` event, built and appended the same
    /// way `bootstrap_init`/`publish_event` would) landing on `agent-bus`
    /// first. Unlike [`inject_commit`], the result passes a real
    /// `load_state`/`load_state_at` replay, so tests that check state after
    /// a successful retry can use it too.
    fn inject_agent_registered(repo_root: &Path, name: &str) -> String {
        let tip = gitrepo::rev_parse(repo_root, BUS_BRANCH).unwrap();
        let tmp = tempfile::tempdir().unwrap();
        run_setup_git(repo_root, &["worktree", "add", "--detach", &tmp.path().to_string_lossy(), BUS_BRANCH]);
        let new_agent = agent(name);
        let data = EventData::AgentRegistered(crate::events::AgentRegistered {
            display_name: crate::scalars::Short::parse(name.to_string()).unwrap(),
            primary_role: crate::events::Role::Implementor,
            purpose: Text::parse("concurrent registration".to_string()).unwrap(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        let observed = Some(ObjectId::parse(tip).unwrap());
        let env = Envelope::new(&new_agent, 0, observed, &data, []);
        storage::append_event(tmp.path(), &env).unwrap();
        run_setup_git(tmp.path(), &["add", "-A"]);
        run_setup_git(tmp.path(), &["commit", "-m", &format!("agent-bus: {name} agent.registered")]);
        let sha = run_setup_git(tmp.path(), &["rev-parse", "HEAD"]);
        run_setup_git(repo_root, &["update-ref", BUS_BRANCH, &sha]);
        run_setup_git(repo_root, &["worktree", "remove", "--force", &tmp.path().to_string_lossy()]);
        sha
    }

    /// Same idea as [`inject_commit`], but *deletes* `file_rel_path` instead
    /// of writing it — used to force a real, unresolvable modify/delete
    /// rebase conflict against a local commit that edits the same path.
    fn inject_delete_commit(repo_root: &Path, file_rel_path: &str) -> String {
        let tmp = tempfile::tempdir().unwrap();
        run_setup_git(repo_root, &["worktree", "add", "--detach", &tmp.path().to_string_lossy(), BUS_BRANCH]);
        std::fs::remove_file(tmp.path().join(file_rel_path)).unwrap();
        run_setup_git(tmp.path(), &["add", "-A"]);
        run_setup_git(tmp.path(), &["commit", "-m", "agent-bus: concurrent delete"]);
        let sha = run_setup_git(tmp.path(), &["rev-parse", "HEAD"]);
        run_setup_git(repo_root, &["update-ref", BUS_BRANCH, &sha]);
        run_setup_git(repo_root, &["worktree", "remove", "--force", &tmp.path().to_string_lossy()]);
        sha
    }

    // ----------------------------------------------------------- discover

    #[test]
    fn discover_detects_missing_and_present_origin_remote() {
        let repo = init_repo();
        let path_str = repo.path().to_string_lossy().to_string();

        let ctx = BusCtx::discover(Some(&path_str)).unwrap();
        assert!(!ctx.has_origin);
        assert!(ctx.repo_root.exists());

        run_setup_git(repo.path(), &["remote", "add", "origin", "https://example.invalid/repo.git"]);
        let ctx2 = BusCtx::discover(Some(&path_str)).unwrap();
        assert!(ctx2.has_origin);
    }

    // ----------------------------------------------------- trivial paths

    #[test]
    fn worktrees_root_and_worktree_path_are_under_git_dir() {
        let repo = init_repo();
        let ctx = BusCtx { repo_root: repo.path().to_path_buf(), has_origin: false };
        assert_eq!(ctx.worktrees_root().unwrap(), repo.path().join(".git").join("agent-bus-worktrees"));
        assert_eq!(
            ctx.worktree_path(&agent("alice")).unwrap(),
            repo.path().join(".git").join("agent-bus-worktrees").join("alice")
        );
    }

    // ------------------------------------------------------- bus_ref_exists

    #[test]
    fn bus_ref_exists_toggles_after_bootstrap() {
        let repo = init_repo();
        let ctx = BusCtx { repo_root: repo.path().to_path_buf(), has_origin: false };
        assert!(!ctx.bus_ref_exists().unwrap());
        bootstrap_init(&ctx, &[agent("alice")], &some_object_id()).unwrap();
        assert!(ctx.bus_ref_exists().unwrap());
    }

    // ----------------------------------------------------------- bus_json

    #[test]
    fn bus_json_errors_before_bootstrap_and_reads_after() {
        let repo = init_repo();
        let ctx = BusCtx { repo_root: repo.path().to_path_buf(), has_origin: false };
        let err = ctx.bus_json().unwrap_err();
        assert!(err.to_string().contains("not found"), "{err}");

        bootstrap_init(&ctx, &[agent("alice")], &some_object_id()).unwrap();
        let _ = ctx.bus_json().unwrap();
    }

    // -------------------------------------------------------- fetch_remote

    #[test]
    fn fetch_remote_creates_local_ref_when_missing_but_origin_has_one() {
        let origin = init_repo();
        let origin_ctx = bootstrap(origin.path(), &["carol"]);
        let origin_tip = gitrepo::rev_parse(&origin_ctx.repo_root, BUS_BRANCH).unwrap();

        let repo = init_repo();
        run_setup_git(repo.path(), &["remote", "add", "origin", &origin.path().to_string_lossy()]);
        let ctx = BusCtx { repo_root: repo.path().to_path_buf(), has_origin: true };
        assert!(!ctx.bus_ref_exists().unwrap());

        ctx.fetch_remote().unwrap();
        assert_eq!(gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap(), origin_tip);
    }

    #[test]
    fn fetch_remote_is_noop_when_local_already_matches_origin() {
        let origin = init_repo();
        let origin_ctx = bootstrap(origin.path(), &["carol"]);
        let origin_tip = gitrepo::rev_parse(&origin_ctx.repo_root, BUS_BRANCH).unwrap();

        let repo = init_repo();
        run_setup_git(repo.path(), &["remote", "add", "origin", &origin.path().to_string_lossy()]);
        run_setup_git(repo.path(), &["fetch", "origin", &format!("{BUS_BRANCH}:{BUS_BRANCH}")]);
        let ctx = BusCtx { repo_root: repo.path().to_path_buf(), has_origin: true };

        ctx.fetch_remote().unwrap();
        assert_eq!(gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap(), origin_tip);
    }

    #[test]
    fn fetch_remote_fast_forwards_local_when_origin_advanced() {
        let origin = init_repo();
        let origin_ctx = bootstrap(origin.path(), &["carol"]);
        let root_tip = gitrepo::rev_parse(&origin_ctx.repo_root, BUS_BRANCH).unwrap();

        let repo = init_repo();
        run_setup_git(repo.path(), &["remote", "add", "origin", &origin.path().to_string_lossy()]);
        run_setup_git(repo.path(), &["fetch", "origin", &format!("{BUS_BRANCH}:{BUS_BRANCH}")]);
        let ctx = BusCtx { repo_root: repo.path().to_path_buf(), has_origin: true };
        assert_eq!(gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap(), root_tip);

        publish_event(&origin_ctx, &agent("carol"), status_event("origin moved on"), vec![]).unwrap();
        let advanced_tip = gitrepo::rev_parse(&origin_ctx.repo_root, BUS_BRANCH).unwrap();
        assert_ne!(advanced_tip, root_tip);

        ctx.fetch_remote().unwrap();
        assert_eq!(gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap(), advanced_tip);
    }

    #[test]
    fn fetch_remote_leaves_local_untouched_when_diverged_from_origin() {
        let origin = init_repo();
        bootstrap(origin.path(), &["carol"]);

        let repo = init_repo();
        run_setup_git(repo.path(), &["remote", "add", "origin", &origin.path().to_string_lossy()]);
        run_setup_git(repo.path(), &["fetch", "origin", &format!("{BUS_BRANCH}:{BUS_BRANCH}")]);
        let ctx = BusCtx { repo_root: repo.path().to_path_buf(), has_origin: true };
        let origin_tip = gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap();

        // Local advances independently of origin (never pushed there).
        let local_tip = inject_commit(repo.path(), "dave/local-only.jsonl", "local only\n");
        assert_ne!(local_tip, origin_tip);

        ctx.fetch_remote().unwrap();
        assert_eq!(
            gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap(),
            local_tip,
            "a local-only commit must not be discarded by fetch_remote"
        );
    }

    #[test]
    fn fetch_remote_is_noop_without_origin() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        // Must not attempt any git call at all: no origin is configured.
        ctx.fetch_remote().unwrap();
    }

    // -------------------------------------------------------- push_remote

    #[test]
    fn push_remote_is_noop_without_origin() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        ctx.push_remote().unwrap();
    }

    #[test]
    fn push_remote_publishes_local_bus_branch_to_origin() {
        let origin = bare_repo();
        let repo = init_repo();
        run_setup_git(repo.path(), &["remote", "add", "origin", &origin.path().to_string_lossy()]);
        let ctx = BusCtx { repo_root: repo.path().to_path_buf(), has_origin: true };
        bootstrap_init(&ctx, &[agent("alice")], &some_object_id()).unwrap();

        ctx.push_remote().unwrap();

        let origin_tip = run_setup_git(origin.path(), &["rev-parse", "--verify", BUS_BRANCH]);
        let local_tip = gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap();
        assert_eq!(origin_tip, local_tip);
    }

    // ----------------------------------------------------- ensure_worktree

    #[test]
    fn ensure_worktree_creates_once_and_reuses_existing_dir() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let wt1 = ctx.ensure_worktree(&alice).unwrap();
        assert!(wt1.exists());
        let wt2 = ctx.ensure_worktree(&alice).unwrap();
        assert_eq!(wt1, wt2);
    }

    // --------------------------------------------------------- load_state

    #[test]
    fn load_state_and_load_state_at_agree_and_see_registered_agents() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let tip = gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap();

        let s1 = ctx.load_state().unwrap();
        let s2 = ctx.load_state_at(&tip).unwrap();
        assert!(s1.agents.contains_key(&alice));
        assert!(s2.agents.contains_key(&alice));
    }

    // -------------------------------------------------------------- sync

    #[test]
    fn sync_when_already_caught_up_returns_target_unchanged() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let target_before = gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap();
        let result = ctx.sync(&agent("alice")).unwrap();
        assert_eq!(result, target_before);
    }

    #[test]
    fn sync_discards_and_fastforwards_when_worktree_is_behind() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let wt = ctx.ensure_worktree(&alice).unwrap();
        let old_head = gitrepo::rev_parse(&wt, "HEAD").unwrap();

        let new_tip = inject_commit(repo.path(), "bob/injected.jsonl", "advance\n");
        assert_ne!(old_head, new_tip);

        let result = ctx.sync(&alice).unwrap();
        assert_eq!(result, new_tip);
        assert_eq!(gitrepo::rev_parse(&wt, "HEAD").unwrap(), new_tip);
    }

    #[test]
    fn sync_rebases_local_unpublished_commits_then_pushes() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let wt = ctx.ensure_worktree(&alice).unwrap();
        std::fs::write(wt.join("alice").join("scratch.txt"), "local work\n").unwrap();
        run_setup_git(&wt, &["add", "-A"]);
        run_setup_git(&wt, &["commit", "-m", "agent-bus: alice local scratch"]);
        let local_head = gitrepo::rev_parse(&wt, "HEAD").unwrap();

        let result = ctx.sync(&alice).unwrap();
        assert_eq!(result, local_head, "the local commit should publish as-is (fast-forward rebase is a no-op)");
        assert_eq!(gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap(), local_head);
    }

    #[test]
    fn sync_rejects_changes_outside_agents_own_directory() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let wt = ctx.ensure_worktree(&alice).unwrap();
        std::fs::write(wt.join("not-alice.txt"), "stray\n").unwrap();

        let err = ctx.sync(&alice).unwrap_err();
        assert!(err.to_string().contains("changes outside its own directory"), "{err}");
    }

    #[test]
    fn sync_allows_uncommitted_changes_within_agents_own_directory() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let wt = ctx.ensure_worktree(&alice).unwrap();
        // Uncommitted, but under alice's own directory: the guard must let
        // this through rather than treating it as a foreign-path violation.
        std::fs::write(wt.join("alice").join("scratch.txt"), "not yet committed\n").unwrap();

        ctx.sync(&alice).unwrap();
    }

    #[test]
    fn sync_retries_after_push_race_then_succeeds() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let wt = ctx.ensure_worktree(&alice).unwrap();
        std::fs::write(wt.join("alice").join("scratch.txt"), "local work\n").unwrap();
        run_setup_git(&wt, &["add", "-A"]);
        run_setup_git(&wt, &["commit", "-m", "agent-bus: alice local scratch"]);

        let repo_root = repo.path().to_path_buf();
        let calls = std::cell::Cell::new(0u32);
        let mock = MockGit::new().on_with(
            |_, a, _| a.first() == Some(&"push"),
            move |dir, args, stdin| {
                let n = calls.get();
                calls.set(n + 1);
                if n == 0 {
                    // Another agent's unrelated publish lands first.
                    inject_agent_registered(&repo_root, "bob");
                    Ok(GitOutput::err("! [rejected] HEAD -> refs/heads/agent-bus (fetch first)"))
                } else {
                    real_git_output(dir, args, stdin)
                }
            },
        );
        let _guard = passthrough(mock).install();

        let tip = ctx.sync(&alice).unwrap();
        assert_eq!(gitrepo::rev_parse(&ctx.repo_root, BUS_BRANCH).unwrap(), tip);
    }

    #[test]
    fn sync_aborts_when_rebase_conflicts() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let wt = ctx.ensure_worktree(&alice).unwrap();
        // A local edit to alice's own segment file...
        std::fs::write(wt.join("alice").join("000000.jsonl"), "{}\n").unwrap();
        run_setup_git(&wt, &["add", "-A"]);
        run_setup_git(&wt, &["commit", "-m", "agent-bus: alice local edit"]);

        let repo_root = repo.path().to_path_buf();
        let mock = MockGit::new().on_with(
            |_, a, _| a.first() == Some(&"push"),
            move |_, _, _| {
                // ...racing a concurrent commit that deletes that same file:
                // a real, unresolvable modify/delete conflict.
                inject_delete_commit(&repo_root, "alice/000000.jsonl");
                Ok(GitOutput::err("! [rejected] HEAD -> refs/heads/agent-bus (fetch first)"))
            },
        );
        let _guard = passthrough(mock).install();

        let err = ctx.sync(&alice).unwrap_err();
        assert!(err.to_string().contains("conflicted"), "{err}");
    }

    #[test]
    fn sync_fails_after_exhausting_push_retries() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let wt = ctx.ensure_worktree(&alice).unwrap();
        std::fs::write(wt.join("alice").join("scratch.txt"), "local work\n").unwrap();
        run_setup_git(&wt, &["add", "-A"]);
        run_setup_git(&wt, &["commit", "-m", "agent-bus: alice local scratch"]);

        let mock = MockGit::new().on_with(
            |_, a, _| a.first() == Some(&"push"),
            |_, _, _| Ok(GitOutput::err("! [rejected] always")),
        );
        let _guard = passthrough(mock).install();

        let err = ctx.sync(&alice).unwrap_err();
        assert!(err.to_string().contains("failed after 10 attempts"), "{err}");
    }

    // ---------------------------------------------------------- publish_event

    #[test]
    fn publish_event_succeeds_on_first_push_and_advances_seq() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let env = publish_event(&ctx, &alice, status_event("hello"), vec![]).unwrap();
        assert_eq!(env.seq, 1);
        assert_eq!(env.agent, alice);
        let state = ctx.load_state().unwrap();
        assert_eq!(state.agents.get(&alice).unwrap().next_seq, 2);
    }

    #[test]
    fn publish_event_rejects_unregistered_agent() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let err = publish_event(&ctx, &agent("bob"), status_event("hi"), vec![]).unwrap_err();
        assert!(err.to_string().contains("is not registered"), "{err}");
    }

    #[test]
    fn publish_event_retries_after_push_race_and_succeeds() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let repo_root = repo.path().to_path_buf();
        let calls = std::cell::Cell::new(0u32);
        let mock = MockGit::new().on_with(
            |_, a, _| a.first() == Some(&"push"),
            move |dir, args, stdin| {
                let n = calls.get();
                calls.set(n + 1);
                if n == 0 {
                    inject_agent_registered(&repo_root, "bob");
                    Ok(GitOutput::err("! [rejected] HEAD -> refs/heads/agent-bus (fetch first)"))
                } else {
                    real_git_output(dir, args, stdin)
                }
            },
        );
        let _guard = passthrough(mock).install();

        let env = publish_event(&ctx, &alice, status_event("first push races"), vec![]).unwrap();
        assert_eq!(env.seq, 1);
        let state = ctx.load_state().unwrap();
        assert!(state.agents.contains_key(&alice));
        assert!(state.agents.contains_key(&agent("bob")), "the concurrent registration must also survive the rebase");
    }

    #[test]
    fn publish_event_aborts_when_rebase_conflicts_after_push_race() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let repo_root = repo.path().to_path_buf();
        let mock = MockGit::new().on_with(
            |_, a, _| a.first() == Some(&"push"),
            move |_, _, _| {
                // alice's own commit (built above, before the first push
                // attempt) modifies alice/000000.jsonl by appending to it;
                // racing a concurrent delete of that exact file guarantees a
                // real, unresolvable modify/delete conflict on retry.
                inject_delete_commit(&repo_root, "alice/000000.jsonl");
                Ok(GitOutput::err("! [rejected] HEAD -> refs/heads/agent-bus (fetch first)"))
            },
        );
        let _guard = passthrough(mock).install();

        let err = publish_event(&ctx, &alice, status_event("will conflict"), vec![]).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("conflicted"), "{msg}");
        assert!(msg.contains("alice"), "{msg}");

        // rebase --abort must have actually run: the worktree is left clean,
        // not stuck mid-conflict.
        let wt = ctx.worktree_path(&alice).unwrap();
        let status = gitrepo::status_porcelain(&wt).unwrap();
        assert!(status.trim().is_empty(), "worktree left dirty after abort: {status}");
    }

    #[test]
    fn publish_event_fails_after_exhausting_push_retries() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let alice = agent("alice");
        let mock = MockGit::new().on_with(
            |_, a, _| a.first() == Some(&"push"),
            |_, _, _| Ok(GitOutput::err("! [rejected] always")),
        );
        let _guard = passthrough(mock).install();

        let err = publish_event(&ctx, &alice, status_event("never lands"), vec![]).unwrap_err();
        assert!(err.to_string().contains("failed after 10 attempts"), "{err}");
    }

    // ------------------------------------------------------- bootstrap_init

    #[test]
    fn bootstrap_init_rejects_when_bus_branch_already_exists() {
        let repo = init_repo();
        let ctx = bootstrap(repo.path(), &["alice"]);
        let err = bootstrap_init(&ctx, &[agent("bob")], &some_object_id()).unwrap_err();
        assert!(err.to_string().contains("already exists"), "{err}");
    }

    #[test]
    fn bootstrap_init_cleans_up_a_stale_staging_directory_from_a_prior_attempt() {
        let repo = init_repo();
        let ctx = BusCtx { repo_root: repo.path().to_path_buf(), has_origin: false };
        // Simulate a previous bootstrap-init that got interrupted before its
        // own end-of-function `remove_dir_all(&staging)` cleanup ran.
        let staging = ctx.worktrees_root().unwrap().join("_bootstrap");
        std::fs::create_dir_all(&staging).unwrap();
        std::fs::write(staging.join("leftover.txt"), b"stale").unwrap();

        bootstrap_init(&ctx, &[agent("alice")], &some_object_id()).unwrap();
        assert!(ctx.bus_ref_exists().unwrap());
    }

    #[test]
    fn bootstrap_init_errors_when_worktrees_root_is_blocked_by_a_file() {
        let repo = init_repo();
        let ctx = BusCtx { repo_root: repo.path().to_path_buf(), has_origin: false };
        // Occupy the directory bootstrap-init needs to create the staging
        // checkout under, with a plain file instead of a directory.
        std::fs::write(ctx.worktrees_root().unwrap(), b"not a directory").unwrap();

        match bootstrap_init(&ctx, &[agent("alice")], &some_object_id()) {
            Err(crate::error::AbError::Io { .. }) => {}
            Err(other) => panic!("expected AbError::Io, got {other}"),
            Ok(()) => panic!("expected bootstrap_init to fail when worktrees_root is blocked"),
        }
    }

    // -------------------------------------------------------- read_json_file

    #[test]
    fn read_json_file_parses_valid_and_errors_on_missing() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("data.json");
        std::fs::write(&path, br#"{"a":1}"#).unwrap();
        let v = read_json_file(&path).unwrap();
        assert_eq!(v["a"], 1);

        let missing = dir.path().join("missing.json");
        assert!(read_json_file(&missing).is_err());
    }
}
