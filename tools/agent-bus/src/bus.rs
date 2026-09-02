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
