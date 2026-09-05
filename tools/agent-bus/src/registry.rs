//! The agent-registry ref and `RosterEpoch`
//! (docs/AGENT_COORDINATION_EVOLUTION.md section 2.1).
//!
//! Membership, host bindings, and coordinator custody change far less often
//! than ordinary events. This low-volume, protected, append-only ref
//! (`refs/heads/agent-registry`) is what makes a "complete frontier"
//! decidable without a global bus-head commit: an epoch names the exact
//! active agent set at one point, and later registrations never retroactively
//! invalidate an earlier authority event that cited it.
//!
//! Registry commits are serialized by remote compare-and-swap (the
//! coordinator layer's job); this module owns the *shape* of an epoch and
//! its validation, not the network round trip that publishes one.

use crate::bootstrap::BusConfig;
use crate::error::{invalid, AbError, AbResult};
use crate::events::Role;
use crate::scalars::{Agent, ObjectId, Short};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::Path;

pub const REGISTRY_REF: &str = "refs/heads/agent-registry";
const EPOCH_FILE: &str = "epoch.json";
/// Written once, in the root epoch's own commit tree only. Every later
/// epoch transition checks out its parent's full tree before adding its own
/// changed `epoch.json`, so this file is carried forward unchanged rather
/// than rewritten -- exactly the "established alongside the registry's root
/// epoch," immutable-for-the-registry's-lifetime placement `bootstrap.rs`'s
/// module doc describes in place of v1's standalone `_bus/BUS.json` commit.
const CONFIG_FILE: &str = "bus_config.json";

/// The registry commit's on-disk content: `RosterEpoch` minus `id`, since a
/// commit can't name its own not-yet-computed sha inside itself. `parent` is
/// carried in the blob (not derived from the git commit parent at read time)
/// so a cold read of one epoch never needs a second git call just to learn
/// its lineage.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct EpochFile {
    parent: Option<ObjectId>,
    active_members: BTreeMap<Agent, MemberBinding>,
}

impl EpochFile {
    fn canonical_bytes(&self) -> Vec<u8> {
        let value = serde_json::to_value(self).expect("EpochFile always serializable");
        serde_json::to_vec(&value).expect("EpochFile value always serializable")
    }
}

/// The current tip of the registry ref, or `None` if it has never been
/// created.
pub fn read_registry_tip(repo: &Path) -> AbResult<Option<ObjectId>> {
    match crate::gitrepo::rev_parse_opt(repo, REGISTRY_REF)? {
        Some(s) => Ok(Some(ObjectId::parse(s)?)),
        None => Ok(None),
    }
}

/// Reads one named, immutable epoch by its commit id -- any epoch ever
/// created, not only the current tip, since an authority event's already
/// -complete frontier must remain re-validatable forever (gate 5's "a later
/// registration does not invalidate it").
pub fn read_epoch(repo: &Path, epoch_id: &ObjectId, worktree: &Path) -> AbResult<RosterEpoch> {
    crate::gitrepo::ensure_bus_worktree(repo, worktree, epoch_id.as_str())?;
    crate::gitrepo::checkout_detach(worktree, epoch_id.as_str())?;
    let bytes = std::fs::read(worktree.join(EPOCH_FILE)).map_err(|e| AbError::Io {
        path: worktree.join(EPOCH_FILE).display().to_string(),
        source: e,
    })?;
    let file: EpochFile =
        serde_json::from_slice(&bytes).map_err(|e| invalid(format!("malformed epoch: {e}")))?;
    Ok(RosterEpoch {
        id: epoch_id.clone(),
        parent: file.parent,
        active_members: file.active_members,
    })
}

/// Reads `tip` and every epoch reachable by walking `parent` back to the
/// root, keyed by each epoch's own id. Complete frontiers must remain
/// re-validatable against the *exact* historical epoch they name, not
/// merely the current tip (gate 5: "a later registration does not
/// invalidate it") -- this is what lets a caller build that full lookup
/// table once per reduction instead of re-walking history per event.
pub fn read_epoch_chain(
    repo: &Path,
    tip: &ObjectId,
    worktree: &Path,
) -> AbResult<BTreeMap<ObjectId, RosterEpoch>> {
    let mut chain = BTreeMap::new();
    let mut next = Some(tip.clone());
    while let Some(id) = next {
        let epoch = read_epoch(repo, &id, worktree)?;
        next = epoch.parent.clone();
        chain.insert(id, epoch);
    }
    Ok(chain)
}

/// Reads the bus-wide `BusConfig` fixed at activation. Any known epoch id
/// works, not only the root: `create_root` writes `bus_config.json` once,
/// and every later epoch transition checks out its parent's full tree
/// before layering its own change on top, so the file reaches every epoch
/// unchanged without this function needing to walk `parent` back to the
/// root itself.
pub fn read_bus_config(repo: &Path, epoch_id: &ObjectId, worktree: &Path) -> AbResult<BusConfig> {
    crate::gitrepo::ensure_bus_worktree(repo, worktree, epoch_id.as_str())?;
    crate::gitrepo::checkout_detach(worktree, epoch_id.as_str())?;
    let bytes = std::fs::read(worktree.join(CONFIG_FILE)).map_err(|e| AbError::Io {
        path: worktree.join(CONFIG_FILE).display().to_string(),
        source: e,
    })?;
    BusConfig::parse(&bytes)
}

/// Creates the registry's root epoch (migration/activation time, section
/// 2.5). Fails if a registry already exists -- there is exactly one root,
/// ever.
pub fn create_root(
    repo: &Path,
    config: &BusConfig,
    active_members: BTreeMap<Agent, MemberBinding>,
    worktree: &Path,
) -> AbResult<RosterEpoch> {
    if read_registry_tip(repo)?.is_some() {
        return Err(invalid(
            "the agent-registry already has a root epoch -- this bus is already activated; \
             use `register` to add a further agent instead of `genesis`",
        ));
    }
    std::fs::create_dir_all(worktree).map_err(|e| AbError::Io {
        path: worktree.display().to_string(),
        source: e,
    })?;
    let tmp_branch = "_tmp_registry_root";
    crate::gitrepo::run_ok(
        repo,
        &[
            "worktree",
            "add",
            "--orphan",
            "-b",
            tmp_branch,
            &worktree.to_string_lossy(),
        ],
    )?;
    crate::storage::atomic_write(&worktree.join(".gitattributes"), b"*.json -text\n")?;
    let file = EpochFile {
        parent: None,
        active_members: active_members.clone(),
    };
    crate::storage::atomic_write(&worktree.join(EPOCH_FILE), &file.canonical_bytes())?;
    crate::storage::atomic_write(&worktree.join(CONFIG_FILE), &config.to_canonical_bytes())?;
    crate::gitrepo::add_all(worktree)?;
    let commit = crate::gitrepo::commit(worktree, "agent-registry: root epoch")?;
    // `update-ref`, not `branch -f`: see `stream::create_root_commit`'s
    // identical comment -- `REGISTRY_REF` is already fully qualified
    // (`refs/heads/agent-registry`), and `git branch -f` does not accept
    // that form as the ref itself.
    crate::gitrepo::run_ok(repo, &["update-ref", REGISTRY_REF, &commit])?;
    crate::gitrepo::run_ok(
        repo,
        &["worktree", "remove", "--force", &worktree.to_string_lossy()],
    )?;
    crate::gitrepo::run_ok(repo, &["branch", "-D", tmp_branch])?;
    Ok(RosterEpoch::root(ObjectId::parse(commit)?, active_members))
}

/// Proposes the next epoch as a child of `expected_parent`: registration,
/// retirement, reassignment, or coordinator succession. Fails closed if the
/// registry has moved since `expected_parent` was read -- the low-volume
/// compare-and-swap point section 2.1 describes, so a losing proposer must
/// re-read the new tip and retry rather than silently overwrite it.
pub fn propose_transition(
    repo: &Path,
    expected_parent: &RosterEpoch,
    new_active_members: BTreeMap<Agent, MemberBinding>,
    worktree: &Path,
) -> AbResult<RosterEpoch> {
    let actual_tip = read_registry_tip(repo)?
        .ok_or_else(|| invalid("the agent-registry has no root epoch yet"))?;
    if actual_tip != expected_parent.id {
        return Err(invalid(format!(
            "the agent-registry has moved: expected parent {}, actual tip {actual_tip} \
             -- re-read the current epoch and retry",
            expected_parent.id
        )));
    }
    crate::gitrepo::ensure_bus_worktree(repo, worktree, expected_parent.id.as_str())?;
    crate::gitrepo::checkout_detach(worktree, expected_parent.id.as_str())?;
    let file = EpochFile {
        parent: Some(expected_parent.id.clone()),
        active_members: new_active_members.clone(),
    };
    crate::storage::atomic_write(&worktree.join(EPOCH_FILE), &file.canonical_bytes())?;
    crate::gitrepo::add_all(worktree)?;
    let commit = crate::gitrepo::commit(worktree, "agent-registry: epoch transition")?;
    let parents = crate::gitrepo::parents_of(repo, &commit)?;
    if parents != vec![expected_parent.id.as_str().to_string()] {
        return Err(invalid(format!(
            "registry commit {commit} does not have exactly one parent equal to {}",
            expected_parent.id
        )));
    }
    // `update-ref`, not `branch -f`: see `stream::create_root_commit`'s
    // identical comment -- `REGISTRY_REF` is already fully qualified
    // (`refs/heads/agent-registry`), and `git branch -f` does not accept
    // that form as the ref itself.
    crate::gitrepo::run_ok(repo, &["update-ref", REGISTRY_REF, &commit])?;
    Ok(expected_parent.child(ObjectId::parse(commit)?, new_active_members))
}

/// Proposes coordinator succession for `target`'s stream custody (section
/// 2.3, gate 19): rebinds it to `proposer`'s own host (`new_host`),
/// incrementing `coordinator_custody_epoch` by exactly one. `proposer` --
/// who becomes the new custodian -- must be either `target`'s own
/// pre-authorized `standby`, or any agent already holding `Role::Coordinator`
/// in `expected_parent`: "the standby or an authorized coordinator on
/// another host." Anyone else is refused before a transition is even
/// attempted, unlike `propose_transition` (used for ordinary registration/
/// retirement/reassignment), which trusts its caller entirely -- custody
/// theft is exactly what this check exists to prevent.
///
/// This alone is what makes gate 19's "exactly once" true: once this
/// transition lands, the *old* `(host, coordinator_custody_epoch)` pair no
/// longer matches `target`'s binding, so `authorize_stream_write` -- called
/// by every future `drain_outbox`/`publish_stream` -- fails closed for the
/// superseded custodian even if it comes back and tries to keep publishing.
/// "Resuming the preserved outbox" needs no separate mechanism: `proposer`'s
/// very next `drain_outbox` call for `target` simply reads whatever is
/// already sitting in `target`'s local outbox directory, unconditionally.
pub fn propose_custody_succession(
    repo: &Path,
    expected_parent: &RosterEpoch,
    proposer: &Agent,
    target: &Agent,
    new_host: Short,
    worktree: &Path,
) -> AbResult<RosterEpoch> {
    let binding = expected_parent.active_members.get(target).ok_or_else(|| {
        invalid(format!(
            "{target} is not an active member of roster epoch {} -- check the agent name is \
             correct, or register it first if it genuinely doesn't exist yet",
            expected_parent.id
        ))
    })?;
    let proposer_is_standby = binding.standby.as_ref() == Some(proposer);
    if !proposer_is_standby && !is_coordinator(expected_parent, proposer) {
        return Err(invalid(format!(
            "{proposer} is not authorized to propose succession for {target}: not its \
             pre-authorized standby and not a coordinator in the current epoch"
        )));
    }
    let mut members = expected_parent.active_members.clone();
    members.insert(
        target.clone(),
        MemberBinding {
            role: binding.role,
            host: new_host,
            coordinator_custody_epoch: binding.coordinator_custody_epoch + 1,
            standby: binding.standby.clone(),
        },
    );
    propose_transition(repo, expected_parent, members, worktree)
}

/// Whether `agent` holds `Role::Coordinator` in `epoch` -- the "an
/// authorized coordinator" half of section 2.3's authorization vocabulary,
/// shared by [`propose_custody_succession`] and [`propose_host_rebind`] so
/// the two can never drift apart into two subtly different notions of
/// coordinator authority.
fn is_coordinator(epoch: &RosterEpoch, agent: &Agent) -> bool {
    epoch
        .active_members
        .get(agent)
        .is_some_and(|b| b.role == Role::Coordinator)
}

/// Relabels the `host` of one or more active members in a *single* epoch
/// transition, changing nothing else about any binding.
///
/// This exists because [`propose_custody_succession`] is the wrong tool for
/// a pure relabel, even though it is the only other thing that writes
/// `host`. Succession deliberately (and correctly, for its own purpose)
/// bumps `coordinator_custody_epoch`, which durably records a failover
/// handover in the registry's permanent history; its CLI caller then also
/// drains and publishes the target's outbox. A caller whose only intent is
/// "this identity's `host` label was a placeholder, give it the real value"
/// wants none of that: no fabricated handover in the record, no surprise
/// publication of whatever happened to be queued, and -- when several
/// identities are being relabeled at once -- no window in which the fleet is
/// half-relabeled because one of N sequential epoch transitions failed, or
/// in which an unrelated concurrent registration invalidates the rest of an
/// in-progress loop.
///
/// So: exactly one `propose_transition` covering every named identity,
/// all-or-nothing. `role`, `standby`, and `coordinator_custody_epoch` are
/// carried through verbatim for every binding, and any identity not named in
/// `new_hosts` is untouched.
///
/// Note that a rebind *does* change who may write the rebound identity's
/// stream, because [`authorize_stream_write`] matches on `(host,
/// coordinator_custody_epoch)`: after a rebind the custodian must present
/// the new host label. That is the intended, and unavoidable, consequence of
/// the binding being the authority -- it is a relabel of where custody
/// lives, not a transfer of it, which is exactly why the custody epoch must
/// *not* move.
///
/// Authorization is coordinator-only: the proposer must already hold
/// `Role::Coordinator` in `expected_parent`. Unlike succession, this is not
/// a per-target operation, so `MemberBinding::standby` -- a pre-authorization
/// scoped to one specific binding's *custody takeover*, for the case where
/// "the active coordinator becomes unavailable" (section 2.3) -- has nothing
/// to say about it: a batch naming five identities has no single target
/// whose standby could be consulted, and stretching the standby clause to
/// mean "may also relabel arbitrary other identities' hosts" would widen it
/// well past what it was reviewed and built for. Fleet-wide roster
/// administration is coordinator work.
pub fn propose_host_rebind(
    repo: &Path,
    expected_parent: &RosterEpoch,
    proposer: &Agent,
    new_hosts: &BTreeMap<Agent, Short>,
    worktree: &Path,
) -> AbResult<RosterEpoch> {
    if new_hosts.is_empty() {
        return Err(invalid(
            "no identity was named to rebind -- pass at least one `--set <identity>=<new-host>`",
        ));
    }
    // Checked before membership, unlike `propose_custody_succession`: an
    // unauthorized proposer is refused on its own terms, rather than the
    // refusal depending on whether the names it happened to pick exist.
    if !is_coordinator(expected_parent, proposer) {
        return Err(invalid(format!(
            "{proposer} is not authorized to rebind hosts: not a coordinator in roster epoch {} \
             -- host rebinding is fleet-wide roster administration, so unlike `succeed` it is \
             not additionally open to a target's pre-authorized standby",
            expected_parent.id
        )));
    }
    let mut members = expected_parent.active_members.clone();
    for (target, host) in new_hosts {
        let binding = members.get_mut(target).ok_or_else(|| {
            invalid(format!(
                "{target} is not an active member of roster epoch {} -- check the agent name is \
                 correct, or register it first if it genuinely doesn't exist yet",
                expected_parent.id
            ))
        })?;
        // Only `host`. `role`, `coordinator_custody_epoch`, and `standby`
        // are deliberately left exactly as they were: this is a relabel, not
        // a reassignment and not a handover.
        binding.host = host.clone();
    }
    propose_transition(repo, expected_parent, members, worktree)
}

/// One active identity's binding within a `RosterEpoch`: which host its
/// executor runs on, and which of that host's coordinator custody epochs is
/// authoritative for advancing this identity's stream. Two coordinators can
/// never both hold the same `(host, custody_epoch)` pair for a live agent
/// (gate 7): custody moves only by a registry epoch transition, never by
/// silent takeover.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberBinding {
    pub role: Role,
    pub host: Short,
    pub coordinator_custody_epoch: u64,
    /// A pre-authorized standby for this binding's stream custody (section
    /// 2.3: "Each host may name a pre-authorized standby in that epoch. If
    /// the active coordinator becomes unavailable, the standby or an
    /// authorized coordinator on another host proposes the registry
    /// succession"). `None` means only an existing `Role::Coordinator`
    /// member of the epoch may propose succession for this binding.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub standby: Option<Agent>,
}

/// A single, immutable roster epoch: `id` is the git commit ID of the
/// `agent-registry` commit that created it, so two epochs are never
/// accidentally aliased and an epoch can always be dereferenced back to its
/// exact durable record without a separate numbering scheme.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RosterEpoch {
    pub id: ObjectId,
    pub parent: Option<ObjectId>,
    pub active_members: BTreeMap<Agent, MemberBinding>,
}

impl RosterEpoch {
    /// Applies one membership change (registration, retirement, reassignment,
    /// or coordinator succession) as a new child epoch. The caller supplies
    /// `new_id` (the resulting registry commit's real git object id) only
    /// after actually constructing that commit -- this function computes the
    /// *content* of the new epoch, not the commit itself, since committing is
    /// the coordinator's compare-and-swap responsibility (section 2.3).
    pub fn child(&self, new_id: ObjectId, active_members: BTreeMap<Agent, MemberBinding>) -> Self {
        RosterEpoch {
            id: new_id,
            parent: Some(self.id.clone()),
            active_members,
        }
    }

    pub fn root(id: ObjectId, active_members: BTreeMap<Agent, MemberBinding>) -> Self {
        RosterEpoch {
            id,
            parent: None,
            active_members,
        }
    }

    pub fn is_active_member(&self, agent: &Agent) -> bool {
        self.active_members.contains_key(agent)
    }
}

/// Gate 6/7 precondition, checked before any stream write is attempted: the
/// agent must actually be an active member of the epoch the writer believes
/// is current, and the binding's `(host, coordinator_custody_epoch)` must
/// match the writer's own claimed custody. A stale or duplicate custodian
/// fails this before it ever races on the stream ref itself.
pub fn authorize_stream_write(
    epoch: &RosterEpoch,
    agent: &Agent,
    host: &Short,
    coordinator_custody_epoch: u64,
) -> AbResult<()> {
    let binding = epoch.active_members.get(agent).ok_or_else(|| {
        invalid(format!(
            "{agent} is not an active member of roster epoch {} -- register it first, or \
             re-read the current registry epoch if this one may be stale",
            epoch.id
        ))
    })?;
    if &binding.host != host || binding.coordinator_custody_epoch != coordinator_custody_epoch {
        return Err(invalid(format!(
            "{agent}'s stream custody in epoch {} belongs to host {} at custody epoch {}, not host {host} at custody epoch {coordinator_custody_epoch}",
            epoch.id, binding.host, binding.coordinator_custody_epoch
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn short(s: &str) -> Short {
        Short::parse(s.to_string()).unwrap()
    }

    fn hash(n: u64) -> ObjectId {
        ObjectId::parse(format!("{n:040x}")).unwrap()
    }

    fn binding(role: Role, host: &str, epoch: u64) -> MemberBinding {
        MemberBinding {
            role,
            host: short(host),
            coordinator_custody_epoch: epoch,
            standby: None,
        }
    }

    fn binding_with_standby(role: Role, host: &str, epoch: u64, standby: &Agent) -> MemberBinding {
        MemberBinding {
            standby: Some(standby.clone()),
            ..binding(role, host, epoch)
        }
    }

    #[test]
    fn child_epoch_chains_to_its_parent() {
        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 0));
        let root = RosterEpoch::root(hash(1), members.clone());
        assert_eq!(root.parent, None);

        members.insert(a("bob"), binding(Role::Reviewer, "host1", 0));
        let child = root.child(hash(2), members);
        assert_eq!(child.parent, Some(hash(1)));
        assert!(child.is_active_member(&a("bob")));
    }

    #[test]
    fn authorize_stream_write_accepts_the_bound_custodian() {
        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 3));
        let epoch = RosterEpoch::root(hash(1), members);
        assert!(authorize_stream_write(&epoch, &a("alice"), &short("host1"), 3).is_ok());
    }

    #[test]
    fn authorize_stream_write_rejects_a_non_member() {
        let epoch = RosterEpoch::root(hash(1), BTreeMap::new());
        let err = authorize_stream_write(&epoch, &a("alice"), &short("host1"), 0).unwrap_err();
        assert!(err.to_string().contains("not an active member"), "{err}");
    }

    /// Gate 7: two coordinators cannot both publish for one custody epoch --
    /// a stale custodian (wrong host, or the right host at a superseded
    /// custody epoch number) must fail closed here rather than race on the
    /// stream ref.
    #[test]
    fn authorize_stream_write_rejects_a_stale_or_wrong_custodian() {
        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 3));
        let epoch = RosterEpoch::root(hash(1), members);

        let wrong_host = authorize_stream_write(&epoch, &a("alice"), &short("host2"), 3);
        assert!(wrong_host.is_err());

        let stale_epoch = authorize_stream_write(&epoch, &a("alice"), &short("host1"), 2);
        assert!(stale_epoch.is_err());
    }

    #[test]
    fn active_member_lookup_is_epoch_relative() {
        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 0));
        let root = RosterEpoch::root(hash(1), members.clone());
        // A later epoch adding "bob" must not retroactively make bob a
        // member of the earlier, immutable root epoch.
        members.insert(a("bob"), binding(Role::Reviewer, "host1", 0));
        let _child = root.child(hash(2), members);
        assert!(!root.is_active_member(&a("bob")));
    }

    // --------------------------------------------------------- git I/O

    fn init_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path();
        std::process::Command::new("git")
            .args(["init", "--quiet", "-b", "main"])
            .arg(path)
            .status()
            .unwrap();
        for args in [
            vec!["config", "user.email", "test@example.com"],
            vec!["config", "user.name", "Test"],
        ] {
            std::process::Command::new("git")
                .arg("-C")
                .arg(path)
                .args(args)
                .status()
                .unwrap();
        }
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

    fn test_config(repo: &Path) -> BusConfig {
        let review_from = crate::gitrepo::rev_parse(repo, "HEAD").unwrap();
        BusConfig::new("sha1".to_string(), ObjectId::parse(review_from).unwrap()).unwrap()
    }

    #[test]
    fn read_registry_tip_is_none_before_creation() {
        let repo = init_repo();
        assert_eq!(read_registry_tip(repo.path()).unwrap(), None);
    }

    #[test]
    fn create_root_then_read_epoch_round_trips() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 0));
        let wt = repo.path().join("_wt_root");
        let epoch = create_root(repo.path(), &config, members.clone(), &wt).unwrap();
        assert_eq!(epoch.parent, None);
        assert_eq!(epoch.active_members, members);
        assert_eq!(
            read_registry_tip(repo.path()).unwrap(),
            Some(epoch.id.clone())
        );

        let read_wt = repo.path().join("_wt_read");
        let read_back = read_epoch(repo.path(), &epoch.id, &read_wt).unwrap();
        assert_eq!(read_back, epoch);
    }

    /// Regression test for a Critical, previously-invisible finding: see
    /// `stream::create_root_commit_writes_exactly_the_correctly_named_ref`'s
    /// identical comment. `REGISTRY_REF` is already fully qualified
    /// (`refs/heads/agent-registry`); an earlier version of this function
    /// used `git branch -f REGISTRY_REF <commit>`, which silently created a
    /// double-prefixed `refs/heads/refs/heads/agent-registry` instead --
    /// invisible to every purely-local round trip via `rev-parse`'s own
    /// fallback resolution, but permanently shadowed the moment a real
    /// fetch (e.g. `sync::synced_snapshot`) ever created the correctly
    /// -named ref.
    #[test]
    fn create_root_writes_exactly_the_correctly_named_ref() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 0));
        let wt = repo.path().join("_wt_root");
        create_root(repo.path(), &config, members, &wt).unwrap();

        let out = crate::gitrepo::run(repo.path(), &["for-each-ref", "--format=%(refname)"])
            .unwrap()
            .stdout;
        let refs: Vec<&str> = out.lines().collect();
        assert!(
            refs.contains(&REGISTRY_REF),
            "expected {REGISTRY_REF} among {refs:?}"
        );
        assert!(
            !refs.iter().any(|r| r.contains("refs/heads/refs/heads")),
            "must never create a double-prefixed ref: {refs:?}"
        );
    }

    #[test]
    fn create_root_rejects_a_second_root() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let wt = repo.path().join("_wt_root");
        create_root(repo.path(), &config, BTreeMap::new(), &wt).unwrap();
        let wt2 = repo.path().join("_wt_root2");
        let err = create_root(repo.path(), &config, BTreeMap::new(), &wt2).unwrap_err();
        assert!(
            err.to_string().contains("already has a root epoch"),
            "{err}"
        );
    }

    #[test]
    fn propose_transition_extends_with_exactly_one_new_commit() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 0));
        let wt = repo.path().join("_wt_root");
        let root = create_root(repo.path(), &config, members.clone(), &wt).unwrap();

        members.insert(a("bob"), binding(Role::Reviewer, "host1", 0));
        let transition_wt = repo.path().join("_wt_transition");
        let child =
            propose_transition(repo.path(), &root, members.clone(), &transition_wt).unwrap();
        assert_eq!(child.parent, Some(root.id.clone()));
        assert_eq!(child.active_members, members);
        assert_eq!(
            read_registry_tip(repo.path()).unwrap(),
            Some(child.id.clone())
        );

        let read_wt = repo.path().join("_wt_read");
        let read_back = read_epoch(repo.path(), &child.id, &read_wt).unwrap();
        assert_eq!(read_back, child);
    }

    /// `bus_config.json` is written once, in the root commit only -- this
    /// confirms it is still readable through a *later* epoch's tree (proving
    /// `propose_transition`'s "checkout parent, layer epoch.json on top"
    /// actually carries it forward) and matches what was passed to
    /// `create_root` byte-for-byte.
    #[test]
    fn read_bus_config_is_visible_through_a_later_epoch() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 0));
        let wt = repo.path().join("_wt_root");
        let root = create_root(repo.path(), &config, members.clone(), &wt).unwrap();

        let root_read_wt = repo.path().join("_wt_config_root");
        assert_eq!(
            read_bus_config(repo.path(), &root.id, &root_read_wt).unwrap(),
            config
        );

        members.insert(a("bob"), binding(Role::Reviewer, "host1", 0));
        let transition_wt = repo.path().join("_wt_transition");
        let child = propose_transition(repo.path(), &root, members, &transition_wt).unwrap();

        let child_read_wt = repo.path().join("_wt_config_child");
        assert_eq!(
            read_bus_config(repo.path(), &child.id, &child_read_wt).unwrap(),
            config
        );
    }

    /// The registry's own compare-and-swap guarantee: a proposal against a
    /// stale parent (the registry already moved) must be refused, not
    /// silently rebased through -- the loser re-reads and retries.
    #[test]
    fn propose_transition_rejects_a_stale_expected_parent() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let wt = repo.path().join("_wt_root");
        let root = create_root(repo.path(), &config, BTreeMap::new(), &wt).unwrap();

        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 0));
        let t1 = repo.path().join("_wt_t1");
        propose_transition(repo.path(), &root, members.clone(), &t1).unwrap();

        // `root` is now stale: the registry has already advanced past it.
        let t2 = repo.path().join("_wt_t2");
        let err = propose_transition(repo.path(), &root, members, &t2).unwrap_err();
        assert!(err.to_string().contains("has moved"), "{err}");
    }

    #[test]
    fn propose_transition_fails_before_any_root_exists() {
        let repo = init_repo();
        let phantom_root = RosterEpoch::root(hash(1), BTreeMap::new());
        let wt = repo.path().join("_wt_transition");
        let err = propose_transition(repo.path(), &phantom_root, BTreeMap::new(), &wt).unwrap_err();
        assert!(err.to_string().contains("no root epoch yet"), "{err}");
    }

    // --------------------------------------------------- custody succession

    fn root_with(
        repo: &Path,
        config: &BusConfig,
        members: BTreeMap<Agent, MemberBinding>,
    ) -> RosterEpoch {
        create_root(repo, config, members, &repo.join("_wt_succession_root")).unwrap()
    }

    /// Gate 19's authorization precondition: the pre-authorized standby may
    /// take over, and doing so bumps custody_epoch by exactly one and moves
    /// `host` to the proposer's own.
    #[test]
    fn standby_may_succeed_its_bound_agent() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let alice = a("alice");
        let alice_standby = a("alice-standby");
        let mut members = BTreeMap::new();
        members.insert(
            alice.clone(),
            binding_with_standby(Role::Implementor, "host1", 3, &alice_standby),
        );
        let root = root_with(repo.path(), &config, members);

        let new_epoch = propose_custody_succession(
            repo.path(),
            &root,
            &alice_standby,
            &alice,
            short("host2"),
            &repo.path().join("_wt_succeed"),
        )
        .unwrap();
        let new_binding = &new_epoch.active_members[&alice];
        assert_eq!(new_binding.host, short("host2"));
        assert_eq!(new_binding.coordinator_custody_epoch, 4);
        // The standby carries forward unchanged -- succession doesn't clear
        // pre-authorization for a *future* succession.
        assert_eq!(new_binding.standby, Some(alice_standby));
    }

    /// "...or an authorized coordinator on another host" -- a coordinator
    /// with no standby relationship to the target may still succeed it.
    #[test]
    fn an_existing_coordinator_may_succeed_any_agent() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let alice = a("alice");
        let coord2 = a("coord2");
        let mut members = BTreeMap::new();
        members.insert(alice.clone(), binding(Role::Implementor, "host1", 0));
        members.insert(coord2.clone(), binding(Role::Coordinator, "host2", 0));
        let root = root_with(repo.path(), &config, members);

        let new_epoch = propose_custody_succession(
            repo.path(),
            &root,
            &coord2,
            &alice,
            short("host2"),
            &repo.path().join("_wt_succeed"),
        )
        .unwrap();
        assert_eq!(new_epoch.active_members[&alice].host, short("host2"));
    }

    /// Neither the target's standby nor a coordinator -- an ordinary
    /// implementor cannot unilaterally steal another agent's custody.
    #[test]
    fn an_unauthorized_agent_cannot_propose_succession() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let alice = a("alice");
        let mallory = a("mallory");
        let mut members = BTreeMap::new();
        members.insert(alice.clone(), binding(Role::Implementor, "host1", 0));
        members.insert(mallory.clone(), binding(Role::Implementor, "host3", 0));
        let root = root_with(repo.path(), &config, members);

        let err = propose_custody_succession(
            repo.path(),
            &root,
            &mallory,
            &alice,
            short("host3"),
            &repo.path().join("_wt_succeed"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("is not authorized"), "{err}");
    }

    #[test]
    fn succession_fails_for_a_target_outside_the_epoch() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let coord1 = a("coord1");
        let ghost = a("ghost");
        let mut members = BTreeMap::new();
        members.insert(coord1.clone(), binding(Role::Coordinator, "host1", 0));
        let root = root_with(repo.path(), &config, members);

        let err = propose_custody_succession(
            repo.path(),
            &root,
            &coord1,
            &ghost,
            short("host2"),
            &repo.path().join("_wt_succeed"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("not an active member"), "{err}");
    }

    /// The core of gate 19: once succession lands, the *old* custodian's
    /// claimed `(host, coordinator_custody_epoch)` no longer authorizes
    /// writes for the target -- `authorize_stream_write` fails it closed
    /// even though nothing about the old custodian's own belief changed.
    #[test]
    fn the_superseded_custodian_can_no_longer_authorize_writes() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let alice = a("alice");
        let alice_standby = a("alice-standby");
        let mut members = BTreeMap::new();
        members.insert(
            alice.clone(),
            binding_with_standby(Role::Implementor, "host1", 0, &alice_standby),
        );
        let root = root_with(repo.path(), &config, members);

        let new_epoch = propose_custody_succession(
            repo.path(),
            &root,
            &alice_standby,
            &alice,
            short("host2"),
            &repo.path().join("_wt_succeed"),
        )
        .unwrap();

        // The old custodian (host1, custody epoch 0) still believes it can
        // write -- authorize_stream_write must refuse it against the new
        // epoch.
        let err = authorize_stream_write(&new_epoch, &alice, &short("host1"), 0).unwrap_err();
        assert!(err.to_string().contains("belongs to host"), "{err}");
        // The new custodian succeeds.
        authorize_stream_write(&new_epoch, &alice, &short("host2"), 1).unwrap();
    }

    // --------------------------------------------------------- host rebind

    fn rebinds(pairs: &[(&str, &str)]) -> BTreeMap<Agent, Short> {
        pairs
            .iter()
            .map(|(agent, host)| (a(agent), short(host)))
            .collect()
    }

    /// The whole point of this primitive existing separately from
    /// `propose_custody_succession`: `host` moves, and *nothing else* about
    /// the binding does -- most importantly not `coordinator_custody_epoch`,
    /// which succession would have bumped, falsely recording a failover
    /// handover that never happened.
    #[test]
    fn rebind_changes_only_the_host_of_the_named_binding() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let coord1 = a("coord1");
        let alice = a("alice");
        let alice_standby = a("alice-standby");
        let mut members = BTreeMap::new();
        members.insert(coord1.clone(), binding(Role::Coordinator, "host1", 0));
        members.insert(
            alice.clone(),
            binding_with_standby(Role::Implementor, "migration", 7, &alice_standby),
        );
        let root = root_with(repo.path(), &config, members);

        let new_epoch = propose_host_rebind(
            repo.path(),
            &root,
            &coord1,
            &rebinds(&[("alice", "host-a")]),
            &repo.path().join("_wt_rebind"),
        )
        .unwrap();

        let rebound = &new_epoch.active_members[&alice];
        assert_eq!(rebound.host, short("host-a"));
        assert_eq!(rebound.coordinator_custody_epoch, 7);
        assert_eq!(rebound.role, Role::Implementor);
        assert_eq!(rebound.standby, Some(alice_standby));
        // Exactly one new epoch, chained to the one it was proposed against.
        assert_eq!(new_epoch.parent, Some(root.id.clone()));
        assert_eq!(
            read_registry_tip(repo.path()).unwrap(),
            Some(new_epoch.id.clone())
        );
        // Everyone not named is byte-identical to before.
        assert_eq!(
            new_epoch.active_members[&coord1],
            root.active_members[&coord1]
        );
    }

    /// The batch guarantee: N identities relabeled produce exactly *one*
    /// child epoch covering all of them, not N chained epochs -- so a
    /// partial failure can never leave the fleet half-relabeled.
    #[test]
    fn rebind_covers_every_named_identity_in_one_epoch() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let coord1 = a("coord1");
        let mut members = BTreeMap::new();
        members.insert(coord1.clone(), binding(Role::Coordinator, "migration", 0));
        members.insert(a("alice"), binding(Role::Implementor, "migration", 2));
        members.insert(a("bob"), binding(Role::Reviewer, "migration", 0));
        members.insert(a("carol"), binding(Role::Implementor, "migration", 0));
        let root = root_with(repo.path(), &config, members);

        let new_epoch = propose_host_rebind(
            repo.path(),
            &root,
            &coord1,
            &rebinds(&[("alice", "host-a"), ("bob", "host-b"), ("coord1", "host-c")]),
            &repo.path().join("_wt_rebind"),
        )
        .unwrap();

        assert_eq!(new_epoch.active_members[&a("alice")].host, short("host-a"));
        assert_eq!(new_epoch.active_members[&a("bob")].host, short("host-b"));
        assert_eq!(new_epoch.active_members[&a("coord1")].host, short("host-c"));
        // Unnamed: untouched.
        assert_eq!(
            new_epoch.active_members[&a("carol")].host,
            short("migration")
        );
        // Custody epochs all carried through verbatim.
        assert_eq!(
            new_epoch.active_members[&a("alice")].coordinator_custody_epoch,
            2
        );
        // One epoch, one parent hop -- not three chained transitions.
        assert_eq!(new_epoch.parent, Some(root.id.clone()));
        let chain = read_epoch_chain(
            repo.path(),
            &new_epoch.id,
            &repo.path().join("_wt_rebind_chain"),
        )
        .unwrap();
        assert_eq!(chain.len(), 2, "root + exactly one rebind epoch: {chain:?}");
    }

    #[test]
    fn rebind_rejects_a_non_coordinator_proposer() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let mallory = a("mallory");
        let mut members = BTreeMap::new();
        members.insert(a("coord1"), binding(Role::Coordinator, "host1", 0));
        members.insert(a("alice"), binding(Role::Implementor, "migration", 0));
        members.insert(mallory.clone(), binding(Role::Implementor, "host3", 0));
        let root = root_with(repo.path(), &config, members);

        let err = propose_host_rebind(
            repo.path(),
            &root,
            &mallory,
            &rebinds(&[("alice", "host-a")]),
            &repo.path().join("_wt_rebind"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("is not authorized"), "{err}");
        // Refused *before* a transition is attempted: the registry did not
        // move at all.
        assert_eq!(read_registry_tip(repo.path()).unwrap(), Some(root.id));
    }

    /// Unlike `succeed`, a target's pre-authorized standby is deliberately
    /// *not* enough here: `standby` authorizes a custody takeover of one
    /// specific binding, not fleet-wide host relabeling.
    #[test]
    fn rebind_rejects_the_targets_standby() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let alice = a("alice");
        let alice_standby = a("alice-standby");
        let mut members = BTreeMap::new();
        members.insert(a("coord1"), binding(Role::Coordinator, "host1", 0));
        members.insert(
            alice.clone(),
            binding_with_standby(Role::Implementor, "migration", 0, &alice_standby),
        );
        members.insert(
            alice_standby.clone(),
            binding(Role::Implementor, "host-b", 0),
        );
        let root = root_with(repo.path(), &config, members);

        let err = propose_host_rebind(
            repo.path(),
            &root,
            &alice_standby,
            &rebinds(&[("alice", "host-a")]),
            &repo.path().join("_wt_rebind"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("is not authorized"), "{err}");
        assert!(err.to_string().contains("standby"), "{err}");
    }

    /// All-or-nothing: one unknown name in a batch refuses the *whole*
    /// batch, so the identities that did exist are not quietly relabeled
    /// while the caller's typo goes unmentioned.
    #[test]
    fn rebind_rejects_a_target_outside_the_epoch_without_moving_the_registry() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let coord1 = a("coord1");
        let mut members = BTreeMap::new();
        members.insert(coord1.clone(), binding(Role::Coordinator, "host1", 0));
        members.insert(a("alice"), binding(Role::Implementor, "migration", 0));
        let root = root_with(repo.path(), &config, members);

        let err = propose_host_rebind(
            repo.path(),
            &root,
            &coord1,
            &rebinds(&[("alice", "host-a"), ("ghost", "host-z")]),
            &repo.path().join("_wt_rebind"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("ghost"), "{err}");
        assert!(err.to_string().contains("not an active member"), "{err}");
        assert_eq!(
            read_registry_tip(repo.path()).unwrap(),
            Some(root.id.clone())
        );
        // alice really is still on the placeholder host.
        let read_back = read_epoch(repo.path(), &root.id, &repo.path().join("_wt_read")).unwrap();
        assert_eq!(
            read_back.active_members[&a("alice")].host,
            short("migration")
        );
    }

    #[test]
    fn rebind_rejects_an_empty_batch() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let coord1 = a("coord1");
        let mut members = BTreeMap::new();
        members.insert(coord1.clone(), binding(Role::Coordinator, "host1", 0));
        let root = root_with(repo.path(), &config, members);

        let err = propose_host_rebind(
            repo.path(),
            &root,
            &coord1,
            &BTreeMap::new(),
            &repo.path().join("_wt_rebind"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("at least one"), "{err}");
    }

    /// The registry's compare-and-swap applies to a rebind exactly as it
    /// does to any other transition: a proposal against an already-superseded
    /// parent is refused, not silently rebased through.
    #[test]
    fn rebind_rejects_a_stale_expected_parent() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let coord1 = a("coord1");
        let mut members = BTreeMap::new();
        members.insert(coord1.clone(), binding(Role::Coordinator, "host1", 0));
        members.insert(a("alice"), binding(Role::Implementor, "migration", 0));
        let root = root_with(repo.path(), &config, members.clone());

        // Somebody else advances the registry first.
        members.insert(a("bob"), binding(Role::Reviewer, "host2", 0));
        propose_transition(repo.path(), &root, members, &repo.path().join("_wt_other")).unwrap();

        let err = propose_host_rebind(
            repo.path(),
            &root,
            &coord1,
            &rebinds(&[("alice", "host-a")]),
            &repo.path().join("_wt_rebind"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("has moved"), "{err}");
    }

    /// A rebind relabels *where* custody lives without moving custody: the
    /// custody epoch is unchanged, so the same custodian keeps writing --
    /// but now presenting the new host label, and no longer the old one.
    /// (Contrast `the_superseded_custodian_can_no_longer_authorize_writes`,
    /// where the epoch number moves too.)
    #[test]
    fn a_rebound_binding_authorizes_the_new_host_at_the_unchanged_custody_epoch() {
        let repo = init_repo();
        let config = test_config(repo.path());
        let coord1 = a("coord1");
        let alice = a("alice");
        let mut members = BTreeMap::new();
        members.insert(coord1.clone(), binding(Role::Coordinator, "host1", 0));
        members.insert(alice.clone(), binding(Role::Implementor, "migration", 4));
        let root = root_with(repo.path(), &config, members);

        let new_epoch = propose_host_rebind(
            repo.path(),
            &root,
            &coord1,
            &rebinds(&[("alice", "host-a")]),
            &repo.path().join("_wt_rebind"),
        )
        .unwrap();

        authorize_stream_write(&new_epoch, &alice, &short("host-a"), 4).unwrap();
        let stale = authorize_stream_write(&new_epoch, &alice, &short("migration"), 4).unwrap_err();
        assert!(stale.to_string().contains("belongs to host"), "{stale}");
    }
}
