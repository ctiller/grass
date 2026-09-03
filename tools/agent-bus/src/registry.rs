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

use crate::error::{invalid, AbError, AbResult};
use crate::events::Role;
use crate::scalars::{Agent, ObjectId, Short};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::Path;

pub const REGISTRY_REF: &str = "refs/heads/agent-registry";
const EPOCH_FILE: &str = "epoch.json";

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

/// Creates the registry's root epoch (migration/activation time, section
/// 2.5). Fails if a registry already exists -- there is exactly one root,
/// ever.
pub fn create_root(
    repo: &Path,
    active_members: BTreeMap<Agent, MemberBinding>,
    worktree: &Path,
) -> AbResult<RosterEpoch> {
    if read_registry_tip(repo)?.is_some() {
        return Err(invalid("the agent-registry already has a root epoch"));
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
    crate::gitrepo::add_all(worktree)?;
    let commit = crate::gitrepo::commit(worktree, "agent-registry: root epoch")?;
    crate::gitrepo::run_ok(repo, &["branch", "-f", REGISTRY_REF, &commit])?;
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
    crate::gitrepo::run_ok(repo, &["branch", "-f", REGISTRY_REF, &commit])?;
    Ok(expected_parent.child(ObjectId::parse(commit)?, new_active_members))
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
            "{agent} is not an active member of roster epoch {}",
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

    #[test]
    fn read_registry_tip_is_none_before_creation() {
        let repo = init_repo();
        assert_eq!(read_registry_tip(repo.path()).unwrap(), None);
    }

    #[test]
    fn create_root_then_read_epoch_round_trips() {
        let repo = init_repo();
        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 0));
        let wt = repo.path().join("_wt_root");
        let epoch = create_root(repo.path(), members.clone(), &wt).unwrap();
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

    #[test]
    fn create_root_rejects_a_second_root() {
        let repo = init_repo();
        let wt = repo.path().join("_wt_root");
        create_root(repo.path(), BTreeMap::new(), &wt).unwrap();
        let wt2 = repo.path().join("_wt_root2");
        let err = create_root(repo.path(), BTreeMap::new(), &wt2).unwrap_err();
        assert!(err.to_string().contains("already has a root epoch"), "{err}");
    }

    #[test]
    fn propose_transition_extends_with_exactly_one_new_commit() {
        let repo = init_repo();
        let mut members = BTreeMap::new();
        members.insert(a("alice"), binding(Role::Implementor, "host1", 0));
        let wt = repo.path().join("_wt_root");
        let root = create_root(repo.path(), members.clone(), &wt).unwrap();

        members.insert(a("bob"), binding(Role::Reviewer, "host1", 0));
        let transition_wt = repo.path().join("_wt_transition");
        let child = propose_transition(repo.path(), &root, members.clone(), &transition_wt).unwrap();
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

    /// The registry's own compare-and-swap guarantee: a proposal against a
    /// stale parent (the registry already moved) must be refused, not
    /// silently rebased through -- the loser re-reads and retries.
    #[test]
    fn propose_transition_rejects_a_stale_expected_parent() {
        let repo = init_repo();
        let wt = repo.path().join("_wt_root");
        let root = create_root(repo.path(), BTreeMap::new(), &wt).unwrap();

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
}
