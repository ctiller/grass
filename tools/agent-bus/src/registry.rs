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

use crate::error::{invalid, AbResult};
use crate::scalars::{Agent, ObjectId, Short};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub const REGISTRY_REF: &str = "refs/heads/agent-registry";

/// AGENT_BUS.md's existing three primary roles; unchanged by version two.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Role {
    Coordinator,
    Implementor,
    Reviewer,
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
}
