//! Causal frontiers (docs/AGENT_COORDINATION_EVOLUTION.md section 2.2).
//!
//! Version one's `Envelope.observed` was a single commit ID: the whole-bus
//! branch tip at publish time, giving a total order for "what did this event
//! see." Version two has no such branch, so an event's causal position is
//! instead a byte-sorted map from agent identity to an exact stream commit
//! and the last event ID it had consumed from that stream -- the `Observed
//! Frontier` below.
//!
//! Most events use a *sparse* frontier naming only the streams their
//! references and authority actually need. An event that grants merge
//! authority, reassigns custody, activates a schema, resolves an all-active
//! audience, or makes another fleet-wide decision instead uses a *complete*
//! frontier: exactly the active member set of one named `RosterEpoch`, no
//! more and no fewer. This is historical completeness relative to a named,
//! immutable epoch -- not a claim to have observed "the world now" -- so a
//! later registration can never retroactively invalidate an earlier
//! authority event's already-complete frontier.

use crate::error::{invalid, AbResult};
use crate::registry::RosterEpoch;
use crate::scalars::{Agent, EventId, ObjectId};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum FrontierKind {
    Sparse,
    Complete,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrontierEntry {
    pub agent: Agent,
    pub stream_tip: ObjectId,
    pub through: EventId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservedFrontier {
    pub kind: FrontierKind,
    pub roster_epoch: ObjectId,
    pub entries: BTreeMap<Agent, FrontierEntry>,
}

impl ObservedFrontier {
    pub fn sparse(roster_epoch: ObjectId, entries: impl IntoIterator<Item = FrontierEntry>) -> Self {
        ObservedFrontier {
            kind: FrontierKind::Sparse,
            roster_epoch,
            entries: entries.into_iter().map(|e| (e.agent.clone(), e)).collect(),
        }
    }

    /// Gate 5: builds a complete frontier for `epoch` from exactly its
    /// active member set. Fails if `stream_tips` is missing an active
    /// member or names an agent the epoch does not recognize, so a
    /// structurally-complete frontier can never omit or misstate membership.
    pub fn complete(
        epoch: &RosterEpoch,
        stream_tips: impl IntoIterator<Item = FrontierEntry>,
    ) -> AbResult<Self> {
        let entries: BTreeMap<Agent, FrontierEntry> =
            stream_tips.into_iter().map(|e| (e.agent.clone(), e)).collect();
        let declared: BTreeSet<&Agent> = entries.keys().collect();
        let expected: BTreeSet<&Agent> = epoch.active_members.keys().collect();
        if declared != expected {
            let missing: Vec<_> = expected.difference(&declared).map(|a| a.as_str()).collect();
            let extra: Vec<_> = declared.difference(&expected).map(|a| a.as_str()).collect();
            return Err(invalid(format!(
                "complete frontier for epoch {} does not match its exact active member set (missing: {missing:?}, extra: {extra:?})",
                epoch.id
            )));
        }
        Ok(ObservedFrontier {
            kind: FrontierKind::Complete,
            roster_epoch: epoch.id.clone(),
            entries,
        })
    }

    /// Gate 5: re-validates a frontier already marked complete against the
    /// exact epoch it claims -- used at read time (e.g. replaying a stream)
    /// where the frontier was constructed elsewhere and must be re-checked
    /// rather than trusted.
    pub fn validate_complete(&self, epoch: &RosterEpoch) -> AbResult<()> {
        if self.kind != FrontierKind::Complete {
            return Err(invalid("frontier is not marked complete"));
        }
        if self.roster_epoch != epoch.id {
            return Err(invalid(format!(
                "frontier names roster epoch {} but epoch {} was supplied for validation",
                self.roster_epoch, epoch.id
            )));
        }
        let declared: BTreeSet<&Agent> = self.entries.keys().collect();
        let expected: BTreeSet<&Agent> = epoch.active_members.keys().collect();
        if declared != expected {
            let missing: Vec<_> = expected.difference(&declared).map(|a| a.as_str()).collect();
            let extra: Vec<_> = declared.difference(&expected).map(|a| a.as_str()).collect();
            return Err(invalid(format!(
                "complete frontier for epoch {} does not match its exact active member set (missing: {missing:?}, extra: {extra:?})",
                epoch.id
            )));
        }
        Ok(())
    }

    /// Gate 4: a cross-agent event reference must occur at or before the
    /// referenced agent's frontier entry. Same-agent causality (an event
    /// referencing an earlier event in its own author's stream) never needs
    /// a frontier entry at all -- it follows the stream's own contiguous
    /// sequence, checked elsewhere.
    pub fn validate_reference(&self, referenced: &EventId) -> AbResult<()> {
        let agent = referenced.agent();
        let entry = self.entries.get(&agent).ok_or_else(|| {
            invalid(format!(
                "reference to {referenced} names an agent absent from the declared frontier"
            ))
        })?;
        if referenced.seq() > entry.through.seq() {
            return Err(invalid(format!(
                "reference to {referenced} occurs after the declared frontier's {agent} position ({})",
                entry.through
            )));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::registry::{MemberBinding, Role};
    use crate::scalars::Short;

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn hash(n: u64) -> ObjectId {
        ObjectId::parse(format!("{n:040x}")).unwrap()
    }

    fn eid(agent: &Agent, seq: u64) -> EventId {
        EventId::new(agent, seq)
    }

    fn entry(agent: &Agent, tip: u64, through_seq: u64) -> FrontierEntry {
        FrontierEntry {
            agent: agent.clone(),
            stream_tip: hash(tip),
            through: eid(agent, through_seq),
        }
    }

    fn epoch_with(members: &[&str]) -> RosterEpoch {
        let mut active_members = BTreeMap::new();
        for m in members {
            active_members.insert(
                a(m),
                MemberBinding {
                    role: Role::Implementor,
                    host: Short::parse("host1".to_string()).unwrap(),
                    coordinator_custody_epoch: 0,
                },
            );
        }
        RosterEpoch::root(hash(999), active_members)
    }

    #[test]
    fn validate_reference_accepts_a_reference_at_or_before_the_frontier() {
        let bob = a("bob");
        let frontier = ObservedFrontier::sparse(hash(1), [entry(&bob, 5, 10)]);
        assert!(frontier.validate_reference(&eid(&bob, 10)).is_ok());
        assert!(frontier.validate_reference(&eid(&bob, 3)).is_ok());
    }

    /// Gate 4: a reference past the declared frontier position must be
    /// rejected -- the author cannot causally depend on something it never
    /// declared having observed.
    #[test]
    fn validate_reference_rejects_a_reference_past_the_frontier() {
        let bob = a("bob");
        let frontier = ObservedFrontier::sparse(hash(1), [entry(&bob, 5, 10)]);
        let err = frontier.validate_reference(&eid(&bob, 11)).unwrap_err();
        assert!(err.to_string().contains("occurs after"), "{err}");
    }

    /// Gate 4: referencing an agent absent from the frontier entirely (not
    /// merely behind it) must also be rejected, not silently treated as "no
    /// constraint."
    #[test]
    fn validate_reference_rejects_an_agent_absent_from_the_frontier() {
        let frontier = ObservedFrontier::sparse(hash(1), []);
        let err = frontier
            .validate_reference(&eid(&a("carol"), 0))
            .unwrap_err();
        assert!(err.to_string().contains("absent from the declared frontier"), "{err}");
    }

    #[test]
    fn complete_accepts_exactly_the_active_member_set() {
        let epoch = epoch_with(&["alice", "bob"]);
        let frontier = ObservedFrontier::complete(
            &epoch,
            [entry(&a("alice"), 1, 0), entry(&a("bob"), 2, 0)],
        )
        .unwrap();
        assert_eq!(frontier.kind, FrontierKind::Complete);
        assert_eq!(frontier.roster_epoch, epoch.id);
    }

    /// Gate 5: an authority event with a complete frontier missing one
    /// member of its named roster epoch is rejected.
    #[test]
    fn complete_rejects_a_frontier_missing_an_active_member() {
        let epoch = epoch_with(&["alice", "bob"]);
        let err = ObservedFrontier::complete(&epoch, [entry(&a("alice"), 1, 0)]).unwrap_err();
        assert!(err.to_string().contains("missing"), "{err}");
        assert!(err.to_string().contains("bob"), "{err}");
    }

    /// The mirror case: a purported member the epoch does not recognize
    /// must also be rejected, not silently accepted as harmless extra data.
    #[test]
    fn complete_rejects_an_extra_member_the_epoch_does_not_recognize() {
        let epoch = epoch_with(&["alice"]);
        let err = ObservedFrontier::complete(
            &epoch,
            [entry(&a("alice"), 1, 0), entry(&a("mallory"), 2, 0)],
        )
        .unwrap_err();
        assert!(err.to_string().contains("extra"), "{err}");
        assert!(err.to_string().contains("mallory"), "{err}");
    }

    /// Gate 5's other half: a *later* registration must not retroactively
    /// invalidate an already-complete frontier built against an earlier,
    /// immutable epoch. Since `epoch_with` returns a root epoch and we never
    /// mutate it, re-validating the same frontier against the same object
    /// after conceptually "more time has passed" must still succeed.
    #[test]
    fn validate_complete_is_stable_against_a_later_registration() {
        let epoch = epoch_with(&["alice"]);
        let frontier = ObservedFrontier::complete(&epoch, [entry(&a("alice"), 1, 0)]).unwrap();
        // A later epoch adds bob; the original epoch object (and anything
        // that already cited it) is untouched and still validates.
        let mut grown = epoch.active_members.clone();
        grown.insert(
            a("bob"),
            MemberBinding {
                role: Role::Reviewer,
                host: Short::parse("host1".to_string()).unwrap(),
                coordinator_custody_epoch: 0,
            },
        );
        let _later_epoch = epoch.child(hash(1000), grown);
        assert!(frontier.validate_complete(&epoch).is_ok());
    }

    #[test]
    fn validate_complete_rejects_a_frontier_marked_sparse() {
        let epoch = epoch_with(&["alice"]);
        let frontier = ObservedFrontier::sparse(epoch.id.clone(), [entry(&a("alice"), 1, 0)]);
        let err = frontier.validate_complete(&epoch).unwrap_err();
        assert!(err.to_string().contains("not marked complete"), "{err}");
    }

    #[test]
    fn validate_complete_rejects_a_mismatched_epoch_id() {
        let epoch = epoch_with(&["alice"]);
        let other_epoch = epoch_with(&["alice"]); // same members, different id (hash(999) both -- construct distinct id)
        let frontier = ObservedFrontier::complete(&epoch, [entry(&a("alice"), 1, 0)]).unwrap();
        // Force a distinct id on the "other" epoch to prove id, not content, is checked.
        let mut other_epoch = other_epoch;
        other_epoch.id = hash(1001);
        let err = frontier.validate_complete(&other_epoch).unwrap_err();
        assert!(err.to_string().contains("names roster epoch"), "{err}");
    }
}
