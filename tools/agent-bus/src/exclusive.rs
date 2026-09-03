//! Order-independent resolution for exclusive-transition races
//! (docs/AGENT_COORDINATION_EVOLUTION.md gates 3, 15, 16).
//!
//! Version one decided who wins a race for one predecessor (e.g. two
//! competing dispositions of the same issue assignment) by processing
//! commits in the single shared branch's fixed order: the first transition
//! walked for a given key was optimistically applied; a later one that had
//! not causally observed it was recorded as concurrent, resetting the
//! earlier one back to a neutral "contested" state pending an explicit
//! `lifecycle.conflict_resolved`. That rule only ever produced one
//! deterministic answer because commit order *was* a canonical, globally
//! agreed-upon fact -- "whoever was walked first" is well-defined only when
//! there is one true walk order.
//!
//! Version two has no such canonical order across independent per-agent
//! streams. Two hosts reducing the exact same set of events in a different
//! internal processing order must still converge to the same answer (gate
//! 16), and incremental replay must match cold replay exactly (gate 15).
//!
//! The fix: a candidate is rejected outright (not merely "loses") if its own
//! frontier causally observed an existing member of the group -- exactly
//! v1's rule, just checked via the frontier instead of a commit index. What
//! changes is what happens to the *surviving* candidates: by construction,
//! every survivor is pairwise non-observing of every other (anything that
//! observed a survivor would itself have been rejected), so there is no
//! causal order left to exploit. The winner among a multi-member group is
//! instead a pure, order-independent function of the group's *membership*
//! (currently: its smallest `EventId`) -- recomputing it from the same final
//! set always gives the same answer, however the set was assembled.

use crate::error::{invalid, AbResult};
use crate::scalars::EventId;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Default)]
pub struct ExclusiveTracker {
    groups: BTreeMap<String, BTreeSet<EventId>>,
    resolved: BTreeMap<String, EventId>,
}

impl ExclusiveTracker {
    /// Records `candidate` as one more claim on `key`, rejecting it outright
    /// if it causally observed (per `observes`) an existing member of the
    /// group or the key's explicit resolution, if any. `observes(other)`
    /// must answer "did `candidate`'s declared frontier see `other`,"
    /// independent of processing order -- typically `ObservedFrontier::
    /// validate_reference` succeeding.
    pub fn record(
        &mut self,
        key: &str,
        candidate: &EventId,
        observes: impl Fn(&EventId) -> bool,
    ) -> AbResult<()> {
        if let Some(winner) = self.resolved.get(key) {
            if !observes(winner) {
                return Err(invalid(format!(
                    "{candidate}: predecessor already has a coordinator-resolved disposition ({winner})"
                )));
            }
            return Err(invalid(format!(
                "{candidate}: predecessor was already resolved ({winner}); this is forward progress, \
                 not a new exclusive claim, and does not belong in this tracker"
            )));
        }
        let group = self.groups.entry(key.to_string()).or_default();
        for existing in group.iter() {
            if observes(existing) {
                return Err(invalid(format!(
                    "{candidate}: predecessor already causally observed a disposition ({existing})"
                )));
            }
        }
        group.insert(candidate.clone());
        Ok(())
    }

    /// Explicitly resolves `key` to `winner` (a `lifecycle.conflict_resolved`
    /// -equivalent event). `winner` must already be a member of the group
    /// (or the sole member of a still-unrecorded group is not required --
    /// resolution can name any candidate that was validly recorded).
    pub fn resolve(&mut self, key: &str, winner: EventId) -> AbResult<()> {
        if self.resolved.contains_key(key) {
            return Err(invalid(format!(
                "{key}: already has a coordinator-resolved disposition"
            )));
        }
        let group = self.groups.get(key);
        if !group.map(|g| g.contains(&winner)).unwrap_or(false) {
            return Err(invalid(format!(
                "{winner} was never recorded as a candidate for {key}"
            )));
        }
        self.resolved.insert(key.to_string(), winner);
        Ok(())
    }

    /// The event whose effect should currently be applied for `key`, or
    /// `None` if the group is genuinely contested (2+ mutually-concurrent
    /// candidates, no explicit resolution yet). A pure function of the
    /// tracker's current membership -- recomputing it after inserting the
    /// same final set of candidates in any order always gives the same
    /// answer (gate 16).
    pub fn winner(&self, key: &str) -> Option<EventId> {
        if let Some(w) = self.resolved.get(key) {
            return Some(w.clone());
        }
        let group = self.groups.get(key)?;
        if group.len() == 1 {
            group.iter().next().cloned()
        } else {
            None
        }
    }

    /// True if `id` is a member of some *other* still-contested group (2+
    /// candidates, no resolution, `id` isn't `winner()`). Mirrors v1's
    /// `predecessor_is_contested`: a new transition must not be allowed to
    /// confirm itself by chaining off `id` while `id`'s own foundation is
    /// still an open race.
    pub fn is_contested(&self, id: &EventId) -> bool {
        self.groups.iter().any(|(key, group)| {
            group.len() > 1 && group.contains(id) && self.winner(key).as_ref() != Some(id)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a(name: &str) -> crate::scalars::Agent {
        crate::scalars::Agent::parse(name.to_string()).unwrap()
    }

    fn eid(agent: &str, seq: u64) -> EventId {
        EventId::new(&a(agent), seq)
    }

    fn none_observed(_: &EventId) -> bool {
        false
    }

    #[test]
    fn a_lone_candidate_wins() {
        let mut t = ExclusiveTracker::default();
        t.record("issue:1", &eid("alice", 0), none_observed).unwrap();
        assert_eq!(t.winner("issue:1"), Some(eid("alice", 0)));
    }

    /// Gate 3: two candidates from the same causal predecessor (neither
    /// observed the other) reduce to the documented lifecycle conflict --
    /// no winner until an explicit resolution.
    #[test]
    fn two_mutually_concurrent_candidates_are_contested() {
        let mut t = ExclusiveTracker::default();
        t.record("issue:1", &eid("alice", 0), none_observed).unwrap();
        t.record("issue:1", &eid("bob", 0), none_observed).unwrap();
        assert_eq!(t.winner("issue:1"), None);
    }

    /// The core order-independence property (gate 16): the same final set
    /// of mutually-concurrent candidates, recorded in either order, must
    /// resolve to the identical winner.
    #[test]
    fn winner_is_independent_of_recording_order() {
        let candidates = [eid("carol", 0), eid("alice", 0), eid("bob", 0)];
        let mut forward = ExclusiveTracker::default();
        for c in &candidates {
            forward.record("issue:1", c, none_observed).unwrap();
        }
        let mut reverse = ExclusiveTracker::default();
        for c in candidates.iter().rev() {
            reverse.record("issue:1", c, none_observed).unwrap();
        }
        assert_eq!(forward.winner("issue:1"), reverse.winner("issue:1"));
        // Three mutually-concurrent candidates: still contested (>1
        // member), not merely "whichever was recorded last."
        assert_eq!(forward.winner("issue:1"), None);
    }

    /// A candidate that causally observed an existing group member must be
    /// rejected outright, not merely lose -- it should have built forward
    /// progress on the observed disposition, not raced it.
    #[test]
    fn a_candidate_observing_an_existing_member_is_rejected() {
        let mut t = ExclusiveTracker::default();
        let first = eid("alice", 0);
        t.record("issue:1", &first, none_observed).unwrap();
        let err = t
            .record("issue:1", &eid("bob", 0), |other| *other == first)
            .unwrap_err();
        assert!(err.to_string().contains("already causally observed"), "{err}");
    }

    #[test]
    fn resolve_picks_the_named_winner_regardless_of_which_arrived_first() {
        let mut t = ExclusiveTracker::default();
        let alice = eid("alice", 0);
        let bob = eid("bob", 0);
        t.record("issue:1", &alice, none_observed).unwrap();
        t.record("issue:1", &bob, none_observed).unwrap();
        assert_eq!(t.winner("issue:1"), None);
        t.resolve("issue:1", bob.clone()).unwrap();
        assert_eq!(t.winner("issue:1"), Some(bob));
    }

    #[test]
    fn resolve_rejects_a_winner_never_recorded_as_a_candidate() {
        let mut t = ExclusiveTracker::default();
        t.record("issue:1", &eid("alice", 0), none_observed).unwrap();
        let err = t.resolve("issue:1", eid("mallory", 0)).unwrap_err();
        assert!(err.to_string().contains("never recorded"), "{err}");
    }

    #[test]
    fn resolve_rejects_a_second_resolution_of_the_same_key() {
        let mut t = ExclusiveTracker::default();
        let alice = eid("alice", 0);
        t.record("issue:1", &alice, none_observed).unwrap();
        t.resolve("issue:1", alice.clone()).unwrap();
        let err = t.resolve("issue:1", alice).unwrap_err();
        assert!(err.to_string().contains("already has a coordinator-resolved"), "{err}");
    }

    /// Once a key is resolved, any further `record` attempt is rejected --
    /// whether or not it observed the winner -- since ordinary forward
    /// progress on a resolved predecessor is a different code path
    /// entirely, not another exclusive claim.
    #[test]
    fn record_after_resolution_is_always_rejected() {
        let mut t = ExclusiveTracker::default();
        let alice = eid("alice", 0);
        t.record("issue:1", &alice, none_observed).unwrap();
        t.resolve("issue:1", alice.clone()).unwrap();

        let observing_the_winner = t.record("issue:1", &eid("bob", 0), |o| *o == alice);
        assert!(observing_the_winner.is_err());

        let not_observing_it = t.record("issue:1", &eid("carol", 0), none_observed);
        assert!(not_observing_it.is_err());
    }

    #[test]
    fn is_contested_is_true_only_for_members_of_an_unresolved_multi_candidate_group() {
        let mut t = ExclusiveTracker::default();
        let alice = eid("alice", 0);
        let bob = eid("bob", 0);
        t.record("solo:1", &alice, none_observed).unwrap();
        assert!(!t.is_contested(&alice), "a lone candidate is never contested");

        t.record("race:1", &alice, none_observed).unwrap();
        t.record("race:1", &bob, none_observed).unwrap();
        assert!(t.is_contested(&alice));
        assert!(t.is_contested(&bob));

        t.resolve("race:1", alice.clone()).unwrap();
        assert!(!t.is_contested(&alice), "the resolved winner is no longer contested");
        assert!(
            t.is_contested(&bob),
            "a resolved group's loser must never become a trusted foundation for later state, \
             even though the race itself is over"
        );
    }

    #[test]
    fn winner_is_none_for_an_unknown_key() {
        let t = ExclusiveTracker::default();
        assert_eq!(t.winner("nonexistent"), None);
    }
}
