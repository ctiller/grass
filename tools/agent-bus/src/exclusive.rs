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

/// What should happen to a candidate's effect, per
/// `ExclusiveTracker::disposition`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Disposition {
    /// This candidate holds the key uncontested, or a coordinator named it
    /// the winner: apply its effect.
    Applies,
    /// Two or more mutually-concurrent candidates and no resolution yet, so
    /// the predecessor goes back to a conflict state pending one.
    Contested,
    /// A coordinator already resolved this key to someone else. The effect
    /// must not apply, and the predecessor must *not* be reset to contested
    /// -- that would undo the resolution.
    Superseded,
}

#[derive(Debug, Clone, Default)]
pub struct ExclusiveTracker {
    groups: BTreeMap<String, BTreeSet<EventId>>,
    resolved: BTreeMap<String, EventId>,
}

impl ExclusiveTracker {
    /// Records `candidate` as one more claim on `key`.
    ///
    /// Refuses only a second claim from the same agent. It is tempting to
    /// also refuse a candidate that causally observed an existing member --
    /// that was this tracker's original rule, and it reads as the right one
    /// -- but reduction cannot ask that question. `apply::topological_order`
    /// builds its edges from `refs` and each stream's own predecessor, never
    /// from `observed`, so a candidate is routinely applied before the very
    /// event its frontier saw. Refusing on the frontier therefore makes the
    /// answer depend on which of two unordered events a host replayed first,
    /// and with no per-event isolation in `reduce` that is every host unable
    /// to reduce the bus at all.
    ///
    /// What survives is the half that is sound: a stream is single-writer
    /// and gets a predecessor edge, so an agent's own events are ordered
    /// against each other in every extension. An agent publishing a second
    /// exclusive claim on the same predecessor is not a race anybody lost,
    /// and refusing it gives the same answer on every host.
    ///
    /// Everything else is recorded, including a claim that arrives after a
    /// coordinator has resolved the key. The winner stays a pure function of
    /// the final membership (`winner`), so hosts that assembled the same set
    /// in different orders still agree.
    ///
    /// Note what this deliberately does *not* read: `resolved`. An earlier
    /// version answered the same-agent question in two branches, one for a
    /// resolved key and one for an unresolved one, and that reintroduced the
    /// whole defect through the back door. `resolved` is written by a
    /// coordinator's `lifecycle.conflict_resolved` on a *different* stream,
    /// which references the racing candidates but has no edge to a later
    /// claim from one of their agents -- so both orders are valid linear
    /// extensions, and the two branches disagreed about them. With a
    /// resolution naming someone *else*'s candidate the resolved branch fell
    /// through to a plain insert and returned `Ok`; without the resolution
    /// yet applied the unresolved branch found the agent's own earlier claim
    /// and returned `Err`. The author's own host was the permissive case
    /// whenever it had fetched the resolution, so `dry_run` passed, the event
    /// published, and every host that had not fetched the resolution first
    /// then failed to reduce the bus at all -- permanently, the log being
    /// append-only.
    ///
    /// Asking only `groups` restores the single-writer justification above in
    /// full: the same-agent members of a group come solely from that agent's
    /// own stream, which every linear extension orders identically, so the
    /// verdict is the same on every host and in every order. A second claim
    /// on the same predecessor is therefore never publishable rather than
    /// publishable-then-fatal-elsewhere.
    pub fn record(&mut self, key: &str, candidate: &EventId) -> AbResult<()> {
        let group = self.groups.entry(key.to_string()).or_default();
        if let Some(existing) = group.iter().find(|e| e.agent() == candidate.agent()) {
            return Err(invalid(format!(
                "{candidate}: this agent already claimed the same predecessor ({existing}); a \
                 further claim on the same predecessor is forward progress from whichever claim \
                 wins, not a new exclusive claim -- name the winning claim as the predecessor \
                 instead"
            )));
        }
        group.insert(candidate.clone());
        Ok(())
    }

    /// What a caller should do with `candidate`'s effect.
    ///
    /// `winner` alone cannot answer this. Once a coordinator has resolved a
    /// key, a late concurrent candidate is neither the winner nor grounds
    /// for treating the predecessor as contested again -- resetting there
    /// would undo the resolution. That third case is `Superseded`.
    pub fn disposition(&self, key: &str, candidate: &EventId) -> Disposition {
        if let Some(w) = self.resolved.get(key) {
            return if w == candidate {
                Disposition::Applies
            } else {
                Disposition::Superseded
            };
        }
        match self.groups.get(key) {
            Some(g) if g.len() == 1 && g.contains(candidate) => Disposition::Applies,
            _ => Disposition::Contested,
        }
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

    /// Finds the still-unresolved group that *contains* `competing` -- how
    /// `lifecycle.conflict_resolved` locates the predecessor key it names by
    /// its competing set rather than by an internal key string the event
    /// format never exposes.
    ///
    /// Containment, not equality. A coordinator names the racers it could
    /// see, and a further candidate may be published concurrently with the
    /// resolution itself. Requiring an exact match meant such a candidate
    /// made the resolution unfindable, so `lifecycle.conflict_resolved`
    /// returned `Err` on any host that had reduced the newcomer first, while
    /// `record` returned `Err` on any host that reduced it second. That pair
    /// was fatal in *both* orders, not merely order-dependent.
    ///
    /// `groups` is a `BTreeMap`, so where more than one group could match,
    /// the choice is deterministic rather than whichever a hash order
    /// happened to yield.
    pub fn key_for_competing(&self, competing: &BTreeSet<EventId>) -> Option<String> {
        self.groups
            .iter()
            .find(|(key, group)| !self.resolved.contains_key(*key) && competing.is_subset(group))
            .map(|(key, _)| key.clone())
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

    #[test]
    fn a_lone_candidate_wins() {
        let mut t = ExclusiveTracker::default();
        t.record("issue:1", &eid("alice", 0)).unwrap();
        assert_eq!(t.winner("issue:1"), Some(eid("alice", 0)));
    }

    /// Gate 3: two candidates from the same causal predecessor (neither
    /// observed the other) reduce to the documented lifecycle conflict --
    /// no winner until an explicit resolution.
    #[test]
    fn two_mutually_concurrent_candidates_are_contested() {
        let mut t = ExclusiveTracker::default();
        t.record("issue:1", &eid("alice", 0)).unwrap();
        t.record("issue:1", &eid("bob", 0)).unwrap();
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
            forward.record("issue:1", c).unwrap();
        }
        let mut reverse = ExclusiveTracker::default();
        for c in candidates.iter().rev() {
            reverse.record("issue:1", c).unwrap();
        }
        assert_eq!(forward.winner("issue:1"), reverse.winner("issue:1"));
        // Three mutually-concurrent candidates: still contested (>1
        // member), not merely "whichever was recorded last."
        assert_eq!(forward.winner("issue:1"), None);
    }

    /// The sound remnant of the old "observed an existing member" rule: an
    /// agent's own second claim on the same predecessor.
    ///
    /// Streams are single-writer and `apply::topological_order` gives each
    /// one a predecessor edge, so an agent's events are ordered against each
    /// other in every linear extension. Refusing this therefore gives the
    /// same answer on every host. The general frontier-based form did not,
    /// which is why it is gone.
    #[test]
    fn a_second_claim_by_the_same_agent_is_rejected() {
        let mut t = ExclusiveTracker::default();
        t.record("issue:1", &eid("alice", 0)).unwrap();
        let err = t.record("issue:1", &eid("alice", 1)).unwrap_err();
        assert!(
            err.to_string()
                .contains("already claimed the same predecessor"),
            "{err}"
        );
    }

    /// A cross-agent claim is recorded, never refused, however late it is.
    ///
    /// This is the totality property the whole reduction-DoS class turns on:
    /// two agents who never observed each other publish competing claims,
    /// and no ordering of them may make a host fail to reduce.
    #[test]
    fn a_cross_agent_claim_is_always_recorded() {
        let mut t = ExclusiveTracker::default();
        t.record("issue:1", &eid("alice", 0)).unwrap();
        t.record("issue:1", &eid("bob", 0)).unwrap();
        t.record("issue:1", &eid("carol", 0)).unwrap();
        assert_eq!(t.winner("issue:1"), None, "three-way race is contested");
    }

    #[test]
    fn resolve_picks_the_named_winner_regardless_of_which_arrived_first() {
        let mut t = ExclusiveTracker::default();
        let alice = eid("alice", 0);
        let bob = eid("bob", 0);
        t.record("issue:1", &alice).unwrap();
        t.record("issue:1", &bob).unwrap();
        assert_eq!(t.winner("issue:1"), None);
        t.resolve("issue:1", bob.clone()).unwrap();
        assert_eq!(t.winner("issue:1"), Some(bob));
    }

    #[test]
    fn resolve_rejects_a_winner_never_recorded_as_a_candidate() {
        let mut t = ExclusiveTracker::default();
        t.record("issue:1", &eid("alice", 0)).unwrap();
        let err = t.resolve("issue:1", eid("mallory", 0)).unwrap_err();
        assert!(err.to_string().contains("never recorded"), "{err}");
    }

    #[test]
    fn resolve_rejects_a_second_resolution_of_the_same_key() {
        let mut t = ExclusiveTracker::default();
        let alice = eid("alice", 0);
        t.record("issue:1", &alice).unwrap();
        t.resolve("issue:1", alice.clone()).unwrap();
        let err = t.resolve("issue:1", alice).unwrap_err();
        assert!(
            err.to_string()
                .contains("already has a coordinator-resolved"),
            "{err}"
        );
    }

    /// A candidate published concurrently with a resolution is recorded,
    /// and the resolution still decides.
    ///
    /// Refusing it was one half of a pair that was fatal in *both* orders:
    /// a third candidate racing a `lifecycle.conflict_resolved` made this
    /// return `Err` on hosts that reduced the resolution first, while
    /// `key_for_competing`'s exact-match requirement made the resolution
    /// itself unfindable on hosts that reduced the candidate first. Neither
    /// host could reduce the bus at all.
    ///
    /// The candidate's own effect must not apply, but nor may the
    /// predecessor be reset to contested -- that would undo the resolution
    /// -- which is what `Disposition::Superseded` exists to say.
    #[test]
    fn a_candidate_racing_a_resolution_is_recorded_and_superseded() {
        let mut t = ExclusiveTracker::default();
        let alice = eid("alice", 0);
        let bob = eid("bob", 0);
        t.record("issue:1", &alice).unwrap();
        t.record("issue:1", &bob).unwrap();
        t.resolve("issue:1", alice.clone()).unwrap();

        let carol = eid("carol", 0);
        t.record("issue:1", &carol)
            .expect("a concurrent third claim must never be fatal");
        assert_eq!(t.winner("issue:1"), Some(alice.clone()));
        assert_eq!(t.disposition("issue:1", &alice), Disposition::Applies);
        assert_eq!(t.disposition("issue:1", &carol), Disposition::Superseded);
        assert_eq!(t.disposition("issue:1", &bob), Disposition::Superseded);
    }

    /// The same agent doing it, though, is still a caller error -- and
    /// soundly so, for the single-writer reason above.
    #[test]
    fn the_resolved_winners_own_agent_may_not_claim_again() {
        let mut t = ExclusiveTracker::default();
        let alice = eid("alice", 0);
        t.record("issue:1", &alice).unwrap();
        t.resolve("issue:1", alice.clone()).unwrap();
        let err = t.record("issue:1", &eid("alice", 1)).unwrap_err();
        assert!(
            err.to_string()
                .contains("already claimed the same predecessor"),
            "{err}"
        );
    }

    /// The same-agent verdict must not depend on whether a coordinator's
    /// resolution -- on a *different* stream, with no edge to this claim --
    /// happened to be replayed first.
    ///
    /// The failing case was a resolution naming somebody *else*'s candidate:
    /// `record` used to take a separate resolved-key branch that only refused
    /// the resolved winner's own agent, so alice's second claim was `Ok` once
    /// bob had been declared the winner and `Err` before that. Both orders are
    /// valid linear extensions and `reduce` has no per-event isolation, so the
    /// permissive order made the event publishable and the other order made
    /// every host that held it unable to reduce the bus at all.
    ///
    /// Asserted on the whole `Result`, not merely on `is_ok`: the message ends
    /// up in a rejection receipt, so two hosts printing different reasons for
    /// the same event would be its own divergence.
    #[test]
    fn a_second_same_agent_claim_gets_the_same_verdict_either_side_of_a_resolution() {
        let (a1, a2, b1) = (eid("alice", 1), eid("alice", 2), eid("bob", 1));

        // The resolution reduced first, naming bob.
        let mut after = ExclusiveTracker::default();
        after.record("k", &a1).unwrap();
        after.record("k", &b1).unwrap();
        after.resolve("k", b1.clone()).unwrap();
        let after_resolution = after.record("k", &a2);

        // alice's second claim reduced first.
        let mut before = ExclusiveTracker::default();
        before.record("k", &a1).unwrap();
        before.record("k", &b1).unwrap();
        let before_resolution = before.record("k", &a2);

        assert_eq!(
            after_resolution.map_err(|e| e.to_string()),
            before_resolution.map_err(|e| e.to_string()),
            "the same-agent refusal must not read `resolved`, which another agent's stream sets"
        );
    }

    /// `key_for_competing` finds the group by containment, so a coordinator
    /// that named only the racers it could see still resolves the key when a
    /// further candidate has joined concurrently.
    #[test]
    fn a_resolution_still_finds_its_group_after_a_late_candidate_joins() {
        let mut t = ExclusiveTracker::default();
        let alice = eid("alice", 0);
        let bob = eid("bob", 0);
        t.record("issue:1", &alice).unwrap();
        t.record("issue:1", &bob).unwrap();
        t.record("issue:1", &eid("carol", 0)).unwrap();

        let named: BTreeSet<EventId> = [alice.clone(), bob].into_iter().collect();
        assert_eq!(
            t.key_for_competing(&named).as_deref(),
            Some("issue:1"),
            "the coordinator named what it saw; a concurrent newcomer must not hide the group"
        );
    }

    #[test]
    fn is_contested_is_true_only_for_members_of_an_unresolved_multi_candidate_group() {
        let mut t = ExclusiveTracker::default();
        let alice = eid("alice", 0);
        let bob = eid("bob", 0);
        t.record("solo:1", &alice).unwrap();
        assert!(
            !t.is_contested(&alice),
            "a lone candidate is never contested"
        );

        t.record("race:1", &alice).unwrap();
        t.record("race:1", &bob).unwrap();
        assert!(t.is_contested(&alice));
        assert!(t.is_contested(&bob));

        t.resolve("race:1", alice.clone()).unwrap();
        assert!(
            !t.is_contested(&alice),
            "the resolved winner is no longer contested"
        );
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
