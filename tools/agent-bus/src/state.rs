//! Reduced bus state (AGENT_BUS.md section 7): what replaying a valid set of
//! event streams derives, and what query/validation commands read back. No
//! derived index is ever committed anywhere -- this is purely an in-memory
//! reduction, rebuilt fresh (or incrementally extended) from stream content.

#![allow(dead_code)]

use crate::bootstrap::BusConfig;
use crate::common::Priority;
use crate::events::*;
use crate::scalars::{Agent, EventId, ObjectId, Short, Text};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ItemStatus {
    Open,
    Terminal(&'static str),
    /// Set the moment a second, genuinely concurrent transition is found for
    /// the same exclusive-transition predecessor (AGENT_BUS.md section 7):
    /// the item's derived "current" state is neutral until a coordinator's
    /// `lifecycle.conflict_resolved` picks a winner.
    LifecycleConflict,
}

#[derive(Debug, Clone)]
pub struct IssueState {
    pub id: EventId,
    pub opener: Agent,
    pub data: IssueOpened,
    pub current_target: Agent,
    pub current_assignment: EventId,
    /// Target agent for each assignment id ever reached (the opening
    /// event's id, plus every successfully-applied `issue.reassigned` id).
    /// Looking up a disposition's authority by the *assignment it names*
    /// rather than by "whatever is current" is what lets two transitions
    /// racing on the same assignment be recognized as concurrent instead of
    /// one hard-failing.
    pub assignment_target: BTreeMap<EventId, Agent>,
    /// Every assignment id ever acknowledged by its target -- membership,
    /// not a flat flag, so "was assignment X acknowledged" is a pure
    /// function of history that a reassignment race's rollback
    /// (`apply::reset_issue_to_conflict`) never needs to separately thread
    /// a "baseline" value through: querying it for whichever assignment id
    /// `current_assignment` gets reset back to always gives the right
    /// answer, since an old assignment id's entry here is never touched
    /// once written.
    pub acknowledged_assignments: BTreeSet<EventId>,
    pub status: ItemStatus,
    pub resolution_summary: Option<Text>,
    pub reassignment_chain: Vec<EventId>,
}

impl IssueState {
    pub fn acknowledged(&self) -> bool {
        self.acknowledged_assignments
            .contains(&self.current_assignment)
    }
}

#[derive(Debug, Clone)]
pub struct DependencyState {
    pub id: EventId,
    pub requester: Agent,
    pub data: DependencyRequested,
    pub current_target: Agent,
    pub current_assignment: EventId,
    pub assignment_target: BTreeMap<EventId, Agent>,
    /// See `IssueState::acknowledged_assignments`.
    pub acknowledged_assignments: BTreeSet<EventId>,
    pub status: ItemStatus,
    pub reassignment_chain: Vec<EventId>,
}

impl DependencyState {
    pub fn acknowledged(&self) -> bool {
        self.acknowledged_assignments
            .contains(&self.current_assignment)
    }
}

#[derive(Debug, Clone)]
pub struct HandoffState {
    pub id: EventId,
    pub offerer: Agent,
    pub data: HandoffOffered,
    pub status: ItemStatus,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FindingDisposition {
    Open,
    Cleared { by_event: EventId },
    Superseded { by_event: EventId, rationale: Text },
}

#[derive(Debug, Clone)]
pub struct FindingState {
    pub changes_event: EventId,
    pub finding_id: Short,
    pub priority: Priority,
    pub locations: Vec<Text>,
    pub rationale: Text,
    pub closure_conditions: Text,
    pub disposition: FindingDisposition,
}

#[derive(Debug, Clone)]
pub struct ReviewChain {
    /// The very first `review.nominated` event id for this workstream.
    pub root: EventId,
    pub nomination_events: Vec<EventId>,
    pub current_nomination: EventId,
    pub current_request: ReviewRequest,
    /// The reviewer named by each nomination-chain link (every other
    /// `ReviewRequest` field is identical across the whole chain by
    /// construction, so only this varies per link).
    pub nomination_reviewer: BTreeMap<EventId, Agent>,
    pub accepted_nominations: std::collections::BTreeSet<EventId>,
    pub decline_or_withdraw_or_reassign_status: ItemStatus,
    pub findings: BTreeMap<(EventId, String), FindingState>,
    /// Sets, not vectors, and that is load-bearing rather than tidiness.
    /// Each of these can now receive entries from two agents who never
    /// observed one another -- two reviewers authorizing the same chain, or
    /// a reviewer's `review.merged` racing a coordinator's
    /// `review.merge_reconciled` -- and reduction records both rather than
    /// making one of the two valid orders fatal. A `Vec` would then hold
    /// them in arrival order, so two hosts that fetched in different orders
    /// would hold different state and gates 15/16 would break in the very
    /// place the totality fix was meant to repair.
    pub authorizations: std::collections::BTreeSet<EventId>,
    /// Receipts recorded so far; concurrently published redundant receipts
    /// with identical authorization-derived values are all kept
    /// (AGENT_BUS_SCHEMA.md section 8).
    pub merged: std::collections::BTreeSet<EventId>,
    pub reconciled: std::collections::BTreeSet<EventId>,
}

impl ReviewChain {
    /// A chain is closed once it's actually merged/reconciled, or once its
    /// current nomination link has been terminally declined or withdrawn (a
    /// *confirmed* reassignment resets that status back to `Open` for the
    /// new link, since the chain continues under a new reviewer rather than
    /// ending).
    pub fn is_closed(&self) -> bool {
        !self.merged.is_empty()
            || !self.reconciled.is_empty()
            || matches!(
                self.decline_or_withdraw_or_reassign_status,
                ItemStatus::Terminal(_)
            )
    }

    pub fn accepted(&self) -> bool {
        self.accepted_nominations.contains(&self.current_nomination)
    }
}

/// Which of the three lifecycle-chain event kinds a recorded transition is
/// (AGENT_BUS_SCHEMA.md `agent.status` / `agent.resumed` / `agent.retired`).
///
/// The distinction that matters to [`AgentState::recompute_lifecycle`] is
/// how each kind *acquires* its predecessor, because that is what says
/// whether two transitions sharing one predecessor are a genuine race:
///
///  - `agent.resumed` and `agent.retired` carry an explicit
///    `previous_lifecycle` field. Two of them naming one predecessor is an
///    exclusive claim on the same fork point, and one of them has to lose.
///  - `agent.status` carries no such field at all. Its predecessor is
///    *inferred* -- it is simply the next event on the identity's own
///    single-writer stream, so it never contends with another status.
///
/// An inferred claim therefore yields to an explicit one: see
/// [`LifecycleTransitionKind::rank`].
// Deliberately not `Ord`: the ordering that decides a race is
// `LifecycleTransitionKind::rank`, and a derived one would silently offer
// declaration order as an alternative answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LifecycleTransitionKind {
    Status,
    Resume,
    Retire,
}

impl LifecycleTransitionKind {
    /// Lower rank wins at a shared predecessor.
    ///
    /// `agent.status` ranks below both explicit transitions, and that is a
    /// deliberate asymmetry rather than an arbitrary one. A status event and
    /// a coordinator's `agent.retired` can only ever share a predecessor by
    /// being concurrent -- a coordinator that had observed the status would
    /// have cited *it* instead -- and if the tie-break between them were the
    /// plain identity order used within a rank, then whether a
    /// user-authorized retirement survived at all would come down to whether
    /// the target's agent name happened to sort before the coordinator's.
    /// That is the same silent-divergence harm this whole chain exists to
    /// remove, just relocated: a routine status ping must not be able to
    /// void a retirement. The status event's own effect (`status`,
    /// `status_note`, product fields) is applied regardless of whether it
    /// wins its chain position, so nothing it actually reports is lost.
    ///
    /// This rank is only ever consulted *between* streams, because
    /// `recompute_lifecycle` eliminates same-stream claims by sequence
    /// number first. That matters: `agent.resumed` is self-published, so a
    /// resumption and a status can only meet each other within one
    /// single-writer stream, where they are not concurrent at all and the
    /// causally earlier one must win outright regardless of kind.
    fn rank(self) -> u8 {
        match self {
            LifecycleTransitionKind::Retire | LifecycleTransitionKind::Resume => 0,
            LifecycleTransitionKind::Status => 1,
        }
    }
}

/// One recorded step of an agent's lifecycle chain: a fact about an event,
/// recorded whether or not that event ends up winning its position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LifecycleTransition {
    /// The chain node this transition claims to follow. For `agent.resumed`
    /// and `agent.retired` this is the payload's `previous_lifecycle`; for
    /// `agent.status` it is the identity's own preceding lifecycle event
    /// ([`AgentState::own_lifecycle_tail`]).
    pub previous: EventId,
    pub kind: LifecycleTransitionKind,
}

#[derive(Debug, Clone)]
pub struct AgentState {
    pub agent: Agent,
    pub display_name: Short,
    pub primary_role: Role,
    pub purpose: Text,
    pub provider: Option<Short>,
    pub model: Option<Short>,
    pub status: LifecycleStatus,
    pub status_note: Text,
    pub product_branch: Option<crate::scalars::Branch>,
    pub product_commit: Option<ObjectId>,
    /// Derived, never assigned by a handler: the head of the lifecycle chain
    /// as [`AgentState::recompute_lifecycle`] currently walks it.
    pub last_lifecycle_event: EventId,
    /// Derived, never assigned by a handler: whether the winning chain head
    /// is an `agent.retired`.
    pub retired: bool,
    /// The identity's `agent.registered` -- the root every chain walk starts
    /// from, kept separately because `last_lifecycle_event` moves.
    pub lifecycle_root: EventId,
    /// The identity's own most recent lifecycle event (`agent.registered`,
    /// `agent.status`, or `agent.resumed`), which is the predecessor the
    /// *next* `agent.status` on that stream inherits. A fold over one
    /// single-writer stream in sequence order, so it is itself independent
    /// of the order streams are reduced in.
    pub own_lifecycle_tail: EventId,
    /// Every lifecycle transition ever recorded against this identity, won
    /// or lost. Append-only: a handler records its event here unconditionally
    /// and then re-derives, so no arrival order can make one host keep a
    /// transition another host dropped.
    pub lifecycle_transitions: BTreeMap<EventId, LifecycleTransition>,
    pub scope: Option<ScopeSet>,
    pub plan: Option<PlanSet>,
    pub progress_tail: Vec<ProgressReported>,
    pub next_seq: u64,
    /// Explicitly selected subscription topics from this agent's most
    /// recent `subscription.set` (docs/AGENT_COORDINATION_EVOLUTION.md
    /// section 4.2) -- role-implied and mandatory topics are not stored
    /// here since they are derived from `primary_role`/`scope`, not
    /// separately declared.
    pub subscribed_topics: crate::scalars::StringSet<crate::scalars::CoordinationTopic>,
}

impl AgentState {
    pub fn active(&self) -> bool {
        !self.retired && !self.status.deactivates()
    }

    /// Records one lifecycle transition and re-derives the chain.
    ///
    /// Unconditional by construction: the caller has no "did this win"
    /// question to answer, because winning is not a property an event has at
    /// the moment it is applied -- it is a property of the recorded *set*,
    /// and a later-arriving concurrent transition can change it. That is
    /// exactly why the two handlers that used to answer the question
    /// themselves ("`previous_lifecycle` doesn't match the current head, so
    /// return `Ok(())`") could not converge: whichever host reduced the
    /// loser first threw it away and never got it back.
    pub fn record_lifecycle_transition(
        &mut self,
        id: EventId,
        previous: EventId,
        kind: LifecycleTransitionKind,
    ) {
        self.lifecycle_transitions
            .insert(id, LifecycleTransition { previous, kind });
        self.recompute_lifecycle();
    }

    /// Derives `retired` and `last_lifecycle_event` from
    /// `lifecycle_transitions` alone -- a pure function of the recorded set,
    /// which is what makes two hosts that fetched the same events in
    /// different orders agree (gate 16).
    ///
    /// Walk from `lifecycle_root`. At each head, take the transitions that
    /// claim it as their predecessor; if there are none the chain ends
    /// there. Otherwise resolve that group in two steps, and the result
    /// becomes the next head:
    ///
    ///  1. Reduce each *stream* to its lowest sequence number. Two claims
    ///     from one identity are never concurrent -- a stream is
    ///     single-writer and totally ordered -- so the later one is simply
    ///     citing a predecessor its own author had already moved past, and
    ///     it loses outright rather than competing. (Sequence numbers are
    ///     compared numerically for exactly this reason: `EventId`'s own
    ///     string ordering stops agreeing with sequence order at two
    ///     digits, `"w:12" < "w:4"`.)
    ///  2. What survives is pairwise concurrent by construction, so there is
    ///     no causal order left to exploit and the winner has to be a pure
    ///     function of the membership: the lowest `(kind rank, agent)`. The
    ///     lowest-identity half of that is the rule `exclusive.rs` already
    ///     documents for two coordinators racing over one predecessor, for
    ///     the same reason.
    ///
    /// Computed afresh from the whole set every time, so a transition that
    /// arrives late can still take a position an earlier one provisionally
    /// held -- the same "unwind to the shared baseline on a concurrent
    /// claim" shape `apply_merge_engine_activated` uses.
    pub fn recompute_lifecycle(&mut self) {
        // Resolved once up front rather than rescanned at each step: an
        // identity's chain is one `agent.status` long per status it ever
        // published, and this runs on every insertion, so a scan per step
        // would make replaying one long-lived stream cubic in its length.
        // Step 1, for every predecessor at once: each stream is represented
        // by its causally earliest claim.
        type Claim<'a> = (u64, &'a EventId, LifecycleTransitionKind);
        let mut per_stream: BTreeMap<&EventId, BTreeMap<Agent, Claim<'_>>> = BTreeMap::new();
        for (id, t) in self.lifecycle_transitions.iter() {
            let seq = id.seq();
            let slot = per_stream
                .entry(&t.previous)
                .or_default()
                .entry(id.agent())
                .or_insert((seq, id, t.kind));
            if seq < slot.0 {
                *slot = (seq, id, t.kind);
            }
        }
        // Step 2: among the mutually-concurrent survivors, lowest
        // `(kind rank, agent)`.
        let winner_by_predecessor: BTreeMap<&EventId, (&EventId, LifecycleTransitionKind)> =
            per_stream
                .iter()
                .filter_map(|(previous, streams)| {
                    streams
                        .iter()
                        .min_by(|(l, (_, _, lk)), (r, (_, _, rk))| {
                            (lk.rank(), *l).cmp(&(rk.rank(), *r))
                        })
                        .map(|(_, (_, id, kind))| (*previous, (*id, *kind)))
                })
                .collect();

        let (head, retired) = {
            let mut head: &EventId = &self.lifecycle_root;
            let mut retired = false;
            // Each step moves `head` onto a transition, so a well-formed
            // chain terminates in at most one step per recorded transition.
            // The bound is what keeps a chain whose `previous` links happen
            // to form a cycle (nothing validates that they cannot) from
            // spinning forever -- reduction must stay total, so this ends
            // the walk rather than reporting an error.
            for _ in 0..self.lifecycle_transitions.len() {
                let Some((id, kind)) = winner_by_predecessor.get(head) else {
                    break;
                };
                match kind {
                    LifecycleTransitionKind::Retire => retired = true,
                    LifecycleTransitionKind::Resume => retired = false,
                    // A status event moves the chain head (so the next
                    // `previous_lifecycle` citing it resolves) without
                    // saying anything about retirement either way.
                    LifecycleTransitionKind::Status => {}
                }
                head = id;
            }
            (head.clone(), retired)
        };
        self.retired = retired;
        self.last_lifecycle_event = head;
    }
}

#[derive(Debug, Clone)]
pub struct BusState {
    pub config: BusConfig,
    /// The *current* registry epoch (docs/AGENT_COORDINATION_EVOLUTION.md
    /// section 2.1). `None` only before migration/activation has ever
    /// established one.
    ///
    /// Read sparingly, and never to decide an already-published event's
    /// authority: this is whatever the registry tip says at *reduction*
    /// time, which for a replayed event is routinely a later epoch than the
    /// one it was authored against -- see `apply::require_bootstrap_
    /// coordinator`. Membership and custody are enforced against this epoch
    /// where that is sound: at publication, by `registry::
    /// authorize_stream_write`.
    pub roster_epoch: Option<crate::registry::RosterEpoch>,
    /// Every epoch reachable from the current registry tip, keyed by its
    /// own id -- what a complete frontier's completeness is actually
    /// checked against (`apply::require_complete_frontier`,
    /// `apply_broadcast_published`). Deliberately distinct from
    /// `roster_epoch`: an authority event's complete frontier names the
    /// exact epoch that was current *when it was authored*, which may be
    /// an older one by the time this reduction runs, and "a later
    /// registration does not invalidate it" (gate 5) is only true if
    /// validation looks the named epoch up here rather than comparing
    /// against whatever is current now.
    pub known_epochs: BTreeMap<ObjectId, crate::registry::RosterEpoch>,
    pub agents: BTreeMap<Agent, AgentState>,
    pub issues: BTreeMap<EventId, IssueState>,
    pub dependencies: BTreeMap<EventId, DependencyState>,
    pub handoffs: BTreeMap<EventId, HandoffState>,
    /// Keyed by every nomination event id in a chain -> chain root id, so a
    /// reassignment event id resolves back to its chain.
    pub review_chain_by_nomination: BTreeMap<EventId, EventId>,
    pub reviews: BTreeMap<EventId, ReviewChain>,
    /// Order-independent exclusive-transition resolution
    /// (docs/AGENT_COORDINATION_EVOLUTION.md gates 3/15/16) -- see
    /// `exclusive.rs`.
    pub exclusive: crate::exclusive::ExclusiveTracker,
    pub kind_of_event: BTreeMap<EventId, String>,
    pub events: BTreeMap<EventId, crate::envelope::Envelope>,
    /// The currently selected merge-engine epoch, or `None` before any
    /// `merge_engine.activated`-equivalent event has ever been reduced.
    pub current_merge_engine_epoch: Option<EventId>,
    /// `(merge_engine, merge_engine_version)` for every known epoch id.
    pub merge_engine_info: BTreeMap<EventId, (Short, Short)>,
    /// Highest `schema.activated` version seen so far (0 = none yet).
    pub activated_schema_version: u32,
    /// Every `audit.reported`, verbatim (AGENT_COORDINATION_EVOLUTION.md
    /// section 2.2). Durable evidence only: like `friction_reports`, and
    /// unlike `issues`, nothing here ever gains a status, an assignment or a
    /// disposition, because the design makes the report non-authoritative
    /// and gives issue lifecycle sole ownership of all three.
    pub audits: BTreeMap<EventId, crate::events::AuditReported>,
    /// Every `friction.reported` event, verbatim -- durable evidence only;
    /// unlike `issues`, nothing here ever gains a status or an assignment
    /// (gate 11: a friction report creates no target obligation).
    pub friction_reports: BTreeMap<EventId, FrictionReported>,
    /// Every `friction.synthesized` event, verbatim.
    pub friction_synthesis: BTreeMap<EventId, FrictionSynthesized>,
    /// The most recent synthesis event for each theme -- what a later
    /// `duplicate_of` reference and `agent-bus friction --theme` both read.
    pub friction_theme_synthesis: BTreeMap<crate::scalars::CoordinationTopic, EventId>,
    /// Every `broadcast.published` event, verbatim.
    pub broadcasts: BTreeMap<EventId, BroadcastPublished>,
    /// Who has acknowledged each broadcast, by `broadcast.acknowledged`.
    /// Absent key == nobody yet. Only ever populated for a broadcast whose
    /// own `acknowledgement` is `required`, but keyed by any broadcast id
    /// for simplicity -- `apply::apply_broadcast_acknowledged` is what
    /// enforces the "must be required" precondition.
    pub broadcast_acknowledged_by: BTreeMap<EventId, BTreeSet<Agent>>,
    /// Who has published a `broadcast.seen` receipt for each broadcast --
    /// purely an optional, non-authoritative audit trail (gate 13: this is
    /// never required, regardless of importance or acknowledgement).
    pub broadcast_seen_by: BTreeMap<EventId, BTreeSet<Agent>>,
}

impl BusState {
    pub fn new(config: BusConfig) -> Self {
        BusState {
            config,
            roster_epoch: None,
            known_epochs: BTreeMap::new(),
            agents: BTreeMap::new(),
            issues: BTreeMap::new(),
            dependencies: BTreeMap::new(),
            handoffs: BTreeMap::new(),
            review_chain_by_nomination: BTreeMap::new(),
            reviews: BTreeMap::new(),
            exclusive: crate::exclusive::ExclusiveTracker::default(),
            kind_of_event: BTreeMap::new(),
            events: BTreeMap::new(),
            current_merge_engine_epoch: None,
            merge_engine_info: BTreeMap::new(),
            activated_schema_version: 0,
            audits: BTreeMap::new(),
            friction_reports: BTreeMap::new(),
            friction_synthesis: BTreeMap::new(),
            friction_theme_synthesis: BTreeMap::new(),
            broadcasts: BTreeMap::new(),
            broadcast_acknowledged_by: BTreeMap::new(),
            broadcast_seen_by: BTreeMap::new(),
        }
    }

    pub fn kind_of_event(&self, id: &EventId) -> Option<&str> {
        self.kind_of_event.get(id).map(|s| s.as_str())
    }

    pub fn kind_of_event_insert(&mut self, id: EventId, kind: &str) {
        self.kind_of_event.insert(id, kind.to_string());
    }

    // Deliberately no `is_bootstrap_coordinator` here any more.
    //
    // It answered "is this agent bound as `Role::Coordinator` in
    // `roster_epoch`", and `apply::require_bootstrap_coordinator` was its
    // only caller. Reading the *live* epoch to judge an event authored
    // against an older one made every historical coordinator event
    // unreducible fleet-wide the moment any epoch dropped that coordinator
    // -- see that function's own doc for the full argument and for where
    // the membership and liveness halves are enforced instead. The helper
    // is gone rather than merely unused so nothing reaches for it again:
    // its own observation, that "a stream existing at all already implies
    // registry authorization (checked by `registry::authorize_stream_write`
    // before the stream was ever created)", is exactly why replay does not
    // need to re-ask it.

    pub fn agent(&self, a: &Agent) -> Option<&AgentState> {
        self.agents.get(a)
    }

    pub fn review_chain(&self, nomination: &EventId) -> Option<&ReviewChain> {
        self.review_chain_by_nomination
            .get(nomination)
            .and_then(|root| self.reviews.get(root))
    }

    pub fn review_chain_mut(&mut self, nomination: &EventId) -> Option<&mut ReviewChain> {
        let root = self.review_chain_by_nomination.get(nomination)?.clone();
        self.reviews.get_mut(&root)
    }
}

pub fn finding_key(changes_event: &EventId, finding_id: &Short) -> String {
    format!("finding:{changes_event}:{}", finding_id.as_str())
}

pub fn issue_key(assignment: &EventId) -> String {
    format!("issue:{assignment}")
}

pub fn dependency_key(assignment: &EventId) -> String {
    format!("dependency:{assignment}")
}

pub fn handoff_key(handoff: &EventId) -> String {
    format!("handoff:{handoff}")
}

pub fn review_key(nomination: &EventId) -> String {
    format!("review:{nomination}")
}
