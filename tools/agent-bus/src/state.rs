//! Reduced bus state (AGENT_BUS.md section 7): what replaying a valid set of
//! event streams derives, and what query/validation commands read back. No
//! derived index is ever committed anywhere -- this is purely an in-memory
//! reduction, rebuilt fresh (or incrementally extended) from stream content.

#![allow(dead_code)]

use crate::bootstrap::BusConfig;
use crate::common::Priority;
use crate::events::*;
use crate::scalars::{Agent, EventId, ObjectId, Short, Text};
use std::collections::BTreeMap;

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
    pub acknowledged: bool,
    pub status: ItemStatus,
    pub resolution_summary: Option<Text>,
    pub reassignment_chain: Vec<EventId>,
}

#[derive(Debug, Clone)]
pub struct DependencyState {
    pub id: EventId,
    pub requester: Agent,
    pub data: DependencyRequested,
    pub current_target: Agent,
    pub current_assignment: EventId,
    pub assignment_target: BTreeMap<EventId, Agent>,
    pub acknowledged: bool,
    pub status: ItemStatus,
    pub reassignment_chain: Vec<EventId>,
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
    pub authorizations: Vec<EventId>,
    /// Receipts recorded so far; concurrently published redundant receipts
    /// with identical authorization-derived values are all kept
    /// (AGENT_BUS_SCHEMA.md section 8).
    pub merged: Vec<EventId>,
    pub reconciled: Vec<EventId>,
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
    pub last_lifecycle_event: EventId,
    pub retired: bool,
    pub scope: Option<ScopeSet>,
    pub plan: Option<PlanSet>,
    pub progress_tail: Vec<ProgressReported>,
    pub next_seq: u64,
}

impl AgentState {
    pub fn active(&self) -> bool {
        !self.retired && !self.status.deactivates()
    }
}

#[derive(Clone)]
pub struct BusState {
    pub config: BusConfig,
    /// The registry epoch this reduction's authority checks are relative to
    /// (docs/AGENT_COORDINATION_EVOLUTION.md section 2.1) -- `None` only
    /// before migration/activation has ever established one.
    pub roster_epoch: Option<crate::registry::RosterEpoch>,
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
}

impl BusState {
    pub fn new(config: BusConfig) -> Self {
        BusState {
            config,
            roster_epoch: None,
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
        }
    }

    pub fn kind_of_event(&self, id: &EventId) -> Option<&str> {
        self.kind_of_event.get(id).map(|s| s.as_str())
    }

    pub fn kind_of_event_insert(&mut self, id: EventId, kind: &str) {
        self.kind_of_event.insert(id, kind.to_string());
    }

    /// Coordinator authority is `Role::Coordinator` membership in the
    /// current roster epoch -- unlike version one's separate immutable
    /// `_bus/BUS.json` list, a stream existing at all already implies
    /// registry authorization (checked by `registry::authorize_stream_write`
    /// before the stream was ever created), so there is nothing further to
    /// consult beyond the epoch itself.
    pub fn is_bootstrap_coordinator(&self, agent: &Agent) -> bool {
        self.roster_epoch
            .as_ref()
            .and_then(|e| e.active_members.get(agent))
            .map(|binding| binding.role == Role::Coordinator)
            .unwrap_or(false)
    }

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
