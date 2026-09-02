//! Reduced bus state (AGENT_BUS.md section 7) plus the bookkeeping needed to
//! detect the concurrent/causal cases in section 10.

//! Several fields here (`ReviewChain::root`, `AgentState::registered_commit_index`,
//! full `FindingState` detail, ...) round out the data model for future query
//! commands (e.g. `review show`) beyond what today's CLI surface reads back.
#![allow(dead_code)]

use crate::bootstrap::BusJson;
use crate::common::Priority;
use crate::events::*;
use crate::scalars::{Agent, EventId, ObjectId, Short, Text};
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ItemStatus {
    Open,
    Terminal(&'static str),
    /// Reserved for a future per-item conflict marker; today `agent-bus
    /// conflicts` is the authoritative, tested signal for this (backed by
    /// `BusState::exclusive`), so no code path constructs this variant yet.
    LifecycleConflict,
}

#[derive(Debug, Clone)]
pub struct IssueState {
    pub id: EventId,
    pub opener: Agent,
    pub data: IssueOpened,
    pub current_target: Agent,
    pub current_assignment: EventId,
    /// Target agent for each assignment id ever reached (the opening event's
    /// id, plus every successfully-applied `issue.reassigned` id). Looking up
    /// a disposition's authority by the *assignment it names* rather than by
    /// "whatever is current" is what lets two transitions racing on the same
    /// assignment be recognized as concurrent instead of one hard-failing.
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
    /// The reviewer named by each nomination-chain link (every field in
    /// `ReviewRequest` besides `reviewer` is identical across the whole
    /// chain by construction, so only this varies per link).
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
    pub fn is_closed(&self) -> bool {
        !self.merged.is_empty() || !self.reconciled.is_empty()
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
    pub registered_commit_index: usize,
}

impl AgentState {
    pub fn active(&self) -> bool {
        !self.retired && !self.status.deactivates()
    }
}

/// A pending concurrent exclusive-transition set, keyed by predecessor.
#[derive(Debug, Clone, Default)]
pub struct ExclusiveTracker {
    pub transitions: Vec<(EventId, usize)>, // (transition event id, commit index)
    pub resolved: Option<EventId>,
}

#[derive(Clone)]
pub struct BusState {
    pub bus_json: BusJson,
    pub agents: BTreeMap<Agent, AgentState>,
    pub issues: BTreeMap<EventId, IssueState>,
    pub dependencies: BTreeMap<EventId, DependencyState>,
    pub handoffs: BTreeMap<EventId, HandoffState>,
    /// Keyed by every nomination event id in a chain -> chain root id, so a
    /// reassignment event id resolves back to its chain.
    pub review_chain_by_nomination: BTreeMap<EventId, EventId>,
    pub reviews: BTreeMap<EventId, ReviewChain>,
    pub exclusive: BTreeMap<String, ExclusiveTracker>,
    pub commit_index_of: BTreeMap<String, usize>,
    pub commit_index_of_event: BTreeMap<EventId, usize>,
    pub kind_of_event: BTreeMap<EventId, String>,
    pub events: BTreeMap<EventId, crate::envelope::Envelope>,
    /// The currently selected merge-engine epoch (a bootstrap coordinator
    /// registration id, or a `merge_engine.activated` event id).
    pub current_merge_engine_epoch: EventId,
    /// `(merge_engine, merge_engine_version)` for every known epoch id.
    pub merge_engine_info: BTreeMap<EventId, (Short, Short)>,
    /// Highest `schema.activated` version seen so far (0 = none yet).
    pub activated_schema_version: u32,
}

impl BusState {
    pub fn new(bus_json: BusJson) -> Self {
        let epoch = bus_json.merge_engine_epoch.clone();
        let mut merge_engine_info = BTreeMap::new();
        merge_engine_info.insert(
            epoch.clone(),
            (
                Short::parse(bus_json.merge_engine.clone())
                    .expect("BUS.json merge_engine already validated"),
                Short::parse(bus_json.merge_engine_version.clone())
                    .expect("BUS.json merge_engine_version already validated"),
            ),
        );
        BusState {
            bus_json,
            agents: BTreeMap::new(),
            issues: BTreeMap::new(),
            dependencies: BTreeMap::new(),
            handoffs: BTreeMap::new(),
            review_chain_by_nomination: BTreeMap::new(),
            reviews: BTreeMap::new(),
            exclusive: BTreeMap::new(),
            commit_index_of: BTreeMap::new(),
            commit_index_of_event: BTreeMap::new(),
            kind_of_event: BTreeMap::new(),
            events: BTreeMap::new(),
            current_merge_engine_epoch: epoch,
            merge_engine_info,
            activated_schema_version: 0,
        }
    }

    pub fn kind_of_event(&self, id: &EventId) -> Option<&str> {
        self.kind_of_event.get(id).map(|s| s.as_str())
    }

    pub fn kind_of_event_insert(&mut self, id: EventId, kind: &str) {
        self.kind_of_event.insert(id, kind.to_string());
    }

    pub fn is_bootstrap_coordinator(&self, agent: &Agent) -> bool {
        self.bus_json.coordinators.iter().any(|c| c == agent)
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
