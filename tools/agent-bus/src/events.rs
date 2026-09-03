//! Event data payloads and the `kind` vocabulary (AGENT_BUS_SCHEMA.md
//! sections 4-9). The lifecycle protocol these describe -- registration,
//! scope claims, issues, dependencies, handoffs, and the review/merge
//! protocol -- is unchanged by the version-two coordination rewrite; only
//! the substrate underneath (envelope, storage, causal ordering) changed.

use crate::common::*;
use crate::error::{invalid, AbResult};
use crate::scalars::{Agent, Branch, CoordinationTopic, EventId, ObjectId, Short, StringSet, Text};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::fmt;

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum Role {
    Implementor,
    Reviewer,
    Coordinator,
    Observer,
}

impl fmt::Display for Role {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Role::Implementor => "implementor",
            Role::Reviewer => "reviewer",
            Role::Coordinator => "coordinator",
            Role::Observer => "observer",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum LifecycleStatus {
    Active,
    Blocked,
    Paused,
    Done,
    Abandoned,
}

impl LifecycleStatus {
    pub fn deactivates(&self) -> bool {
        matches!(self, LifecycleStatus::Done | LifecycleStatus::Abandoned)
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum IssueKind {
    Bug,
    Request,
    Question,
    ScopeConflict,
}

// ---------------------------------------------------------------- lifecycle

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AgentRegistered {
    pub display_name: Short,
    pub primary_role: Role,
    pub purpose: Text,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub product_base: Option<ObjectId>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub product_branch: Option<Branch>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub provider: Option<Short>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub model: Option<Short>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AgentStatusEvent {
    pub status: LifecycleStatus,
    pub note: Text,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub product_branch: Option<Branch>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub product_commit: Option<ObjectId>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AgentResumed {
    pub previous_lifecycle: EventId,
    pub reason: Text,
    pub user_authority: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AgentRetired {
    pub target: Agent,
    pub previous_lifecycle: EventId,
    pub reason: Text,
    pub user_authority: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SchemaActivated {
    pub version: u32,
    pub design_commit: ObjectId,
    pub helper_commit: ObjectId,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MergeEngineActivated {
    pub previous_epoch: EventId,
    pub merge_engine: Short,
    pub merge_engine_version: Short,
    pub design_commit: ObjectId,
    pub helper_commit: ObjectId,
}

// ------------------------------------------------------ scope/plan/progress

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScopeSet {
    pub base_code_commit: ObjectId,
    pub exclusive: StringSet<crate::scalars::PathClaim>,
    pub shared: StringSet<crate::scalars::PathClaim>,
    pub exports: StringSet<Short>,
    pub depends_on: Vec<DependencyImport>,
    pub note: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PlanSet {
    pub summary: Text,
    pub steps: Vec<PlanStep>,
    pub risks: Vec<Text>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProgressReported {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub product_commit: Option<ObjectId>,
    pub completed: Vec<Text>,
    pub current: Vec<Text>,
    pub next: Vec<Text>,
    pub blockers: Vec<Text>,
    pub verification: Vec<Text>,
}

// --------------------------------------------------------------- issues

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IssueOpened {
    pub target: Agent,
    pub issue_kind: IssueKind,
    pub severity: Priority,
    pub summary: Text,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code_commit: Option<ObjectId>,
    pub locations: Vec<Text>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected: Option<Text>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub observed_behavior: Option<Text>,
    pub reproduction: Vec<Text>,
    pub blocks: StringSet<EventId>,
    pub evidence: StringSet<EventId>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IssueAcknowledged {
    pub issue: EventId,
    pub assignment: EventId,
    pub note: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IssueResolved {
    pub issue: EventId,
    pub assignment: EventId,
    pub summary: Text,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fix_commit: Option<ObjectId>,
    pub verification: Vec<Text>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IssueRejected {
    pub issue: EventId,
    pub assignment: EventId,
    pub reason: Text,
    pub normative_refs: Vec<Text>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IssueReassigned {
    pub issue: EventId,
    pub previous_assignment: EventId,
    pub previous_target: Agent,
    pub new_target: Agent,
    pub reason: Text,
}

// ------------------------------------------------------ dependencies/handoffs

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DependencyRequested {
    pub target: Agent,
    pub interface: Short,
    pub needed_by: Text,
    pub blocking: bool,
    pub summary: Text,
    pub evidence: StringSet<EventId>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DependencyAcknowledged {
    pub dependency: EventId,
    pub assignment: EventId,
    pub note: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DependencyResolved {
    pub dependency: EventId,
    pub assignment: EventId,
    pub summary: Text,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub product_commit: Option<ObjectId>,
    pub verification: Vec<Text>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DependencyRejected {
    pub dependency: EventId,
    pub assignment: EventId,
    pub reason: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DependencyReassigned {
    pub dependency: EventId,
    pub previous_assignment: EventId,
    pub previous_target: Agent,
    pub new_target: Agent,
    pub reason: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HandoffOffered {
    pub receiver: Agent,
    pub scope: StringSet<crate::scalars::PathClaim>,
    pub product_branch: Branch,
    pub product_commit: ObjectId,
    pub verification: Vec<Text>,
    pub known_issues: StringSet<EventId>,
    pub evidence: StringSet<EventId>,
    pub summary: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HandoffAccepted {
    pub handoff: EventId,
    pub note: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HandoffDeclined {
    pub handoff: EventId,
    pub reason: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HandoffWithdrawn {
    pub handoff: EventId,
    pub reason: Text,
}

// ----------------------------------------------------------------- review

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewRequest {
    pub authors: StringSet<Agent>,
    pub product_branch: Branch,
    pub reviewer: Agent,
    pub required_checks: Vec<Text>,
    pub review_scope: StringSet<crate::scalars::PathClaim>,
    pub summary: Text,
    pub target_branch: Branch,
    pub evidence: StringSet<EventId>,
}

pub type ReviewNominated = ReviewRequest;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewNominationAccepted {
    pub nomination: EventId,
    pub note: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewNominationDeclined {
    pub nomination: EventId,
    pub reason: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewChangesRequested {
    pub nomination: EventId,
    pub reviewed_commit: ObjectId,
    pub findings: Vec<Finding>,
    pub evidence: StringSet<EventId>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewFindingsCleared {
    pub nomination: EventId,
    pub changes_event: EventId,
    pub finding_id: Short,
    pub resolved_commit: ObjectId,
    pub summary: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewFindingsSuperseded {
    pub nomination: EventId,
    pub changes_event: EventId,
    pub finding_id: Short,
    pub rationale: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewReassigned {
    pub authors: StringSet<Agent>,
    pub product_branch: Branch,
    pub reviewer: Agent,
    pub required_checks: Vec<Text>,
    pub review_scope: StringSet<crate::scalars::PathClaim>,
    pub summary: Text,
    pub target_branch: Branch,
    pub evidence: StringSet<EventId>,
    pub replaces: EventId,
    pub reason: Text,
    pub inherited_findings: Vec<FindingRef>,
}

impl ReviewReassigned {
    pub fn request(&self) -> ReviewRequest {
        ReviewRequest {
            authors: self.authors.clone(),
            product_branch: self.product_branch.clone(),
            reviewer: self.reviewer.clone(),
            required_checks: self.required_checks.clone(),
            review_scope: self.review_scope.clone(),
            summary: self.summary.clone(),
            target_branch: self.target_branch.clone(),
            evidence: self.evidence.clone(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewWithdrawn {
    pub nomination: EventId,
    pub reason: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewMergeAuthorized {
    pub nomination: EventId,
    pub product_branch: Branch,
    pub previous_main: ObjectId,
    pub reviewed_commit: ObjectId,
    pub candidate: ObjectId,
    pub merge_engine_epoch: EventId,
    pub checks: Vec<CheckResult>,
    pub finding_dispositions: Vec<FindingDisposition>,
    pub evidence: StringSet<EventId>,
    pub reviewed_scope: StringSet<crate::scalars::PathClaim>,
    pub limitations: Vec<Text>,
    pub summary: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewMerged {
    pub authorization: EventId,
    pub previous_main: ObjectId,
    pub main_commit: ObjectId,
    pub product_branch: Branch,
    pub reviewed_commit: ObjectId,
    pub summary: Text,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewMergeReconciled {
    pub authorization: EventId,
    pub previous_main: ObjectId,
    pub main_commit: ObjectId,
    pub product_branch: Branch,
    pub reviewed_commit: ObjectId,
    pub reason: Text,
    pub user_authority: Text,
}

// ------------------------------------------------- lifecycle conflict resolution

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LifecycleConflictResolved {
    pub root: EventId,
    pub competing: StringSet<EventId>,
    pub selected: EventId,
    pub reason: Text,
    pub user_authority: Text,
}

// ------------------------------------------------------------------ friction

/// docs/AGENT_COORDINATION_EVOLUTION.md section 3.1. Deliberately not an
/// issue: creates no target obligation, blocks nothing, and assigns no
/// repair work (gate 11) -- `likely_owner` is triage context only, never a
/// target the way `IssueOpened.target` is.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FrictionReported {
    pub area: CoordinationTopic,
    pub summary: Short,
    pub impact: crate::common::Impact,
    pub evidence: StringSet<EventId>,
    pub product_locations: Vec<Text>,
    pub measurements: Vec<crate::common::Measurement>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub frequency: Option<crate::common::Frequency>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub workaround: Option<Text>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggestion: Option<Text>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub likely_owner: Option<Agent>,
}

/// docs/AGENT_COORDINATION_EVOLUTION.md section 3.3: the design steward's
/// periodic grouping of reports under one theme with exactly one
/// disposition. `promoted_to`/`duplicate_of`/`revisit_trigger` are each
/// required or forbidden depending on `disposition` -- see
/// `apply::apply_friction_synthesized`, not enforced structurally here.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FrictionSynthesized {
    pub theme: CoordinationTopic,
    pub reports: StringSet<EventId>,
    pub disposition: crate::common::FrictionDispositionKind,
    pub rationale: Text,
    /// Required when `disposition` is `promoted`: the issue/dependency event
    /// this synthesis turned into targeted, obligated work.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub promoted_to: Option<EventId>,
    /// Required when `disposition` is `duplicate`: the existing theme's own
    /// prior `friction.synthesized` event.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub duplicate_of: Option<EventId>,
    /// Required when `disposition` is `deferred`: what should trigger
    /// revisiting this theme.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub revisit_trigger: Option<Text>,
}

// ----------------------------------------------------------------- broadcast

/// docs/AGENT_COORDINATION_EVOLUTION.md section 4.2: a replacement
/// declaration of an agent's *explicitly* selected subscription topics.
/// Role-implied topics, interfaces named in scope dependencies, and
/// mandatory safety/active-protocol topics are not carried here -- those
/// are computed from already-known state (`primary_role`, `scope`), not
/// separately declared, so this event only ever needs to state what the
/// agent additionally opted into.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SubscriptionSet {
    pub topics: StringSet<CoordinationTopic>,
}

/// docs/AGENT_COORDINATION_EVOLUTION.md section 4.1's `Broadcast` record.
/// `audience_snapshot` is the checked publisher's own resolution of
/// `audience_selector` against `audience_epoch`, fixed at publish time --
/// "later scope, role, or subscription changes do not retroactively change
/// who was addressed" (section 4.2, gate 12).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BroadcastPublished {
    pub topics: StringSet<CoordinationTopic>,
    pub importance: crate::common::Importance,
    pub summary: Short,
    pub detail: Text,
    pub affected_paths: StringSet<crate::scalars::PathClaim>,
    pub affected_interfaces: StringSet<Short>,
    pub product_commits: StringSet<ObjectId>,
    pub audience_selector: crate::common::AudienceSelector,
    /// The exact roster epoch `audience_selector` was resolved against --
    /// what a later validator re-resolves the selector relative to, to
    /// confirm `audience_snapshot` rather than merely trust it.
    pub audience_epoch: ObjectId,
    pub audience_snapshot: StringSet<Agent>,
    pub acknowledgement: crate::common::AckRequirement,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub deadline: Option<crate::scalars::Timestamp>,
    pub supersedes: StringSet<EventId>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub workaround: Option<Text>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expiry_condition: Option<Text>,
}

/// docs/AGENT_COORDINATION_EVOLUTION.md section 4.2: an explicit,
/// batchable acknowledgement of one or more `acknowledgement: required`
/// broadcasts -- never implies the announced problem is fixed.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BroadcastAcknowledged {
    pub broadcasts: StringSet<EventId>,
}

/// docs/AGENT_COORDINATION_EVOLUTION.md section 4.2: an optional, batched,
/// non-authoritative read receipt -- "reading position is disposable local
/// state by default"; this is only ever published when an auditable
/// receipt is specifically useful, never required (gate 13).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BroadcastSeen {
    pub broadcasts: StringSet<EventId>,
}

// -------------------------------------------------------------- EventData

macro_rules! event_data {
    ($( $variant:ident($ty:ty) = $kind:literal ),+ $(,)?) => {
        #[derive(Debug, Clone)]
        pub enum EventData {
            $( $variant($ty), )+
        }

        impl EventData {
            pub fn kind(&self) -> &'static str {
                match self {
                    $( EventData::$variant(_) => $kind, )+
                }
            }

            pub fn to_value(&self) -> serde_json::Value {
                match self {
                    $( EventData::$variant(d) => serde_json::to_value(d).expect("event data always serializable"), )+
                }
            }

            pub fn from_kind_and_value(kind: &str, value: serde_json::Value) -> AbResult<EventData> {
                match kind {
                    $( $kind => Ok(EventData::$variant(
                        serde_json::from_value(value).map_err(|e| invalid(format!("malformed {kind} data: {e}")))?,
                    )), )+
                    other => Err(invalid(format!("unknown event kind: {other}"))),
                }
            }

            pub fn all_kinds() -> Vec<&'static str> {
                vec![ $( $kind, )+ ]
            }
        }
    };
}

event_data! {
    AgentRegistered(AgentRegistered) = "agent.registered",
    AgentStatus(AgentStatusEvent) = "agent.status",
    AgentResumed(AgentResumed) = "agent.resumed",
    AgentRetired(AgentRetired) = "agent.retired",
    SchemaActivated(SchemaActivated) = "schema.activated",
    MergeEngineActivated(MergeEngineActivated) = "merge_engine.activated",
    ScopeSet(ScopeSet) = "scope.set",
    PlanSet(PlanSet) = "plan.set",
    ProgressReported(ProgressReported) = "progress.reported",
    IssueOpened(IssueOpened) = "issue.opened",
    IssueAcknowledged(IssueAcknowledged) = "issue.acknowledged",
    IssueResolved(IssueResolved) = "issue.resolved",
    IssueRejected(IssueRejected) = "issue.rejected",
    IssueReassigned(IssueReassigned) = "issue.reassigned",
    DependencyRequested(DependencyRequested) = "dependency.requested",
    DependencyAcknowledged(DependencyAcknowledged) = "dependency.acknowledged",
    DependencyResolved(DependencyResolved) = "dependency.resolved",
    DependencyRejected(DependencyRejected) = "dependency.rejected",
    DependencyReassigned(DependencyReassigned) = "dependency.reassigned",
    HandoffOffered(HandoffOffered) = "handoff.offered",
    HandoffAccepted(HandoffAccepted) = "handoff.accepted",
    HandoffDeclined(HandoffDeclined) = "handoff.declined",
    HandoffWithdrawn(HandoffWithdrawn) = "handoff.withdrawn",
    ReviewNominated(ReviewNominated) = "review.nominated",
    ReviewNominationAccepted(ReviewNominationAccepted) = "review.nomination_accepted",
    ReviewNominationDeclined(ReviewNominationDeclined) = "review.nomination_declined",
    ReviewChangesRequested(ReviewChangesRequested) = "review.changes_requested",
    ReviewFindingsCleared(ReviewFindingsCleared) = "review.findings_cleared",
    ReviewFindingsSuperseded(ReviewFindingsSuperseded) = "review.findings_superseded",
    ReviewReassigned(ReviewReassigned) = "review.reassigned",
    ReviewWithdrawn(ReviewWithdrawn) = "review.withdrawn",
    ReviewMergeAuthorized(ReviewMergeAuthorized) = "review.merge_authorized",
    ReviewMerged(ReviewMerged) = "review.merged",
    ReviewMergeReconciled(ReviewMergeReconciled) = "review.merge_reconciled",
    LifecycleConflictResolved(LifecycleConflictResolved) = "lifecycle.conflict_resolved",
    FrictionReported(FrictionReported) = "friction.reported",
    FrictionSynthesized(FrictionSynthesized) = "friction.synthesized",
    SubscriptionSet(SubscriptionSet) = "subscription.set",
    BroadcastPublished(BroadcastPublished) = "broadcast.published",
    BroadcastAcknowledged(BroadcastAcknowledged) = "broadcast.acknowledged",
    BroadcastSeen(BroadcastSeen) = "broadcast.seen",
}

impl EventData {
    /// The exact set of event IDs `refs` must equal (AGENT_BUS_SCHEMA.md
    /// section 2: "Every event ID occurring in `data` occurs in `refs`, and
    /// `refs` equals exactly the unique event IDs contained in `data`.").
    pub fn referenced_ids(&self) -> BTreeSet<EventId> {
        match self {
            EventData::AgentRegistered(_) => BTreeSet::new(),
            EventData::AgentStatus(_) => BTreeSet::new(),
            EventData::AgentResumed(d) => [d.previous_lifecycle.clone()].into(),
            EventData::AgentRetired(d) => [d.previous_lifecycle.clone()].into(),
            EventData::SchemaActivated(_) => BTreeSet::new(),
            EventData::MergeEngineActivated(d) => [d.previous_epoch.clone()].into(),
            EventData::ScopeSet(_) => BTreeSet::new(),
            EventData::PlanSet(_) => BTreeSet::new(),
            EventData::ProgressReported(_) => BTreeSet::new(),
            EventData::IssueOpened(d) => d
                .blocks
                .iter()
                .cloned()
                .chain(d.evidence.iter().cloned())
                .collect(),
            EventData::IssueAcknowledged(d) => [d.issue.clone(), d.assignment.clone()].into(),
            EventData::IssueResolved(d) => [d.issue.clone(), d.assignment.clone()].into(),
            EventData::IssueRejected(d) => [d.issue.clone(), d.assignment.clone()].into(),
            EventData::IssueReassigned(d) => {
                [d.issue.clone(), d.previous_assignment.clone()].into()
            }
            EventData::DependencyRequested(d) => d.evidence.iter().cloned().collect(),
            EventData::DependencyAcknowledged(d) => {
                [d.dependency.clone(), d.assignment.clone()].into()
            }
            EventData::DependencyResolved(d) => {
                [d.dependency.clone(), d.assignment.clone()].into()
            }
            EventData::DependencyRejected(d) => {
                [d.dependency.clone(), d.assignment.clone()].into()
            }
            EventData::DependencyReassigned(d) => {
                [d.dependency.clone(), d.previous_assignment.clone()].into()
            }
            EventData::HandoffOffered(d) => d
                .known_issues
                .iter()
                .cloned()
                .chain(d.evidence.iter().cloned())
                .collect(),
            EventData::HandoffAccepted(d) => [d.handoff.clone()].into(),
            EventData::HandoffDeclined(d) => [d.handoff.clone()].into(),
            EventData::HandoffWithdrawn(d) => [d.handoff.clone()].into(),
            EventData::ReviewNominated(d) => d.evidence.iter().cloned().collect(),
            EventData::ReviewNominationAccepted(d) => [d.nomination.clone()].into(),
            EventData::ReviewNominationDeclined(d) => [d.nomination.clone()].into(),
            EventData::ReviewChangesRequested(d) => [d.nomination.clone()]
                .into_iter()
                .chain(d.evidence.iter().cloned())
                .collect(),
            EventData::ReviewFindingsCleared(d) => {
                [d.nomination.clone(), d.changes_event.clone()].into()
            }
            EventData::ReviewFindingsSuperseded(d) => {
                [d.nomination.clone(), d.changes_event.clone()].into()
            }
            EventData::ReviewReassigned(d) => [d.replaces.clone()]
                .into_iter()
                .chain(d.inherited_findings.iter().map(|f| f.changes_event.clone()))
                .chain(d.evidence.iter().cloned())
                .collect(),
            EventData::ReviewWithdrawn(d) => [d.nomination.clone()].into(),
            EventData::ReviewMergeAuthorized(d) => {
                [d.nomination.clone(), d.merge_engine_epoch.clone()]
                    .into_iter()
                    .chain(d.finding_dispositions.iter().map(|f| f.changes_event.clone()))
                    .chain(d.evidence.iter().cloned())
                    .collect()
            }
            EventData::ReviewMerged(d) => [d.authorization.clone()].into(),
            EventData::ReviewMergeReconciled(d) => [d.authorization.clone()].into(),
            EventData::LifecycleConflictResolved(d) => [d.root.clone()]
                .into_iter()
                .chain(d.competing.iter().cloned())
                .collect(),
            EventData::FrictionReported(d) => d.evidence.iter().cloned().collect(),
            EventData::FrictionSynthesized(d) => d
                .reports
                .iter()
                .cloned()
                .chain(d.promoted_to.iter().cloned())
                .chain(d.duplicate_of.iter().cloned())
                .collect(),
            EventData::SubscriptionSet(_) => BTreeSet::new(),
            EventData::BroadcastPublished(d) => d.supersedes.iter().cloned().collect(),
            EventData::BroadcastAcknowledged(d) => d.broadcasts.iter().cloned().collect(),
            EventData::BroadcastSeen(d) => d.broadcasts.iter().cloned().collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn eid(agent: &str, seq: u64) -> EventId {
        EventId::new(&a(agent), seq)
    }

    fn short(s: &str) -> Short {
        Short::parse(s.to_string()).unwrap()
    }

    fn text(s: &str) -> Text {
        Text::parse(s.to_string()).unwrap()
    }

    #[test]
    fn role_display_covers_every_variant() {
        assert_eq!(Role::Implementor.to_string(), "implementor");
        assert_eq!(Role::Reviewer.to_string(), "reviewer");
        assert_eq!(Role::Coordinator.to_string(), "coordinator");
        assert_eq!(Role::Observer.to_string(), "observer");
    }

    #[test]
    fn lifecycle_status_deactivates_covers_every_variant() {
        assert!(!LifecycleStatus::Active.deactivates());
        assert!(!LifecycleStatus::Blocked.deactivates());
        assert!(!LifecycleStatus::Paused.deactivates());
        assert!(LifecycleStatus::Done.deactivates());
        assert!(LifecycleStatus::Abandoned.deactivates());
    }

    /// Every declared kind must round-trip through `to_value` /
    /// `from_kind_and_value` and report the matching `kind()` string --
    /// proves the macro-generated dispatch table is complete and self
    /// -consistent, not just individually testable per variant.
    #[test]
    fn dispatch_kind_all_kinds_and_value_roundtrip() {
        let previous = eid("alice", 0);
        let samples: Vec<EventData> = vec![
            EventData::AgentRegistered(AgentRegistered {
                display_name: short("Alice"),
                primary_role: Role::Implementor,
                purpose: text("x"),
                product_base: None,
                product_branch: None,
                provider: None,
                model: None,
            }),
            EventData::AgentStatus(AgentStatusEvent {
                status: LifecycleStatus::Active,
                note: text(""),
                product_branch: None,
                product_commit: None,
            }),
            EventData::AgentResumed(AgentResumed {
                previous_lifecycle: previous.clone(),
                reason: text("r"),
                user_authority: text("u"),
            }),
            EventData::AgentRetired(AgentRetired {
                target: a("bob"),
                previous_lifecycle: previous.clone(),
                reason: text("r"),
                user_authority: text("u"),
            }),
            EventData::SchemaActivated(SchemaActivated {
                version: 1,
                design_commit: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                helper_commit: crate::scalars::ObjectId::parse("b".repeat(40)).unwrap(),
            }),
            EventData::MergeEngineActivated(MergeEngineActivated {
                previous_epoch: previous.clone(),
                merge_engine: short("git-ort"),
                merge_engine_version: short("2.53.0"),
                design_commit: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                helper_commit: crate::scalars::ObjectId::parse("b".repeat(40)).unwrap(),
            }),
            EventData::ScopeSet(ScopeSet {
                base_code_commit: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                exclusive: StringSet::default(),
                shared: StringSet::default(),
                exports: StringSet::default(),
                depends_on: vec![],
                note: text(""),
            }),
            EventData::PlanSet(PlanSet {
                summary: text("s"),
                steps: vec![],
                risks: vec![],
            }),
            EventData::ProgressReported(ProgressReported {
                product_commit: None,
                completed: vec![],
                current: vec![],
                next: vec![],
                blockers: vec![],
                verification: vec![],
            }),
            EventData::IssueOpened(IssueOpened {
                target: a("bob"),
                issue_kind: IssueKind::Bug,
                severity: Priority::Normal,
                summary: text("s"),
                code_commit: None,
                locations: vec![],
                expected: None,
                observed_behavior: None,
                reproduction: vec![],
                blocks: StringSet::default(),
                evidence: StringSet::default(),
            }),
            EventData::IssueAcknowledged(IssueAcknowledged {
                issue: previous.clone(),
                assignment: previous.clone(),
                note: text(""),
            }),
            EventData::IssueResolved(IssueResolved {
                issue: previous.clone(),
                assignment: previous.clone(),
                summary: text("s"),
                fix_commit: None,
                verification: vec![],
            }),
            EventData::IssueRejected(IssueRejected {
                issue: previous.clone(),
                assignment: previous.clone(),
                reason: text("r"),
                normative_refs: vec![],
            }),
            EventData::IssueReassigned(IssueReassigned {
                issue: previous.clone(),
                previous_assignment: previous.clone(),
                previous_target: a("bob"),
                new_target: a("carol"),
                reason: text("r"),
            }),
            EventData::DependencyRequested(DependencyRequested {
                target: a("bob"),
                interface: short("iface"),
                needed_by: text("soon"),
                blocking: true,
                summary: text("s"),
                evidence: StringSet::default(),
            }),
            EventData::DependencyAcknowledged(DependencyAcknowledged {
                dependency: previous.clone(),
                assignment: previous.clone(),
                note: text(""),
            }),
            EventData::DependencyResolved(DependencyResolved {
                dependency: previous.clone(),
                assignment: previous.clone(),
                summary: text("s"),
                product_commit: None,
                verification: vec![],
            }),
            EventData::DependencyRejected(DependencyRejected {
                dependency: previous.clone(),
                assignment: previous.clone(),
                reason: text("r"),
            }),
            EventData::DependencyReassigned(DependencyReassigned {
                dependency: previous.clone(),
                previous_assignment: previous.clone(),
                previous_target: a("bob"),
                new_target: a("carol"),
                reason: text("r"),
            }),
            EventData::HandoffOffered(HandoffOffered {
                receiver: a("bob"),
                scope: StringSet::default(),
                product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                product_commit: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                verification: vec![],
                known_issues: StringSet::default(),
                evidence: StringSet::default(),
                summary: text("s"),
            }),
            EventData::HandoffAccepted(HandoffAccepted {
                handoff: previous.clone(),
                note: text(""),
            }),
            EventData::HandoffDeclined(HandoffDeclined {
                handoff: previous.clone(),
                reason: text("r"),
            }),
            EventData::HandoffWithdrawn(HandoffWithdrawn {
                handoff: previous.clone(),
                reason: text("r"),
            }),
            EventData::ReviewNominated(ReviewRequest {
                authors: StringSet::from_iter([a("alice")]),
                product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                reviewer: a("bob"),
                required_checks: vec![],
                review_scope: StringSet::default(),
                summary: text("s"),
                target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
                evidence: StringSet::default(),
            }),
            EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: previous.clone(),
                note: text(""),
            }),
            EventData::ReviewNominationDeclined(ReviewNominationDeclined {
                nomination: previous.clone(),
                reason: text("r"),
            }),
            EventData::ReviewChangesRequested(ReviewChangesRequested {
                nomination: previous.clone(),
                reviewed_commit: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                findings: vec![],
                evidence: StringSet::default(),
            }),
            EventData::ReviewFindingsCleared(ReviewFindingsCleared {
                nomination: previous.clone(),
                changes_event: previous.clone(),
                finding_id: short("f1"),
                resolved_commit: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                summary: text("s"),
            }),
            EventData::ReviewFindingsSuperseded(ReviewFindingsSuperseded {
                nomination: previous.clone(),
                changes_event: previous.clone(),
                finding_id: short("f1"),
                rationale: text("r"),
            }),
            EventData::ReviewReassigned(ReviewReassigned {
                authors: StringSet::from_iter([a("alice")]),
                product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                reviewer: a("carol"),
                required_checks: vec![],
                review_scope: StringSet::default(),
                summary: text("s"),
                target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
                evidence: StringSet::default(),
                replaces: previous.clone(),
                reason: text("r"),
                inherited_findings: vec![],
            }),
            EventData::ReviewWithdrawn(ReviewWithdrawn {
                nomination: previous.clone(),
                reason: text("r"),
            }),
            EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
                nomination: previous.clone(),
                product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                previous_main: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                reviewed_commit: crate::scalars::ObjectId::parse("b".repeat(40)).unwrap(),
                candidate: crate::scalars::ObjectId::parse("c".repeat(40)).unwrap(),
                merge_engine_epoch: previous.clone(),
                checks: vec![],
                finding_dispositions: vec![],
                evidence: StringSet::default(),
                reviewed_scope: StringSet::default(),
                limitations: vec![],
                summary: text("s"),
            }),
            EventData::ReviewMerged(ReviewMerged {
                authorization: previous.clone(),
                previous_main: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                main_commit: crate::scalars::ObjectId::parse("b".repeat(40)).unwrap(),
                product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                reviewed_commit: crate::scalars::ObjectId::parse("c".repeat(40)).unwrap(),
                summary: text("s"),
            }),
            EventData::ReviewMergeReconciled(ReviewMergeReconciled {
                authorization: previous.clone(),
                previous_main: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                main_commit: crate::scalars::ObjectId::parse("b".repeat(40)).unwrap(),
                product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                reviewed_commit: crate::scalars::ObjectId::parse("c".repeat(40)).unwrap(),
                reason: text("r"),
                user_authority: text("u"),
            }),
            EventData::LifecycleConflictResolved(LifecycleConflictResolved {
                root: previous.clone(),
                competing: StringSet::from_iter([previous.clone(), eid("bob", 0)]),
                selected: previous.clone(),
                reason: text("r"),
                user_authority: text("u"),
            }),
            EventData::FrictionReported(FrictionReported {
                area: CoordinationTopic::parse("proof.rebuild".into()).unwrap(),
                summary: short("s"),
                impact: crate::common::Impact::Rebuild,
                evidence: StringSet::default(),
                product_locations: vec![],
                measurements: vec![],
                frequency: None,
                workaround: None,
                suggestion: None,
                likely_owner: None,
            }),
            EventData::FrictionSynthesized(FrictionSynthesized {
                theme: CoordinationTopic::parse("proof.rebuild".into()).unwrap(),
                reports: StringSet::from_iter([previous.clone()]),
                disposition: crate::common::FrictionDispositionKind::AcceptedCost,
                rationale: text("r"),
                promoted_to: None,
                duplicate_of: None,
                revisit_trigger: None,
            }),
            EventData::SubscriptionSet(SubscriptionSet {
                topics: StringSet::from_iter([CoordinationTopic::parse("safety.memory".into()).unwrap()]),
            }),
            EventData::BroadcastPublished(BroadcastPublished {
                topics: StringSet::from_iter([CoordinationTopic::parse("release.main".into()).unwrap()]),
                importance: crate::common::Importance::Informational,
                summary: short("s"),
                detail: text("d"),
                affected_paths: StringSet::default(),
                affected_interfaces: StringSet::default(),
                product_commits: StringSet::default(),
                audience_selector: crate::common::AudienceSelector::AllActive,
                audience_epoch: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                audience_snapshot: StringSet::from_iter([a("bob")]),
                acknowledgement: crate::common::AckRequirement::None,
                deadline: None,
                supersedes: StringSet::default(),
                workaround: None,
                expiry_condition: None,
            }),
            EventData::BroadcastAcknowledged(BroadcastAcknowledged {
                broadcasts: StringSet::from_iter([previous.clone()]),
            }),
            EventData::BroadcastSeen(BroadcastSeen {
                broadcasts: StringSet::from_iter([previous.clone()]),
            }),
        ];

        let all_kinds: BTreeSet<&str> = EventData::all_kinds().into_iter().collect();
        let mut seen_kinds = BTreeSet::new();
        for sample in &samples {
            let kind = sample.kind();
            seen_kinds.insert(kind);
            let value = sample.to_value();
            let round_tripped = EventData::from_kind_and_value(kind, value.clone())
                .unwrap_or_else(|e| panic!("{kind} failed to round-trip: {e}"));
            assert_eq!(round_tripped.kind(), kind);
            assert_eq!(round_tripped.to_value(), value);
        }
        assert_eq!(
            seen_kinds, all_kinds,
            "every declared kind must have a sample exercising its round trip"
        );
    }

    #[test]
    fn referenced_ids_covers_every_event_kind() {
        // A spot check per shape, not every field: registration/status carry
        // no refs; single-ref events carry exactly one; multi-ref events
        // (issue/dependency assignment pairs, review chains) carry the
        // documented set.
        assert!(EventData::AgentRegistered(AgentRegistered {
            display_name: short("a"),
            primary_role: Role::Implementor,
            purpose: text("x"),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        })
        .referenced_ids()
        .is_empty());

        let prev = eid("alice", 0);
        assert_eq!(
            EventData::AgentResumed(AgentResumed {
                previous_lifecycle: prev.clone(),
                reason: text("r"),
                user_authority: text("u"),
            })
            .referenced_ids(),
            [prev.clone()].into()
        );

        let issue = eid("bob", 1);
        let assignment = eid("bob", 2);
        assert_eq!(
            EventData::IssueResolved(IssueResolved {
                issue: issue.clone(),
                assignment: assignment.clone(),
                summary: text("s"),
                fix_commit: None,
                verification: vec![],
            })
            .referenced_ids(),
            [issue, assignment].into()
        );

        let report = eid("carol", 3);
        let promoted = eid("carol", 4);
        assert_eq!(
            EventData::FrictionReported(FrictionReported {
                area: CoordinationTopic::parse("proof.rebuild".into()).unwrap(),
                summary: short("s"),
                impact: crate::common::Impact::Rebuild,
                evidence: StringSet::from_iter([report.clone()]),
                product_locations: vec![],
                measurements: vec![],
                frequency: None,
                workaround: None,
                suggestion: None,
                likely_owner: None,
            })
            .referenced_ids(),
            [report.clone()].into()
        );
        assert_eq!(
            EventData::FrictionSynthesized(FrictionSynthesized {
                theme: CoordinationTopic::parse("proof.rebuild".into()).unwrap(),
                reports: StringSet::from_iter([report.clone()]),
                disposition: crate::common::FrictionDispositionKind::Promoted,
                rationale: text("r"),
                promoted_to: Some(promoted.clone()),
                duplicate_of: None,
                revisit_trigger: None,
            })
            .referenced_ids(),
            [report, promoted].into()
        );

        assert_eq!(
            EventData::SubscriptionSet(SubscriptionSet {
                topics: StringSet::default(),
            })
            .referenced_ids(),
            BTreeSet::new()
        );

        let broadcast = eid("dave", 5);
        assert_eq!(
            EventData::BroadcastPublished(BroadcastPublished {
                topics: StringSet::default(),
                importance: crate::common::Importance::Critical,
                summary: short("s"),
                detail: text("d"),
                affected_paths: StringSet::default(),
                affected_interfaces: StringSet::default(),
                product_commits: StringSet::default(),
                audience_selector: crate::common::AudienceSelector::AllActive,
                audience_epoch: crate::scalars::ObjectId::parse("a".repeat(40)).unwrap(),
                audience_snapshot: StringSet::from_iter([a("bob")]),
                acknowledgement: crate::common::AckRequirement::Required,
                deadline: None,
                supersedes: StringSet::from_iter([broadcast.clone()]),
                workaround: None,
                expiry_condition: None,
            })
            .referenced_ids(),
            [broadcast.clone()].into()
        );
        assert_eq!(
            EventData::BroadcastAcknowledged(BroadcastAcknowledged {
                broadcasts: StringSet::from_iter([broadcast.clone()]),
            })
            .referenced_ids(),
            [broadcast.clone()].into()
        );
        assert_eq!(
            EventData::BroadcastSeen(BroadcastSeen {
                broadcasts: StringSet::from_iter([broadcast.clone()]),
            })
            .referenced_ids(),
            [broadcast].into()
        );
    }

    #[test]
    fn issue_opened_rejects_duplicate_evidence_ids() {
        let dup = eid("alice", 0);
        let value = serde_json::json!({
            "target": "bob",
            "issue_kind": "bug",
            "severity": "normal",
            "summary": "s",
            "locations": [],
            "reproduction": [],
            "blocks": [],
            "evidence": [dup.to_string(), dup.to_string()],
        });
        let err = EventData::from_kind_and_value("issue.opened", value).unwrap_err();
        assert!(err.to_string().contains("duplicate"), "{err}");
    }

    #[test]
    fn deny_unknown_fields_is_enforced() {
        let value = serde_json::json!({
            "status": "active",
            "note": "",
            "surprise": true,
        });
        let err = EventData::from_kind_and_value("agent.status", value).unwrap_err();
        assert!(err.to_string().contains("malformed"), "{err}");
    }

    #[test]
    fn text_field_rejects_out_of_bounds_length() {
        let value = serde_json::json!({
            "status": "active",
            "note": "x".repeat(4097),
        });
        assert!(EventData::from_kind_and_value("agent.status", value).is_err());
    }
}
