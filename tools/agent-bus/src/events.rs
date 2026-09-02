//! Event data payloads (AGENT_BUS_SCHEMA.md sections 4-9) and the `kind` vocabulary.

use crate::common::*;
use crate::error::{invalid, AbResult};
use crate::scalars::{Agent, Branch, EventId, ObjectId, Short, StringSet, Text};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::fmt;

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
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

// -------------------------------------------------------- scope/plan/progress

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

// ----------------------------------------------------------------- issues

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

/// Not itself (de)serialized: `#[serde(flatten)]` is incompatible with
/// `deny_unknown_fields`, so `ReviewNominated`/`ReviewReassigned` inline these
/// fields directly and expose this as a comparison/copy view.
#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewNominated {
    pub authors: StringSet<Agent>,
    pub product_branch: Branch,
    pub reviewer: Agent,
    pub required_checks: Vec<Text>,
    pub review_scope: StringSet<crate::scalars::PathClaim>,
    pub summary: Text,
    pub target_branch: Branch,
    pub evidence: StringSet<EventId>,
}

impl ReviewNominated {
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

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LifecycleConflictResolved {
    pub root: EventId,
    pub competing: StringSet<EventId>,
    pub selected: EventId,
    pub reason: Text,
    pub user_authority: Text,
}

// ------------------------------------------------------------------ dispatch

macro_rules! event_data_enum {
    ($( $variant:ident => $kind:expr => $ty:ty ),+ $(,)?) => {
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

            pub fn all_kinds() -> &'static [&'static str] {
                &[ $( $kind ),+ ]
            }

            pub fn from_kind_and_value(kind: &str, value: serde_json::Value) -> AbResult<EventData> {
                match kind {
                    $( $kind => Ok(EventData::$variant(
                        serde_json::from_value(value).map_err(|e| invalid(format!("data for {kind}: {e}")))?
                    )), )+
                    other => Err(invalid(format!("unknown event kind: {other}"))),
                }
            }

            pub fn to_value(&self) -> serde_json::Value {
                match self {
                    $( EventData::$variant(d) => serde_json::to_value(d).expect("serializable"), )+
                }
            }
        }
    };
}

event_data_enum! {
    AgentRegistered => "agent.registered" => AgentRegistered,
    AgentStatus => "agent.status" => AgentStatusEvent,
    AgentResumed => "agent.resumed" => AgentResumed,
    AgentRetired => "agent.retired" => AgentRetired,
    SchemaActivated => "schema.activated" => SchemaActivated,
    MergeEngineActivated => "merge_engine.activated" => MergeEngineActivated,
    ScopeSet => "scope.set" => ScopeSet,
    PlanSet => "plan.set" => PlanSet,
    ProgressReported => "progress.reported" => ProgressReported,
    IssueOpened => "issue.opened" => IssueOpened,
    IssueAcknowledged => "issue.acknowledged" => IssueAcknowledged,
    IssueResolved => "issue.resolved" => IssueResolved,
    IssueRejected => "issue.rejected" => IssueRejected,
    IssueReassigned => "issue.reassigned" => IssueReassigned,
    DependencyRequested => "dependency.requested" => DependencyRequested,
    DependencyAcknowledged => "dependency.acknowledged" => DependencyAcknowledged,
    DependencyResolved => "dependency.resolved" => DependencyResolved,
    DependencyRejected => "dependency.rejected" => DependencyRejected,
    DependencyReassigned => "dependency.reassigned" => DependencyReassigned,
    HandoffOffered => "handoff.offered" => HandoffOffered,
    HandoffAccepted => "handoff.accepted" => HandoffAccepted,
    HandoffDeclined => "handoff.declined" => HandoffDeclined,
    HandoffWithdrawn => "handoff.withdrawn" => HandoffWithdrawn,
    ReviewNominated => "review.nominated" => ReviewNominated,
    ReviewNominationAccepted => "review.nomination_accepted" => ReviewNominationAccepted,
    ReviewNominationDeclined => "review.nomination_declined" => ReviewNominationDeclined,
    ReviewChangesRequested => "review.changes_requested" => ReviewChangesRequested,
    ReviewFindingsCleared => "review.findings_cleared" => ReviewFindingsCleared,
    ReviewFindingsSuperseded => "review.findings_superseded" => ReviewFindingsSuperseded,
    ReviewReassigned => "review.reassigned" => ReviewReassigned,
    ReviewWithdrawn => "review.withdrawn" => ReviewWithdrawn,
    ReviewMergeAuthorized => "review.merge_authorized" => ReviewMergeAuthorized,
    ReviewMerged => "review.merged" => ReviewMerged,
    ReviewMergeReconciled => "review.merge_reconciled" => ReviewMergeReconciled,
    LifecycleConflictResolved => "lifecycle.conflict_resolved" => LifecycleConflictResolved,
}

impl EventData {
    /// The exact set of event IDs that must appear in the envelope `refs` field
    /// (AGENT_BUS_SCHEMA.md section 2: "refs equals exactly the unique event IDs contained in data").
    pub fn referenced_ids(&self) -> BTreeSet<EventId> {
        let mut out = BTreeSet::new();
        match self {
            EventData::AgentRegistered(_) => {}
            EventData::AgentStatus(_) => {}
            EventData::AgentResumed(d) => {
                out.insert(d.previous_lifecycle.clone());
            }
            EventData::AgentRetired(d) => {
                out.insert(d.previous_lifecycle.clone());
            }
            EventData::SchemaActivated(_) => {}
            EventData::MergeEngineActivated(d) => {
                out.insert(d.previous_epoch.clone());
            }
            EventData::ScopeSet(_) => {}
            EventData::PlanSet(_) => {}
            EventData::ProgressReported(_) => {}
            EventData::IssueOpened(d) => {
                out.extend(d.blocks.iter().cloned());
                out.extend(d.evidence.iter().cloned());
            }
            EventData::IssueAcknowledged(d) => {
                out.insert(d.issue.clone());
                out.insert(d.assignment.clone());
            }
            EventData::IssueResolved(d) => {
                out.insert(d.issue.clone());
                out.insert(d.assignment.clone());
            }
            EventData::IssueRejected(d) => {
                out.insert(d.issue.clone());
                out.insert(d.assignment.clone());
            }
            EventData::IssueReassigned(d) => {
                out.insert(d.issue.clone());
                out.insert(d.previous_assignment.clone());
            }
            EventData::DependencyRequested(d) => {
                out.extend(d.evidence.iter().cloned());
            }
            EventData::DependencyAcknowledged(d) => {
                out.insert(d.dependency.clone());
                out.insert(d.assignment.clone());
            }
            EventData::DependencyResolved(d) => {
                out.insert(d.dependency.clone());
                out.insert(d.assignment.clone());
            }
            EventData::DependencyRejected(d) => {
                out.insert(d.dependency.clone());
                out.insert(d.assignment.clone());
            }
            EventData::DependencyReassigned(d) => {
                out.insert(d.dependency.clone());
                out.insert(d.previous_assignment.clone());
            }
            EventData::HandoffOffered(d) => {
                out.extend(d.known_issues.iter().cloned());
                out.extend(d.evidence.iter().cloned());
            }
            EventData::HandoffAccepted(d) => {
                out.insert(d.handoff.clone());
            }
            EventData::HandoffDeclined(d) => {
                out.insert(d.handoff.clone());
            }
            EventData::HandoffWithdrawn(d) => {
                out.insert(d.handoff.clone());
            }
            EventData::ReviewNominated(d) => {
                out.extend(d.evidence.iter().cloned());
            }
            EventData::ReviewNominationAccepted(d) => {
                out.insert(d.nomination.clone());
            }
            EventData::ReviewNominationDeclined(d) => {
                out.insert(d.nomination.clone());
            }
            EventData::ReviewChangesRequested(d) => {
                out.insert(d.nomination.clone());
                out.extend(d.evidence.iter().cloned());
            }
            EventData::ReviewFindingsCleared(d) => {
                out.insert(d.nomination.clone());
                out.insert(d.changes_event.clone());
            }
            EventData::ReviewFindingsSuperseded(d) => {
                out.insert(d.nomination.clone());
                out.insert(d.changes_event.clone());
            }
            EventData::ReviewReassigned(d) => {
                out.insert(d.replaces.clone());
                for f in &d.inherited_findings {
                    out.insert(f.changes_event.clone());
                }
                out.extend(d.evidence.iter().cloned());
            }
            EventData::ReviewWithdrawn(d) => {
                out.insert(d.nomination.clone());
            }
            EventData::ReviewMergeAuthorized(d) => {
                out.insert(d.nomination.clone());
                out.insert(d.merge_engine_epoch.clone());
                for fd in &d.finding_dispositions {
                    out.insert(fd.changes_event.clone());
                }
                out.extend(d.evidence.iter().cloned());
            }
            EventData::ReviewMerged(d) => {
                out.insert(d.authorization.clone());
            }
            EventData::ReviewMergeReconciled(d) => {
                out.insert(d.authorization.clone());
            }
            EventData::LifecycleConflictResolved(d) => {
                out.insert(d.root.clone());
                out.extend(d.competing.iter().cloned());
            }
        }
        out
    }
}
