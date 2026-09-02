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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{
        CheckOutcome, CheckResult, DependencyImport, Finding, FindingDisposition, FindingDispositionKind,
        FindingRef, PlanStep, PlanStepState, Priority,
    };
    use crate::scalars::PathClaim;

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn eid(agent: &Agent, seq: u64) -> EventId {
        EventId::new(agent, seq)
    }

    fn hash(n: u64) -> String {
        format!("{n:040x}")
    }

    fn oid(n: u64) -> ObjectId {
        ObjectId::parse(hash(n)).unwrap()
    }

    fn short(s: &str) -> Short {
        Short::parse(s.to_string()).unwrap()
    }

    fn text(s: &str) -> Text {
        Text::parse(s.to_string()).unwrap()
    }

    fn branch(s: &str) -> Branch {
        Branch::parse(s.to_string()).unwrap()
    }

    fn pc(s: &str) -> PathClaim {
        PathClaim::parse(s.to_string()).unwrap()
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

    #[test]
    fn dispatch_kind_all_kinds_and_value_roundtrip() {
        assert_eq!(EventData::all_kinds().len(), 35);
        let schema = EventData::SchemaActivated(SchemaActivated {
            version: 1,
            design_commit: oid(1),
            helper_commit: oid(2),
        });
        assert_eq!(schema.kind(), "schema.activated");
        let value = schema.to_value();
        let round_tripped = EventData::from_kind_and_value("schema.activated", value).unwrap();
        assert_eq!(round_tripped.kind(), "schema.activated");

        assert!(EventData::from_kind_and_value("not.a.kind", serde_json::json!({})).is_err());
        // Well-formed kind, malformed data for it.
        assert!(EventData::from_kind_and_value("schema.activated", serde_json::json!({"nonsense": true})).is_err());
    }

    #[test]
    fn deny_unknown_fields_is_enforced() {
        let mut value = serde_json::json!({
            "version": 1,
            "design_commit": hash(1),
            "helper_commit": hash(2),
        });
        assert!(serde_json::from_value::<SchemaActivated>(value.clone()).is_ok());
        value["surprise"] = serde_json::json!("unexpected");
        let err = serde_json::from_value::<SchemaActivated>(value).unwrap_err();
        assert!(err.to_string().contains("unknown field"), "{err}");
    }

    #[test]
    fn issue_opened_rejects_duplicate_evidence_ids() {
        let ev = eid(&a("bob"), 1);
        let value = serde_json::json!({
            "target": "bob",
            "issue_kind": "bug",
            "severity": "high",
            "summary": "s",
            "locations": [],
            "reproduction": [],
            "blocks": [],
            "evidence": [ev.to_string(), ev.to_string()],
        });
        let err = serde_json::from_value::<IssueOpened>(value).unwrap_err();
        assert!(err.to_string().contains("duplicate"), "{err}");
    }

    #[test]
    fn text_field_rejects_out_of_bounds_length() {
        let too_long = "x".repeat(4097);
        let value = serde_json::json!({
            "status": "active",
            "note": too_long,
        });
        assert!(serde_json::from_value::<AgentStatusEvent>(value).is_err());
    }

    #[test]
    fn referenced_ids_covers_every_event_kind() {
        let alice = a("alice");
        let bob = a("bob");

        // ---- kinds with no referenced ids at all ----
        let reg = AgentRegistered {
            display_name: short("Alice"),
            primary_role: Role::Implementor,
            purpose: text("does stuff"),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        };
        assert!(EventData::AgentRegistered(reg).referenced_ids().is_empty());

        let status = AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: text(""),
            product_branch: None,
            product_commit: None,
        };
        assert!(EventData::AgentStatus(status).referenced_ids().is_empty());

        let schema = SchemaActivated { version: 1, design_commit: oid(1), helper_commit: oid(2) };
        assert!(EventData::SchemaActivated(schema).referenced_ids().is_empty());

        let scope = ScopeSet {
            base_code_commit: oid(3),
            exclusive: StringSet::build(vec![pc("a/**")]),
            shared: StringSet::default(),
            exports: StringSet::default(),
            depends_on: vec![DependencyImport { agent: bob.clone(), interface: short("api") }],
            note: text("n"),
        };
        assert!(EventData::ScopeSet(scope).referenced_ids().is_empty());

        let plan = PlanSet {
            summary: text("s"),
            steps: vec![PlanStep { id: short("s1"), state: PlanStepState::Active, text: text("t") }],
            risks: vec![text("r")],
        };
        assert!(EventData::PlanSet(plan).referenced_ids().is_empty());

        let progress = ProgressReported {
            product_commit: Some(oid(4)),
            completed: vec![text("c")],
            current: vec![],
            next: vec![],
            blockers: vec![],
            verification: vec![],
        };
        assert!(EventData::ProgressReported(progress).referenced_ids().is_empty());

        // ---- single previous_lifecycle / previous_epoch ----
        let prev = eid(&alice, 3);
        let resumed = AgentResumed { previous_lifecycle: prev.clone(), reason: text("r"), user_authority: text("u") };
        assert_eq!(EventData::AgentResumed(resumed).referenced_ids(), BTreeSet::from([prev.clone()]));

        let retired = AgentRetired {
            target: alice.clone(),
            previous_lifecycle: prev.clone(),
            reason: text("r"),
            user_authority: text("u"),
        };
        assert_eq!(EventData::AgentRetired(retired).referenced_ids(), BTreeSet::from([prev.clone()]));

        let epoch = eid(&alice, 0);
        let mea = MergeEngineActivated {
            previous_epoch: epoch.clone(),
            merge_engine: short("git-ort"),
            merge_engine_version: short("2.53.0"),
            design_commit: oid(5),
            helper_commit: oid(6),
        };
        assert_eq!(EventData::MergeEngineActivated(mea).referenced_ids(), BTreeSet::from([epoch.clone()]));

        // ---- issue.* ----
        let ev1 = eid(&alice, 1);
        let ev2 = eid(&bob, 2);
        let issue_opened = IssueOpened {
            target: bob.clone(),
            issue_kind: IssueKind::Bug,
            severity: Priority::High,
            summary: text("s"),
            code_commit: Some(oid(7)),
            locations: vec![text("f:1")],
            expected: Some(text("e")),
            observed_behavior: Some(text("o")),
            reproduction: vec![],
            blocks: StringSet::build(vec![ev1.clone()]),
            evidence: StringSet::build(vec![ev2.clone()]),
        };
        assert_eq!(
            EventData::IssueOpened(issue_opened).referenced_ids(),
            [ev1.clone(), ev2.clone()].into_iter().collect()
        );

        let issue_id = eid(&bob, 1);
        let assign_id = eid(&bob, 2);
        let ack = IssueAcknowledged { issue: issue_id.clone(), assignment: assign_id.clone(), note: text("n") };
        assert_eq!(
            EventData::IssueAcknowledged(ack).referenced_ids(),
            BTreeSet::from([issue_id.clone(), assign_id.clone()])
        );

        let resolved = IssueResolved {
            issue: issue_id.clone(),
            assignment: assign_id.clone(),
            summary: text("s"),
            fix_commit: Some(oid(8)),
            verification: vec![],
        };
        assert_eq!(
            EventData::IssueResolved(resolved).referenced_ids(),
            BTreeSet::from([issue_id.clone(), assign_id.clone()])
        );

        let rejected =
            IssueRejected { issue: issue_id.clone(), assignment: assign_id.clone(), reason: text("r"), normative_refs: vec![] };
        assert_eq!(
            EventData::IssueRejected(rejected).referenced_ids(),
            BTreeSet::from([issue_id.clone(), assign_id.clone()])
        );

        let reassigned = IssueReassigned {
            issue: issue_id.clone(),
            previous_assignment: assign_id.clone(),
            previous_target: alice.clone(),
            new_target: bob.clone(),
            reason: text("r"),
        };
        assert_eq!(
            EventData::IssueReassigned(reassigned).referenced_ids(),
            BTreeSet::from([issue_id.clone(), assign_id.clone()])
        );

        // ---- dependency.* ----
        let dep_requested = DependencyRequested {
            target: bob.clone(),
            interface: short("api"),
            needed_by: text("soon"),
            blocking: true,
            summary: text("s"),
            evidence: StringSet::build(vec![ev1.clone()]),
        };
        assert_eq!(EventData::DependencyRequested(dep_requested).referenced_ids(), BTreeSet::from([ev1.clone()]));

        let dep_id = eid(&alice, 5);
        let dep_assign = eid(&alice, 6);
        let dep_ack = DependencyAcknowledged { dependency: dep_id.clone(), assignment: dep_assign.clone(), note: text("n") };
        assert_eq!(
            EventData::DependencyAcknowledged(dep_ack).referenced_ids(),
            BTreeSet::from([dep_id.clone(), dep_assign.clone()])
        );

        let dep_resolved = DependencyResolved {
            dependency: dep_id.clone(),
            assignment: dep_assign.clone(),
            summary: text("s"),
            product_commit: Some(oid(9)),
            verification: vec![],
        };
        assert_eq!(
            EventData::DependencyResolved(dep_resolved).referenced_ids(),
            BTreeSet::from([dep_id.clone(), dep_assign.clone()])
        );

        let dep_rejected =
            DependencyRejected { dependency: dep_id.clone(), assignment: dep_assign.clone(), reason: text("r") };
        assert_eq!(
            EventData::DependencyRejected(dep_rejected).referenced_ids(),
            BTreeSet::from([dep_id.clone(), dep_assign.clone()])
        );

        let dep_reassigned = DependencyReassigned {
            dependency: dep_id.clone(),
            previous_assignment: dep_assign.clone(),
            previous_target: alice.clone(),
            new_target: bob.clone(),
            reason: text("r"),
        };
        assert_eq!(
            EventData::DependencyReassigned(dep_reassigned).referenced_ids(),
            BTreeSet::from([dep_id.clone(), dep_assign.clone()])
        );

        // ---- handoff.* ----
        let issue_ref = eid(&bob, 9);
        let evid_ref = eid(&bob, 10);
        let handoff_offered = HandoffOffered {
            receiver: bob.clone(),
            scope: StringSet::build(vec![pc("a/**")]),
            product_branch: branch("refs/heads/agent/alice/x"),
            product_commit: oid(10),
            verification: vec![],
            known_issues: StringSet::build(vec![issue_ref.clone()]),
            evidence: StringSet::build(vec![evid_ref.clone()]),
            summary: text("s"),
        };
        assert_eq!(
            EventData::HandoffOffered(handoff_offered).referenced_ids(),
            [issue_ref.clone(), evid_ref.clone()].into_iter().collect()
        );

        let handoff_id = eid(&alice, 11);
        let handoff_accepted = HandoffAccepted { handoff: handoff_id.clone(), note: text("n") };
        assert_eq!(EventData::HandoffAccepted(handoff_accepted).referenced_ids(), BTreeSet::from([handoff_id.clone()]));

        let handoff_declined = HandoffDeclined { handoff: handoff_id.clone(), reason: text("r") };
        assert_eq!(EventData::HandoffDeclined(handoff_declined).referenced_ids(), BTreeSet::from([handoff_id.clone()]));

        let handoff_withdrawn = HandoffWithdrawn { handoff: handoff_id.clone(), reason: text("r") };
        assert_eq!(
            EventData::HandoffWithdrawn(handoff_withdrawn).referenced_ids(),
            BTreeSet::from([handoff_id.clone()])
        );

        // ---- review.* ----
        let review_evidence = eid(&bob, 12);
        let review_nominated = ReviewNominated {
            authors: StringSet::build(vec![alice.clone()]),
            product_branch: branch("refs/heads/agent/alice/x"),
            reviewer: bob.clone(),
            required_checks: vec![text("build")],
            review_scope: StringSet::build(vec![pc("a/**")]),
            summary: text("s"),
            target_branch: branch("refs/heads/main"),
            evidence: StringSet::build(vec![review_evidence.clone()]),
        };
        assert_eq!(
            EventData::ReviewNominated(review_nominated.clone()).referenced_ids(),
            BTreeSet::from([review_evidence.clone()])
        );
        let req = review_nominated.request();
        assert_eq!(req.reviewer, bob);

        let nomination_id = eid(&alice, 13);
        let nom_accepted = ReviewNominationAccepted { nomination: nomination_id.clone(), note: text("n") };
        assert_eq!(
            EventData::ReviewNominationAccepted(nom_accepted).referenced_ids(),
            BTreeSet::from([nomination_id.clone()])
        );

        let nom_declined = ReviewNominationDeclined { nomination: nomination_id.clone(), reason: text("r") };
        assert_eq!(
            EventData::ReviewNominationDeclined(nom_declined).referenced_ids(),
            BTreeSet::from([nomination_id.clone()])
        );

        let changes_evidence = eid(&bob, 14);
        let changes_requested = ReviewChangesRequested {
            nomination: nomination_id.clone(),
            reviewed_commit: oid(11),
            findings: vec![Finding {
                id: short("f1"),
                priority: Priority::High,
                locations: vec![text("f:1")],
                rationale: text("r"),
                closure_conditions: text("c"),
            }],
            evidence: StringSet::build(vec![changes_evidence.clone()]),
        };
        assert_eq!(
            EventData::ReviewChangesRequested(changes_requested).referenced_ids(),
            BTreeSet::from([nomination_id.clone(), changes_evidence.clone()])
        );

        let changes_event = eid(&bob, 15);
        let findings_cleared = ReviewFindingsCleared {
            nomination: nomination_id.clone(),
            changes_event: changes_event.clone(),
            finding_id: short("f1"),
            resolved_commit: oid(12),
            summary: text("s"),
        };
        assert_eq!(
            EventData::ReviewFindingsCleared(findings_cleared).referenced_ids(),
            BTreeSet::from([nomination_id.clone(), changes_event.clone()])
        );

        let findings_superseded = ReviewFindingsSuperseded {
            nomination: nomination_id.clone(),
            changes_event: changes_event.clone(),
            finding_id: short("f1"),
            rationale: text("r"),
        };
        assert_eq!(
            EventData::ReviewFindingsSuperseded(findings_superseded).referenced_ids(),
            BTreeSet::from([nomination_id.clone(), changes_event.clone()])
        );

        let replaces = nomination_id.clone();
        let review_reassigned = ReviewReassigned {
            authors: StringSet::build(vec![alice.clone()]),
            product_branch: branch("refs/heads/agent/alice/x"),
            reviewer: bob.clone(),
            required_checks: vec![],
            review_scope: StringSet::build(vec![pc("a/**")]),
            summary: text("s"),
            target_branch: branch("refs/heads/main"),
            evidence: StringSet::build(vec![review_evidence.clone()]),
            replaces: replaces.clone(),
            reason: text("r"),
            inherited_findings: vec![FindingRef { changes_event: changes_event.clone(), finding_id: short("f1") }],
        };
        let expected: BTreeSet<EventId> =
            [replaces.clone(), changes_event.clone(), review_evidence.clone()].into_iter().collect();
        assert_eq!(EventData::ReviewReassigned(review_reassigned.clone()).referenced_ids(), expected);
        let req2 = review_reassigned.request();
        assert_eq!(req2.reviewer, bob);

        let review_withdrawn = ReviewWithdrawn { nomination: nomination_id.clone(), reason: text("r") };
        assert_eq!(
            EventData::ReviewWithdrawn(review_withdrawn).referenced_ids(),
            BTreeSet::from([nomination_id.clone()])
        );

        let merge_epoch = eid(&alice, 0);
        let fd_changes_event = eid(&bob, 16);
        let merge_evidence = eid(&bob, 17);
        let merge_authorized = ReviewMergeAuthorized {
            nomination: nomination_id.clone(),
            product_branch: branch("refs/heads/agent/alice/x"),
            previous_main: oid(13),
            reviewed_commit: oid(14),
            candidate: oid(15),
            merge_engine_epoch: merge_epoch.clone(),
            checks: vec![CheckResult { command: text("build"), result: CheckOutcome::Passed, evidence: None }],
            finding_dispositions: vec![FindingDisposition {
                changes_event: fd_changes_event.clone(),
                finding_id: short("f1"),
                disposition: FindingDispositionKind::Cleared,
                rationale: text("r"),
            }],
            evidence: StringSet::build(vec![merge_evidence.clone()]),
            reviewed_scope: StringSet::build(vec![pc("a/**")]),
            limitations: vec![],
            summary: text("s"),
        };
        let expected: BTreeSet<EventId> =
            [nomination_id.clone(), merge_epoch.clone(), fd_changes_event.clone(), merge_evidence.clone()]
                .into_iter()
                .collect();
        assert_eq!(EventData::ReviewMergeAuthorized(merge_authorized).referenced_ids(), expected);

        let authorization_id = eid(&bob, 18);
        let review_merged = ReviewMerged {
            authorization: authorization_id.clone(),
            previous_main: oid(16),
            main_commit: oid(17),
            product_branch: branch("refs/heads/main"),
            reviewed_commit: oid(18),
            summary: text("s"),
        };
        assert_eq!(
            EventData::ReviewMerged(review_merged).referenced_ids(),
            BTreeSet::from([authorization_id.clone()])
        );

        let review_reconciled = ReviewMergeReconciled {
            authorization: authorization_id.clone(),
            previous_main: oid(19),
            main_commit: oid(20),
            product_branch: branch("refs/heads/main"),
            reviewed_commit: oid(21),
            reason: text("r"),
            user_authority: text("u"),
        };
        assert_eq!(
            EventData::ReviewMergeReconciled(review_reconciled).referenced_ids(),
            BTreeSet::from([authorization_id.clone()])
        );

        // ---- lifecycle.conflict_resolved ----
        let root = eid(&alice, 20);
        let comp1 = eid(&alice, 21);
        let comp2 = eid(&bob, 22);
        let lifecycle_resolved = LifecycleConflictResolved {
            root: root.clone(),
            competing: StringSet::build(vec![comp1.clone(), comp2.clone()]),
            selected: comp1.clone(),
            reason: text("r"),
            user_authority: text("u"),
        };
        let expected: BTreeSet<EventId> = [root.clone(), comp1.clone(), comp2.clone()].into_iter().collect();
        assert_eq!(EventData::LifecycleConflictResolved(lifecycle_resolved).referenced_ids(), expected);
    }
}
