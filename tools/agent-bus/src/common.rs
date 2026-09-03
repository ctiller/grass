//! Common records shared across event kinds (AGENT_BUS_SCHEMA.md section 3).

use crate::scalars::{Agent, EventId, Short, Text};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(deny_unknown_fields)]
pub struct DependencyImport {
    pub agent: Agent,
    pub interface: Short,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum PlanStepState {
    Pending,
    Active,
    Done,
    Dropped,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PlanStep {
    pub id: Short,
    pub state: PlanStepState,
    pub text: Text,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum Priority {
    Critical,
    High,
    Normal,
    Low,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Finding {
    pub id: Short,
    pub priority: Priority,
    pub locations: Vec<Text>,
    pub rationale: Text,
    pub closure_conditions: Text,
}

/// A finding's global identity is `(changes_event, finding_id)` -- the id
/// alone is only unique within one `review.changes_requested`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(deny_unknown_fields)]
pub struct FindingRef {
    pub changes_event: EventId,
    pub finding_id: Short,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum FindingDispositionKind {
    Cleared,
    Superseded,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FindingDisposition {
    pub changes_event: EventId,
    pub finding_id: Short,
    pub disposition: FindingDispositionKind,
    pub rationale: Text,
}

/// Occurs only inside `review.merge_authorized`, so `Passed` is its sole
/// variant: a failed check is reported through `progress.reported` (and
/// normally produces `review.changes_requested`) rather than appearing here.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CheckOutcome {
    Passed,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CheckResult {
    pub command: Text,
    pub result: CheckOutcome,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub evidence: Option<Text>,
}
