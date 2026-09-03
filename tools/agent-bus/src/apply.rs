//! Semantic validation and state reduction (AGENT_BUS.md section 7,
//! AGENT_BUS_SCHEMA.md sections 4-10). Reduces a set of per-agent streams
//! into a `BusState`, in any dependency-respecting order -- unlike version
//! one's single linear branch, there is no canonical global order, so every
//! rule here is written to depend only on already-applied state and the
//! current event's own declared frontier, never on "what position was this
//! walked at." Git/product-repo cross-checks (candidate tags, merge
//! -authorship trailers, `main` history) are deliberately NOT done here.

use crate::bootstrap::BusConfig;
use crate::envelope::Envelope;
use crate::error::{invalid, AbResult};
use crate::events::*;
use crate::scalars::{Agent, EventId};
use crate::state::*;
use std::collections::{BTreeMap, BTreeSet};

/// Reduces every known stream into a `BusState`. `streams` maps each agent
/// to its full, already-validated event list (`stream::read_stream`), in
/// stream order. Processes events in a dependency-respecting order (each
/// event only after every event its frontier named as observed, and after
/// its own stream's immediately preceding event); any valid such order
/// gives the identical final state (gates 15/16), since exclusive
/// -transition resolution is itself order-independent (`exclusive.rs`) and
/// every per-kind rule below only ever inspects already-applied state plus
/// the current event's own declared references.
pub fn reduce(
    config: BusConfig,
    roster_epoch: Option<crate::registry::RosterEpoch>,
    streams: &BTreeMap<Agent, Vec<Envelope>>,
) -> AbResult<BusState> {
    let mut state = BusState::new(config);
    state.roster_epoch = roster_epoch;
    for env in topological_order(streams)? {
        apply_event(&mut state, env)?;
        state.kind_of_event_insert(env.id.clone(), &env.kind);
        state.events.insert(env.id.clone(), env.clone());
        if let Some(ag) = state.agents.get_mut(&env.agent) {
            ag.next_seq = ag.next_seq.max(env.seq + 1);
        }
    }
    Ok(state)
}

/// Applies additional already-reduced events onto an existing state (used
/// for incremental validation): the events must already be in a
/// dependency-respecting order relative to `state` and each other.
pub fn reduce_onto(mut state: BusState, new_events: &[Envelope]) -> AbResult<BusState> {
    for env in new_events {
        apply_event(&mut state, env)?;
        state.kind_of_event_insert(env.id.clone(), &env.kind);
        state.events.insert(env.id.clone(), env.clone());
        if let Some(ag) = state.agents.get_mut(&env.agent) {
            ag.next_seq = ag.next_seq.max(env.seq + 1);
        }
    }
    Ok(state)
}

/// Dry-run one not-yet-published event against `state` (a clone is mutated
/// and discarded), so a submission command can refuse to publish an event
/// that reduction would reject.
pub fn dry_run(state: &BusState, env: &Envelope) -> AbResult<()> {
    let mut trial = state.clone();
    apply_event(&mut trial, env)
}

/// A valid linear extension of the causal partial order: each event only
/// after its own stream's immediately preceding event and after every
/// cross-agent event it references. Ties are broken by `EventId` purely for
/// deterministic, reproducible test behavior -- correctness does not depend
/// on which valid order is chosen (gate 16).
fn topological_order(streams: &BTreeMap<Agent, Vec<Envelope>>) -> AbResult<Vec<&Envelope>> {
    let mut by_id: BTreeMap<EventId, &Envelope> = BTreeMap::new();
    for events in streams.values() {
        for e in events {
            by_id.insert(e.id.clone(), e);
        }
    }
    let mut deps: BTreeMap<EventId, Vec<EventId>> = BTreeMap::new();
    for events in streams.values() {
        for (i, e) in events.iter().enumerate() {
            let mut d = Vec::new();
            if i > 0 {
                d.push(events[i - 1].id.clone());
            }
            for r in e.refs.iter() {
                if r.agent() != e.agent {
                    d.push(r.clone());
                }
            }
            deps.insert(e.id.clone(), d);
        }
    }

    let mut remaining_deps = deps.clone();
    let mut ready: std::collections::BTreeSet<EventId> = remaining_deps
        .iter()
        .filter(|(_, d)| d.is_empty())
        .map(|(id, _)| id.clone())
        .collect();
    let mut dependents: BTreeMap<EventId, Vec<EventId>> = BTreeMap::new();
    for (id, d) in &deps {
        for dep in d {
            dependents.entry(dep.clone()).or_default().push(id.clone());
        }
    }

    let mut order = Vec::new();
    while let Some(id) = ready.iter().next().cloned() {
        ready.remove(&id);
        remaining_deps.remove(&id);
        order.push(id.clone());
        if let Some(children) = dependents.get(&id) {
            for child in children {
                if let Some(d) = remaining_deps.get_mut(child) {
                    d.retain(|x| x != &id);
                    if d.is_empty() {
                        ready.insert(child.clone());
                    }
                }
            }
        }
    }
    if order.len() != by_id.len() {
        return Err(invalid(
            "event dependency graph has a cycle or an unresolvable reference",
        ));
    }
    Ok(order.into_iter().map(|id| by_id[&id]).collect())
}

fn apply_event(state: &mut BusState, env: &Envelope) -> AbResult<()> {
    let data = env.typed_data()?;

    if env.seq == 0 {
        if !matches!(data, EventData::AgentRegistered(_)) {
            return Err(invalid(format!(
                "{}: sequence zero must be agent.registered",
                env.id
            )));
        }
    } else {
        let expected = state
            .agents
            .get(&env.agent)
            .ok_or_else(|| invalid(format!("{}: agent {} is not registered", env.id, env.agent)))?
            .next_seq;
        if env.seq != expected {
            return Err(invalid(format!(
                "{}: out-of-order sequence (expected {expected}, got {})",
                env.id, env.seq
            )));
        }
    }

    match &data {
        EventData::AgentRegistered(d) => apply_registered(state, env, d)?,
        EventData::AgentStatus(d) => apply_status(state, env, d)?,
        EventData::AgentResumed(d) => apply_resumed(state, env, d)?,
        EventData::AgentRetired(d) => apply_retired(state, env, d)?,
        EventData::SchemaActivated(d) => apply_schema_activated(state, env, d)?,
        EventData::MergeEngineActivated(d) => apply_merge_engine_activated(state, env, d)?,
        EventData::ScopeSet(d) => apply_scope_set(state, env, d)?,
        EventData::PlanSet(d) => apply_plan_set(state, env, d)?,
        EventData::ProgressReported(d) => apply_progress(state, env, d)?,
        EventData::IssueOpened(d) => apply_issue_opened(state, env, d)?,
        EventData::IssueAcknowledged(d) => apply_issue_ack(state, env, d)?,
        EventData::IssueResolved(d) => {
            apply_issue_terminal(state, env, &data, &d.issue, &d.assignment, "resolved")?
        }
        EventData::IssueRejected(d) => {
            apply_issue_terminal(state, env, &data, &d.issue, &d.assignment, "rejected")?
        }
        EventData::IssueReassigned(d) => apply_issue_reassigned(state, env, d)?,
        EventData::DependencyRequested(d) => apply_dependency_requested(state, env, d)?,
        EventData::DependencyAcknowledged(d) => apply_dependency_ack(state, env, d)?,
        EventData::DependencyResolved(d) => apply_dependency_terminal(
            state,
            env,
            &data,
            &d.dependency,
            &d.assignment,
            "resolved",
        )?,
        EventData::DependencyRejected(d) => apply_dependency_terminal(
            state,
            env,
            &data,
            &d.dependency,
            &d.assignment,
            "rejected",
        )?,
        EventData::DependencyReassigned(d) => apply_dependency_reassigned(state, env, d)?,
        EventData::HandoffOffered(d) => apply_handoff_offered(state, env, d)?,
        EventData::HandoffAccepted(d) => {
            apply_handoff_terminal(state, env, &d.handoff, "accepted")?
        }
        EventData::HandoffDeclined(d) => {
            apply_handoff_terminal(state, env, &d.handoff, "declined")?
        }
        EventData::HandoffWithdrawn(d) => {
            apply_handoff_terminal(state, env, &d.handoff, "withdrawn")?
        }
        EventData::ReviewNominated(d) => apply_review_nominated(state, env, d)?,
        EventData::ReviewNominationAccepted(d) => apply_review_accept(state, env, d)?,
        EventData::ReviewNominationDeclined(d) => {
            apply_review_closing(state, env, &d.nomination, "declined")?
        }
        EventData::ReviewChangesRequested(d) => apply_review_changes(state, env, d)?,
        EventData::ReviewFindingsCleared(d) => apply_finding_disposition(
            state,
            env,
            &data,
            &d.nomination,
            &d.changes_event,
            &d.finding_id,
        )?,
        EventData::ReviewFindingsSuperseded(d) => apply_finding_disposition(
            state,
            env,
            &data,
            &d.nomination,
            &d.changes_event,
            &d.finding_id,
        )?,
        EventData::ReviewReassigned(d) => apply_review_reassigned(state, env, d)?,
        EventData::ReviewWithdrawn(d) => {
            apply_review_closing(state, env, &d.nomination, "withdrawn")?
        }
        EventData::ReviewMergeAuthorized(d) => apply_review_merge_authorized(state, env, d)?,
        EventData::ReviewMerged(d) => apply_review_merged(state, env, d)?,
        EventData::ReviewMergeReconciled(d) => apply_review_merge_reconciled(state, env, d)?,
        EventData::LifecycleConflictResolved(d) => apply_conflict_resolved(state, env, d)?,
        EventData::FrictionReported(d) => apply_friction_reported(state, env, d)?,
        EventData::FrictionSynthesized(d) => apply_friction_synthesized(state, env, d)?,
        EventData::SubscriptionSet(d) => apply_subscription_set(state, env, d)?,
        EventData::BroadcastPublished(d) => apply_broadcast_published(state, env, d)?,
        EventData::BroadcastAcknowledged(d) => apply_broadcast_acknowledged(state, env, d)?,
        EventData::BroadcastSeen(d) => apply_broadcast_seen(state, env, d)?,
    }
    Ok(())
}

fn require_agent<'a>(state: &'a BusState, a: &Agent) -> AbResult<&'a AgentState> {
    state
        .agents
        .get(a)
        .ok_or_else(|| invalid(format!("unregistered agent: {a}")))
}

fn require_active_role<'a>(state: &'a BusState, a: &Agent, role: Role) -> AbResult<&'a AgentState> {
    let ag = require_agent(state, a)?;
    if ag.primary_role != role {
        return Err(invalid(format!("{a} does not have role {role}")));
    }
    if !ag.active() {
        return Err(invalid(format!("{a} is not active")));
    }
    Ok(ag)
}

fn require_bootstrap_coordinator(state: &BusState, a: &Agent) -> AbResult<()> {
    if !state.is_bootstrap_coordinator(a) {
        return Err(invalid(format!(
            "{a} is not a coordinator in the current roster epoch"
        )));
    }
    require_active_role(state, a, Role::Coordinator)?;
    Ok(())
}

// ------------------------------------------------------------------ lifecycle

fn apply_registered(
    state: &mut BusState,
    env: &Envelope,
    d: &AgentRegistered,
) -> AbResult<()> {
    if env.seq != 0 {
        return Err(invalid(format!(
            "{}: agent.registered must be sequence zero",
            env.id
        )));
    }
    if state.agents.contains_key(&env.agent) {
        return Err(invalid(format!("{} is already registered", env.agent)));
    }
    if Agent::is_reserved(env.agent.as_str()) {
        return Err(invalid(format!(
            "{} begins with reserved prefix _",
            env.agent
        )));
    }
    if d.primary_role != Role::Implementor
        && (d.product_base.is_some() || d.product_branch.is_some())
    {
        return Err(invalid(format!(
            "{}: product fields are permitted only for an implementor",
            env.id
        )));
    }
    state.agents.insert(
        env.agent.clone(),
        AgentState {
            agent: env.agent.clone(),
            display_name: d.display_name.clone(),
            primary_role: d.primary_role,
            purpose: d.purpose.clone(),
            provider: d.provider.clone(),
            model: d.model.clone(),
            status: LifecycleStatus::Active,
            status_note: crate::scalars::Text::parse(String::new()).expect("empty text is valid"),
            product_branch: d.product_branch.clone(),
            product_commit: None,
            last_lifecycle_event: env.id.clone(),
            retired: false,
            scope: None,
            plan: None,
            progress_tail: Vec::new(),
            next_seq: 1,
            subscribed_topics: crate::scalars::StringSet::default(),
        },
    );
    Ok(())
}

fn apply_status(state: &mut BusState, env: &Envelope, d: &AgentStatusEvent) -> AbResult<()> {
    let ag = require_agent(state, &env.agent)?;
    if ag.primary_role != Role::Implementor
        && (d.product_branch.is_some() || d.product_commit.is_some())
    {
        return Err(invalid(format!(
            "{}: product fields are permitted only for an implementor",
            env.id
        )));
    }
    let ag = state.agents.get_mut(&env.agent).expect("just checked");
    ag.status = d.status;
    ag.status_note = d.note.clone();
    if d.product_branch.is_some() {
        ag.product_branch = d.product_branch.clone();
    }
    if d.product_commit.is_some() {
        ag.product_commit = d.product_commit.clone();
    }
    ag.last_lifecycle_event = env.id.clone();
    Ok(())
}

fn apply_resumed(state: &mut BusState, env: &Envelope, d: &AgentResumed) -> AbResult<()> {
    let ag = require_agent(state, &env.agent)?;
    if ag.last_lifecycle_event != d.previous_lifecycle {
        return Err(invalid(format!(
            "{}: previous_lifecycle {} does not match {}'s latest lifecycle event {}",
            env.id, d.previous_lifecycle, env.agent, ag.last_lifecycle_event
        )));
    }
    let ag = state.agents.get_mut(&env.agent).expect("just checked");
    ag.retired = false;
    ag.status = LifecycleStatus::Active;
    ag.last_lifecycle_event = env.id.clone();
    Ok(())
}

fn apply_retired(state: &mut BusState, env: &Envelope, d: &AgentRetired) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    if d.target == env.agent {
        return Err(invalid(format!("{}: cannot retire self", env.id)));
    }
    let target = require_agent(state, &d.target)?;
    if target.last_lifecycle_event != d.previous_lifecycle {
        return Err(invalid(format!(
            "{}: previous_lifecycle {} does not match {}'s latest lifecycle event {}",
            env.id, d.previous_lifecycle, d.target, target.last_lifecycle_event
        )));
    }
    let target = state.agents.get_mut(&d.target).expect("just checked");
    target.retired = true;
    target.last_lifecycle_event = env.id.clone();
    Ok(())
}

fn apply_schema_activated(state: &mut BusState, env: &Envelope, d: &SchemaActivated) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    if d.version <= state.activated_schema_version {
        return Err(invalid(format!(
            "{}: schema version {} is not greater than the currently activated {}",
            env.id, d.version, state.activated_schema_version
        )));
    }
    state.activated_schema_version = d.version;
    Ok(())
}

fn apply_merge_engine_activated(
    state: &mut BusState,
    env: &Envelope,
    d: &MergeEngineActivated,
) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    if !state.merge_engine_info.contains_key(&d.previous_epoch) {
        return Err(invalid(format!(
            "{}: previous_epoch {} is not a known prior engine activation",
            env.id, d.previous_epoch
        )));
    }
    if state.exclusive.is_contested(&d.previous_epoch) {
        return Err(invalid(format!(
            "{}: previous_epoch {} is itself part of an unresolved lifecycle conflict",
            env.id, d.previous_epoch
        )));
    }
    if d.merge_engine.as_str() != crate::bootstrap::SUPPORTED_MERGE_ENGINE {
        return Err(invalid(format!(
            "{}: unsupported merge_engine {}",
            env.id, d.merge_engine
        )));
    }
    let key = format!("engine_epoch:{}", d.previous_epoch);
    state.exclusive.record(&key, &env.id, |other| {
        env.observed.validate_reference(other).is_ok()
    })?;
    state
        .merge_engine_info
        .insert(env.id.clone(), (d.merge_engine.clone(), d.merge_engine_version.clone()));
    if state.exclusive.winner(&key).as_ref() == Some(&env.id) {
        state.current_merge_engine_epoch = Some(env.id.clone());
    }
    Ok(())
}

// ------------------------------------------------------------ scope/plan/progress

fn apply_scope_set(state: &mut BusState, env: &Envelope, d: &ScopeSet) -> AbResult<()> {
    require_active_role(state, &env.agent, Role::Implementor)?;
    let mut seen: Vec<(Agent, crate::scalars::Short)> = Vec::new();
    for dep in &d.depends_on {
        seen.push((dep.agent.clone(), dep.interface.clone()));
    }
    let mut sorted = seen.clone();
    sorted.sort_by(|a, b| (a.0.as_str(), a.1.as_str()).cmp(&(b.0.as_str(), b.1.as_str())));
    if sorted != seen {
        return Err(invalid(format!(
            "{}: depends_on is not sorted by (agent, interface)",
            env.id
        )));
    }
    let mut dedup = seen.clone();
    dedup.dedup();
    if dedup.len() != seen.len() {
        return Err(invalid(format!(
            "{}: depends_on contains a duplicate (agent, interface) pair",
            env.id
        )));
    }
    let ag = state.agents.get_mut(&env.agent).expect("checked by require_active_role");
    ag.scope = Some(d.clone());
    Ok(())
}

fn apply_plan_set(state: &mut BusState, env: &Envelope, d: &PlanSet) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    let mut ids = std::collections::BTreeSet::new();
    for step in &d.steps {
        if !ids.insert(step.id.as_str()) {
            return Err(invalid(format!("{}: duplicate plan step id {}", env.id, step.id)));
        }
    }
    let active_count = d
        .steps
        .iter()
        .filter(|s| s.state == crate::common::PlanStepState::Active)
        .count();
    if active_count > 1 {
        return Err(invalid(format!(
            "{}: at most one plan step may be active",
            env.id
        )));
    }
    let ag = state.agents.get_mut(&env.agent).expect("checked above");
    ag.plan = Some(d.clone());
    Ok(())
}

fn apply_progress(state: &mut BusState, env: &Envelope, d: &ProgressReported) -> AbResult<()> {
    let ag = require_agent(state, &env.agent)?;
    if ag.primary_role != Role::Implementor && d.product_commit.is_some() {
        return Err(invalid(format!(
            "{}: product_commit is permitted only for an implementor",
            env.id
        )));
    }
    let ag = state.agents.get_mut(&env.agent).expect("just checked");
    ag.progress_tail.push(d.clone());
    if ag.progress_tail.len() > 20 {
        ag.progress_tail.remove(0);
    }
    Ok(())
}

// ------------------------------------------------------------------ issues

fn apply_issue_opened(state: &mut BusState, env: &Envelope, d: &IssueOpened) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    require_agent(state, &d.target)?;
    state.issues.insert(
        env.id.clone(),
        IssueState {
            id: env.id.clone(),
            opener: env.agent.clone(),
            data: d.clone(),
            current_target: d.target.clone(),
            current_assignment: env.id.clone(),
            assignment_target: [(env.id.clone(), d.target.clone())].into(),
            acknowledged: false,
            status: ItemStatus::Open,
            resolution_summary: None,
            reassignment_chain: vec![],
        },
    );
    Ok(())
}

fn apply_issue_ack(state: &mut BusState, env: &Envelope, d: &IssueAcknowledged) -> AbResult<()> {
    let issue = state
        .issues
        .get(&d.issue)
        .ok_or_else(|| invalid(format!("{}: unknown issue {}", env.id, d.issue)))?;
    let expected_target = issue
        .assignment_target
        .get(&d.assignment)
        .ok_or_else(|| invalid(format!("{}: unknown assignment {}", env.id, d.assignment)))?;
    if expected_target != &env.agent {
        return Err(invalid(format!(
            "{}: only that assignment's target may acknowledge this issue",
            env.id
        )));
    }
    if issue.current_assignment != d.assignment {
        return Err(invalid(format!(
            "{}: assignment {} is not the issue's current assignment",
            env.id, d.assignment
        )));
    }
    let issue = state.issues.get_mut(&d.issue).expect("just checked");
    if issue.acknowledged {
        return Err(invalid(format!("{}: issue already acknowledged", env.id)));
    }
    issue.acknowledged = true;
    Ok(())
}

fn apply_issue_terminal(
    state: &mut BusState,
    env: &Envelope,
    data: &EventData,
    issue_id: &EventId,
    assignment: &EventId,
    label: &'static str,
) -> AbResult<()> {
    let issue = state
        .issues
        .get(issue_id)
        .ok_or_else(|| invalid(format!("{}: unknown issue {issue_id}", env.id)))?;
    let expected_target = issue
        .assignment_target
        .get(assignment)
        .ok_or_else(|| invalid(format!("{}: unknown assignment {assignment}", env.id)))?;
    if expected_target != &env.agent {
        return Err(invalid(format!(
            "{}: only that assignment's target may dispose of this issue",
            env.id
        )));
    }
    if state.exclusive.is_contested(assignment) {
        return Err(invalid(format!(
            "{}: assignment {assignment} is itself part of an unresolved lifecycle conflict",
            env.id
        )));
    }
    let key = issue_key(assignment);
    state.exclusive.record(&key, &env.id, |other| {
        env.observed.validate_reference(other).is_ok() || other.agent() == env.agent
    })?;
    let expected_target = expected_target.clone();
    if state.exclusive.winner(&key).as_ref() == Some(&env.id) {
        apply_issue_terminal_effect(state, data, label);
    } else {
        reset_issue_to_conflict(state, issue_id, assignment, &expected_target);
    }
    Ok(())
}

fn apply_issue_terminal_effect(state: &mut BusState, data: &EventData, label: &'static str) {
    let (issue_id, summary) = match data {
        EventData::IssueResolved(d) => (&d.issue, Some(d.summary.clone())),
        EventData::IssueRejected(d) => (&d.issue, None),
        _ => return,
    };
    if let Some(issue) = state.issues.get_mut(issue_id) {
        issue.status = ItemStatus::Terminal(label);
        issue.resolution_summary = summary;
    }
}

/// The moment a second, genuinely concurrent transition is found for the
/// same exclusive-transition predecessor, the item's derived "current"
/// state resets to neutral (`LifecycleConflict`) -- including undoing
/// *every* field an earlier candidate's effect may have optimistically
/// applied before the concurrent one arrived, not just `status`: a
/// reassignment that had provisionally won might already have moved
/// `current_target`/`current_assignment` and appended to
/// `reassignment_chain`, and all of that must unwind back to the shared
/// pre-race baseline (`assignment`, `target`) every member of this group
/// agrees was true before any of them won. This must be re-derivable
/// regardless of processing order (gates 15/16): whichever candidate
/// happens to be seen first in a given reduction, the group's *final*
/// membership always ends up at this same neutral baseline once it has two
/// or more members with no explicit resolution.
fn reset_issue_to_conflict(
    state: &mut BusState,
    issue_id: &EventId,
    assignment: &EventId,
    target: &Agent,
) {
    if let Some(issue) = state.issues.get_mut(issue_id) {
        issue.status = ItemStatus::LifecycleConflict;
        issue.resolution_summary = None;
        issue.current_assignment = assignment.clone();
        issue.current_target = target.clone();
    }
}

fn apply_issue_reassigned(state: &mut BusState, env: &Envelope, d: &IssueReassigned) -> AbResult<()> {
    // Deliberately no upfront `issue.status != Open` check here: `status` is
    // itself a derived, potentially-provisional effect of the exclusive
    // tracker below. A reassignment that is genuinely concurrent with an
    // already-applied resolve/reject (neither observed the other) must be
    // recorded as a competing candidate, not rejected merely because the
    // other side happened to apply first in this particular reduction
    // order -- exactly the order-dependence gates 15/16 forbid. The
    // tracker's own `record` already rejects a reassignment that *did*
    // causally observe an existing disposition on this assignment.
    let issue = state
        .issues
        .get(&d.issue)
        .ok_or_else(|| invalid(format!("{}: unknown issue {}", env.id, d.issue)))?;
    let expected_target = issue
        .assignment_target
        .get(&d.previous_assignment)
        .ok_or_else(|| {
            invalid(format!(
                "{}: unknown previous_assignment {}",
                env.id, d.previous_assignment
            ))
        })?;
    if expected_target != &d.previous_target {
        return Err(invalid(format!(
            "{}: previous_target {} does not match assignment's actual target {}",
            env.id, d.previous_target, expected_target
        )));
    }
    let is_opener = issue.opener == env.agent;
    if !is_opener {
        require_bootstrap_coordinator(state, &env.agent)?;
    }
    if state.exclusive.is_contested(&d.previous_assignment) {
        return Err(invalid(format!(
            "{}: previous_assignment {} is itself part of an unresolved lifecycle conflict",
            env.id, d.previous_assignment
        )));
    }
    let key = issue_key(&d.previous_assignment);
    state.exclusive.record(&key, &env.id, |other| {
        env.observed.validate_reference(other).is_ok() || other.agent() == env.agent
    })?;
    if state.exclusive.winner(&key).as_ref() == Some(&env.id) {
        issue_reassign_effect(state, &env.id, d);
    } else {
        reset_issue_to_conflict(state, &d.issue, &d.previous_assignment, &d.previous_target);
    }
    Ok(())
}

fn issue_reassign_effect(state: &mut BusState, env_id: &EventId, d: &IssueReassigned) {
    if let Some(issue) = state.issues.get_mut(&d.issue) {
        issue.current_target = d.new_target.clone();
        issue.current_assignment = env_id.clone();
        issue.acknowledged = false;
        issue
            .assignment_target
            .insert(env_id.clone(), d.new_target.clone());
        issue.reassignment_chain.push(env_id.clone());
        // A confirmed reassignment (whether the sole candidate, or the
        // explicitly resolved winner of a former conflict) leaves the issue
        // open under its new target -- never Terminal or still
        // LifecycleConflict.
        issue.status = ItemStatus::Open;
    }
}

// ------------------------------------------------------ dependencies/handoffs

fn apply_dependency_requested(
    state: &mut BusState,
    env: &Envelope,
    d: &DependencyRequested,
) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    require_agent(state, &d.target)?;
    state.dependencies.insert(
        env.id.clone(),
        DependencyState {
            id: env.id.clone(),
            requester: env.agent.clone(),
            data: d.clone(),
            current_target: d.target.clone(),
            current_assignment: env.id.clone(),
            assignment_target: [(env.id.clone(), d.target.clone())].into(),
            acknowledged: false,
            status: ItemStatus::Open,
            reassignment_chain: vec![],
        },
    );
    Ok(())
}

fn apply_dependency_ack(
    state: &mut BusState,
    env: &Envelope,
    d: &DependencyAcknowledged,
) -> AbResult<()> {
    let dep = state
        .dependencies
        .get(&d.dependency)
        .ok_or_else(|| invalid(format!("{}: unknown dependency {}", env.id, d.dependency)))?;
    let expected_target = dep
        .assignment_target
        .get(&d.assignment)
        .ok_or_else(|| invalid(format!("{}: unknown assignment {}", env.id, d.assignment)))?;
    if expected_target != &env.agent {
        return Err(invalid(format!(
            "{}: only that assignment's target may acknowledge this dependency",
            env.id
        )));
    }
    if dep.current_assignment != d.assignment {
        return Err(invalid(format!(
            "{}: assignment {} is not the dependency's current assignment",
            env.id, d.assignment
        )));
    }
    let dep = state.dependencies.get_mut(&d.dependency).expect("just checked");
    if dep.acknowledged {
        return Err(invalid(format!(
            "{}: dependency already acknowledged",
            env.id
        )));
    }
    dep.acknowledged = true;
    Ok(())
}

fn apply_dependency_terminal(
    state: &mut BusState,
    env: &Envelope,
    data: &EventData,
    dependency_id: &EventId,
    assignment: &EventId,
    label: &'static str,
) -> AbResult<()> {
    let dep = state
        .dependencies
        .get(dependency_id)
        .ok_or_else(|| invalid(format!("{}: unknown dependency {dependency_id}", env.id)))?;
    let expected_target = dep
        .assignment_target
        .get(assignment)
        .ok_or_else(|| invalid(format!("{}: unknown assignment {assignment}", env.id)))?;
    if expected_target != &env.agent {
        return Err(invalid(format!(
            "{}: only that assignment's target may dispose of this dependency",
            env.id
        )));
    }
    if state.exclusive.is_contested(assignment) {
        return Err(invalid(format!(
            "{}: assignment {assignment} is itself part of an unresolved lifecycle conflict",
            env.id
        )));
    }
    let expected_target = expected_target.clone();
    let key = dependency_key(assignment);
    state.exclusive.record(&key, &env.id, |other| {
        env.observed.validate_reference(other).is_ok() || other.agent() == env.agent
    })?;
    if state.exclusive.winner(&key).as_ref() == Some(&env.id) {
        dependency_terminal_effect(state, data, dependency_id, label);
    } else {
        reset_dependency_to_conflict(state, dependency_id, assignment, &expected_target);
    }
    Ok(())
}

fn dependency_terminal_effect(
    state: &mut BusState,
    data: &EventData,
    dependency_id: &EventId,
    label: &'static str,
) {
    if let EventData::DependencyResolved(_) | EventData::DependencyRejected(_) = data {
        if let Some(dep) = state.dependencies.get_mut(dependency_id) {
            dep.status = ItemStatus::Terminal(label);
        }
    }
}

/// See `reset_issue_to_conflict`'s doc comment -- same rationale (including
/// undoing every field a provisionally-applied reassignment may have
/// changed, not just `status`), applied to dependencies.
fn reset_dependency_to_conflict(
    state: &mut BusState,
    dependency_id: &EventId,
    assignment: &EventId,
    target: &Agent,
) {
    if let Some(dep) = state.dependencies.get_mut(dependency_id) {
        dep.status = ItemStatus::LifecycleConflict;
        dep.current_assignment = assignment.clone();
        dep.current_target = target.clone();
    }
}

fn apply_dependency_reassigned(
    state: &mut BusState,
    env: &Envelope,
    d: &DependencyReassigned,
) -> AbResult<()> {
    // See apply_issue_reassigned's comment on why there is deliberately no
    // upfront `dep.status != Open` check: that would reintroduce exactly
    // the order-dependence gates 15/16 forbid.
    let dep = state
        .dependencies
        .get(&d.dependency)
        .ok_or_else(|| invalid(format!("{}: unknown dependency {}", env.id, d.dependency)))?;
    let expected_target = dep
        .assignment_target
        .get(&d.previous_assignment)
        .ok_or_else(|| {
            invalid(format!(
                "{}: unknown previous_assignment {}",
                env.id, d.previous_assignment
            ))
        })?;
    if expected_target != &d.previous_target {
        return Err(invalid(format!(
            "{}: previous_target {} does not match assignment's actual target {}",
            env.id, d.previous_target, expected_target
        )));
    }
    let is_requester = dep.requester == env.agent;
    if !is_requester {
        require_bootstrap_coordinator(state, &env.agent)?;
    }
    if state.exclusive.is_contested(&d.previous_assignment) {
        return Err(invalid(format!(
            "{}: previous_assignment {} is itself part of an unresolved lifecycle conflict",
            env.id, d.previous_assignment
        )));
    }
    let key = dependency_key(&d.previous_assignment);
    state.exclusive.record(&key, &env.id, |other| {
        env.observed.validate_reference(other).is_ok() || other.agent() == env.agent
    })?;
    if state.exclusive.winner(&key).as_ref() == Some(&env.id) {
        dependency_reassign_effect(state, &env.id, d);
    } else {
        reset_dependency_to_conflict(
            state,
            &d.dependency,
            &d.previous_assignment,
            &d.previous_target,
        );
    }
    Ok(())
}

fn dependency_reassign_effect(state: &mut BusState, env_id: &EventId, d: &DependencyReassigned) {
    if let Some(dep) = state.dependencies.get_mut(&d.dependency) {
        dep.current_target = d.new_target.clone();
        dep.current_assignment = env_id.clone();
        dep.acknowledged = false;
        dep.assignment_target
            .insert(env_id.clone(), d.new_target.clone());
        dep.reassignment_chain.push(env_id.clone());
        dep.status = ItemStatus::Open;
    }
}

fn apply_handoff_offered(state: &mut BusState, env: &Envelope, d: &HandoffOffered) -> AbResult<()> {
    require_active_role(state, &env.agent, Role::Implementor)?;
    require_agent(state, &d.receiver)?;
    state.handoffs.insert(
        env.id.clone(),
        HandoffState {
            id: env.id.clone(),
            offerer: env.agent.clone(),
            data: d.clone(),
            status: ItemStatus::Open,
        },
    );
    Ok(())
}

fn apply_handoff_terminal(
    state: &mut BusState,
    env: &Envelope,
    handoff_id: &EventId,
    label: &'static str,
) -> AbResult<()> {
    let handoff = state
        .handoffs
        .get(handoff_id)
        .ok_or_else(|| invalid(format!("{}: unknown handoff {handoff_id}", env.id)))?;
    let is_receiver = handoff.data.receiver == env.agent;
    let is_offerer = handoff.offerer == env.agent;
    match label {
        "accepted" | "declined" => {
            if !is_receiver {
                return Err(invalid(format!(
                    "{}: only the receiver may dispose of this handoff",
                    env.id
                )));
            }
        }
        "withdrawn" => {
            if !is_offerer {
                return Err(invalid(format!(
                    "{}: only the offerer may withdraw this handoff",
                    env.id
                )));
            }
        }
        _ => unreachable!(),
    }
    if state.exclusive.is_contested(handoff_id) {
        return Err(invalid(format!(
            "{}: handoff {handoff_id} is itself part of an unresolved lifecycle conflict",
            env.id
        )));
    }
    let key = handoff_key(handoff_id);
    state.exclusive.record(&key, &env.id, |other| {
        env.observed.validate_reference(other).is_ok() || other.agent() == env.agent
    })?;
    if state.exclusive.winner(&key).as_ref() == Some(&env.id) {
        handoff_terminal_effect(state, handoff_id, label);
    } else {
        reset_handoff_to_conflict(state, handoff_id);
    }
    Ok(())
}

fn handoff_terminal_effect(state: &mut BusState, handoff_id: &EventId, label: &'static str) {
    if let Some(h) = state.handoffs.get_mut(handoff_id) {
        h.status = ItemStatus::Terminal(label);
    }
}

/// See `reset_issue_to_conflict`'s doc comment -- same rationale, applied to
/// handoffs.
fn reset_handoff_to_conflict(state: &mut BusState, handoff_id: &EventId) {
    if let Some(h) = state.handoffs.get_mut(handoff_id) {
        h.status = ItemStatus::LifecycleConflict;
    }
}

// ------------------------------------------------------------------- review

fn apply_review_nominated(state: &mut BusState, env: &Envelope, d: &ReviewRequest) -> AbResult<()> {
    if !d.authors.iter().any(|a| a == &env.agent) {
        return Err(invalid(format!(
            "{}: emitter must be one of the nomination's authors",
            env.id
        )));
    }
    for author in d.authors.iter() {
        require_active_role(state, author, Role::Implementor)?;
    }
    if d.authors.iter().any(|a| a == &d.reviewer) {
        return Err(invalid(format!(
            "{}: reviewer must not be one of the authors",
            env.id
        )));
    }
    require_active_role(state, &d.reviewer, Role::Reviewer)?;
    if d.target_branch.as_str() != "refs/heads/main" {
        return Err(invalid(format!(
            "{}: target_branch must be refs/heads/main",
            env.id
        )));
    }
    state.reviews.insert(
        env.id.clone(),
        ReviewChain {
            root: env.id.clone(),
            nomination_events: vec![env.id.clone()],
            current_nomination: env.id.clone(),
            current_request: d.clone(),
            nomination_reviewer: [(env.id.clone(), d.reviewer.clone())].into(),
            accepted_nominations: Default::default(),
            decline_or_withdraw_or_reassign_status: ItemStatus::Open,
            findings: BTreeMap::new(),
            authorizations: vec![],
            merged: vec![],
            reconciled: vec![],
        },
    );
    state
        .review_chain_by_nomination
        .insert(env.id.clone(), env.id.clone());
    Ok(())
}

fn apply_review_accept(
    state: &mut BusState,
    env: &Envelope,
    d: &ReviewNominationAccepted,
) -> AbResult<()> {
    let chain = state
        .review_chain(&d.nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {}", env.id, d.nomination)))?;
    if chain.current_nomination != d.nomination {
        return Err(invalid(format!(
            "{}: {} is not the current nomination in its chain",
            env.id, d.nomination
        )));
    }
    let expected_reviewer = chain
        .nomination_reviewer
        .get(&d.nomination)
        .expect("every nomination has a reviewer");
    if expected_reviewer != &env.agent {
        return Err(invalid(format!(
            "{}: only the named reviewer may accept this nomination",
            env.id
        )));
    }
    if chain.accepted_nominations.contains(&d.nomination) {
        return Err(invalid(format!("{}: nomination already accepted", env.id)));
    }
    let chain = state.review_chain_mut(&d.nomination).expect("just checked");
    chain.accepted_nominations.insert(d.nomination.clone());
    Ok(())
}

fn apply_review_closing(
    state: &mut BusState,
    env: &Envelope,
    nomination: &EventId,
    label: &'static str,
) -> AbResult<()> {
    // Deliberately no upfront `chain.is_closed()` or `current_nomination ==
    // nomination` check here: see apply_issue_reassigned's comment. A
    // decline/withdraw genuinely concurrent with an already-processed
    // reassignment on this same nomination must be recorded as a competing
    // candidate, not rejected merely because the other side happened to be
    // reduced first and provisionally advanced `current_nomination` away
    // from the id this event actually names.
    let chain = state
        .review_chain(nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {nomination}", env.id)))?;
    match label {
        "declined" => {
            let reviewer = chain.nomination_reviewer.get(nomination).unwrap();
            if reviewer != &env.agent {
                return Err(invalid(format!(
                    "{}: only the named reviewer may decline this nomination",
                    env.id
                )));
            }
            if chain.accepted_nominations.contains(nomination) {
                return Err(invalid(format!(
                    "{}: an accepted nomination cannot be declined",
                    env.id
                )));
            }
        }
        "withdrawn" => {
            if !chain.current_request.authors.iter().any(|a| a == &env.agent) {
                return Err(invalid(format!(
                    "{}: only an author may withdraw this nomination",
                    env.id
                )));
            }
            if !chain.authorizations.is_empty() {
                return Err(invalid(format!(
                    "{}: cannot withdraw after merge authorization",
                    env.id
                )));
            }
        }
        _ => unreachable!(),
    }
    let key = review_key(nomination);
    state.exclusive.record(&key, &env.id, |other| {
        env.observed.validate_reference(other).is_ok() || other.agent() == env.agent
    })?;
    if state.exclusive.winner(&key).as_ref() == Some(&env.id) {
        let chain = state.review_chain_mut(nomination).expect("just checked");
        chain.decline_or_withdraw_or_reassign_status = ItemStatus::Terminal(label);
    } else {
        reset_review_to_conflict(state, nomination);
    }
    Ok(())
}

/// See `reset_issue_to_conflict`'s doc comment for the general rationale.
/// Reviews need more than a status reset: a reassignment racing against
/// this decline/withdraw may have already provisionally extended the chain
/// to a new nomination link before the conflict was discovered. That link
/// is fully retracted -- removed from `nomination_events`,
/// `nomination_reviewer`, and `review_chain_by_nomination` -- and
/// `current_nomination`/`current_request` revert to the shared pre-race
/// baseline (`nomination`'s own already-reduced request), recovered from
/// its own event rather than re-derived, since nothing else records what a
/// nomination's request was independent of the chain's current (possibly
/// -reverting) state.
fn reset_review_to_conflict(state: &mut BusState, nomination: &EventId) {
    let Some(root) = state.review_chain_by_nomination.get(nomination).cloned() else {
        return;
    };
    let baseline_request = state.events.get(nomination).and_then(|env| {
        env.typed_data().ok().and_then(|d| match d {
            EventData::ReviewNominated(r) => Some(r),
            EventData::ReviewReassigned(r) => Some(r.request()),
            _ => None,
        })
    });
    let Some(chain) = state.reviews.get_mut(&root) else {
        return;
    };
    chain.decline_or_withdraw_or_reassign_status = ItemStatus::LifecycleConflict;
    if chain.current_nomination != *nomination {
        let provisional = chain.current_nomination.clone();
        chain.nomination_events.retain(|id| id != &provisional);
        chain.nomination_reviewer.remove(&provisional);
        chain.current_nomination = nomination.clone();
        if let Some(r) = baseline_request {
            chain.current_request = r;
        }
        state.review_chain_by_nomination.remove(&provisional);
    }
}

fn apply_review_changes(
    state: &mut BusState,
    env: &Envelope,
    d: &ReviewChangesRequested,
) -> AbResult<()> {
    let chain = state
        .review_chain(&d.nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {}", env.id, d.nomination)))?;
    if chain.current_nomination != d.nomination {
        return Err(invalid(format!(
            "{}: {} is not the current nomination in its chain",
            env.id, d.nomination
        )));
    }
    let reviewer = chain.nomination_reviewer.get(&d.nomination).unwrap();
    if reviewer != &env.agent {
        return Err(invalid(format!(
            "{}: only the accepting reviewer may request changes",
            env.id
        )));
    }
    if d.findings.is_empty() {
        return Err(invalid(format!("{}: findings must be nonempty", env.id)));
    }
    let mut ids = std::collections::BTreeSet::new();
    for f in &d.findings {
        if !ids.insert(f.id.as_str()) {
            return Err(invalid(format!("{}: duplicate finding id {}", env.id, f.id)));
        }
    }
    let chain = state.review_chain_mut(&d.nomination).expect("just checked");
    for f in &d.findings {
        chain.findings.insert(
            (env.id.clone(), f.id.as_str().to_string()),
            FindingState {
                changes_event: env.id.clone(),
                finding_id: f.id.clone(),
                priority: f.priority,
                locations: f.locations.clone(),
                rationale: f.rationale.clone(),
                closure_conditions: f.closure_conditions.clone(),
                disposition: FindingDisposition::Open,
            },
        );
    }
    Ok(())
}

fn apply_finding_disposition(
    state: &mut BusState,
    env: &Envelope,
    data: &EventData,
    nomination: &EventId,
    changes_event: &EventId,
    finding_id: &crate::scalars::Short,
) -> AbResult<()> {
    let chain = state
        .review_chain(nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {nomination}", env.id)))?;
    // Authority belongs to the reviewer of the chain's *current* nomination
    // link specifically -- a reviewer who has since been superseded by a
    // reassignment must not retain disposal authority merely by citing
    // their own now-stale nomination id, even though that id's own
    // nomination_reviewer entry never gets removed (it stays as a durable
    // record of who accepted that particular link).
    if chain.current_nomination != *nomination {
        return Err(invalid(format!(
            "{}: {nomination} is not the current nomination in its chain",
            env.id
        )));
    }
    let reviewer = chain.nomination_reviewer.get(nomination).cloned();
    if reviewer.as_ref() != Some(&env.agent) {
        return Err(invalid(format!(
            "{}: only the accepting reviewer for the current nomination may dispose of findings",
            env.id
        )));
    }
    let key = (changes_event.clone(), finding_id.as_str().to_string());
    let finding = chain
        .findings
        .get(&key)
        .ok_or_else(|| invalid(format!("{}: unknown finding {}", env.id, finding_id)))?;
    if finding.disposition != FindingDisposition::Open {
        return Err(invalid(format!("{}: finding is not open", env.id)));
    }
    let chain = state.review_chain_mut(nomination).expect("just checked");
    let finding = chain.findings.get_mut(&key).expect("just checked");
    finding.disposition = match data {
        EventData::ReviewFindingsCleared(_) => FindingDisposition::Cleared {
            by_event: env.id.clone(),
        },
        EventData::ReviewFindingsSuperseded(d) => FindingDisposition::Superseded {
            by_event: env.id.clone(),
            rationale: d.rationale.clone(),
        },
        _ => unreachable!(),
    };
    Ok(())
}

fn apply_review_reassigned(
    state: &mut BusState,
    env: &Envelope,
    d: &ReviewReassigned,
) -> AbResult<()> {
    // Note: only the decline/withdraw/reassign race is checked via the
    // exclusive tracker below (see apply_issue_reassigned's comment for
    // why there is no upfront check on *that* status specifically). A real
    // product merge or reconciliation is a stronger, always-final fact
    // unrelated to that race and is still checked eagerly here -- it must
    // block reassignment unconditionally, not be treated as one more
    // competing candidate.
    let chain = state
        .review_chain(&d.replaces)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {}", env.id, d.replaces)))?;
    if !chain.merged.is_empty() || !chain.reconciled.is_empty() {
        return Err(invalid(format!(
            "{}: cannot reassign a review chain that has already merged or reconciled",
            env.id
        )));
    }
    // Deliberately no upfront `current_nomination == d.replaces` check: a
    // second, genuinely concurrent reassignment (or a reassignment racing a
    // decline that never moves `current_nomination` at all) must not be
    // rejected merely because a different competing candidate happened to
    // be reduced first and provisionally advanced the chain. `chain.
    // current_request`'s non-reviewer fields are compared below regardless
    // of which link is currently "current" -- every valid reassignment from
    // the same predecessor must carry the identical non-reviewer fields, so
    // this comparison is meaningful even against another concurrent
    // reassignment's already-applied state.
    let same_except_reviewer = {
        let mut a = d.request();
        a.reviewer = chain.current_request.reviewer.clone();
        a == chain.current_request
    };
    if !same_except_reviewer {
        return Err(invalid(format!(
            "{}: reassignment must copy the request exactly except reviewer",
            env.id
        )));
    }
    if d.reviewer == chain.current_request.reviewer {
        return Err(invalid(format!(
            "{}: replacement reviewer must differ from the current reviewer",
            env.id
        )));
    }
    require_active_role(state, &d.reviewer, Role::Reviewer)?;
    let is_author = chain.current_request.authors.iter().any(|a| a == &env.agent);
    if !is_author {
        require_bootstrap_coordinator(state, &env.agent)?;
    }
    let still_open: std::collections::BTreeSet<(EventId, String)> = chain
        .findings
        .iter()
        .filter(|(_, f)| f.disposition == FindingDisposition::Open)
        .map(|(k, _)| k.clone())
        .collect();
    let inherited: std::collections::BTreeSet<(EventId, String)> = d
        .inherited_findings
        .iter()
        .map(|f| (f.changes_event.clone(), f.finding_id.as_str().to_string()))
        .collect();
    if inherited != still_open || d.inherited_findings.len() != inherited.len() {
        return Err(invalid(format!(
            "{}: inherited_findings must equal every still-open finding exactly once",
            env.id
        )));
    }

    let root = chain.root.clone();
    let key = review_key(&d.replaces);
    state.exclusive.record(&key, &env.id, |other| {
        env.observed.validate_reference(other).is_ok() || other.agent() == env.agent
    })?;
    if state.exclusive.winner(&key).as_ref() == Some(&env.id) {
        let chain_mut = state.reviews.get_mut(&root).expect("chain exists");
        chain_mut.nomination_events.push(env.id.clone());
        chain_mut.current_nomination = env.id.clone();
        chain_mut.current_request = d.request();
        chain_mut
            .nomination_reviewer
            .insert(env.id.clone(), d.reviewer.clone());
        chain_mut.decline_or_withdraw_or_reassign_status = ItemStatus::Open;
        state
            .review_chain_by_nomination
            .insert(env.id.clone(), root);
    } else {
        reset_review_to_conflict(state, &d.replaces);
    }
    Ok(())
}

fn apply_review_merge_authorized(
    state: &mut BusState,
    env: &Envelope,
    d: &ReviewMergeAuthorized,
) -> AbResult<()> {
    let chain = state
        .review_chain(&d.nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {}", env.id, d.nomination)))?;
    if chain.current_nomination != d.nomination {
        return Err(invalid(format!(
            "{}: {} is not the current nomination in its chain",
            env.id, d.nomination
        )));
    }
    let reviewer = chain.nomination_reviewer.get(&d.nomination).unwrap();
    if reviewer != &env.agent {
        return Err(invalid(format!(
            "{}: only the accepting reviewer may authorize a merge",
            env.id
        )));
    }
    if d.reviewed_scope != chain.current_request.review_scope {
        return Err(invalid(format!(
            "{}: reviewed_scope must equal the nomination's review_scope exactly",
            env.id
        )));
    }
    for check in &d.checks {
        if !chain.current_request.required_checks.iter().any(|c| c.as_str() == check.command.as_str())
        {
            // Extra checks beyond required are fine; required checks must
            // all be present, verified below.
        }
    }
    for required in chain.current_request.required_checks.iter() {
        if !d.checks.iter().any(|c| c.command.as_str() == required.as_str()) {
            return Err(invalid(format!(
                "{}: required check {required} is absent",
                env.id
            )));
        }
    }
    for f in chain.findings.values() {
        if f.disposition == FindingDisposition::Open {
            return Err(invalid(format!(
                "{}: finding {} lacks a terminal disposition",
                env.id, f.finding_id
            )));
        }
    }
    let chain_mut = state.review_chain_mut(&d.nomination).expect("checked above");
    chain_mut.authorizations.push(env.id.clone());
    Ok(())
}

fn apply_review_merged(state: &mut BusState, env: &Envelope, d: &ReviewMerged) -> AbResult<()> {
    let auth_kind = state.kind_of_event(&d.authorization);
    if auth_kind != Some("review.merge_authorized") {
        return Err(invalid(format!(
            "{}: authorization {} is not a review.merge_authorized event",
            env.id, d.authorization
        )));
    }
    let auth_env = state
        .events
        .get(&d.authorization)
        .ok_or_else(|| invalid(format!("{}: unknown authorization {}", env.id, d.authorization)))?;
    if auth_env.agent != env.agent {
        return Err(invalid(format!(
            "{}: only the authorizing reviewer may emit review.merged",
            env.id
        )));
    }
    let EventData::ReviewMergeAuthorized(auth) = auth_env.typed_data()? else {
        unreachable!("kind already checked")
    };
    if d.previous_main != auth.previous_main
        || d.reviewed_commit != auth.reviewed_commit
        || d.product_branch != auth.product_branch
        || d.main_commit != auth.candidate
    {
        return Err(invalid(format!(
            "{}: values must equal the authorization and main_commit must equal the candidate",
            env.id
        )));
    }
    let root = state
        .review_chain_by_nomination
        .get(&auth.nomination)
        .cloned()
        .ok_or_else(|| invalid(format!("{}: unknown nomination chain", env.id)))?;
    let chain = state.reviews.get_mut(&root).expect("chain exists");
    chain.merged.push(env.id.clone());
    Ok(())
}

fn apply_review_merge_reconciled(
    state: &mut BusState,
    env: &Envelope,
    d: &ReviewMergeReconciled,
) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    let auth_env = state
        .events
        .get(&d.authorization)
        .ok_or_else(|| invalid(format!("{}: unknown authorization {}", env.id, d.authorization)))?;
    let EventData::ReviewMergeAuthorized(auth) = auth_env.typed_data()? else {
        return Err(invalid(format!(
            "{}: authorization {} is not a review.merge_authorized event",
            env.id, d.authorization
        )));
    };
    if d.previous_main != auth.previous_main
        || d.reviewed_commit != auth.reviewed_commit
        || d.product_branch != auth.product_branch
        || d.main_commit != auth.candidate
    {
        return Err(invalid(format!(
            "{}: values must equal the authorization and main_commit must equal the candidate",
            env.id
        )));
    }
    let root = state
        .review_chain_by_nomination
        .get(&auth.nomination)
        .cloned()
        .ok_or_else(|| invalid(format!("{}: unknown nomination chain", env.id)))?;
    let chain = state.reviews.get(&root).expect("chain exists");
    if !chain.merged.is_empty() || !chain.reconciled.is_empty() {
        return Err(invalid(format!(
            "{}: a merged or reconciled receipt already exists",
            env.id
        )));
    }
    let chain = state.reviews.get_mut(&root).expect("chain exists");
    chain.reconciled.push(env.id.clone());
    Ok(())
}

fn apply_conflict_resolved(
    state: &mut BusState,
    env: &Envelope,
    d: &LifecycleConflictResolved,
) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    if d.competing.len() < 2 {
        return Err(invalid(format!(
            "{}: competing must have at least two members",
            env.id
        )));
    }
    if !d.competing.iter().any(|c| c == &d.selected) {
        return Err(invalid(format!(
            "{}: selected must be a member of competing",
            env.id
        )));
    }
    // Find the exclusive-tracker key whose group exactly matches `competing`.
    let key = state
        .exclusive
        .key_with_exact_group(&d.competing.iter().cloned().collect())
        .ok_or_else(|| {
            invalid(format!(
                "{}: no unresolved conflict has exactly this competing set",
                env.id
            ))
        })?;
    state.exclusive.resolve(&key, d.selected.clone())?;
    // Apply the winner's now-confirmed effect. `winner_env` is looked up
    // from state.events rather than trusting `data`'s own kind label,
    // so the dispatch below is driven by what was actually recorded, not by
    // an unchecked claim.
    let winner_env = state
        .events
        .get(&d.selected)
        .cloned()
        .ok_or_else(|| invalid(format!("{}: selected event {} is unknown", env.id, d.selected)))?;
    let data = winner_env.typed_data()?;
    match &data {
        EventData::IssueResolved(_) => apply_issue_terminal_effect(state, &data, "resolved"),
        EventData::IssueRejected(_) => apply_issue_terminal_effect(state, &data, "rejected"),
        EventData::IssueReassigned(rd) => issue_reassign_effect(state, &d.selected, rd),
        EventData::DependencyResolved(_) => {
            dependency_terminal_effect(state, &data, &dependency_from(&data), "resolved")
        }
        EventData::DependencyRejected(_) => {
            dependency_terminal_effect(state, &data, &dependency_from(&data), "rejected")
        }
        EventData::DependencyReassigned(rd) => dependency_reassign_effect(state, &d.selected, rd),
        EventData::HandoffAccepted(hd) => {
            handoff_terminal_effect(state, &hd.handoff, "accepted")
        }
        EventData::HandoffDeclined(hd) => {
            handoff_terminal_effect(state, &hd.handoff, "declined")
        }
        EventData::HandoffWithdrawn(hd) => {
            handoff_terminal_effect(state, &hd.handoff, "withdrawn")
        }
        other => {
            return Err(invalid(format!(
                "{}: selected event kind {} is not an exclusive-transition winner this helper \
                 knows how to confirm",
                env.id,
                other.kind()
            )))
        }
    }
    Ok(())
}

// -------------------------------------------------------------- friction

/// docs/AGENT_COORDINATION_EVOLUTION.md section 3.1. Records the report and
/// nothing else -- gate 11's "no target obligation" means there is no
/// status, assignment, or acknowledgement to derive here, unlike every
/// issue/dependency/handoff handler above.
fn apply_friction_reported(
    state: &mut BusState,
    env: &Envelope,
    d: &FrictionReported,
) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    if let Some(owner) = &d.likely_owner {
        require_agent(state, owner)?;
    }
    // "evidence fields are required when the report makes a quantitative
    // claim" (section 3.1) -- read as: citing measurements is exactly what
    // makes a report's claim quantitative.
    if !d.measurements.is_empty() && d.evidence.is_empty() {
        return Err(invalid(format!(
            "{}: a friction report with measurements must cite supporting evidence",
            env.id
        )));
    }
    state.friction_reports.insert(env.id.clone(), d.clone());
    Ok(())
}

/// docs/AGENT_COORDINATION_EVOLUTION.md section 3.3. `disposition` fixes
/// which of `promoted_to`/`duplicate_of`/`revisit_trigger` is required; the
/// other two must be absent so a synthesis event can never carry a
/// companion field its own disposition disclaims.
fn apply_friction_synthesized(
    state: &mut BusState,
    env: &Envelope,
    d: &FrictionSynthesized,
) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    if d.reports.is_empty() {
        return Err(invalid(format!(
            "{}: friction.synthesized must group at least one report",
            env.id
        )));
    }
    for r in d.reports.iter() {
        if !state.friction_reports.contains_key(r) {
            return Err(invalid(format!(
                "{}: cites unknown friction report {r}",
                env.id
            )));
        }
    }
    use crate::common::FrictionDispositionKind as K;
    let (needs_promoted, needs_duplicate, needs_revisit) = match d.disposition {
        K::Promoted => (true, false, false),
        K::Duplicate => (false, true, false),
        K::Deferred => (false, false, true),
        K::AcceptedCost | K::NeedsEvidence => (false, false, false),
    };
    if needs_promoted != d.promoted_to.is_some() {
        return Err(invalid(format!(
            "{}: promoted_to must be set if and only if disposition is promoted",
            env.id
        )));
    }
    if needs_duplicate != d.duplicate_of.is_some() {
        return Err(invalid(format!(
            "{}: duplicate_of must be set if and only if disposition is duplicate",
            env.id
        )));
    }
    if needs_revisit != d.revisit_trigger.is_some() {
        return Err(invalid(format!(
            "{}: revisit_trigger must be set if and only if disposition is deferred",
            env.id
        )));
    }
    if let Some(dup) = &d.duplicate_of {
        if !state.friction_synthesis.contains_key(dup) {
            return Err(invalid(format!(
                "{}: duplicate_of names unknown synthesis event {dup}",
                env.id
            )));
        }
    }
    state
        .friction_theme_synthesis
        .insert(d.theme.clone(), env.id.clone());
    state.friction_synthesis.insert(env.id.clone(), d.clone());
    Ok(())
}

// ------------------------------------------------------------- broadcasts

fn apply_subscription_set(
    state: &mut BusState,
    env: &Envelope,
    d: &SubscriptionSet,
) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    let ag = state.agents.get_mut(&env.agent).expect("just checked");
    ag.subscribed_topics = d.topics.clone();
    Ok(())
}

/// Resolves `selector` against `epoch`'s active membership (docs/AGENT_
/// COORDINATION_EVOLUTION.md section 4.2). Used both to check a claimed
/// `audience_snapshot` at reduction time and, later, by a CLI command
/// composing a new broadcast.
pub fn resolve_audience(
    state: &BusState,
    selector: &crate::common::AudienceSelector,
    epoch: &crate::registry::RosterEpoch,
) -> BTreeSet<Agent> {
    use crate::common::AudienceSelector as Sel;
    match selector {
        Sel::Agents(set) => set
            .iter()
            .filter(|a| epoch.is_active_member(a))
            .cloned()
            .collect(),
        Sel::Roles(roles) => epoch
            .active_members
            .iter()
            .filter(|(_, binding)| roles.contains(&binding.role))
            .map(|(a, _)| a.clone())
            .collect(),
        Sel::TopicSubscribers(topic) => epoch
            .active_members
            .keys()
            .filter(|a| {
                state
                    .agents
                    .get(*a)
                    .is_some_and(|s| s.subscribed_topics.iter().any(|t| t == topic))
            })
            .cloned()
            .collect(),
        Sel::InterfaceDependents(interface) => epoch
            .active_members
            .keys()
            .filter(|a| {
                state
                    .agents
                    .get(*a)
                    .and_then(|s| s.scope.as_ref())
                    .is_some_and(|scope| scope.depends_on.iter().any(|dep| &dep.interface == interface))
            })
            .cloned()
            .collect(),
        Sel::AllActive => epoch.active_members.keys().cloned().collect(),
    }
}

/// docs/AGENT_COORDINATION_EVOLUTION.md section 4.1-4.2. `audience_snapshot`
/// is not trusted as authored -- it is recomputed here by resolving
/// `audience_selector` against the exact `audience_epoch` and rejected on
/// any mismatch (gate 12: "audience resolution is exact"), the same pattern
/// `frontier::validate_complete` uses for authority events.
fn apply_broadcast_published(
    state: &mut BusState,
    env: &Envelope,
    d: &BroadcastPublished,
) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    if d.audience_snapshot.is_empty() {
        return Err(invalid(format!("{}: audience_snapshot must not be empty", env.id)));
    }
    let epoch = state
        .roster_epoch
        .as_ref()
        .filter(|e| e.id == d.audience_epoch)
        .ok_or_else(|| {
            invalid(format!(
                "{}: audience_epoch {} is not the current roster epoch",
                env.id, d.audience_epoch
            ))
        })?;
    let resolved = resolve_audience(state, &d.audience_selector, epoch);
    let claimed: BTreeSet<Agent> = d.audience_snapshot.iter().cloned().collect();
    if resolved != claimed {
        return Err(invalid(format!(
            "{}: audience_snapshot does not match resolving audience_selector against epoch {}",
            env.id, d.audience_epoch
        )));
    }
    for id in d.supersedes.iter() {
        if !state.broadcasts.contains_key(id) {
            return Err(invalid(format!("{}: supersedes unknown broadcast {id}", env.id)));
        }
    }
    state.broadcasts.insert(env.id.clone(), d.clone());
    Ok(())
}

/// docs/AGENT_COORDINATION_EVOLUTION.md section 4.2: only a broadcast whose
/// own `acknowledgement` is `required` accepts an acknowledgement, and only
/// from an agent its `audience_snapshot` actually named -- an unaddressed
/// bystander cannot manufacture an acknowledgement receipt.
fn apply_broadcast_acknowledged(
    state: &mut BusState,
    env: &Envelope,
    d: &BroadcastAcknowledged,
) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    if d.broadcasts.is_empty() {
        return Err(invalid(format!(
            "{}: broadcast.acknowledged must name at least one broadcast",
            env.id
        )));
    }
    for id in d.broadcasts.iter() {
        let broadcast = state
            .broadcasts
            .get(id)
            .ok_or_else(|| invalid(format!("{}: unknown broadcast {id}", env.id)))?;
        if broadcast.acknowledgement != crate::common::AckRequirement::Required {
            return Err(invalid(format!(
                "{}: broadcast {id} does not require acknowledgement",
                env.id
            )));
        }
        if !broadcast
            .audience_snapshot
            .iter()
            .any(|a| a == &env.agent)
        {
            return Err(invalid(format!(
                "{}: {} was not addressed by broadcast {id}",
                env.id, env.agent
            )));
        }
    }
    for id in d.broadcasts.iter() {
        state
            .broadcast_acknowledged_by
            .entry(id.clone())
            .or_default()
            .insert(env.agent.clone());
    }
    Ok(())
}

/// docs/AGENT_COORDINATION_EVOLUTION.md section 4.2: a purely optional,
/// non-authoritative read receipt -- gate 13's "informational broadcasts
/// cause no mandatory acknowledgement events" holds trivially here since
/// nothing ever requires this kind to be published at all.
fn apply_broadcast_seen(state: &mut BusState, env: &Envelope, d: &BroadcastSeen) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    if d.broadcasts.is_empty() {
        return Err(invalid(format!(
            "{}: broadcast.seen must name at least one broadcast",
            env.id
        )));
    }
    for id in d.broadcasts.iter() {
        if !state.broadcasts.contains_key(id) {
            return Err(invalid(format!("{}: unknown broadcast {id}", env.id)));
        }
    }
    for id in d.broadcasts.iter() {
        state
            .broadcast_seen_by
            .entry(id.clone())
            .or_default()
            .insert(env.agent.clone());
    }
    Ok(())
}

fn dependency_from(data: &EventData) -> EventId {
    match data {
        EventData::DependencyResolved(d) => d.dependency.clone(),
        EventData::DependencyRejected(d) => d.dependency.clone(),
        _ => unreachable!("caller already matched on these two variants"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::Priority;
    use crate::frontier::{FrontierEntry, ObservedFrontier};
    use crate::registry::{MemberBinding, RosterEpoch};
    use crate::scalars::{Branch, ObjectId, Short, StringSet, Text};

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn short(s: &str) -> Short {
        Short::parse(s.to_string()).unwrap()
    }

    fn text(s: &str) -> Text {
        Text::parse(s.to_string()).unwrap()
    }

    fn hash(n: u64) -> ObjectId {
        ObjectId::parse(format!("{n:040x}")).unwrap()
    }

    fn config() -> BusConfig {
        BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: hash(1),
            merge_engine: crate::bootstrap::SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION.to_string(),
        }
    }

    fn epoch_with(members: &[(&str, Role)]) -> RosterEpoch {
        let mut active_members = BTreeMap::new();
        for (name, role) in members {
            active_members.insert(
                a(name),
                MemberBinding {
                    role: *role,
                    host: short("host1"),
                    coordinator_custody_epoch: 0,
                },
            );
        }
        RosterEpoch::root(hash(999), active_members)
    }

    fn empty_state(members: &[(&str, Role)]) -> BusState {
        let mut state = BusState::new(config());
        state.roster_epoch = Some(epoch_with(members));
        state
    }

    fn no_frontier() -> crate::frontier::ObservedFrontier {
        ObservedFrontier::sparse(hash(1), [])
    }

    /// A frontier that has causally observed `ids` (each at exactly its own
    /// seq -- enough for `validate_reference` to accept a same-position
    /// reference).
    fn frontier_seeing(ids: &[&EventId]) -> ObservedFrontier {
        ObservedFrontier::sparse(
            hash(1),
            ids.iter().map(|id| FrontierEntry {
                agent: id.agent(),
                stream_tip: hash(1),
                through: (*id).clone(),
            }),
        )
    }

    fn register(agent: &Agent, role: Role) -> Envelope {
        let data = EventData::AgentRegistered(AgentRegistered {
            display_name: short(agent.as_str()),
            primary_role: role,
            purpose: text("x"),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        Envelope::new(agent, 0, no_frontier(), &data, [])
    }

    fn apply_ok(state: &mut BusState, env: &Envelope) {
        apply_event(state, env).unwrap_or_else(|e| panic!("{}: {e}", env.id));
        state.kind_of_event_insert(env.id.clone(), &env.kind);
        state.events.insert(env.id.clone(), env.clone());
        if let Some(ag) = state.agents.get_mut(&env.agent) {
            ag.next_seq = ag.next_seq.max(env.seq + 1);
        }
    }

    #[test]
    fn registers_an_implementor() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        assert!(state.agents.contains_key(&alice));
        assert!(state.agents[&alice].active());
    }

    #[test]
    fn rejects_a_double_registration() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let err = apply_event(&mut state, &register(&alice, Role::Implementor)).unwrap_err();
        assert!(err.to_string().contains("already registered"), "{err}");
    }

    #[test]
    fn rejects_product_fields_for_a_non_implementor() {
        let bob = a("bob");
        let data = EventData::AgentRegistered(AgentRegistered {
            display_name: short("bob"),
            primary_role: Role::Reviewer,
            purpose: text("x"),
            product_base: Some(hash(1)),
            product_branch: None,
            provider: None,
            model: None,
        });
        let env = Envelope::new(&bob, 0, no_frontier(), &data, []);
        let mut state = empty_state(&[]);
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("permitted only for an implementor"), "{err}");
    }

    /// A genuine exclusive-transition race needs two *different* agents:
    /// one stream is inherently ordered (a later event from the same author
    /// always causally follows an earlier one), so the realistic race this
    /// models is the target resolving an issue while, unaware of that, the
    /// opener concurrently reassigns the same assignment -- both legitimate
    /// actors on the same predecessor, neither having observed the other.
    #[test]
    fn issue_resolve_and_reassign_race_produces_a_lifecycle_conflict() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&carol, Role::Implementor));

        let issue_data = EventData::IssueOpened(IssueOpened {
            target: bob.clone(),
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
        });
        let issue_env = Envelope::new(&alice, 1, no_frontier(), &issue_data, []);
        apply_ok(&mut state, &issue_env);

        let resolve = EventData::IssueResolved(IssueResolved {
            issue: issue_env.id.clone(),
            assignment: issue_env.id.clone(),
            summary: text("done"),
            fix_commit: None,
            verification: vec![],
        });
        let resolve_env = Envelope::new(&bob, 1, no_frontier(), &resolve, [issue_env.id.clone()]);

        let reassign = EventData::IssueReassigned(IssueReassigned {
            issue: issue_env.id.clone(),
            previous_assignment: issue_env.id.clone(),
            previous_target: bob.clone(),
            new_target: carol.clone(),
            reason: text("bob is unavailable"),
        });
        // alice (the opener) builds this from the same starting state as
        // bob's resolve, never having observed it -- a genuine concurrent
        // claim on the same previous_assignment.
        let reassign_env = Envelope::new(
            &alice,
            2,
            no_frontier(),
            &reassign,
            [issue_env.id.clone()],
        );

        apply_ok(&mut state, &resolve_env);
        apply_ok(&mut state, &reassign_env);

        // Resolve applied first (provisionally) and set Terminal; the
        // reassign arriving concurrently must reset that back to neutral --
        // not leave the stale Terminal in place merely because it happened
        // to be seen first in this reduction order.
        assert_eq!(
            state.issues[&issue_env.id].status,
            ItemStatus::LifecycleConflict
        );
        assert_eq!(state.issues[&issue_env.id].current_target, bob);
        assert!(state.exclusive.is_contested(&resolve_env.id));
        assert!(state.exclusive.is_contested(&reassign_env.id));
    }

    /// Gate 16, exercised at the full apply.rs level (not just exclusive.rs
    /// in isolation): the exact same two racing events, reduced in the
    /// opposite order, must converge to the identical final state --
    /// including the derived `IssueState` fields the previous test checked,
    /// not merely the exclusive tracker's own bookkeeping.
    #[test]
    fn issue_race_converges_to_the_same_state_regardless_of_reduction_order() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");

        let issue_data = EventData::IssueOpened(IssueOpened {
            target: bob.clone(),
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
        });
        let issue_env = Envelope::new(&alice, 1, no_frontier(), &issue_data, []);

        let resolve = EventData::IssueResolved(IssueResolved {
            issue: issue_env.id.clone(),
            assignment: issue_env.id.clone(),
            summary: text("done"),
            fix_commit: None,
            verification: vec![],
        });
        let resolve_env = Envelope::new(&bob, 1, no_frontier(), &resolve, [issue_env.id.clone()]);
        let reassign = EventData::IssueReassigned(IssueReassigned {
            issue: issue_env.id.clone(),
            previous_assignment: issue_env.id.clone(),
            previous_target: bob.clone(),
            new_target: carol.clone(),
            reason: text("bob is unavailable"),
        });
        let reassign_env = Envelope::new(&alice, 2, no_frontier(), &reassign, [issue_env.id.clone()]);

        let mut forward = empty_state(&[]);
        apply_ok(&mut forward, &register(&alice, Role::Implementor));
        apply_ok(&mut forward, &register(&bob, Role::Implementor));
        apply_ok(&mut forward, &register(&carol, Role::Implementor));
        apply_ok(&mut forward, &issue_env);
        apply_ok(&mut forward, &resolve_env);
        apply_ok(&mut forward, &reassign_env);

        let mut reverse = empty_state(&[]);
        apply_ok(&mut reverse, &register(&alice, Role::Implementor));
        apply_ok(&mut reverse, &register(&bob, Role::Implementor));
        apply_ok(&mut reverse, &register(&carol, Role::Implementor));
        apply_ok(&mut reverse, &issue_env);
        apply_ok(&mut reverse, &reassign_env);
        apply_ok(&mut reverse, &resolve_env);

        assert_eq!(
            forward.issues[&issue_env.id].status,
            reverse.issues[&issue_env.id].status
        );
        assert_eq!(
            forward.issues[&issue_env.id].status,
            ItemStatus::LifecycleConflict
        );
        assert_eq!(
            forward.issues[&issue_env.id].current_target,
            reverse.issues[&issue_env.id].current_target
        );
    }

    #[test]
    fn lifecycle_conflict_resolved_confirms_the_selected_winner() {
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&carol, Role::Implementor));
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));

        let issue_data = EventData::IssueOpened(IssueOpened {
            target: bob.clone(),
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
        });
        let issue_env = Envelope::new(&alice, 1, no_frontier(), &issue_data, []);
        apply_ok(&mut state, &issue_env);

        let resolve = EventData::IssueResolved(IssueResolved {
            issue: issue_env.id.clone(),
            assignment: issue_env.id.clone(),
            summary: text("done"),
            fix_commit: None,
            verification: vec![],
        });
        let resolve_env = Envelope::new(&bob, 1, no_frontier(), &resolve, [issue_env.id.clone()]);
        let reassign = EventData::IssueReassigned(IssueReassigned {
            issue: issue_env.id.clone(),
            previous_assignment: issue_env.id.clone(),
            previous_target: bob.clone(),
            new_target: carol.clone(),
            reason: text("bob is unavailable"),
        });
        let reassign_env = Envelope::new(
            &alice,
            2,
            no_frontier(),
            &reassign,
            [issue_env.id.clone()],
        );
        apply_ok(&mut state, &resolve_env);
        apply_ok(&mut state, &reassign_env);
        assert_eq!(
            state.issues[&issue_env.id].status,
            ItemStatus::LifecycleConflict
        );

        let resolved_data = EventData::LifecycleConflictResolved(LifecycleConflictResolved {
            root: resolve_env.id.clone(),
            competing: StringSet::from_iter([resolve_env.id.clone(), reassign_env.id.clone()]),
            selected: resolve_env.id.clone(),
            reason: text("user said so"),
            user_authority: text("the user"),
        });
        let resolved_env = Envelope::new(
            &coord1,
            1,
            frontier_seeing(&[&resolve_env.id, &reassign_env.id]),
            &resolved_data,
            [resolve_env.id.clone(), reassign_env.id.clone()],
        );
        apply_ok(&mut state, &resolved_env);

        assert_eq!(
            state.issues[&issue_env.id].status,
            ItemStatus::Terminal("resolved")
        );
        assert_eq!(state.issues[&issue_env.id].current_target, bob);
        assert!(!state.exclusive.is_contested(&resolve_env.id));
    }

    #[test]
    fn review_nominate_accept_authorize_merge_round_trips() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));

        let request = ReviewRequest {
            authors: StringSet::from_iter([alice.clone()]),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewer: bob.clone(),
            required_checks: vec![text("build")],
            review_scope: StringSet::default(),
            summary: text("s"),
            target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
        };
        let nominate_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::ReviewNominated(request.clone()),
            [],
        );
        apply_ok(&mut state, &nominate_env);

        let accept_data = EventData::ReviewNominationAccepted(ReviewNominationAccepted {
            nomination: nominate_env.id.clone(),
            note: text(""),
        });
        let accept_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&nominate_env.id]),
            &accept_data,
            [nominate_env.id.clone()],
        );
        apply_ok(&mut state, &accept_env);
        assert!(state.review_chain(&nominate_env.id).unwrap().accepted());

        let authorize_data = EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
            nomination: nominate_env.id.clone(),
            product_branch: request.product_branch.clone(),
            previous_main: hash(2),
            reviewed_commit: hash(3),
            candidate: hash(4),
            merge_engine_epoch: EventId::new(&a("coord1"), 0),
            checks: vec![crate::common::CheckResult {
                command: text("build"),
                result: crate::common::CheckOutcome::Passed,
                evidence: None,
            }],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::default(),
            limitations: vec![],
            summary: text("looks good"),
        });
        let authorize_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &authorize_data,
            [nominate_env.id.clone(), EventId::new(&a("coord1"), 0)],
        );
        apply_ok(&mut state, &authorize_env);
        assert_eq!(
            state.review_chain(&nominate_env.id).unwrap().authorizations,
            vec![authorize_env.id.clone()]
        );

        let merged_data = EventData::ReviewMerged(ReviewMerged {
            authorization: authorize_env.id.clone(),
            previous_main: hash(2),
            main_commit: hash(4),
            product_branch: request.product_branch,
            reviewed_commit: hash(3),
            summary: text("merged"),
        });
        let merged_env = Envelope::new(
            &bob,
            3,
            frontier_seeing(&[&authorize_env.id]),
            &merged_data,
            [authorize_env.id.clone()],
        );
        apply_ok(&mut state, &merged_env);
        assert!(state.review_chain(&nominate_env.id).unwrap().is_closed());
    }

    #[test]
    fn review_merge_authorized_rejects_a_missing_required_check() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let request = ReviewRequest {
            authors: StringSet::from_iter([alice.clone()]),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewer: bob.clone(),
            required_checks: vec![text("build"), text("test")],
            review_scope: StringSet::default(),
            summary: text("s"),
            target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
        };
        let nominate_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::ReviewNominated(request),
            [],
        );
        apply_ok(&mut state, &nominate_env);
        let accept_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: nominate_env.id.clone(),
                note: text(""),
            }),
            [nominate_env.id.clone()],
        );
        apply_ok(&mut state, &accept_env);

        let authorize_data = EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
            nomination: nominate_env.id.clone(),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            previous_main: hash(2),
            reviewed_commit: hash(3),
            candidate: hash(4),
            merge_engine_epoch: EventId::new(&a("coord1"), 0),
            checks: vec![crate::common::CheckResult {
                command: text("build"),
                result: crate::common::CheckOutcome::Passed,
                evidence: None,
            }],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::default(),
            limitations: vec![],
            summary: text("s"),
        });
        let authorize_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &authorize_data,
            [nominate_env.id.clone(), EventId::new(&a("coord1"), 0)],
        );
        let err = apply_event(&mut state, &authorize_env).unwrap_err();
        assert!(err.to_string().contains("required check"), "{err}");
    }

    /// AGENT_BUS.md section 10: "review decline/withdraw/reassign from one
    /// nomination" is an exclusive set. An author reassigning to a new
    /// reviewer, concurrent with the (unaware, not-yet-superseded) reviewer
    /// declining, must produce a lifecycle conflict -- not let whichever one
    /// happens to be reduced first silently win, and not leave the chain in
    /// a state that depends on reduction order.
    #[test]
    fn review_decline_and_reassign_race_produces_a_lifecycle_conflict() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");

        let request = ReviewRequest {
            authors: StringSet::from_iter([alice.clone()]),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewer: bob.clone(),
            required_checks: vec![],
            review_scope: StringSet::default(),
            summary: text("s"),
            target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
        };
        let nominate_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::ReviewNominated(request.clone()),
            [],
        );

        let decline_data = EventData::ReviewNominationDeclined(ReviewNominationDeclined {
            nomination: nominate_env.id.clone(),
            reason: text("too busy"),
        });
        let decline_env = Envelope::new(
            &bob,
            1,
            no_frontier(),
            &decline_data,
            [nominate_env.id.clone()],
        );

        let reassign_data = EventData::ReviewReassigned(ReviewReassigned {
            authors: request.authors.clone(),
            product_branch: request.product_branch.clone(),
            reviewer: carol.clone(),
            required_checks: request.required_checks.clone(),
            review_scope: request.review_scope.clone(),
            summary: request.summary.clone(),
            target_branch: request.target_branch.clone(),
            evidence: request.evidence.clone(),
            replaces: nominate_env.id.clone(),
            reason: text("bob went quiet"),
            inherited_findings: vec![],
        });
        let reassign_env = Envelope::new(
            &alice,
            2,
            no_frontier(),
            &reassign_data,
            [nominate_env.id.clone()],
        );

        let mut forward = empty_state(&[]);
        apply_ok(&mut forward, &register(&alice, Role::Implementor));
        apply_ok(&mut forward, &register(&bob, Role::Reviewer));
        apply_ok(&mut forward, &register(&carol, Role::Reviewer));
        apply_ok(&mut forward, &nominate_env);
        apply_ok(&mut forward, &decline_env);
        apply_ok(&mut forward, &reassign_env);

        let mut reverse = empty_state(&[]);
        apply_ok(&mut reverse, &register(&alice, Role::Implementor));
        apply_ok(&mut reverse, &register(&bob, Role::Reviewer));
        apply_ok(&mut reverse, &register(&carol, Role::Reviewer));
        apply_ok(&mut reverse, &nominate_env);
        apply_ok(&mut reverse, &reassign_env);
        apply_ok(&mut reverse, &decline_env);

        for (label, state) in [("forward", &forward), ("reverse", &reverse)] {
            let chain = state.review_chain(&nominate_env.id).unwrap();
            assert_eq!(
                chain.decline_or_withdraw_or_reassign_status,
                ItemStatus::LifecycleConflict,
                "{label} order"
            );
            assert_eq!(
                chain.current_nomination, nominate_env.id,
                "{label} order: the provisional reassignment link must be fully retracted, \
                 not left dangling as the chain's current nomination"
            );
            assert_eq!(chain.current_request, request, "{label} order");
            assert!(
                !state
                    .review_chain_by_nomination
                    .contains_key(&reassign_env.id),
                "{label} order: the retracted link's phantom mapping must not remain queryable"
            );
        }
    }

    #[test]
    fn scope_conflict_via_exclusive_overlap_is_reported_not_rejected() {
        // AGENT_BUS.md 6.2: "Active exclusive/exclusive overlap is a
        // conflict... Validation reports these states but does not reject
        // the bus merely because a scope conflict exists." Both scope.set
        // events must apply successfully even though they overlap.
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let claim = crate::scalars::PathClaim::parse("Grass/Shared/**".into()).unwrap();
        let scope_data = |agent: &Agent| {
            EventData::ScopeSet(ScopeSet {
                base_code_commit: hash(1),
                exclusive: StringSet::from_iter([claim.clone()]),
                shared: StringSet::default(),
                exports: StringSet::default(),
                depends_on: vec![],
                note: text(agent.as_str()),
            })
        };
        apply_ok(
            &mut state,
            &Envelope::new(&alice, 1, no_frontier(), &scope_data(&alice), []),
        );
        apply_ok(
            &mut state,
            &Envelope::new(&bob, 1, no_frontier(), &scope_data(&bob), []),
        );
        assert!(state.agents[&alice].scope.is_some());
        assert!(state.agents[&bob].scope.is_some());
    }

    // -------------------------------------------------------------- friction

    fn topic(s: &str) -> crate::scalars::CoordinationTopic {
        crate::scalars::CoordinationTopic::parse(s.to_string()).unwrap()
    }

    fn friction_report(area: &str) -> FrictionReported {
        FrictionReported {
            area: topic(area),
            summary: short("s"),
            impact: crate::common::Impact::Rebuild,
            evidence: StringSet::default(),
            product_locations: vec![],
            measurements: vec![],
            frequency: None,
            workaround: None,
            suggestion: None,
            likely_owner: None,
        }
    }

    /// Gate 11: a friction report is recorded as evidence and creates no
    /// target obligation -- unlike `issue.opened`, nothing in `state` gains
    /// a status, an assignment, or an acknowledgement duty from it.
    #[test]
    fn friction_report_creates_no_target_obligation() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::FrictionReported(friction_report("proof.rebuild")),
            [],
        );
        apply_ok(&mut state, &env);
        assert!(state.friction_reports.contains_key(&env.id));
        assert!(state.issues.is_empty());
        assert!(state.dependencies.is_empty());
        assert!(state.handoffs.is_empty());
    }

    #[test]
    fn friction_report_with_measurements_requires_evidence() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let mut data = friction_report("proof.rebuild");
        data.measurements = vec![crate::common::Measurement {
            metric: short("wall_time_seconds"),
            value: 120,
            unit: None,
        }];
        let env = Envelope::new(&alice, 1, no_frontier(), &EventData::FrictionReported(data), []);
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("must cite supporting evidence"), "{err}");
    }

    fn synthesized(
        theme: &str,
        reports: &[&EventId],
        disposition: crate::common::FrictionDispositionKind,
    ) -> FrictionSynthesized {
        FrictionSynthesized {
            theme: topic(theme),
            reports: StringSet::from_iter(reports.iter().map(|r| (*r).clone())),
            disposition,
            rationale: text("r"),
            promoted_to: None,
            duplicate_of: None,
            revisit_trigger: None,
        }
    }

    #[test]
    fn friction_synthesized_rejects_a_report_it_never_saw() {
        let mut state = empty_state(&[]);
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let phantom = EventId::new(&a("alice"), 1);
        let env = Envelope::new(
            &coord1,
            1,
            no_frontier(),
            &EventData::FrictionSynthesized(synthesized(
                "proof.rebuild",
                &[&phantom],
                crate::common::FrictionDispositionKind::AcceptedCost,
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("unknown friction report"), "{err}");
    }

    /// `accepted_cost` and `needs_evidence` are the two dispositions with no
    /// companion field at all -- the happy path with none of promoted_to/
    /// duplicate_of/revisit_trigger set.
    #[test]
    fn friction_synthesized_accepted_cost_needs_no_companion_field() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let report_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::FrictionReported(friction_report("proof.rebuild")),
            [],
        );
        apply_ok(&mut state, &report_env);

        let env = Envelope::new(
            &coord1,
            1,
            no_frontier(),
            &EventData::FrictionSynthesized(synthesized(
                "proof.rebuild",
                &[&report_env.id],
                crate::common::FrictionDispositionKind::AcceptedCost,
            )),
            [],
        );
        apply_ok(&mut state, &env);
        assert_eq!(
            state.friction_theme_synthesis.get(&topic("proof.rebuild")),
            Some(&env.id)
        );
    }

    #[test]
    fn friction_synthesized_promoted_requires_promoted_to() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let report_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::FrictionReported(friction_report("proof.rebuild")),
            [],
        );
        apply_ok(&mut state, &report_env);

        let env = Envelope::new(
            &coord1,
            1,
            no_frontier(),
            &EventData::FrictionSynthesized(synthesized(
                "proof.rebuild",
                &[&report_env.id],
                crate::common::FrictionDispositionKind::Promoted,
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("promoted_to must be set"),
            "{err}"
        );
    }

    #[test]
    fn friction_synthesized_duplicate_must_name_a_known_prior_synthesis() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let report_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::FrictionReported(friction_report("proof.rebuild")),
            [],
        );
        apply_ok(&mut state, &report_env);

        let mut data = synthesized(
            "proof.rebuild",
            &[&report_env.id],
            crate::common::FrictionDispositionKind::Duplicate,
        );
        data.duplicate_of = Some(EventId::new(&coord1, 99));
        let env = Envelope::new(&coord1, 1, no_frontier(), &EventData::FrictionSynthesized(data), []);
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("unknown synthesis event"), "{err}");
    }

    #[test]
    fn friction_synthesized_deferred_requires_revisit_trigger() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let report_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::FrictionReported(friction_report("proof.rebuild")),
            [],
        );
        apply_ok(&mut state, &report_env);

        let env = Envelope::new(
            &coord1,
            1,
            no_frontier(),
            &EventData::FrictionSynthesized(synthesized(
                "proof.rebuild",
                &[&report_env.id],
                crate::common::FrictionDispositionKind::Deferred,
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("revisit_trigger must be set"),
            "{err}"
        );
    }

    // ------------------------------------------------------------- broadcasts

    fn broadcast(
        audience_epoch: ObjectId,
        selector: crate::common::AudienceSelector,
        snapshot: &[&Agent],
        acknowledgement: crate::common::AckRequirement,
    ) -> BroadcastPublished {
        BroadcastPublished {
            topics: StringSet::from_iter([topic("release.main")]),
            importance: crate::common::Importance::Informational,
            summary: short("s"),
            detail: text("d"),
            affected_paths: StringSet::default(),
            affected_interfaces: StringSet::default(),
            product_commits: StringSet::default(),
            audience_selector: selector,
            audience_epoch,
            audience_snapshot: StringSet::from_iter(snapshot.iter().map(|a| (*a).clone())),
            acknowledgement,
            deadline: None,
            supersedes: StringSet::default(),
            workaround: None,
            expiry_condition: None,
        }
    }

    #[test]
    fn broadcast_all_active_resolves_to_every_active_member() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Implementor),
            ("coord1", Role::Coordinator),
        ]);
        let alice = a("alice");
        let bob = a("bob");
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let epoch_id = state.roster_epoch.as_ref().unwrap().id.clone();

        let env = Envelope::new(
            &coord1,
            1,
            no_frontier(),
            &EventData::BroadcastPublished(broadcast(
                epoch_id,
                crate::common::AudienceSelector::AllActive,
                &[&alice, &bob, &coord1],
                crate::common::AckRequirement::None,
            )),
            [],
        );
        apply_ok(&mut state, &env);
        assert!(state.broadcasts.contains_key(&env.id));
    }

    #[test]
    fn broadcast_rejects_an_audience_snapshot_that_omits_an_active_member() {
        let mut state = empty_state(&[("alice", Role::Implementor), ("bob", Role::Implementor)]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let epoch_id = state.roster_epoch.as_ref().unwrap().id.clone();

        let env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::BroadcastPublished(broadcast(
                epoch_id,
                crate::common::AudienceSelector::AllActive,
                &[&alice], // missing bob
                crate::common::AckRequirement::None,
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("does not match resolving"), "{err}");
    }

    #[test]
    fn broadcast_topic_subscribers_resolves_from_subscription_set() {
        let mut state = empty_state(&[("alice", Role::Implementor), ("bob", Role::Implementor)]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(
            &mut state,
            &Envelope::new(
                &alice,
                1,
                no_frontier(),
                &EventData::SubscriptionSet(SubscriptionSet {
                    topics: StringSet::from_iter([topic("safety.memory")]),
                }),
                [],
            ),
        );
        let epoch_id = state.roster_epoch.as_ref().unwrap().id.clone();

        let env = Envelope::new(
            &alice,
            2,
            no_frontier(),
            &EventData::BroadcastPublished(broadcast(
                epoch_id,
                crate::common::AudienceSelector::TopicSubscribers(topic("safety.memory")),
                &[&alice],
                crate::common::AckRequirement::None,
            )),
            [],
        );
        apply_ok(&mut state, &env);
        assert!(state.broadcasts.contains_key(&env.id));
    }

    #[test]
    fn broadcast_rejects_a_stale_audience_epoch() {
        let mut state = empty_state(&[("alice", Role::Implementor)]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));

        let env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::BroadcastPublished(broadcast(
                hash(12345), // not the current roster epoch id
                crate::common::AudienceSelector::AllActive,
                &[&alice],
                crate::common::AckRequirement::None,
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("is not the current roster epoch"), "{err}");
    }

    #[test]
    fn broadcast_acknowledged_requires_required_acknowledgement() {
        let mut state = empty_state(&[("alice", Role::Implementor)]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let epoch_id = state.roster_epoch.as_ref().unwrap().id.clone();

        let broadcast_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::BroadcastPublished(broadcast(
                epoch_id,
                crate::common::AudienceSelector::AllActive,
                &[&alice],
                crate::common::AckRequirement::None, // not required
            )),
            [],
        );
        apply_ok(&mut state, &broadcast_env);

        let env = Envelope::new(
            &alice,
            2,
            no_frontier(),
            &EventData::BroadcastAcknowledged(BroadcastAcknowledged {
                broadcasts: StringSet::from_iter([broadcast_env.id.clone()]),
            }),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("does not require acknowledgement"), "{err}");
    }

    #[test]
    fn broadcast_acknowledged_rejects_an_agent_outside_the_audience() {
        let mut state = empty_state(&[("alice", Role::Implementor), ("bob", Role::Implementor)]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let epoch_id = state.roster_epoch.as_ref().unwrap().id.clone();

        let broadcast_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::BroadcastPublished(broadcast(
                epoch_id,
                crate::common::AudienceSelector::Agents(StringSet::from_iter([alice.clone()])),
                &[&alice], // bob is not addressed
                crate::common::AckRequirement::Required,
            )),
            [],
        );
        apply_ok(&mut state, &broadcast_env);

        let env = Envelope::new(
            &bob,
            1,
            no_frontier(),
            &EventData::BroadcastAcknowledged(BroadcastAcknowledged {
                broadcasts: StringSet::from_iter([broadcast_env.id.clone()]),
            }),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("was not addressed"), "{err}");
    }

    #[test]
    fn broadcast_acknowledged_by_an_addressed_agent_records_it() {
        let mut state = empty_state(&[("alice", Role::Implementor)]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let epoch_id = state.roster_epoch.as_ref().unwrap().id.clone();

        let broadcast_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::BroadcastPublished(broadcast(
                epoch_id,
                crate::common::AudienceSelector::AllActive,
                &[&alice],
                crate::common::AckRequirement::Required,
            )),
            [],
        );
        apply_ok(&mut state, &broadcast_env);

        let env = Envelope::new(
            &alice,
            2,
            no_frontier(),
            &EventData::BroadcastAcknowledged(BroadcastAcknowledged {
                broadcasts: StringSet::from_iter([broadcast_env.id.clone()]),
            }),
            [],
        );
        apply_ok(&mut state, &env);
        assert!(state.broadcast_acknowledged_by[&broadcast_env.id].contains(&alice));
    }

    /// Gate 13: `broadcast.seen` never implies the announced problem is
    /// fixed and is accepted regardless of `acknowledgement` -- unlike
    /// `broadcast.acknowledged`, there is no "required" precondition at all.
    #[test]
    fn broadcast_seen_is_accepted_for_an_informational_broadcast() {
        let mut state = empty_state(&[("alice", Role::Implementor)]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let epoch_id = state.roster_epoch.as_ref().unwrap().id.clone();

        let broadcast_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::BroadcastPublished(broadcast(
                epoch_id,
                crate::common::AudienceSelector::AllActive,
                &[&alice],
                crate::common::AckRequirement::None,
            )),
            [],
        );
        apply_ok(&mut state, &broadcast_env);

        let env = Envelope::new(
            &alice,
            2,
            no_frontier(),
            &EventData::BroadcastSeen(BroadcastSeen {
                broadcasts: StringSet::from_iter([broadcast_env.id.clone()]),
            }),
            [],
        );
        apply_ok(&mut state, &env);
        assert!(state.broadcast_seen_by[&broadcast_env.id].contains(&alice));
    }
}
