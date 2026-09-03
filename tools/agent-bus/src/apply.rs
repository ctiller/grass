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
use crate::scalars::{Agent, EventId, ObjectId};
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
    known_epochs: BTreeMap<ObjectId, crate::registry::RosterEpoch>,
    streams: &BTreeMap<Agent, Vec<Envelope>>,
) -> AbResult<BusState> {
    let mut state = BusState::new(config);
    state.roster_epoch = roster_epoch;
    state.known_epochs = known_epochs;
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
        EventData::DependencyResolved(d) => {
            apply_dependency_terminal(state, env, &data, &d.dependency, &d.assignment, "resolved")?
        }
        EventData::DependencyRejected(d) => {
            apply_dependency_terminal(state, env, &data, &d.dependency, &d.assignment, "rejected")?
        }
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

fn apply_registered(state: &mut BusState, env: &Envelope, d: &AgentRegistered) -> AbResult<()> {
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

/// Section 2.2's complete-frontier requirement for fleet-wide authority
/// events ("events that grant merge authority... activate schemas... or
/// make another fleet-wide decision use a complete frontier relative to
/// one exact RosterEpoch", gate 5/12). Validates against the *exact* epoch
/// `env.observed` itself names (`state.known_epochs`), never against
/// whatever epoch happens to be current at reduction time: those are
/// frequently different (any later registration/retirement/succession
/// advances `state.roster_epoch` while an already-published authority
/// event's frontier still names the older epoch it was actually authored
/// against), and "a later registration can never retroactively invalidate
/// an earlier authority event's already-complete frontier" is only true if
/// validation looks the named epoch up rather than compares against "now."
fn require_complete_frontier(state: &BusState, env: &Envelope) -> AbResult<()> {
    if env.observed.kind != crate::frontier::FrontierKind::Complete {
        return Err(invalid(format!(
            "{}: this event requires a complete frontier, not a sparse one",
            env.id
        )));
    }
    let epoch = state
        .known_epochs
        .get(&env.observed.roster_epoch)
        .ok_or_else(|| {
            invalid(format!(
                "{}: frontier names roster epoch {}, which is not a known epoch",
                env.id, env.observed.roster_epoch
            ))
        })?;
    env.observed.validate_complete(epoch)
}

fn apply_schema_activated(
    state: &mut BusState,
    env: &Envelope,
    d: &SchemaActivated,
) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    require_complete_frontier(state, env)?;
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
    require_complete_frontier(state, env)?;
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
    if d.merge_engine_version.as_str() != crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION {
        return Err(invalid(format!(
            "{}: unsupported merge_engine_version {}",
            env.id, d.merge_engine_version
        )));
    }
    let key = format!("engine_epoch:{}", d.previous_epoch);
    state.exclusive.record(&key, &env.id, |other| {
        env.observed.validate_reference(other).is_ok()
    })?;
    state.merge_engine_info.insert(
        env.id.clone(),
        (d.merge_engine.clone(), d.merge_engine_version.clone()),
    );
    if state.exclusive.winner(&key).as_ref() == Some(&env.id) {
        state.current_merge_engine_epoch = Some(env.id.clone());
    } else {
        // A second, genuinely concurrent candidate turned this group
        // contested -- unwind `current_merge_engine_epoch` back to the
        // shared pre-race baseline every candidate in this group agrees on
        // (`d.previous_epoch`), the same "provisional apply, then reset on
        // conflict" pattern `reset_issue_to_conflict`/`reset_dependency_to_
        // conflict` use. Idempotent: a third+ candidate in an already-
        // contested group finds this already at baseline and just resets
        // it to the same value again.
        state.current_merge_engine_epoch = Some(d.previous_epoch.clone());
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
    let ag = state
        .agents
        .get_mut(&env.agent)
        .expect("checked by require_active_role");
    ag.scope = Some(d.clone());
    Ok(())
}

fn apply_plan_set(state: &mut BusState, env: &Envelope, d: &PlanSet) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    let mut ids = std::collections::BTreeSet::new();
    for step in &d.steps {
        if !ids.insert(step.id.as_str()) {
            return Err(invalid(format!(
                "{}: duplicate plan step id {}",
                env.id, step.id
            )));
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
            acknowledged_assignments: BTreeSet::new(),
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
    if issue.acknowledged() {
        return Err(invalid(format!("{}: issue already acknowledged", env.id)));
    }
    issue.acknowledged_assignments.insert(d.assignment.clone());
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
        if issue.current_assignment != *assignment {
            // A provisional reassignment already ran before this conflict
            // was detected (exclusive::winner() gives a lone candidate the
            // group's effect until a second member arrives) -- retract
            // exactly what it added, not just the derived `status`/
            // `current_*` fields. Any later member of the same group
            // observes current_assignment already at baseline and takes
            // this branch as a no-op, so this fires at most once per race
            // regardless of group size or processing order (gates 15/16).
            let provisional = issue.current_assignment.clone();
            issue.assignment_target.remove(&provisional);
            issue.reassignment_chain.retain(|id| id != &provisional);
        }
        issue.current_assignment = assignment.clone();
        issue.current_target = target.clone();
    }
}

fn apply_issue_reassigned(
    state: &mut BusState,
    env: &Envelope,
    d: &IssueReassigned,
) -> AbResult<()> {
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
        // No `acknowledged` reset needed: `env_id` is a brand-new assignment
        // id that has never been inserted into `acknowledged_assignments`,
        // so `issue.acknowledged()` is automatically false for it.
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
            acknowledged_assignments: BTreeSet::new(),
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
    let dep = state
        .dependencies
        .get_mut(&d.dependency)
        .expect("just checked");
    if dep.acknowledged() {
        return Err(invalid(format!(
            "{}: dependency already acknowledged",
            env.id
        )));
    }
    dep.acknowledged_assignments.insert(d.assignment.clone());
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
/// retracting exactly the `assignment_target`/`reassignment_chain` entry a
/// provisionally-applied reassignment may have added, not just `status`),
/// applied to dependencies.
fn reset_dependency_to_conflict(
    state: &mut BusState,
    dependency_id: &EventId,
    assignment: &EventId,
    target: &Agent,
) {
    if let Some(dep) = state.dependencies.get_mut(dependency_id) {
        dep.status = ItemStatus::LifecycleConflict;
        if dep.current_assignment != *assignment {
            let provisional = dep.current_assignment.clone();
            dep.assignment_target.remove(&provisional);
            dep.reassignment_chain.retain(|id| id != &provisional);
        }
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
        // See issue_reassign_effect: no `acknowledged` reset needed, since
        // `env_id` is a brand-new assignment id never yet acknowledged.
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
            if !chain
                .current_request
                .authors
                .iter()
                .any(|a| a == &env.agent)
            {
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
            return Err(invalid(format!(
                "{}: duplicate finding id {}",
                env.id, f.id
            )));
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
    let is_author = chain
        .current_request
        .authors
        .iter()
        .any(|a| a == &env.agent);
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
    require_complete_frontier(state, env)?;
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
    // AGENT_BUS_SCHEMA.md: "merge_engine_epoch is the selected engine epoch
    // visible in the authorization's observed state" -- not merely some
    // historically-known activation, but the one currently selected.
    if Some(&d.merge_engine_epoch) != state.current_merge_engine_epoch.as_ref() {
        return Err(invalid(format!(
            "{}: merge_engine_epoch {} is not the currently selected merge engine epoch",
            env.id, d.merge_engine_epoch
        )));
    }
    for check in &d.checks {
        if !chain
            .current_request
            .required_checks
            .iter()
            .any(|c| c.as_str() == check.command.as_str())
        {
            // Extra checks beyond required are fine; required checks must
            // all be present, verified below.
        }
    }
    for required in chain.current_request.required_checks.iter() {
        if !d
            .checks
            .iter()
            .any(|c| c.command.as_str() == required.as_str())
        {
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
    // AGENT_BUS_SCHEMA.md section 10: "Only unresolved issues whose `blocks`
    // set names an event in the active nomination chain block
    // authorization." A resolved/rejected (Terminal) issue never blocks,
    // even if its `blocks` set still names a chain event -- disposition is
    // permanent, so there is nothing left to re-check once it fires.
    for issue in state.issues.values() {
        if matches!(issue.status, ItemStatus::Terminal(_)) {
            continue;
        }
        if let Some(blocked) = issue
            .data
            .blocks
            .iter()
            .find(|b| chain.nomination_events.contains(b))
        {
            return Err(invalid(format!(
                "{}: unresolved issue {} blocks authorization via nomination-chain event {blocked}",
                env.id, issue.id
            )));
        }
    }
    let chain_mut = state
        .review_chain_mut(&d.nomination)
        .expect("checked above");
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
    let auth_env = state.events.get(&d.authorization).ok_or_else(|| {
        invalid(format!(
            "{}: unknown authorization {}",
            env.id, d.authorization
        ))
    })?;
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
    let auth_env = state.events.get(&d.authorization).ok_or_else(|| {
        invalid(format!(
            "{}: unknown authorization {}",
            env.id, d.authorization
        ))
    })?;
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
    let winner_env = state.events.get(&d.selected).cloned().ok_or_else(|| {
        invalid(format!(
            "{}: selected event {} is unknown",
            env.id, d.selected
        ))
    })?;
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
        EventData::HandoffAccepted(hd) => handoff_terminal_effect(state, &hd.handoff, "accepted"),
        EventData::HandoffDeclined(hd) => handoff_terminal_effect(state, &hd.handoff, "declined"),
        EventData::HandoffWithdrawn(hd) => handoff_terminal_effect(state, &hd.handoff, "withdrawn"),
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
                    .is_some_and(|scope| {
                        scope
                            .depends_on
                            .iter()
                            .any(|dep| &dep.interface == interface)
                    })
            })
            .cloned()
            .collect(),
        Sel::AllActive => epoch.active_members.keys().cloned().collect(),
    }
}

/// Section 4.2: "Selectors involving all active agents, and every
/// required-ack broadcast to a derived audience, require a complete
/// frontier for that epoch. An explicit list may use a sparse frontier
/// containing each named identity." Two independent triggers, either one
/// requiring completeness: the selector is `AllActive`, or it's a derived
/// (non-explicit-list) selector on a required-ack broadcast.
pub fn broadcast_requires_complete_frontier(d: &BroadcastPublished) -> bool {
    use crate::common::AudienceSelector as Sel;
    match &d.audience_selector {
        Sel::AllActive => true,
        Sel::Agents(_) => false,
        Sel::Roles(_) | Sel::TopicSubscribers(_) | Sel::InterfaceDependents(_) => {
            d.acknowledgement == crate::common::AckRequirement::Required
        }
    }
}

/// docs/AGENT_COORDINATION_EVOLUTION.md section 4.1-4.2. `audience_snapshot`
/// is not trusted as authored -- it is recomputed here by resolving
/// `audience_selector` against the exact `audience_epoch` and rejected on
/// any mismatch (gate 12: "audience resolution is exact"). That alone
/// proves the *named* audience is exactly right; it says nothing about
/// whether the publisher actually had causal visibility into each member's
/// stream when it computed that answer, which is what `env.observed`
/// itself (checked here via `broadcast_requires_complete_frontier` and
/// `ObservedFrontier::validate_complete`) is for -- the two checks are
/// independent and both required.
fn apply_broadcast_published(
    state: &mut BusState,
    env: &Envelope,
    d: &BroadcastPublished,
) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    if d.audience_snapshot.is_empty() {
        return Err(invalid(format!(
            "{}: audience_snapshot must not be empty",
            env.id
        )));
    }
    let epoch = state.known_epochs.get(&d.audience_epoch).ok_or_else(|| {
        invalid(format!(
            "{}: audience_epoch {} is not a known roster epoch",
            env.id, d.audience_epoch
        ))
    })?;
    if broadcast_requires_complete_frontier(d) {
        if env.observed.kind != crate::frontier::FrontierKind::Complete {
            return Err(invalid(format!(
                "{}: this audience selector requires a complete frontier, not a sparse one",
                env.id
            )));
        }
        env.observed.validate_complete(epoch)?;
    }
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
            return Err(invalid(format!(
                "{}: supersedes unknown broadcast {id}",
                env.id
            )));
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
        if !broadcast.audience_snapshot.iter().any(|a| a == &env.agent) {
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
                    standby: None,
                },
            );
        }
        RosterEpoch::root(hash(999), active_members)
    }

    fn empty_state(members: &[(&str, Role)]) -> BusState {
        let mut state = BusState::new(config());
        let epoch = epoch_with(members);
        state.known_epochs.insert(epoch.id.clone(), epoch.clone());
        state.roster_epoch = Some(epoch);
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
        assert!(
            err.to_string()
                .contains("permitted only for an implementor"),
            "{err}"
        );
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
        let reassign_env =
            Envelope::new(&alice, 2, no_frontier(), &reassign, [issue_env.id.clone()]);

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
        let reassign_env =
            Envelope::new(&alice, 2, no_frontier(), &reassign, [issue_env.id.clone()]);

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

    /// Adversarial-review regression: two racing `IssueReassigned` events
    /// (not `IssueResolved` vs `IssueReassigned` -- the only combination
    /// `issue_race_converges_to_the_same_state_regardless_of_reduction_order`
    /// exercises, which never touches `reassignment_chain`/
    /// `assignment_target` since `apply_issue_terminal_effect` doesn't
    /// mutate either). This is the one code path that can leave a
    /// provisionally-applied reassignment's bookkeeping stuck if
    /// `reset_issue_to_conflict` only reverts `status`/`current_*`.
    #[test]
    fn two_racing_issue_reassignments_converge_with_no_stale_chain_entry() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let dave = a("dave");

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

        let to_carol = EventData::IssueReassigned(IssueReassigned {
            issue: issue_env.id.clone(),
            previous_assignment: issue_env.id.clone(),
            previous_target: bob.clone(),
            new_target: carol.clone(),
            reason: text("r1"),
        });
        let to_carol_env =
            Envelope::new(&alice, 2, no_frontier(), &to_carol, [issue_env.id.clone()]);
        // Authored by a *different* agent than `to_carol_env` -- same-agent
        // events are always causally ordered by stream position (the
        // exclusive tracker treats any two events from the same author as
        // observing each other), so a genuine race needs two agents.
        // coord1 stands in for the bootstrap coordinator, the other agent
        // `apply_issue_reassigned` allows to reassign a non-owned issue.
        let coord1 = a("coord1");
        let to_dave = EventData::IssueReassigned(IssueReassigned {
            issue: issue_env.id.clone(),
            previous_assignment: issue_env.id.clone(),
            previous_target: bob.clone(),
            new_target: dave.clone(),
            reason: text("r2"),
        });
        let to_dave_env =
            Envelope::new(&coord1, 1, no_frontier(), &to_dave, [issue_env.id.clone()]);

        let run = |order: &[&Envelope]| {
            let mut state = empty_state(&[
                ("alice", Role::Implementor),
                ("bob", Role::Implementor),
                ("carol", Role::Implementor),
                ("dave", Role::Implementor),
                ("coord1", Role::Coordinator),
            ]);
            apply_ok(&mut state, &register(&alice, Role::Implementor));
            apply_ok(&mut state, &register(&bob, Role::Implementor));
            apply_ok(&mut state, &register(&carol, Role::Implementor));
            apply_ok(&mut state, &register(&dave, Role::Implementor));
            apply_ok(&mut state, &register(&a("coord1"), Role::Coordinator));
            apply_ok(&mut state, &issue_env);
            for env in order {
                apply_ok(&mut state, env);
            }
            state
        };

        let forward = run(&[&to_carol_env, &to_dave_env]);
        let reverse = run(&[&to_dave_env, &to_carol_env]);

        for state in [&forward, &reverse] {
            let issue = &state.issues[&issue_env.id];
            assert_eq!(issue.status, ItemStatus::LifecycleConflict);
            assert_eq!(issue.current_assignment, issue_env.id);
            assert_eq!(issue.current_target, bob);
            assert!(
                issue.reassignment_chain.is_empty(),
                "both racing candidates' provisional chain entries must be fully retracted: {:?}",
                issue.reassignment_chain
            );
            assert_eq!(
                issue.assignment_target.len(),
                1,
                "only the issue's own opening assignment id should remain: {:?}",
                issue.assignment_target
            );
        }
        assert_eq!(
            forward.issues[&issue_env.id].reassignment_chain,
            reverse.issues[&issue_env.id].reassignment_chain
        );

        // Resolving to the winner must append it exactly once -- not twice
        // (the already-provisionally-applied case) and not alongside the
        // loser's now-stale id (the never-retracted case).
        let mut state = forward;
        let resolved_data = EventData::LifecycleConflictResolved(LifecycleConflictResolved {
            root: to_carol_env.id.clone(),
            competing: StringSet::from_iter([to_carol_env.id.clone(), to_dave_env.id.clone()]),
            selected: to_carol_env.id.clone(),
            reason: text("user said so"),
            user_authority: text("the user"),
        });
        let resolved_env = Envelope::new(
            &a("coord1"),
            2, // coord1:1 is to_dave_env, already applied to `forward`
            frontier_seeing(&[&to_carol_env.id, &to_dave_env.id]),
            &resolved_data,
            [to_carol_env.id.clone(), to_dave_env.id.clone()],
        );
        apply_ok(&mut state, &resolved_env);
        let issue = &state.issues[&issue_env.id];
        assert_eq!(issue.reassignment_chain, vec![to_carol_env.id.clone()]);
        assert_eq!(issue.current_target, carol);
        assert_eq!(issue.assignment_target.len(), 2);
    }

    /// Adversarial-review regression: `acknowledged_assignments` (unlike a
    /// flat bool) survives a reassignment race intact -- if the *baseline*
    /// assignment had been acknowledged before the race began, resetting
    /// back to that baseline after a lost race must still report it as
    /// acknowledged, not silently lose that fact because a provisional
    /// effect overwrote it in between.
    #[test]
    fn acknowledged_status_survives_a_reassignment_race_reset() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let coord1 = a("coord1");

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

        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Implementor),
            ("carol", Role::Implementor),
            ("coord1", Role::Coordinator),
        ]);
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&carol, Role::Implementor));
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        apply_ok(&mut state, &issue_env);

        let ack_data = EventData::IssueAcknowledged(IssueAcknowledged {
            issue: issue_env.id.clone(),
            assignment: issue_env.id.clone(),
            note: text(""),
        });
        let ack_env = Envelope::new(&bob, 1, no_frontier(), &ack_data, [issue_env.id.clone()]);
        apply_ok(&mut state, &ack_env);
        assert!(state.issues[&issue_env.id].acknowledged());

        // Two racing reassignments off the (acknowledged) baseline.
        let to_carol = EventData::IssueReassigned(IssueReassigned {
            issue: issue_env.id.clone(),
            previous_assignment: issue_env.id.clone(),
            previous_target: bob.clone(),
            new_target: carol.clone(),
            reason: text("r1"),
        });
        let to_carol_env =
            Envelope::new(&alice, 2, no_frontier(), &to_carol, [issue_env.id.clone()]);
        apply_ok(&mut state, &to_carol_env);
        // Sole candidate so far: provisionally applied, so acknowledged
        // resets to false for the *new* assignment -- expected, not yet a
        // conflict.
        assert!(!state.issues[&issue_env.id].acknowledged());

        let to_dave = EventData::IssueReassigned(IssueReassigned {
            issue: issue_env.id.clone(),
            previous_assignment: issue_env.id.clone(),
            previous_target: bob.clone(),
            new_target: a("dave"),
            reason: text("r2"),
        });
        let to_dave_env =
            Envelope::new(&coord1, 1, no_frontier(), &to_dave, [issue_env.id.clone()]);
        apply_ok(&mut state, &to_dave_env);

        let issue = &state.issues[&issue_env.id];
        assert_eq!(issue.status, ItemStatus::LifecycleConflict);
        assert_eq!(issue.current_assignment, issue_env.id);
        assert!(
            issue.acknowledged(),
            "resetting back to the baseline assignment must recover its true acknowledged status"
        );
    }

    /// The dependency-side twin of
    /// `two_racing_issue_reassignments_converge_with_no_stale_chain_entry`
    /// -- `reset_dependency_to_conflict` had the identical incomplete-
    /// rollback gap as its issue counterpart.
    #[test]
    fn two_racing_dependency_reassignments_converge_with_no_stale_chain_entry() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let coord1 = a("coord1");

        let dep_data = EventData::DependencyRequested(DependencyRequested {
            target: bob.clone(),
            interface: short("x"),
            needed_by: text("soon"),
            blocking: false,
            summary: text("s"),
            evidence: StringSet::default(),
        });
        let dep_env = Envelope::new(&alice, 1, no_frontier(), &dep_data, []);

        let to_carol = EventData::DependencyReassigned(DependencyReassigned {
            dependency: dep_env.id.clone(),
            previous_assignment: dep_env.id.clone(),
            previous_target: bob.clone(),
            new_target: carol.clone(),
            reason: text("r1"),
        });
        let to_carol_env = Envelope::new(&alice, 2, no_frontier(), &to_carol, [dep_env.id.clone()]);
        let to_dave = EventData::DependencyReassigned(DependencyReassigned {
            dependency: dep_env.id.clone(),
            previous_assignment: dep_env.id.clone(),
            previous_target: bob.clone(),
            new_target: a("dave"),
            reason: text("r2"),
        });
        let to_dave_env = Envelope::new(&coord1, 1, no_frontier(), &to_dave, [dep_env.id.clone()]);

        let run = |order: &[&Envelope]| {
            let mut state = empty_state(&[
                ("alice", Role::Implementor),
                ("bob", Role::Implementor),
                ("carol", Role::Implementor),
                ("dave", Role::Implementor),
                ("coord1", Role::Coordinator),
            ]);
            apply_ok(&mut state, &register(&alice, Role::Implementor));
            apply_ok(&mut state, &register(&bob, Role::Implementor));
            apply_ok(&mut state, &register(&carol, Role::Implementor));
            apply_ok(&mut state, &register(&a("dave"), Role::Implementor));
            apply_ok(&mut state, &register(&coord1, Role::Coordinator));
            apply_ok(&mut state, &dep_env);
            for env in order {
                apply_ok(&mut state, env);
            }
            state
        };

        let forward = run(&[&to_carol_env, &to_dave_env]);
        let reverse = run(&[&to_dave_env, &to_carol_env]);
        for state in [&forward, &reverse] {
            let dep = &state.dependencies[&dep_env.id];
            assert_eq!(dep.status, ItemStatus::LifecycleConflict);
            assert_eq!(dep.current_assignment, dep_env.id);
            assert!(
                dep.reassignment_chain.is_empty(),
                "{:?}",
                dep.reassignment_chain
            );
            assert_eq!(dep.assignment_target.len(), 1);
        }
        assert_eq!(
            forward.dependencies[&dep_env.id].reassignment_chain,
            reverse.dependencies[&dep_env.id].reassignment_chain
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
        let reassign_env =
            Envelope::new(&alice, 2, no_frontier(), &reassign, [issue_env.id.clone()]);
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

        let engine_epoch = EventId::new(&a("coord1"), 0);
        state.merge_engine_info.insert(
            engine_epoch.clone(),
            (
                short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
                short(crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION),
            ),
        );
        state.current_merge_engine_epoch = Some(engine_epoch.clone());
        let epoch = state.roster_epoch.as_ref().unwrap().clone();

        let authorize_data = EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
            nomination: nominate_env.id.clone(),
            product_branch: request.product_branch.clone(),
            previous_main: hash(2),
            reviewed_commit: hash(3),
            candidate: hash(4),
            merge_engine_epoch: engine_epoch,
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
            complete_frontier(&epoch),
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
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
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

        let engine_epoch = EventId::new(&a("coord1"), 0);
        state.merge_engine_info.insert(
            engine_epoch.clone(),
            (
                short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
                short(crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION),
            ),
        );
        state.current_merge_engine_epoch = Some(engine_epoch.clone());

        let authorize_data = EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
            nomination: nominate_env.id.clone(),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            previous_main: hash(2),
            reviewed_commit: hash(3),
            candidate: hash(4),
            merge_engine_epoch: engine_epoch,
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
            complete_frontier(&epoch),
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
        let env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::FrictionReported(data),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("must cite supporting evidence"),
            "{err}"
        );
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
        assert!(err.to_string().contains("promoted_to must be set"), "{err}");
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
        let env = Envelope::new(
            &coord1,
            1,
            no_frontier(),
            &EventData::FrictionSynthesized(data),
            [],
        );
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

    /// A structurally-complete frontier (every active member named, at an
    /// arbitrary stream position) -- enough to satisfy `validate_complete`
    /// without needing a real git stream behind each entry, since `apply.rs`
    /// tests construct envelopes directly rather than through `stream.rs`.
    fn complete_frontier(epoch: &crate::registry::RosterEpoch) -> ObservedFrontier {
        let entries = epoch.active_members.keys().map(|agent| FrontierEntry {
            agent: agent.clone(),
            stream_tip: hash(1),
            through: EventId::new(agent, 0),
        });
        ObservedFrontier::complete(epoch, entries).unwrap()
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
        let epoch = state.roster_epoch.as_ref().unwrap().clone();

        let env = Envelope::new(
            &coord1,
            1,
            complete_frontier(&epoch),
            &EventData::BroadcastPublished(broadcast(
                epoch.id.clone(),
                crate::common::AudienceSelector::AllActive,
                &[&alice, &bob, &coord1],
                crate::common::AckRequirement::None,
            )),
            [],
        );
        apply_ok(&mut state, &env);
        assert!(state.broadcasts.contains_key(&env.id));
    }

    /// A sparse frontier claiming `AllActive` must be rejected outright,
    /// before the audience_snapshot comparison even runs -- gate 12's
    /// completeness requirement is about the frontier itself, not just
    /// whether the claimed snapshot happens to look right.
    #[test]
    fn broadcast_all_active_rejects_a_sparse_frontier() {
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
                &[&alice, &bob],
                crate::common::AckRequirement::None,
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("requires a complete frontier"),
            "{err}"
        );
    }

    #[test]
    fn broadcast_rejects_an_audience_snapshot_that_omits_an_active_member() {
        let mut state = empty_state(&[("alice", Role::Implementor), ("bob", Role::Implementor)]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();

        let env = Envelope::new(
            &alice,
            1,
            complete_frontier(&epoch),
            &EventData::BroadcastPublished(broadcast(
                epoch.id.clone(),
                crate::common::AudienceSelector::AllActive,
                &[&alice], // missing bob
                crate::common::AckRequirement::None,
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("does not match resolving"),
            "{err}"
        );
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
    fn broadcast_rejects_an_unknown_audience_epoch() {
        let mut state = empty_state(&[("alice", Role::Implementor)]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));

        let env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::BroadcastPublished(broadcast(
                hash(12345), // never a real epoch id in this state
                crate::common::AudienceSelector::AllActive,
                &[&alice],
                crate::common::AckRequirement::None,
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("is not a known roster epoch"),
            "{err}"
        );
    }

    #[test]
    fn broadcast_acknowledged_requires_required_acknowledgement() {
        let mut state = empty_state(&[("alice", Role::Implementor)]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();

        let broadcast_env = Envelope::new(
            &alice,
            1,
            complete_frontier(&epoch),
            &EventData::BroadcastPublished(broadcast(
                epoch.id.clone(),
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
        assert!(
            err.to_string().contains("does not require acknowledgement"),
            "{err}"
        );
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
        let epoch = state.roster_epoch.as_ref().unwrap().clone();

        let broadcast_env = Envelope::new(
            &alice,
            1,
            complete_frontier(&epoch),
            &EventData::BroadcastPublished(broadcast(
                epoch.id.clone(),
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
        let epoch = state.roster_epoch.as_ref().unwrap().clone();

        let broadcast_env = Envelope::new(
            &alice,
            1,
            complete_frontier(&epoch),
            &EventData::BroadcastPublished(broadcast(
                epoch.id.clone(),
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

    // ------------------------------------------------------------ handoffs

    fn handoff_offer(receiver: &Agent) -> HandoffOffered {
        HandoffOffered {
            receiver: receiver.clone(),
            scope: StringSet::default(),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            product_commit: hash(5),
            verification: vec![],
            known_issues: StringSet::default(),
            evidence: StringSet::default(),
            summary: text("done"),
        }
    }

    #[test]
    fn handoff_offer_then_accept_round_trips() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));

        let offer_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::HandoffOffered(handoff_offer(&bob)),
            [],
        );
        apply_ok(&mut state, &offer_env);
        assert_eq!(state.handoffs[&offer_env.id].status, ItemStatus::Open);

        let accept_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&offer_env.id]),
            &EventData::HandoffAccepted(HandoffAccepted {
                handoff: offer_env.id.clone(),
                note: text(""),
            }),
            [],
        );
        apply_ok(&mut state, &accept_env);
        assert_eq!(
            state.handoffs[&offer_env.id].status,
            ItemStatus::Terminal("accepted")
        );
    }

    #[test]
    fn handoff_decline_by_the_receiver_succeeds() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let offer_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::HandoffOffered(handoff_offer(&bob)),
            [],
        );
        apply_ok(&mut state, &offer_env);

        let decline_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&offer_env.id]),
            &EventData::HandoffDeclined(HandoffDeclined {
                handoff: offer_env.id.clone(),
                reason: text("not my area"),
            }),
            [],
        );
        apply_ok(&mut state, &decline_env);
        assert_eq!(
            state.handoffs[&offer_env.id].status,
            ItemStatus::Terminal("declined")
        );
    }

    #[test]
    fn handoff_withdraw_by_the_offerer_succeeds() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let offer_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::HandoffOffered(handoff_offer(&bob)),
            [],
        );
        apply_ok(&mut state, &offer_env);

        let withdraw_env = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&offer_env.id]),
            &EventData::HandoffWithdrawn(HandoffWithdrawn {
                handoff: offer_env.id.clone(),
                reason: text("plans changed"),
            }),
            [],
        );
        apply_ok(&mut state, &withdraw_env);
        assert_eq!(
            state.handoffs[&offer_env.id].status,
            ItemStatus::Terminal("withdrawn")
        );
    }

    #[test]
    fn rejects_a_handoff_offer_from_a_non_implementor() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Reviewer));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let offer_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::HandoffOffered(handoff_offer(&bob)),
            [],
        );
        let err = apply_event(&mut state, &offer_env).unwrap_err();
        assert!(err.to_string().contains("does not have role"), "{err}");
    }

    #[test]
    fn rejects_a_handoff_offer_to_an_unregistered_receiver() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let offer_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::HandoffOffered(handoff_offer(&a("bob"))),
            [],
        );
        let err = apply_event(&mut state, &offer_env).unwrap_err();
        assert!(err.to_string().contains("unregistered agent"), "{err}");
    }

    #[test]
    fn rejects_handoff_accept_by_a_non_receiver() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&carol, Role::Implementor));
        let offer_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::HandoffOffered(handoff_offer(&bob)),
            [],
        );
        apply_ok(&mut state, &offer_env);

        let accept_env = Envelope::new(
            &carol,
            1,
            frontier_seeing(&[&offer_env.id]),
            &EventData::HandoffAccepted(HandoffAccepted {
                handoff: offer_env.id.clone(),
                note: text(""),
            }),
            [],
        );
        let err = apply_event(&mut state, &accept_env).unwrap_err();
        assert!(
            err.to_string().contains("only the receiver may dispose"),
            "{err}"
        );
    }

    #[test]
    fn rejects_handoff_decline_by_a_non_receiver() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&carol, Role::Implementor));
        let offer_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::HandoffOffered(handoff_offer(&bob)),
            [],
        );
        apply_ok(&mut state, &offer_env);

        let decline_env = Envelope::new(
            &carol,
            1,
            frontier_seeing(&[&offer_env.id]),
            &EventData::HandoffDeclined(HandoffDeclined {
                handoff: offer_env.id.clone(),
                reason: text("not my problem"),
            }),
            [],
        );
        let err = apply_event(&mut state, &decline_env).unwrap_err();
        assert!(
            err.to_string().contains("only the receiver may dispose"),
            "{err}"
        );
    }

    #[test]
    fn rejects_handoff_withdraw_by_a_non_offerer() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let offer_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::HandoffOffered(handoff_offer(&bob)),
            [],
        );
        apply_ok(&mut state, &offer_env);

        // bob is the receiver, not the offerer.
        let withdraw_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&offer_env.id]),
            &EventData::HandoffWithdrawn(HandoffWithdrawn {
                handoff: offer_env.id.clone(),
                reason: text("r"),
            }),
            [],
        );
        let err = apply_event(&mut state, &withdraw_env).unwrap_err();
        assert!(
            err.to_string().contains("only the offerer may withdraw"),
            "{err}"
        );
    }

    /// Pins down the actual (non-`LifecycleConflict`) behavior for a second
    /// disposal attempt that causally observed the first: `apply_handoff_
    /// terminal` routes every disposal through the same `ExclusiveTracker`
    /// used for issue/dependency/review terminal transitions, and a
    /// candidate that observed an existing group member is hard-rejected
    /// outright by `ExclusiveTracker::record` -- it never gets the chance to
    /// become a second, genuinely concurrent candidate the way an
    /// unaware-of-each-other race would.
    #[test]
    fn rejects_disposing_of_an_already_terminal_handoff() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let offer_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::HandoffOffered(handoff_offer(&bob)),
            [],
        );
        apply_ok(&mut state, &offer_env);

        let accept_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&offer_env.id]),
            &EventData::HandoffAccepted(HandoffAccepted {
                handoff: offer_env.id.clone(),
                note: text(""),
            }),
            [],
        );
        apply_ok(&mut state, &accept_env);

        let decline_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&offer_env.id, &accept_env.id]),
            &EventData::HandoffDeclined(HandoffDeclined {
                handoff: offer_env.id.clone(),
                reason: text("changed my mind"),
            }),
            [],
        );
        let err = apply_event(&mut state, &decline_env).unwrap_err();
        assert!(
            err.to_string().contains("already causally observed"),
            "{err}"
        );
        assert_eq!(
            state.handoffs[&offer_env.id].status,
            ItemStatus::Terminal("accepted"),
            "the rejected second attempt must not disturb the confirmed disposition"
        );
    }

    /// Mirrors `review_decline_and_reassign_race_produces_a_lifecycle_
    /// conflict` for handoffs. Accept/decline are both only ever authored by
    /// the receiver, so those two can never race (one stream is always
    /// ordered relative to itself); withdraw (offerer) vs accept (receiver)
    /// is the one combination that can, since the two are different agents'
    /// mutually-unaware streams.
    #[test]
    fn handoff_accept_and_withdraw_race_produces_a_lifecycle_conflict() {
        let alice = a("alice");
        let bob = a("bob");
        let offer_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::HandoffOffered(handoff_offer(&bob)),
            [],
        );
        let accept_env = Envelope::new(
            &bob,
            1,
            no_frontier(),
            &EventData::HandoffAccepted(HandoffAccepted {
                handoff: offer_env.id.clone(),
                note: text(""),
            }),
            [],
        );
        let withdraw_env = Envelope::new(
            &alice,
            2,
            no_frontier(),
            &EventData::HandoffWithdrawn(HandoffWithdrawn {
                handoff: offer_env.id.clone(),
                reason: text("changed plans"),
            }),
            [],
        );

        let mut forward = empty_state(&[]);
        apply_ok(&mut forward, &register(&alice, Role::Implementor));
        apply_ok(&mut forward, &register(&bob, Role::Implementor));
        apply_ok(&mut forward, &offer_env);
        apply_ok(&mut forward, &accept_env);
        apply_ok(&mut forward, &withdraw_env);

        let mut reverse = empty_state(&[]);
        apply_ok(&mut reverse, &register(&alice, Role::Implementor));
        apply_ok(&mut reverse, &register(&bob, Role::Implementor));
        apply_ok(&mut reverse, &offer_env);
        apply_ok(&mut reverse, &withdraw_env);
        apply_ok(&mut reverse, &accept_env);

        for (label, state) in [("forward", &forward), ("reverse", &reverse)] {
            assert_eq!(
                state.handoffs[&offer_env.id].status,
                ItemStatus::LifecycleConflict,
                "{label} order"
            );
            assert!(
                state.exclusive.is_contested(&accept_env.id),
                "{label} order"
            );
            assert!(
                state.exclusive.is_contested(&withdraw_env.id),
                "{label} order"
            );
        }
    }

    // ------------------------------------------------------- schema/merge engine

    /// Regression test for a bug caught in adversarial review: an earlier
    /// version of `require_complete_frontier` validated a complete frontier
    /// against `state.roster_epoch` -- whatever epoch happens to be current
    /// *right now* -- instead of looking up the frontier's own claimed epoch
    /// in `state.known_epochs`. Since `sync::reduce_local` always re-reduces
    /// every event against the latest registry tip, that meant a single
    /// later registry transition (another agent registering, retiring, or a
    /// coordinator succession) would permanently break reduction of every
    /// earlier authority event still naming the older epoch -- a
    /// fleet-wide, unrecoverable DoS, directly contradicting AGENT_BUS.md
    /// gate 5's "a later registration does not invalidate it". This proves
    /// the fixed behavior: an event whose frontier names an epoch that is
    /// still present in `known_epochs` remains valid even after the roster
    /// has since moved on to a strictly later epoch.
    #[test]
    fn require_complete_frontier_validates_against_the_frontiers_own_epoch_not_the_current_one() {
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let old_epoch = state.roster_epoch.as_ref().unwrap().clone();

        // Simulate a later registry transition that advances the current
        // epoch without retiring coord1 -- e.g. a new agent registering.
        let mut new_members = old_epoch.active_members.clone();
        new_members.insert(
            a("dave"),
            MemberBinding {
                role: Role::Implementor,
                host: short("host1"),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        let new_epoch = old_epoch.child(hash(1000), new_members);
        state
            .known_epochs
            .insert(new_epoch.id.clone(), new_epoch.clone());
        state.roster_epoch = Some(new_epoch);

        // An event whose frontier still names the OLDER epoch must remain
        // valid: it is checked against the epoch it actually names, not
        // against whatever epoch is current at reduction time.
        let env = Envelope::new(
            &coord1,
            1,
            complete_frontier(&old_epoch),
            &EventData::SchemaActivated(SchemaActivated {
                version: 2,
                design_commit: hash(1),
                helper_commit: hash(2),
            }),
            [],
        );
        apply_ok(&mut state, &env);
        assert_eq!(state.activated_schema_version, 2);
    }

    #[test]
    fn schema_activated_requires_a_strictly_increasing_version() {
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();

        let activate = |version: u32| {
            EventData::SchemaActivated(SchemaActivated {
                version,
                design_commit: hash(1),
                helper_commit: hash(2),
            })
        };
        let first_env = Envelope::new(&coord1, 1, complete_frontier(&epoch), &activate(2), []);
        apply_ok(&mut state, &first_env);
        assert_eq!(state.activated_schema_version, 2);

        let same_version_env =
            Envelope::new(&coord1, 2, complete_frontier(&epoch), &activate(2), []);
        let err = apply_event(&mut state, &same_version_env).unwrap_err();
        assert!(err.to_string().contains("is not greater than"), "{err}");

        let lower_version_env =
            Envelope::new(&coord1, 2, complete_frontier(&epoch), &activate(1), []);
        let err = apply_event(&mut state, &lower_version_env).unwrap_err();
        assert!(err.to_string().contains("is not greater than"), "{err}");
    }

    #[test]
    fn rejects_schema_activated_by_a_non_coordinator() {
        let mut state = empty_state(&[("alice", Role::Implementor)]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::SchemaActivated(SchemaActivated {
                version: 2,
                design_commit: hash(1),
                helper_commit: hash(2),
            }),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("is not a coordinator"), "{err}");
    }

    /// `apply_merge_engine_activated` requires `previous_epoch` to already
    /// be a known prior activation -- there is no implicit genesis, so tests
    /// that need one seed `state.merge_engine_info` directly, standing in
    /// for whatever earlier migration/bootstrap event would have recorded
    /// the real genesis epoch.
    fn seed_merge_engine_genesis(state: &mut BusState) -> EventId {
        let genesis = EventId::new(&a("coord1"), 0);
        state.merge_engine_info.insert(
            genesis.clone(),
            (
                short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
                short(crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION),
            ),
        );
        genesis
    }

    fn merge_engine_activated(previous_epoch: &EventId) -> MergeEngineActivated {
        MergeEngineActivated {
            previous_epoch: previous_epoch.clone(),
            merge_engine: short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
            merge_engine_version: short(crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION),
            design_commit: hash(1),
            helper_commit: hash(2),
        }
    }

    #[test]
    fn merge_engine_activated_happy_path_advances_the_current_epoch() {
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let genesis = seed_merge_engine_genesis(&mut state);

        let env = Envelope::new(
            &coord1,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(merge_engine_activated(&genesis)),
            [],
        );
        apply_ok(&mut state, &env);
        assert_eq!(state.current_merge_engine_epoch, Some(env.id.clone()));
        assert!(state.merge_engine_info.contains_key(&env.id));
    }

    #[test]
    fn rejects_merge_engine_activated_with_an_unknown_previous_epoch() {
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let env = Envelope::new(
            &coord1,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(merge_engine_activated(&EventId::new(&coord1, 0))),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("is not a known prior engine activation"),
            "{err}"
        );
    }

    #[test]
    fn rejects_merge_engine_activated_by_a_non_coordinator() {
        let mut state = empty_state(&[("alice", Role::Implementor)]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let genesis = seed_merge_engine_genesis(&mut state);
        let env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::MergeEngineActivated(merge_engine_activated(&genesis)),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("is not a coordinator"), "{err}");
    }

    #[test]
    fn rejects_merge_engine_activated_with_an_unsupported_engine() {
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let genesis = seed_merge_engine_genesis(&mut state);
        let mut data = merge_engine_activated(&genesis);
        data.merge_engine = short("some-other-engine");
        let env = Envelope::new(
            &coord1,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(data),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("unsupported merge_engine"),
            "{err}"
        );
    }

    /// The version half of the pinned merge engine, checked independently
    /// of the engine name (found by a design-fidelity review: only the
    /// name was validated, never the version).
    #[test]
    fn rejects_merge_engine_activated_with_an_unsupported_version() {
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let genesis = seed_merge_engine_genesis(&mut state);
        let mut data = merge_engine_activated(&genesis);
        data.merge_engine_version = short("0.0.1");
        let env = Envelope::new(
            &coord1,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(data),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("unsupported merge_engine_version"),
            "{err}"
        );
    }

    #[test]
    fn rejects_merge_engine_activated_when_previous_epoch_is_itself_contested() {
        let mut state =
            empty_state(&[("coord1", Role::Coordinator), ("coord2", Role::Coordinator)]);
        let coord1 = a("coord1");
        let coord2 = a("coord2");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        apply_ok(&mut state, &register(&coord2, Role::Coordinator));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let genesis = seed_merge_engine_genesis(&mut state);

        // Two genuinely concurrent activations both built off `genesis`,
        // from different coordinators, neither observing the other.
        let candidate_a = Envelope::new(
            &coord1,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(merge_engine_activated(&genesis)),
            [],
        );
        let candidate_b = Envelope::new(
            &coord2,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(merge_engine_activated(&genesis)),
            [],
        );
        apply_ok(&mut state, &candidate_a);
        apply_ok(&mut state, &candidate_b);
        assert!(state.exclusive.is_contested(&candidate_a.id));

        let downstream = Envelope::new(
            &coord1,
            2,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(merge_engine_activated(&candidate_a.id)),
            [],
        );
        let err = apply_event(&mut state, &downstream).unwrap_err();
        assert!(
            err.to_string()
                .contains("is itself part of an unresolved lifecycle conflict"),
            "{err}"
        );
    }

    /// A second, genuinely concurrent `merge_engine.activated` candidate
    /// must reset `current_merge_engine_epoch` back to the shared pre-race
    /// baseline (`previous_epoch`), not leave it stuck at whichever
    /// candidate happened to be recorded first -- the same "provisional
    /// apply, then reset on conflict" rule issue/dependency reassignment
    /// races already follow. Both candidates end up contested, and the
    /// group's convergence must not depend on which one was applied first
    /// (gates 15/16).
    #[test]
    fn merge_engine_race_resets_current_epoch_to_the_pre_race_baseline() {
        let mut state =
            empty_state(&[("coord1", Role::Coordinator), ("coord2", Role::Coordinator)]);
        let coord1 = a("coord1");
        let coord2 = a("coord2");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        apply_ok(&mut state, &register(&coord2, Role::Coordinator));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let genesis = seed_merge_engine_genesis(&mut state);

        let candidate_a = Envelope::new(
            &coord1,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(merge_engine_activated(&genesis)),
            [],
        );
        apply_ok(&mut state, &candidate_a);
        assert_eq!(
            state.current_merge_engine_epoch,
            Some(candidate_a.id.clone())
        );

        let candidate_b = Envelope::new(
            &coord2,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(merge_engine_activated(&genesis)),
            [],
        );
        apply_ok(&mut state, &candidate_b);
        assert!(state.exclusive.is_contested(&candidate_a.id));
        assert!(state.exclusive.is_contested(&candidate_b.id));
        assert_eq!(state.current_merge_engine_epoch, Some(genesis));
    }

    /// The reverse-order twin: the same final state regardless of which
    /// candidate was recorded first.
    #[test]
    fn merge_engine_race_converges_regardless_of_order() {
        let run = |first: &Agent, second: &Agent| {
            let mut state =
                empty_state(&[("coord1", Role::Coordinator), ("coord2", Role::Coordinator)]);
            apply_ok(&mut state, &register(&a("coord1"), Role::Coordinator));
            apply_ok(&mut state, &register(&a("coord2"), Role::Coordinator));
            let epoch = state.roster_epoch.as_ref().unwrap().clone();
            let genesis = seed_merge_engine_genesis(&mut state);
            apply_ok(
                &mut state,
                &Envelope::new(
                    first,
                    1,
                    complete_frontier(&epoch),
                    &EventData::MergeEngineActivated(merge_engine_activated(&genesis)),
                    [],
                ),
            );
            apply_ok(
                &mut state,
                &Envelope::new(
                    second,
                    1,
                    complete_frontier(&epoch),
                    &EventData::MergeEngineActivated(merge_engine_activated(&genesis)),
                    [],
                ),
            );
            state.current_merge_engine_epoch
        };
        let forward = run(&a("coord1"), &a("coord2"));
        let reverse = run(&a("coord2"), &a("coord1"));
        assert_eq!(forward, reverse);
    }

    // ------------------------------------------------ dependency lifecycle

    fn dependency_request(target: &Agent) -> DependencyRequested {
        DependencyRequested {
            target: target.clone(),
            interface: short("x"),
            needed_by: text("soon"),
            blocking: false,
            summary: text("s"),
            evidence: StringSet::default(),
        }
    }

    #[test]
    fn rejects_a_dependency_request_naming_an_unregistered_target() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::DependencyRequested(dependency_request(&a("bob"))),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("unregistered agent"), "{err}");
    }

    #[test]
    fn dependency_ack_then_resolve_round_trips() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));

        let dep_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::DependencyRequested(dependency_request(&bob)),
            [],
        );
        apply_ok(&mut state, &dep_env);

        let ack_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&dep_env.id]),
            &EventData::DependencyAcknowledged(DependencyAcknowledged {
                dependency: dep_env.id.clone(),
                assignment: dep_env.id.clone(),
                note: text(""),
            }),
            [],
        );
        apply_ok(&mut state, &ack_env);
        assert!(state.dependencies[&dep_env.id].acknowledged());

        let resolve_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&dep_env.id]),
            &EventData::DependencyResolved(DependencyResolved {
                dependency: dep_env.id.clone(),
                assignment: dep_env.id.clone(),
                summary: text("done"),
                product_commit: None,
                verification: vec![],
            }),
            [],
        );
        apply_ok(&mut state, &resolve_env);
        assert_eq!(
            state.dependencies[&dep_env.id].status,
            ItemStatus::Terminal("resolved")
        );
    }

    #[test]
    fn dependency_reject_marks_it_terminal() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let dep_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::DependencyRequested(dependency_request(&bob)),
            [],
        );
        apply_ok(&mut state, &dep_env);

        let reject_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&dep_env.id]),
            &EventData::DependencyRejected(DependencyRejected {
                dependency: dep_env.id.clone(),
                assignment: dep_env.id.clone(),
                reason: text("not needed"),
            }),
            [],
        );
        apply_ok(&mut state, &reject_env);
        assert_eq!(
            state.dependencies[&dep_env.id].status,
            ItemStatus::Terminal("rejected")
        );
    }

    #[test]
    fn rejects_dependency_ack_by_a_non_target() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&carol, Role::Implementor));
        let dep_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::DependencyRequested(dependency_request(&bob)),
            [],
        );
        apply_ok(&mut state, &dep_env);

        let ack_env = Envelope::new(
            &carol,
            1,
            frontier_seeing(&[&dep_env.id]),
            &EventData::DependencyAcknowledged(DependencyAcknowledged {
                dependency: dep_env.id.clone(),
                assignment: dep_env.id.clone(),
                note: text(""),
            }),
            [],
        );
        let err = apply_event(&mut state, &ack_env).unwrap_err();
        assert!(
            err.to_string()
                .contains("only that assignment's target may acknowledge this dependency"),
            "{err}"
        );
    }

    #[test]
    fn rejects_dependency_ack_referencing_an_unknown_assignment() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let dep_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::DependencyRequested(dependency_request(&bob)),
            [],
        );
        apply_ok(&mut state, &dep_env);

        let bogus_assignment = EventId::new(&alice, 99);
        let ack_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&dep_env.id]),
            &EventData::DependencyAcknowledged(DependencyAcknowledged {
                dependency: dep_env.id.clone(),
                assignment: bogus_assignment,
                note: text(""),
            }),
            [],
        );
        let err = apply_event(&mut state, &ack_env).unwrap_err();
        assert!(err.to_string().contains("unknown assignment"), "{err}");
    }

    #[test]
    fn rejects_a_double_dependency_acknowledgement() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let dep_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::DependencyRequested(dependency_request(&bob)),
            [],
        );
        apply_ok(&mut state, &dep_env);

        let ack_data = || {
            EventData::DependencyAcknowledged(DependencyAcknowledged {
                dependency: dep_env.id.clone(),
                assignment: dep_env.id.clone(),
                note: text(""),
            })
        };
        let ack_env = Envelope::new(&bob, 1, frontier_seeing(&[&dep_env.id]), &ack_data(), []);
        apply_ok(&mut state, &ack_env);

        let second_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&dep_env.id, &ack_env.id]),
            &ack_data(),
            [],
        );
        let err = apply_event(&mut state, &second_env).unwrap_err();
        assert!(
            err.to_string().contains("dependency already acknowledged"),
            "{err}"
        );
    }

    #[test]
    fn rejects_dependency_ack_against_a_superseded_assignment() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Implementor),
            ("carol", Role::Implementor),
        ]);
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&carol, Role::Implementor));
        let dep_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::DependencyRequested(dependency_request(&bob)),
            [],
        );
        apply_ok(&mut state, &dep_env);

        let reassign_env = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&dep_env.id]),
            &EventData::DependencyReassigned(DependencyReassigned {
                dependency: dep_env.id.clone(),
                previous_assignment: dep_env.id.clone(),
                previous_target: bob.clone(),
                new_target: carol.clone(),
                reason: text("bob is busy"),
            }),
            [],
        );
        apply_ok(&mut state, &reassign_env);

        // bob still tries to acknowledge the now-superseded original
        // assignment rather than the reassignment's new one.
        let ack_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&dep_env.id]),
            &EventData::DependencyAcknowledged(DependencyAcknowledged {
                dependency: dep_env.id.clone(),
                assignment: dep_env.id.clone(),
                note: text(""),
            }),
            [],
        );
        let err = apply_event(&mut state, &ack_env).unwrap_err();
        assert!(
            err.to_string()
                .contains("is not the dependency's current assignment"),
            "{err}"
        );
    }

    #[test]
    fn rejects_dependency_reassignment_with_a_mismatched_previous_target() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&carol, Role::Implementor));
        let dep_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::DependencyRequested(dependency_request(&bob)),
            [],
        );
        apply_ok(&mut state, &dep_env);

        let reassign_env = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&dep_env.id]),
            &EventData::DependencyReassigned(DependencyReassigned {
                dependency: dep_env.id.clone(),
                previous_assignment: dep_env.id.clone(),
                previous_target: carol.clone(), // actual target is bob
                new_target: carol.clone(),
                reason: text("r"),
            }),
            [],
        );
        let err = apply_event(&mut state, &reassign_env).unwrap_err();
        assert!(
            err.to_string()
                .contains("does not match assignment's actual target"),
            "{err}"
        );
    }

    #[test]
    fn rejects_dependency_reassignment_by_neither_requester_nor_coordinator() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&carol, Role::Implementor));
        let dep_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::DependencyRequested(dependency_request(&bob)),
            [],
        );
        apply_ok(&mut state, &dep_env);

        // carol is neither the requester (alice) nor a coordinator.
        let reassign_env = Envelope::new(
            &carol,
            1,
            frontier_seeing(&[&dep_env.id]),
            &EventData::DependencyReassigned(DependencyReassigned {
                dependency: dep_env.id.clone(),
                previous_assignment: dep_env.id.clone(),
                previous_target: bob.clone(),
                new_target: carol.clone(),
                reason: text("r"),
            }),
            [],
        );
        let err = apply_event(&mut state, &reassign_env).unwrap_err();
        assert!(err.to_string().contains("is not a coordinator"), "{err}");
    }

    #[test]
    fn rejects_dependency_reassignment_of_an_unknown_dependency() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let bogus = EventId::new(&alice, 99);
        let reassign_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::DependencyReassigned(DependencyReassigned {
                dependency: bogus.clone(),
                previous_assignment: bogus,
                previous_target: alice.clone(),
                new_target: alice.clone(),
                reason: text("r"),
            }),
            [],
        );
        let err = apply_event(&mut state, &reassign_env).unwrap_err();
        assert!(err.to_string().contains("unknown dependency"), "{err}");
    }

    // ------------------------------------------------- review merge authorization

    fn review_request(authors: &[&Agent], reviewer: &Agent) -> ReviewRequest {
        ReviewRequest {
            authors: StringSet::from_iter(authors.iter().map(|a| (*a).clone())),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewer: reviewer.clone(),
            required_checks: vec![],
            review_scope: StringSet::default(),
            summary: text("s"),
            target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
        }
    }

    /// Nominates (from `author` at `author_seq`) and accepts (from
    /// `reviewer` at `reviewer_seq`), returning both envelopes. Shared setup
    /// for the merge-authorization/merged/reconciled/finding-disposition
    /// tests below, all of which need an accepted chain before they can
    /// exercise their own specific rejection branch.
    /// The merge-engine epoch id `merge_authorized()` defaults to. Seeded
    /// as the current selection by `nominate_and_accept` (below) so every
    /// existing merge-authorization test's baseline stays valid without
    /// each one separately wiring up `apply_merge_engine_activated` --
    /// `apply_review_merge_authorized` now requires `merge_engine_epoch` to
    /// equal `state.current_merge_engine_epoch` exactly.
    fn default_merge_engine_epoch() -> EventId {
        EventId::new(&a("coord1"), 0)
    }

    fn nominate_and_accept(
        state: &mut BusState,
        author: &Agent,
        author_seq: u64,
        reviewer: &Agent,
        reviewer_seq: u64,
    ) -> (Envelope, Envelope) {
        let engine_epoch = default_merge_engine_epoch();
        state
            .merge_engine_info
            .entry(engine_epoch.clone())
            .or_insert_with(|| {
                (
                    short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
                    short(crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION),
                )
            });
        state.current_merge_engine_epoch.get_or_insert(engine_epoch);

        let request = review_request(&[author], reviewer);
        let nominate_env = Envelope::new(
            author,
            author_seq,
            no_frontier(),
            &EventData::ReviewNominated(request),
            [],
        );
        apply_ok(state, &nominate_env);
        let accept_env = Envelope::new(
            reviewer,
            reviewer_seq,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: nominate_env.id.clone(),
                note: text(""),
            }),
            [],
        );
        apply_ok(state, &accept_env);
        (nominate_env, accept_env)
    }

    fn merge_authorized(
        nomination: &EventId,
        reviewed_scope: StringSet<crate::scalars::PathClaim>,
        required_checks: &[Text],
    ) -> ReviewMergeAuthorized {
        ReviewMergeAuthorized {
            nomination: nomination.clone(),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            previous_main: hash(2),
            reviewed_commit: hash(3),
            candidate: hash(4),
            merge_engine_epoch: default_merge_engine_epoch(),
            checks: required_checks
                .iter()
                .map(|c| crate::common::CheckResult {
                    command: c.clone(),
                    result: crate::common::CheckOutcome::Passed,
                    evidence: None,
                })
                .collect(),
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope,
            limitations: vec![],
            summary: text("s"),
        }
    }

    #[test]
    fn review_merge_authorized_rejects_an_unknown_nomination() {
        let mut state = empty_state(&[]);
        let bob = a("bob");
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let bogus = EventId::new(&a("alice"), 1);
        let env = Envelope::new(
            &bob,
            1,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(merge_authorized(&bogus, StringSet::default(), &[])),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("unknown nomination"), "{err}");
    }

    #[test]
    fn review_merge_authorized_rejects_authorization_by_a_non_reviewer() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        let env = Envelope::new(
            &alice,
            2,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(merge_authorized(
                &nominate_env.id,
                StringSet::default(),
                &[],
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("only the accepting reviewer may authorize a merge"),
            "{err}"
        );
    }

    #[test]
    fn review_merge_authorized_rejects_a_reviewed_scope_mismatch() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        let claim = crate::scalars::PathClaim::parse("src/**".into()).unwrap();
        let authorize = merge_authorized(&nominate_env.id, StringSet::from_iter([claim]), &[]);
        let env = Envelope::new(
            &bob,
            2,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(authorize),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("reviewed_scope must equal the nomination's review_scope exactly"),
            "{err}"
        );
    }

    #[test]
    fn review_merge_authorized_rejects_a_stale_nomination_after_reassignment() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&carol, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        let request = review_request(&[&alice], &bob);
        let reassign_env = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewReassigned(ReviewReassigned {
                authors: request.authors.clone(),
                product_branch: request.product_branch.clone(),
                reviewer: carol.clone(),
                required_checks: request.required_checks.clone(),
                review_scope: request.review_scope.clone(),
                summary: request.summary.clone(),
                target_branch: request.target_branch.clone(),
                evidence: request.evidence.clone(),
                replaces: nominate_env.id.clone(),
                reason: text("bob is out"),
                inherited_findings: vec![],
            }),
            [],
        );
        apply_ok(&mut state, &reassign_env);

        let env = Envelope::new(
            &bob,
            2,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(merge_authorized(
                &nominate_env.id,
                StringSet::default(),
                &[],
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("is not the current nomination in its chain"),
            "{err}"
        );
    }

    fn finding(id: &str) -> crate::common::Finding {
        crate::common::Finding {
            id: short(id),
            priority: Priority::Normal,
            locations: vec![],
            rationale: text("r"),
            closure_conditions: text("c"),
        }
    }

    #[test]
    fn review_merge_authorized_rejects_an_open_finding() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        let changes_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewChangesRequested(ReviewChangesRequested {
                nomination: nominate_env.id.clone(),
                reviewed_commit: hash(3),
                findings: vec![finding("f1")],
                evidence: StringSet::default(),
            }),
            [],
        );
        apply_ok(&mut state, &changes_env);

        let env = Envelope::new(
            &bob,
            3,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(merge_authorized(
                &nominate_env.id,
                StringSet::default(),
                &[],
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("lacks a terminal disposition"),
            "{err}"
        );
    }

    /// AGENT_BUS_SCHEMA.md section 10: "Only unresolved issues whose
    /// `blocks` set names an event in the active nomination chain block
    /// authorization."
    #[test]
    fn review_merge_authorized_rejects_when_an_open_issue_blocks_the_nomination_chain() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        let issue_data = EventData::IssueOpened(IssueOpened {
            target: alice.clone(),
            issue_kind: IssueKind::Bug,
            severity: Priority::Critical,
            summary: text("blocking bug"),
            code_commit: None,
            locations: vec![],
            expected: None,
            observed_behavior: None,
            reproduction: vec![],
            blocks: StringSet::from_iter([nominate_env.id.clone()]),
            evidence: StringSet::default(),
        });
        let issue_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &issue_data,
            [nominate_env.id.clone()],
        );
        apply_ok(&mut state, &issue_env);

        let env = Envelope::new(
            &bob,
            3,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(merge_authorized(
                &nominate_env.id,
                StringSet::default(),
                &[],
            )),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("blocks authorization"), "{err}");
    }

    /// The companion positive case: once the blocking issue is resolved
    /// (Terminal), authorization proceeds normally -- disposition is what
    /// matters, not the mere existence of a `blocks` reference.
    #[test]
    fn review_merge_authorized_succeeds_once_the_blocking_issue_is_resolved() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        let issue_data = EventData::IssueOpened(IssueOpened {
            target: alice.clone(),
            issue_kind: IssueKind::Bug,
            severity: Priority::Critical,
            summary: text("blocking bug"),
            code_commit: None,
            locations: vec![],
            expected: None,
            observed_behavior: None,
            reproduction: vec![],
            blocks: StringSet::from_iter([nominate_env.id.clone()]),
            evidence: StringSet::default(),
        });
        let issue_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &issue_data,
            [nominate_env.id.clone()],
        );
        apply_ok(&mut state, &issue_env);

        let resolve_env = Envelope::new(
            &alice,
            2,
            no_frontier(),
            &EventData::IssueResolved(IssueResolved {
                issue: issue_env.id.clone(),
                assignment: issue_env.id.clone(),
                summary: text("fixed"),
                fix_commit: None,
                verification: vec![],
            }),
            [],
        );
        apply_ok(&mut state, &resolve_env);

        let env = Envelope::new(
            &bob,
            3,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(merge_authorized(
                &nominate_env.id,
                StringSet::default(),
                &[],
            )),
            [],
        );
        apply_ok(&mut state, &env);
        assert_eq!(
            state.review_chain(&nominate_env.id).unwrap().authorizations,
            vec![env.id]
        );
    }

    /// `ReviewMergeAuthorized.merge_engine_epoch` must equal the currently
    /// selected engine epoch (AGENT_BUS_SCHEMA.md: "the selected engine
    /// epoch visible in the authorization's observed state") -- a stale or
    /// fabricated epoch id must be refused, not accepted just as readily as
    /// the real current one.
    #[test]
    fn review_merge_authorized_rejects_a_stale_or_unknown_merge_engine_epoch() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        let mut authorize = merge_authorized(&nominate_env.id, StringSet::default(), &[]);
        // `nominate_and_accept` seeded `default_merge_engine_epoch()` as the
        // current selection; this names something else entirely.
        authorize.merge_engine_epoch = EventId::new(&a("nobody"), 7);
        let env = Envelope::new(
            &bob,
            2,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(authorize),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("is not the currently selected merge engine epoch"),
            "{err}"
        );
    }

    // ------------------------------------------------- review merged / reconciled

    #[test]
    fn review_merged_rejects_an_authorization_of_the_wrong_kind() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        // Points at the nomination event itself -- a real, known event, but
        // of kind review.nominated, not review.merge_authorized.
        let merged_data = EventData::ReviewMerged(ReviewMerged {
            authorization: nominate_env.id.clone(),
            previous_main: hash(2),
            main_commit: hash(4),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewed_commit: hash(3),
            summary: text("merged"),
        });
        let env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &merged_data,
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("is not a review.merge_authorized event"),
            "{err}"
        );
    }

    #[test]
    fn review_merged_rejects_emission_by_a_non_authorizing_reviewer() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let authorize = merge_authorized(&nominate_env.id, StringSet::default(), &[]);
        let authorize_env = Envelope::new(
            &bob,
            2,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(authorize.clone()),
            [],
        );
        apply_ok(&mut state, &authorize_env);

        let merged_data = EventData::ReviewMerged(ReviewMerged {
            authorization: authorize_env.id.clone(),
            previous_main: authorize.previous_main,
            main_commit: authorize.candidate,
            product_branch: authorize.product_branch.clone(),
            reviewed_commit: authorize.reviewed_commit,
            summary: text("merged"),
        });
        let env = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&authorize_env.id]),
            &merged_data,
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("only the authorizing reviewer may emit review.merged"),
            "{err}"
        );
    }

    #[test]
    fn review_merged_rejects_a_main_commit_that_does_not_match_the_candidate() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let authorize = merge_authorized(&nominate_env.id, StringSet::default(), &[]);
        let authorize_env = Envelope::new(
            &bob,
            2,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(authorize.clone()),
            [],
        );
        apply_ok(&mut state, &authorize_env);

        let merged_data = EventData::ReviewMerged(ReviewMerged {
            authorization: authorize_env.id.clone(),
            previous_main: authorize.previous_main,
            main_commit: hash(999), // does not match authorize.candidate
            product_branch: authorize.product_branch.clone(),
            reviewed_commit: authorize.reviewed_commit,
            summary: text("merged"),
        });
        let env = Envelope::new(
            &bob,
            3,
            frontier_seeing(&[&authorize_env.id]),
            &merged_data,
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("main_commit must equal the candidate"),
            "{err}"
        );
    }

    #[test]
    fn review_merge_reconciled_rejects_a_non_coordinator() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let authorize = merge_authorized(&nominate_env.id, StringSet::default(), &[]);
        let authorize_env = Envelope::new(
            &bob,
            2,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(authorize.clone()),
            [],
        );
        apply_ok(&mut state, &authorize_env);

        let reconciled_data = EventData::ReviewMergeReconciled(ReviewMergeReconciled {
            authorization: authorize_env.id.clone(),
            previous_main: authorize.previous_main,
            main_commit: authorize.candidate,
            product_branch: authorize.product_branch.clone(),
            reviewed_commit: authorize.reviewed_commit,
            reason: text("r"),
            user_authority: text("coord1"),
        });
        // alice is an author, not a coordinator.
        let env = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&authorize_env.id]),
            &reconciled_data,
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("is not a coordinator"), "{err}");
    }

    #[test]
    fn review_merge_reconciled_rejects_an_unknown_authorization() {
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let bogus = EventId::new(&a("bob"), 1);
        let reconciled_data = EventData::ReviewMergeReconciled(ReviewMergeReconciled {
            authorization: bogus,
            previous_main: hash(2),
            main_commit: hash(4),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewed_commit: hash(3),
            reason: text("r"),
            user_authority: text("coord1"),
        });
        let env = Envelope::new(&coord1, 1, no_frontier(), &reconciled_data, []);
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(err.to_string().contains("unknown authorization"), "{err}");
    }

    #[test]
    fn review_merge_reconciled_rejects_an_authorization_of_the_wrong_kind() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Reviewer),
            ("coord1", Role::Coordinator),
        ]);
        let alice = a("alice");
        let bob = a("bob");
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        let reconciled_data = EventData::ReviewMergeReconciled(ReviewMergeReconciled {
            authorization: nominate_env.id.clone(),
            previous_main: hash(2),
            main_commit: hash(4),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewed_commit: hash(3),
            reason: text("r"),
            user_authority: text("coord1"),
        });
        let env = Envelope::new(
            &coord1,
            1,
            frontier_seeing(&[&nominate_env.id]),
            &reconciled_data,
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("is not a review.merge_authorized event"),
            "{err}"
        );
    }

    #[test]
    fn review_merge_reconciled_rejects_a_value_mismatch() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Reviewer),
            ("coord1", Role::Coordinator),
        ]);
        let alice = a("alice");
        let bob = a("bob");
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let authorize = merge_authorized(&nominate_env.id, StringSet::default(), &[]);
        let authorize_env = Envelope::new(
            &bob,
            2,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(authorize.clone()),
            [],
        );
        apply_ok(&mut state, &authorize_env);

        let reconciled_data = EventData::ReviewMergeReconciled(ReviewMergeReconciled {
            authorization: authorize_env.id.clone(),
            previous_main: hash(999), // mismatch
            main_commit: authorize.candidate,
            product_branch: authorize.product_branch.clone(),
            reviewed_commit: authorize.reviewed_commit,
            reason: text("r"),
            user_authority: text("coord1"),
        });
        let env = Envelope::new(
            &coord1,
            1,
            frontier_seeing(&[&authorize_env.id]),
            &reconciled_data,
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("main_commit must equal the candidate"),
            "{err}"
        );
    }

    #[test]
    fn review_merge_reconciled_rejects_a_second_receipt() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Reviewer),
            ("coord1", Role::Coordinator),
        ]);
        let alice = a("alice");
        let bob = a("bob");
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let authorize = merge_authorized(&nominate_env.id, StringSet::default(), &[]);
        let authorize_env = Envelope::new(
            &bob,
            2,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(authorize.clone()),
            [],
        );
        apply_ok(&mut state, &authorize_env);

        let reconciled_data = || {
            EventData::ReviewMergeReconciled(ReviewMergeReconciled {
                authorization: authorize_env.id.clone(),
                previous_main: authorize.previous_main.clone(),
                main_commit: authorize.candidate.clone(),
                product_branch: authorize.product_branch.clone(),
                reviewed_commit: authorize.reviewed_commit.clone(),
                reason: text("r"),
                user_authority: text("coord1"),
            })
        };
        let first_env = Envelope::new(
            &coord1,
            1,
            frontier_seeing(&[&authorize_env.id]),
            &reconciled_data(),
            [],
        );
        apply_ok(&mut state, &first_env);

        let second_env = Envelope::new(
            &coord1,
            2,
            frontier_seeing(&[&authorize_env.id, &first_env.id]),
            &reconciled_data(),
            [],
        );
        let err = apply_event(&mut state, &second_env).unwrap_err();
        assert!(
            err.to_string()
                .contains("a merged or reconciled receipt already exists"),
            "{err}"
        );
    }

    // ------------------------------------------------------ finding disposition

    #[test]
    fn finding_superseded_records_the_rationale() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let changes_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewChangesRequested(ReviewChangesRequested {
                nomination: nominate_env.id.clone(),
                reviewed_commit: hash(3),
                findings: vec![finding("f1")],
                evidence: StringSet::default(),
            }),
            [],
        );
        apply_ok(&mut state, &changes_env);

        let superseded_env = Envelope::new(
            &bob,
            3,
            frontier_seeing(&[&nominate_env.id, &changes_env.id]),
            &EventData::ReviewFindingsSuperseded(ReviewFindingsSuperseded {
                nomination: nominate_env.id.clone(),
                changes_event: changes_env.id.clone(),
                finding_id: short("f1"),
                rationale: text("no longer applicable"),
            }),
            [],
        );
        apply_ok(&mut state, &superseded_env);

        let chain = state.review_chain(&nominate_env.id).unwrap();
        let key = (changes_env.id.clone(), "f1".to_string());
        match &chain.findings[&key].disposition {
            FindingDisposition::Superseded {
                by_event,
                rationale,
            } => {
                assert_eq!(by_event, &superseded_env.id);
                assert_eq!(rationale.as_str(), "no longer applicable");
            }
            other => panic!("expected Superseded, got {other:?}"),
        }
    }

    #[test]
    fn rejects_finding_disposal_by_a_non_reviewer() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let changes_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewChangesRequested(ReviewChangesRequested {
                nomination: nominate_env.id.clone(),
                reviewed_commit: hash(3),
                findings: vec![finding("f1")],
                evidence: StringSet::default(),
            }),
            [],
        );
        apply_ok(&mut state, &changes_env);

        let cleared_env = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&nominate_env.id, &changes_env.id]),
            &EventData::ReviewFindingsCleared(ReviewFindingsCleared {
                nomination: nominate_env.id.clone(),
                changes_event: changes_env.id.clone(),
                finding_id: short("f1"),
                resolved_commit: hash(4),
                summary: text("fixed"),
            }),
            [],
        );
        let err = apply_event(&mut state, &cleared_env).unwrap_err();
        assert!(
            err.to_string()
                .contains("only the accepting reviewer for the current nomination may dispose"),
            "{err}"
        );
    }

    #[test]
    fn rejects_disposal_of_an_unknown_finding() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let changes_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewChangesRequested(ReviewChangesRequested {
                nomination: nominate_env.id.clone(),
                reviewed_commit: hash(3),
                findings: vec![finding("f1")],
                evidence: StringSet::default(),
            }),
            [],
        );
        apply_ok(&mut state, &changes_env);

        let cleared_env = Envelope::new(
            &bob,
            3,
            frontier_seeing(&[&nominate_env.id, &changes_env.id]),
            &EventData::ReviewFindingsCleared(ReviewFindingsCleared {
                nomination: nominate_env.id.clone(),
                changes_event: changes_env.id.clone(),
                finding_id: short("does-not-exist"),
                resolved_commit: hash(4),
                summary: text("fixed"),
            }),
            [],
        );
        let err = apply_event(&mut state, &cleared_env).unwrap_err();
        assert!(err.to_string().contains("unknown finding"), "{err}");
    }

    #[test]
    fn rejects_finding_disposal_against_a_stale_nomination() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&carol, Role::Reviewer));
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let changes_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewChangesRequested(ReviewChangesRequested {
                nomination: nominate_env.id.clone(),
                reviewed_commit: hash(3),
                findings: vec![finding("f1")],
                evidence: StringSet::default(),
            }),
            [],
        );
        apply_ok(&mut state, &changes_env);

        let request = review_request(&[&alice], &bob);
        let reassign_env = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&nominate_env.id, &changes_env.id]),
            &EventData::ReviewReassigned(ReviewReassigned {
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
                inherited_findings: vec![crate::common::FindingRef {
                    changes_event: changes_env.id.clone(),
                    finding_id: short("f1"),
                }],
            }),
            [],
        );
        apply_ok(&mut state, &reassign_env);

        // bob (the superseded reviewer) still tries to clear the finding
        // under the now-stale nomination id.
        let cleared_env = Envelope::new(
            &bob,
            3,
            frontier_seeing(&[&nominate_env.id, &changes_env.id]),
            &EventData::ReviewFindingsCleared(ReviewFindingsCleared {
                nomination: nominate_env.id.clone(),
                changes_event: changes_env.id.clone(),
                finding_id: short("f1"),
                resolved_commit: hash(4),
                summary: text("fixed"),
            }),
            [],
        );
        let err = apply_event(&mut state, &cleared_env).unwrap_err();
        assert!(
            err.to_string()
                .contains("is not the current nomination in its chain"),
            "{err}"
        );
    }

    /// Design-fidelity note: unlike issue/dependency/handoff/review terminal
    /// dispositions, `apply_finding_disposition` never touches `state.
    /// exclusive` at all -- a second disposal attempt of an
    /// already-dispositioned finding is hard-rejected outright ("finding is
    /// not open"), never routed through a `LifecycleConflict` the way a
    /// genuinely concurrent race on any other exclusive-transition set in
    /// this file would be. (True concurrency isn't even structurally
    /// possible here today, since disposal authority is pinned to a single
    /// agent -- the current nomination's accepting reviewer -- so this test
    /// exercises the simpler, always-reachable case: a second, already
    /// causally-ordered attempt by that same reviewer.) This pins down that
    /// actual behavior as a baseline for any future fix to diff against; it
    /// is not a statement that the current behavior is correct.
    #[test]
    fn a_second_disposal_of_an_already_cleared_finding_is_hard_rejected_not_a_lifecycle_conflict() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let changes_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewChangesRequested(ReviewChangesRequested {
                nomination: nominate_env.id.clone(),
                reviewed_commit: hash(3),
                findings: vec![finding("f1")],
                evidence: StringSet::default(),
            }),
            [],
        );
        apply_ok(&mut state, &changes_env);

        let cleared_data = || {
            EventData::ReviewFindingsCleared(ReviewFindingsCleared {
                nomination: nominate_env.id.clone(),
                changes_event: changes_env.id.clone(),
                finding_id: short("f1"),
                resolved_commit: hash(4),
                summary: text("fixed"),
            })
        };
        let first_env = Envelope::new(
            &bob,
            3,
            frontier_seeing(&[&nominate_env.id, &changes_env.id]),
            &cleared_data(),
            [],
        );
        apply_ok(&mut state, &first_env);

        let second_env = Envelope::new(
            &bob,
            4,
            frontier_seeing(&[&nominate_env.id, &changes_env.id, &first_env.id]),
            &cleared_data(),
            [],
        );
        let err = apply_event(&mut state, &second_env).unwrap_err();
        assert!(err.to_string().contains("finding is not open"), "{err}");
        assert!(
            !state.exclusive.is_contested(&first_env.id),
            "no exclusive-tracker bookkeeping is created for findings at all"
        );
    }
}
