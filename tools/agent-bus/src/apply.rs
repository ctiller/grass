//! Semantic validation + state reduction: replays a [`history::Walk`] into a
//! [`BusState`], enforcing AGENT_BUS_SCHEMA.md's per-kind rules and
//! AGENT_BUS.md section 10's cross-kind lifecycle laws. Git/product-repo
//! cross-checks (candidate tags, merge-authorship trailers, `main` history)
//! are deliberately NOT done here; see `commands/review.rs` and
//! `commands/audit.rs`, which run against real git state after a pure replay.

use crate::common::FindingDispositionKind;
use crate::error::{invalid, AbResult};
use crate::events::*;
use crate::history::{Walk, WalkedCommit};
use crate::scalars::{Agent, EventId};
use crate::state::*;
use std::collections::BTreeMap;

pub fn replay(walk: &Walk) -> AbResult<BusState> {
    let mut state = BusState::new(walk.bus_json.clone());
    for commit in &walk.commits {
        apply_commit(&mut state, commit)?;
    }
    Ok(state)
}

/// Apply additional already-walked commits onto an existing state (used for
/// `validate --incremental`).
pub fn replay_onto(mut state: BusState, commits: &[WalkedCommit]) -> AbResult<BusState> {
    for commit in commits {
        apply_commit(&mut state, commit)?;
    }
    Ok(state)
}

/// Dry-run one not-yet-published event against `state` (a clone is mutated
/// and discarded), so mutation commands can refuse to publish an event that
/// bus-log replay would reject. `commit_idx` need not correspond to a real
/// commit since the mutated clone is thrown away; it only has to be greater
/// than every index already recorded in `state.commit_index_of`.
pub fn dry_run(state: &BusState, env: &crate::envelope::Envelope) -> AbResult<()> {
    let mut trial = state.clone();
    let commit_idx = trial.commit_index_of.values().copied().max().unwrap_or(0) + 1;
    apply_event(&mut trial, env, commit_idx, false)
}

fn apply_commit(state: &mut BusState, commit: &WalkedCommit) -> AbResult<()> {
    if commit.is_repair {
        // Structural content validation of repair commits happens in
        // `commands::validate`; replay simply does not treat them as events.
        state.commit_index_of.insert(commit.commit.clone(), commit.index);
        return Ok(());
    }
    state.commit_index_of.insert(commit.commit.clone(), commit.index);
    for env in &commit.new_events {
        apply_event(state, env, commit.index, commit.is_bootstrap_root)?;
        state
            .commit_index_of_event
            .insert(env.id.clone(), commit.index);
        state.events.insert(env.id.clone(), env.clone());
        if let Some(ag) = state.agents.get_mut(&env.agent) {
            ag.next_seq = ag.next_seq.max(env.seq + 1);
        }
    }
    Ok(())
}

fn observed_index(state: &BusState, env: &crate::envelope::Envelope) -> AbResult<Option<usize>> {
    match &env.observed {
        None => Ok(None),
        Some(oid) => match state.commit_index_of.get(oid.as_str()) {
            Some(i) => Ok(Some(*i)),
            None => Err(invalid(format!(
                "{}: observed commit {} is not part of known bus history",
                env.id, oid
            ))),
        },
    }
}

fn check_refs_visible(state: &BusState, env: &crate::envelope::Envelope, observed_idx: Option<usize>) -> AbResult<()> {
    for r in env.refs.iter() {
        if r.agent() == env.agent && r.seq() < env.seq {
            continue; // same-agent earlier contiguous local event
        }
        let idx = state.commit_index_of_event.get(r).copied();
        match (idx, observed_idx) {
            (Some(i), Some(o)) if i <= o => {}
            _ => {
                return Err(invalid(format!(
                    "{}: reference {r} is not visible from its observed state",
                    env.id
                )))
            }
        }
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
        return Err(invalid(format!("{a} is not named in BUS.json coordinators")));
    }
    require_active_role(state, a, Role::Coordinator)?;
    Ok(())
}

/// True if `id` is itself a member of some *other* exclusive-transition
/// group that is still an unresolved race (2+ transitions, no
/// `lifecycle.conflict_resolved` winner yet, and `id` isn't that winner).
/// Referential facts (e.g. "this reassignment id names this target") stay
/// eagerly recorded regardless of Apply/Concurrent outcome so a named party
/// can act on their own not-yet-confirmed transition — but a *new* exclusive
/// transition that would chain authoritative "current" state off of `id`
/// must not be allowed to confirm itself while `id`'s own foundation is
/// still contested, or the new transition could become "current" purely by
/// virtue of nothing else happening to contest *it*, even though the
/// predecessor it was built on never actually won its own race.
fn predecessor_is_contested(state: &BusState, id: &EventId) -> bool {
    state.exclusive.values().any(|t| {
        t.transitions.len() > 1 && t.transitions.iter().any(|(member, _)| member == id) && t.resolved.as_ref() != Some(id)
    })
}

/// Outcome of feeding one event into an exclusive-transition predecessor
/// group (AGENT_BUS.md section 10). Only two outcomes reach call sites — a
/// causally-later claim on an already-settled predecessor is rejected
/// directly by `record_exclusive` below, so callers never need a third arm.
enum Exclusivity {
    /// First transition for this predecessor: apply its effect now, so later
    /// events in the same walk can build on it (an ordinary reassign-then-act
    /// sequence is the overwhelmingly common case, not the exception).
    Apply,
    /// Genuinely concurrent with an existing transition (neither observed the
    /// other): record but do not apply this transition's effect, and reset
    /// whatever the earlier (optimistically-applied) transition's effect
    /// changed back to a neutral "contested" state, since it turns out not to
    /// have been uncontested after all. `lifecycle.conflict_resolved` is what
    /// later picks a real winner and applies its effect for good.
    Concurrent,
}

fn record_exclusive(
    state: &mut BusState,
    key: String,
    this_event: &EventId,
    this_commit_idx: usize,
    observed_idx: Option<usize>,
) -> AbResult<Exclusivity> {
    let tracker = state.exclusive.entry(key).or_default();
    if tracker.resolved.is_some() {
        return Err(invalid(format!(
            "{this_event}: predecessor already has a coordinator-resolved disposition"
        )));
    }
    if tracker.transitions.is_empty() {
        tracker.transitions.push((this_event.clone(), this_commit_idx));
        return Ok(Exclusivity::Apply);
    }
    // Did this event causally observe any existing transition?
    let observed_any = tracker
        .transitions
        .iter()
        .any(|(_, idx)| observed_idx.map(|o| *idx <= o).unwrap_or(false));
    if observed_any {
        let prev = tracker.transitions[0].0.clone();
        return Err(invalid(format!(
            "{this_event}: predecessor already causally observed a disposition ({prev})"
        )));
    }
    tracker.transitions.push((this_event.clone(), this_commit_idx));
    Ok(Exclusivity::Concurrent)
}

fn apply_event(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    commit_idx: usize,
    is_bootstrap_root: bool,
) -> AbResult<()> {
    let observed_idx = observed_index(state, env)?;
    check_refs_visible(state, env, observed_idx)?;
    let data = env.typed_data()?;

    if env.seq == 0 {
        if !matches!(data, EventData::AgentRegistered(_)) {
            return Err(invalid(format!("{}: sequence zero must be agent.registered", env.id)));
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
        EventData::AgentRegistered(d) => apply_registered(state, env, d, is_bootstrap_root)?,
        EventData::AgentStatus(d) => apply_status(state, env, d)?,
        EventData::AgentResumed(d) => apply_resumed(state, env, d)?,
        EventData::AgentRetired(d) => apply_retired(state, env, d)?,
        EventData::SchemaActivated(d) => apply_schema_activated(state, env, d)?,
        EventData::MergeEngineActivated(d) => apply_merge_engine_activated(state, env, commit_idx, d)?,
        EventData::ScopeSet(d) => apply_scope_set(state, env, d)?,
        EventData::PlanSet(d) => apply_plan_set(state, env, d)?,
        EventData::ProgressReported(d) => apply_progress(state, env, d)?,
        EventData::IssueOpened(d) => apply_issue_opened(state, env, d)?,
        EventData::IssueAcknowledged(d) => apply_issue_ack(state, env, d)?,
        EventData::IssueResolved(d) => {
            apply_issue_terminal(state, env, &data, commit_idx, &d.issue, &d.assignment, "resolved")?
        }
        EventData::IssueRejected(d) => {
            apply_issue_terminal(state, env, &data, commit_idx, &d.issue, &d.assignment, "rejected")?
        }
        EventData::IssueReassigned(d) => apply_issue_reassigned(state, env, commit_idx, d)?,
        EventData::DependencyRequested(d) => apply_dependency_requested(state, env, d)?,
        EventData::DependencyAcknowledged(d) => apply_dependency_ack(state, env, d)?,
        EventData::DependencyResolved(d) => {
            apply_dependency_terminal(state, env, &data, commit_idx, &d.dependency, &d.assignment, "resolved")?
        }
        EventData::DependencyRejected(d) => {
            apply_dependency_terminal(state, env, &data, commit_idx, &d.dependency, &d.assignment, "rejected")?
        }
        EventData::DependencyReassigned(d) => apply_dependency_reassigned(state, env, commit_idx, d)?,
        EventData::HandoffOffered(d) => apply_handoff_offered(state, env, d)?,
        EventData::HandoffAccepted(d) => apply_handoff_terminal(state, env, commit_idx, &d.handoff, "accepted")?,
        EventData::HandoffDeclined(d) => apply_handoff_terminal(state, env, commit_idx, &d.handoff, "declined")?,
        EventData::HandoffWithdrawn(d) => apply_handoff_terminal(state, env, commit_idx, &d.handoff, "withdrawn")?,
        EventData::ReviewNominated(d) => apply_review_nominated(state, env, d)?,
        EventData::ReviewNominationAccepted(d) => apply_review_accept(state, env, d)?,
        EventData::ReviewNominationDeclined(d) => {
            apply_review_closing(state, env, commit_idx, &d.nomination, "declined")?
        }
        EventData::ReviewChangesRequested(d) => apply_review_changes(state, env, d)?,
        EventData::ReviewFindingsCleared(d) => {
            apply_finding_disposition(state, env, &data, commit_idx, &d.nomination, &d.changes_event, &d.finding_id)?
        }
        EventData::ReviewFindingsSuperseded(d) => {
            apply_finding_disposition(state, env, &data, commit_idx, &d.nomination, &d.changes_event, &d.finding_id)?
        }
        EventData::ReviewReassigned(d) => apply_review_reassigned(state, env, commit_idx, d)?,
        EventData::ReviewWithdrawn(d) => {
            apply_review_closing(state, env, commit_idx, &d.nomination, "withdrawn")?
        }
        EventData::ReviewMergeAuthorized(d) => apply_review_authorized(state, env, d)?,
        EventData::ReviewMerged(d) => apply_review_merged(state, env, d)?,
        EventData::ReviewMergeReconciled(d) => apply_review_reconciled(state, env, d)?,
        EventData::LifecycleConflictResolved(d) => apply_conflict_resolved(state, env, d)?,
    }

    state.kind_of_event_insert(env.id.clone(), data.kind());
    Ok(())
}

// ------------------------------------------------------------------ lifecycle

fn apply_registered(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    d: &AgentRegistered,
    is_bootstrap_root: bool,
) -> AbResult<()> {
    if env.seq != 0 {
        return Err(invalid(format!("{}: agent.registered must be sequence zero", env.id)));
    }
    if state.agents.contains_key(&env.agent) {
        return Err(invalid(format!("{} is already registered", env.agent)));
    }
    if crate::scalars::Agent::is_reserved(env.agent.as_str()) {
        return Err(invalid(format!("{} begins with reserved prefix _", env.agent)));
    }
    if d.primary_role == Role::Coordinator {
        if !state.is_bootstrap_coordinator(&env.agent) {
            return Err(invalid(format!(
                "{} registers as coordinator but is not named in BUS.json",
                env.agent
            )));
        }
        if env.observed.is_some() {
            return Err(invalid(format!(
                "{}: coordinator registration must have observed: null",
                env.id
            )));
        }
    } else if env.observed.is_none() {
        return Err(invalid(format!(
            "{}: only bootstrap coordinator registrations may have observed: null",
            env.id
        )));
    }
    if !is_bootstrap_root && d.primary_role == Role::Coordinator {
        return Err(invalid(format!(
            "{}: coordinator registrations occur only in the bootstrap root commit",
            env.id
        )));
    }
    if (d.product_base.is_some() || d.product_branch.is_some()) && d.primary_role != Role::Implementor {
        return Err(invalid(format!(
            "{}: product_base/product_branch are permitted only for implementor",
            env.id
        )));
    }
    if let Some(b) = &d.product_branch {
        if !b.is_product_branch_for(&env.agent) {
            return Err(invalid(format!(
                "{}: product_branch must match refs/heads/agent/{}/<topic>",
                env.id, env.agent
            )));
        }
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
            status_note: crate::scalars::Text::parse(String::new()).unwrap(),
            product_branch: d.product_branch.clone(),
            product_commit: None,
            last_lifecycle_event: env.id.clone(),
            retired: false,
            scope: None,
            plan: None,
            progress_tail: Vec::new(),
            next_seq: 1,
            registered_commit_index: 0,
        },
    );
    Ok(())
}

fn apply_status(state: &mut BusState, env: &crate::envelope::Envelope, d: &AgentStatusEvent) -> AbResult<()> {
    let role = require_agent(state, &env.agent)?.primary_role;
    if (d.product_branch.is_some() || d.product_commit.is_some()) && role != Role::Implementor {
        return Err(invalid(format!(
            "{}: product fields are permitted only for implementor",
            env.id
        )));
    }
    if let Some(b) = &d.product_branch {
        if !b.is_product_branch_for(&env.agent) {
            return Err(invalid(format!(
                "{}: product_branch must match refs/heads/agent/{}/<topic>",
                env.id, env.agent
            )));
        }
    }
    let ag = state.agents.get_mut(&env.agent).unwrap();
    ag.status = d.status;
    ag.status_note = d.note.clone();
    if let Some(b) = &d.product_branch {
        ag.product_branch = Some(b.clone());
    }
    if let Some(c) = &d.product_commit {
        ag.product_commit = Some(c.clone());
    }
    ag.last_lifecycle_event = env.id.clone();
    Ok(())
}

fn apply_resumed(state: &mut BusState, env: &crate::envelope::Envelope, d: &AgentResumed) -> AbResult<()> {
    // AGENT_BUS_SCHEMA.md section 4: "The referenced event is either the same
    // identity's latest own lifecycle event of any status or the latest
    // `agent.retired` targeting it." `AgentState::last_lifecycle_event` is
    // kept as exactly that union: it is updated both by the identity's own
    // lifecycle events and by a coordinator's `agent.retired` targeting it
    // (see `apply_retired`), so a single equality check covers both cases.
    let ag = require_agent(state, &env.agent)?;
    if d.previous_lifecycle != ag.last_lifecycle_event {
        return Err(invalid(format!(
            "{}: previous_lifecycle must be {}'s latest lifecycle event (own or a coordinator retirement targeting it)",
            env.id, env.agent
        )));
    }
    let ag = state.agents.get_mut(&env.agent).unwrap();
    ag.status = LifecycleStatus::Active;
    ag.retired = false;
    ag.last_lifecycle_event = env.id.clone();
    Ok(())
}

fn apply_retired(state: &mut BusState, env: &crate::envelope::Envelope, d: &AgentRetired) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    if d.target == env.agent {
        return Err(invalid(format!("{}: coordinator cannot retire itself", env.id)));
    }
    let target = require_agent(state, &d.target)?;
    if d.previous_lifecycle != target.last_lifecycle_event {
        return Err(invalid(format!(
            "{}: previous_lifecycle must be {}'s latest lifecycle event",
            env.id, d.target
        )));
    }
    let target = state.agents.get_mut(&d.target).unwrap();
    target.retired = true;
    target.last_lifecycle_event = env.id.clone();
    Ok(())
}

fn apply_schema_activated(state: &mut BusState, env: &crate::envelope::Envelope, d: &SchemaActivated) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    if d.version <= state.activated_schema_version {
        return Err(invalid(format!(
            "{}: version {} is not greater than the last activated version {}",
            env.id, d.version, state.activated_schema_version
        )));
    }
    state.activated_schema_version = d.version;
    Ok(())
}

/// `merge_engine.activated` (AGENT_BUS_SCHEMA.md section 4). `previous_epoch`
/// plays the same "predecessor" role as an issue/dependency assignment or a
/// review nomination: concurrent activations naming the same predecessor are
/// each valid and reduce to a lifecycle conflict (AGENT_BUS_SCHEMA.md
/// section 10) rather than one hard-failing the other, so authority here is
/// checked against the claimed predecessor rather than "the" current epoch.
fn apply_merge_engine_activated(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    commit_idx: usize,
    d: &MergeEngineActivated,
) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    if !state.merge_engine_info.contains_key(&d.previous_epoch) {
        return Err(invalid(format!(
            "{}: previous_epoch {} is not a known bootstrap registration or prior engine activation",
            env.id, d.previous_epoch
        )));
    }
    if predecessor_is_contested(state, &d.previous_epoch) {
        return Err(invalid(format!(
            "{}: previous_epoch {} is itself part of an unresolved lifecycle conflict",
            env.id, d.previous_epoch
        )));
    }
    if d.merge_engine.as_str() != crate::bootstrap::SUPPORTED_MERGE_ENGINE {
        return Err(invalid(format!("{}: unsupported merge_engine {}", env.id, d.merge_engine)));
    }
    let idx = observed_index(state, env)?;
    let outcome = record_exclusive(state, format!("engine_epoch:{}", d.previous_epoch), &env.id, commit_idx, idx)?;
    match outcome {
        Exclusivity::Apply => apply_merge_engine_activated_effect(state, &env.id, &EventData::MergeEngineActivated(d.clone())),
        Exclusivity::Concurrent => {
            // Neither racer becomes the selected epoch (AGENT_BUS_SCHEMA.md
            // section 4: "no candidate may use either until a coordinator
            // selects one"); reverting the pointer to the pre-race epoch is
            // sufficient since there is no separate "status" field here.
            state.current_merge_engine_epoch = d.previous_epoch.clone();
        }
    }
    Ok(())
}

fn apply_merge_engine_activated_effect(state: &mut BusState, event_id: &EventId, data: &EventData) {
    let d = match data {
        EventData::MergeEngineActivated(d) => d,
        _ => return,
    };
    state
        .merge_engine_info
        .insert(event_id.clone(), (d.merge_engine.clone(), d.merge_engine_version.clone()));
    state.current_merge_engine_epoch = event_id.clone();
}

// ------------------------------------------------------------ scope/plan/progress

fn apply_scope_set(state: &mut BusState, env: &crate::envelope::Envelope, d: &ScopeSet) -> AbResult<()> {
    require_active_role(state, &env.agent, Role::Implementor)?;
    let mut seen: Vec<(Agent, crate::scalars::Short)> = Vec::new();
    for dep in &d.depends_on {
        seen.push((dep.agent.clone(), dep.interface.clone()));
    }
    let mut sorted = seen.clone();
    sorted.sort_by(|a, b| (a.0.as_str(), a.1.as_str()).cmp(&(b.0.as_str(), b.1.as_str())));
    if sorted != seen {
        return Err(invalid(format!("{}: depends_on is not sorted by (agent, interface)", env.id)));
    }
    for w in sorted.windows(2) {
        if w[0] == w[1] {
            return Err(invalid(format!("{}: duplicate depends_on pair", env.id)));
        }
    }
    let ag = state.agents.get_mut(&env.agent).unwrap();
    ag.scope = Some(d.clone());
    Ok(())
}

fn apply_plan_set(state: &mut BusState, env: &crate::envelope::Envelope, d: &PlanSet) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    let mut ids = std::collections::BTreeSet::new();
    let mut active_count = 0;
    for step in &d.steps {
        if !ids.insert(step.id.as_str().to_string()) {
            return Err(invalid(format!("{}: duplicate plan step id {}", env.id, step.id)));
        }
        if step.state == crate::common::PlanStepState::Active {
            active_count += 1;
        }
    }
    if active_count > 1 {
        return Err(invalid(format!("{}: at most one plan step may be active", env.id)));
    }
    let ag = state.agents.get_mut(&env.agent).unwrap();
    ag.plan = Some(d.clone());
    Ok(())
}

fn apply_progress(state: &mut BusState, env: &crate::envelope::Envelope, d: &ProgressReported) -> AbResult<()> {
    let role = require_agent(state, &env.agent)?.primary_role;
    if d.product_commit.is_some() && role != Role::Implementor {
        return Err(invalid(format!(
            "{}: product_commit is permitted only for implementor",
            env.id
        )));
    }
    let ag = state.agents.get_mut(&env.agent).unwrap();
    ag.progress_tail.push(d.clone());
    if ag.progress_tail.len() > 20 {
        ag.progress_tail.remove(0);
    }
    Ok(())
}

// ------------------------------------------------------------------- issues

fn apply_issue_opened(state: &mut BusState, env: &crate::envelope::Envelope, d: &IssueOpened) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    require_agent(state, &d.target)?;
    for b in d.blocks.iter() {
        match state.kind_of_event(b) {
            Some(k) if k == "review.nominated" || k == "review.reassigned" => {}
            _ => {
                return Err(invalid(format!(
                    "{}: blocks member {b} is not a review.nominated/reassigned event",
                    env.id
                )))
            }
        }
    }
    let mut assignment_target = BTreeMap::new();
    assignment_target.insert(env.id.clone(), d.target.clone());
    state.issues.insert(
        env.id.clone(),
        IssueState {
            id: env.id.clone(),
            opener: env.agent.clone(),
            data: d.clone(),
            current_target: d.target.clone(),
            current_assignment: env.id.clone(),
            assignment_target,
            acknowledged: false,
            status: ItemStatus::Open,
            resolution_summary: None,
            reassignment_chain: Vec::new(),
        },
    );
    Ok(())
}

fn apply_issue_ack(state: &mut BusState, env: &crate::envelope::Envelope, d: &IssueAcknowledged) -> AbResult<()> {
    let issue = state
        .issues
        .get(&d.issue)
        .ok_or_else(|| invalid(format!("{}: unknown issue {}", env.id, d.issue)))?;
    let expected_target = issue
        .assignment_target
        .get(&d.assignment)
        .ok_or_else(|| invalid(format!("{}: unknown assignment {}", env.id, d.assignment)))?;
    if expected_target != &env.agent {
        return Err(invalid(format!("{}: only that assignment's target may acknowledge", env.id)));
    }
    if issue.acknowledged {
        return Err(invalid(format!("{}: issue already acknowledged", env.id)));
    }
    state.issues.get_mut(&d.issue).unwrap().acknowledged = true;
    Ok(())
}

/// `issue.resolved`/`issue.rejected`/`issue.reassigned` are the exclusive
/// "resolve/reject/reassign from one assignment" trio (AGENT_BUS.md section
/// 10). Authority and the exclusivity key are both derived from the
/// assignment id *named by the event*, not from whatever the issue's overall
/// `current_assignment` happens to be by the time this replays — otherwise
/// whichever of two genuinely concurrent transitions lands second in commit
/// order would hard-fail instead of correctly reducing to a lifecycle
/// conflict.
fn apply_issue_terminal(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    data: &EventData,
    commit_idx: usize,
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
        return Err(invalid(format!("{}: only that assignment's target may dispose of this issue", env.id)));
    }
    if predecessor_is_contested(state, assignment) {
        return Err(invalid(format!(
            "{}: assignment {} is itself part of an unresolved lifecycle conflict",
            env.id, assignment
        )));
    }
    let idx = observed_index(state, env)?;
    let outcome = record_exclusive(state, issue_key(assignment), &env.id, commit_idx, idx)?;
    let issue_id = issue_id.clone();
    match outcome {
        Exclusivity::Apply => apply_issue_terminal_effect(state, data, label),
        Exclusivity::Concurrent => reset_issue_to_conflict(state, &issue_id, assignment),
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

/// Resets an issue's derived "current" state to neutral the moment a
/// predecessor turns out to be genuinely contested: whichever transition
/// happened to be walked first may have optimistically set `status`/
/// `current_target`/`current_assignment`, and none of those are correct until
/// `lifecycle.conflict_resolved` picks a real winner. `predecessor` (the
/// shared assignment id every racer names) always has an `assignment_target`
/// entry already, since it was recorded before this exclusivity group could
/// exist.
fn reset_issue_to_conflict(state: &mut BusState, issue_id: &EventId, predecessor: &EventId) {
    if let Some(issue) = state.issues.get_mut(issue_id) {
        if let Some(target) = issue.assignment_target.get(predecessor).cloned() {
            issue.current_assignment = predecessor.clone();
            issue.current_target = target;
        }
        issue.status = ItemStatus::LifecycleConflict;
        issue.resolution_summary = None;
    }
}

fn apply_issue_reassigned(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    commit_idx: usize,
    d: &IssueReassigned,
) -> AbResult<()> {
    let issue = state
        .issues
        .get(&d.issue)
        .ok_or_else(|| invalid(format!("{}: unknown issue {}", env.id, d.issue)))?;
    let expected_target = issue
        .assignment_target
        .get(&d.previous_assignment)
        .ok_or_else(|| invalid(format!("{}: unknown assignment {}", env.id, d.previous_assignment)))?;
    if expected_target != &d.previous_target {
        return Err(invalid(format!("{}: previous_target does not match that assignment's target", env.id)));
    }
    if predecessor_is_contested(state, &d.previous_assignment) {
        return Err(invalid(format!(
            "{}: previous_assignment {} is itself part of an unresolved lifecycle conflict",
            env.id, d.previous_assignment
        )));
    }
    if !(env.agent == issue.opener || state.is_bootstrap_coordinator(&env.agent)) {
        return Err(invalid(format!(
            "{}: only the opener or a bootstrap coordinator may reassign",
            env.id
        )));
    }
    require_agent(state, &d.new_target)?;
    let idx = observed_index(state, env)?;
    let outcome = record_exclusive(state, issue_key(&d.previous_assignment), &env.id, commit_idx, idx)?;
    let this_event_id = env.id.clone();
    let issue_id = d.issue.clone();
    let previous_assignment = d.previous_assignment.clone();
    // The new assignment id is always registered (so its named target can act
    // on it, e.g. acknowledge or resolve) regardless of whether this specific
    // reassignment turns out to be the issue's confirmed winner.
    if let Some(issue) = state.issues.get_mut(&issue_id) {
        issue.assignment_target.insert(this_event_id.clone(), d.new_target.clone());
    }
    match outcome {
        Exclusivity::Apply => {
            apply_issue_reassigned_effect(state, &this_event_id, &EventData::IssueReassigned(d.clone()))
        }
        Exclusivity::Concurrent => reset_issue_to_conflict(state, &issue_id, &previous_assignment),
    }
    Ok(())
}

fn apply_issue_reassigned_effect(state: &mut BusState, event_id: &EventId, data: &EventData) {
    let d = match data {
        EventData::IssueReassigned(d) => d,
        _ => return,
    };
    if let Some(issue) = state.issues.get_mut(&d.issue) {
        issue.current_target = d.new_target.clone();
        issue.current_assignment = event_id.clone();
        issue.assignment_target.insert(event_id.clone(), d.new_target.clone());
        issue.reassignment_chain.push(event_id.clone());
        // A confirmed reassignment (whether uncontested or the winner of a
        // resolved conflict) leaves the issue open and actionable again, not
        // stuck showing a stale `LifecycleConflict` marker from a race it
        // just won.
        issue.status = ItemStatus::Open;
    }
}

// -------------------------------------------------------------- dependencies

fn apply_dependency_requested(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    d: &DependencyRequested,
) -> AbResult<()> {
    require_agent(state, &env.agent)?;
    require_agent(state, &d.target)?;
    let mut assignment_target = BTreeMap::new();
    assignment_target.insert(env.id.clone(), d.target.clone());
    state.dependencies.insert(
        env.id.clone(),
        DependencyState {
            id: env.id.clone(),
            requester: env.agent.clone(),
            data: d.clone(),
            current_target: d.target.clone(),
            current_assignment: env.id.clone(),
            assignment_target,
            acknowledged: false,
            status: ItemStatus::Open,
            reassignment_chain: Vec::new(),
        },
    );
    Ok(())
}

fn apply_dependency_ack(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
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
        return Err(invalid(format!("{}: only that assignment's target may acknowledge", env.id)));
    }
    state.dependencies.get_mut(&d.dependency).unwrap().acknowledged = true;
    Ok(())
}

/// See `apply_issue_terminal`'s doc comment: same "key/authority off the
/// named assignment, not the current one" fix applies here.
fn apply_dependency_terminal(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    data: &EventData,
    commit_idx: usize,
    dep_id: &EventId,
    assignment: &EventId,
    label: &'static str,
) -> AbResult<()> {
    let dep = state
        .dependencies
        .get(dep_id)
        .ok_or_else(|| invalid(format!("{}: unknown dependency {dep_id}", env.id)))?;
    let expected_target = dep
        .assignment_target
        .get(assignment)
        .ok_or_else(|| invalid(format!("{}: unknown assignment {assignment}", env.id)))?;
    if expected_target != &env.agent {
        return Err(invalid(format!("{}: only that assignment's target may dispose of this dependency", env.id)));
    }
    if predecessor_is_contested(state, assignment) {
        return Err(invalid(format!(
            "{}: assignment {} is itself part of an unresolved lifecycle conflict",
            env.id, assignment
        )));
    }
    let idx = observed_index(state, env)?;
    let outcome = record_exclusive(state, dependency_key(assignment), &env.id, commit_idx, idx)?;
    let dep_id = dep_id.clone();
    match outcome {
        Exclusivity::Apply => apply_dependency_terminal_effect(state, data, label),
        Exclusivity::Concurrent => reset_dependency_to_conflict(state, &dep_id, assignment),
    }
    Ok(())
}

fn apply_dependency_terminal_effect(state: &mut BusState, data: &EventData, label: &'static str) {
    let dep_id = match data {
        EventData::DependencyResolved(d) => &d.dependency,
        EventData::DependencyRejected(d) => &d.dependency,
        _ => return,
    };
    if let Some(dep) = state.dependencies.get_mut(dep_id) {
        dep.status = ItemStatus::Terminal(label);
    }
}

/// See `reset_issue_to_conflict`'s doc comment; same rationale.
fn reset_dependency_to_conflict(state: &mut BusState, dep_id: &EventId, predecessor: &EventId) {
    if let Some(dep) = state.dependencies.get_mut(dep_id) {
        if let Some(target) = dep.assignment_target.get(predecessor).cloned() {
            dep.current_assignment = predecessor.clone();
            dep.current_target = target;
        }
        dep.status = ItemStatus::LifecycleConflict;
    }
}

fn apply_dependency_reassigned(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    commit_idx: usize,
    d: &DependencyReassigned,
) -> AbResult<()> {
    let dep = state
        .dependencies
        .get(&d.dependency)
        .ok_or_else(|| invalid(format!("{}: unknown dependency {}", env.id, d.dependency)))?;
    let expected_target = dep
        .assignment_target
        .get(&d.previous_assignment)
        .ok_or_else(|| invalid(format!("{}: unknown assignment {}", env.id, d.previous_assignment)))?;
    if expected_target != &d.previous_target {
        return Err(invalid(format!("{}: previous_target does not match that assignment's target", env.id)));
    }
    if predecessor_is_contested(state, &d.previous_assignment) {
        return Err(invalid(format!(
            "{}: previous_assignment {} is itself part of an unresolved lifecycle conflict",
            env.id, d.previous_assignment
        )));
    }
    if !(env.agent == dep.requester || state.is_bootstrap_coordinator(&env.agent)) {
        return Err(invalid(format!(
            "{}: only the opener or a bootstrap coordinator may reassign",
            env.id
        )));
    }
    require_agent(state, &d.new_target)?;
    let idx = observed_index(state, env)?;
    let outcome = record_exclusive(state, dependency_key(&d.previous_assignment), &env.id, commit_idx, idx)?;
    let this_event_id = env.id.clone();
    let dep_id = d.dependency.clone();
    let previous_assignment = d.previous_assignment.clone();
    if let Some(dep) = state.dependencies.get_mut(&dep_id) {
        dep.assignment_target.insert(this_event_id.clone(), d.new_target.clone());
    }
    match outcome {
        Exclusivity::Apply => {
            apply_dependency_reassigned_effect(state, &this_event_id, &EventData::DependencyReassigned(d.clone()))
        }
        Exclusivity::Concurrent => reset_dependency_to_conflict(state, &dep_id, &previous_assignment),
    }
    Ok(())
}

fn apply_dependency_reassigned_effect(state: &mut BusState, event_id: &EventId, data: &EventData) {
    let d = match data {
        EventData::DependencyReassigned(d) => d,
        _ => return,
    };
    if let Some(dep) = state.dependencies.get_mut(&d.dependency) {
        dep.current_target = d.new_target.clone();
        dep.current_assignment = event_id.clone();
        dep.assignment_target.insert(event_id.clone(), d.new_target.clone());
        dep.reassignment_chain.push(event_id.clone());
        dep.status = ItemStatus::Open;
    }
}

// ----------------------------------------------------------------- handoffs

fn apply_handoff_offered(state: &mut BusState, env: &crate::envelope::Envelope, d: &HandoffOffered) -> AbResult<()> {
    require_active_role(state, &env.agent, Role::Implementor)?;
    require_agent(state, &d.receiver)?;
    if !d.product_branch.is_product_branch_for(&env.agent) {
        return Err(invalid(format!(
            "{}: product_branch must match refs/heads/agent/{}/<topic>",
            env.id, env.agent
        )));
    }
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
    env: &crate::envelope::Envelope,
    commit_idx: usize,
    handoff_id: &EventId,
    label: &'static str,
) -> AbResult<()> {
    let h = state
        .handoffs
        .get(handoff_id)
        .ok_or_else(|| invalid(format!("{}: unknown handoff {handoff_id}", env.id)))?;
    let ok_actor = match label {
        "accepted" | "declined" => env.agent == h.data.receiver,
        "withdrawn" => env.agent == h.offerer,
        _ => false,
    };
    if !ok_actor {
        return Err(invalid(format!("{}: {label} emitted by unauthorized agent", env.id)));
    }
    let idx = observed_index(state, env)?;
    let outcome = record_exclusive(state, handoff_key(handoff_id), &env.id, commit_idx, idx)?;
    match outcome {
        Exclusivity::Apply => apply_handoff_terminal_effect(state, handoff_id, label),
        Exclusivity::Concurrent => {
            if let Some(h) = state.handoffs.get_mut(handoff_id) {
                h.status = ItemStatus::LifecycleConflict;
            }
        }
    }
    Ok(())
}

fn apply_handoff_terminal_effect(state: &mut BusState, handoff_id: &EventId, label: &'static str) {
    if let Some(h) = state.handoffs.get_mut(handoff_id) {
        h.status = ItemStatus::Terminal(label);
    }
}

// ------------------------------------------------------------------- review

fn apply_review_nominated(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    d: &ReviewNominated,
) -> AbResult<()> {
    require_active_role(state, &env.agent, Role::Implementor)?;
    if !d.authors.iter().any(|a| a == &env.agent) {
        return Err(invalid(format!("{}: nominating author must be in authors", env.id)));
    }
    for a in d.authors.iter() {
        require_active_role(state, a, Role::Implementor)?;
    }
    require_active_role(state, &d.reviewer, Role::Reviewer)?;
    if d.authors.iter().any(|a| a == &d.reviewer) {
        return Err(invalid(format!("{}: reviewer cannot be an author", env.id)));
    }
    if d.target_branch.as_str() != "refs/heads/main" {
        return Err(invalid(format!("{}: target_branch must be refs/heads/main in V1", env.id)));
    }
    // AGENT_BUS_SCHEMA.md section 1 / AGENT_REVIEW.md section 1 rule 1:
    // product branches match refs/heads/agent/<Agent>/<topic> and are never
    // `main` itself; a multi-author branch names its coordinating author.
    if !d.authors.iter().any(|a| d.product_branch.is_product_branch_for(a)) {
        return Err(invalid(format!(
            "{}: product_branch must match refs/heads/agent/<author>/<topic> for some author",
            env.id
        )));
    }
    let request = d.request();
    let mut nomination_reviewer = BTreeMap::new();
    nomination_reviewer.insert(env.id.clone(), d.reviewer.clone());
    state.reviews.insert(
        env.id.clone(),
        ReviewChain {
            root: env.id.clone(),
            nomination_events: vec![env.id.clone()],
            current_nomination: env.id.clone(),
            current_request: request,
            nomination_reviewer,
            accepted_nominations: std::collections::BTreeSet::new(),
            decline_or_withdraw_or_reassign_status: ItemStatus::Open,
            findings: BTreeMap::new(),
            authorizations: Vec::new(),
            merged: Vec::new(),
            reconciled: Vec::new(),
        },
    );
    state.review_chain_by_nomination.insert(env.id.clone(), env.id.clone());
    Ok(())
}

fn apply_review_accept(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    d: &ReviewNominationAccepted,
) -> AbResult<()> {
    let chain = state
        .review_chain(&d.nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {}", env.id, d.nomination)))?;
    let expected_reviewer = chain
        .nomination_reviewer
        .get(&d.nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination link {}", env.id, d.nomination)))?;
    if expected_reviewer != &env.agent {
        return Err(invalid(format!("{}: only the named reviewer may accept", env.id)));
    }
    if chain.accepted_nominations.contains(&d.nomination) {
        return Err(invalid(format!("{}: nomination already accepted", env.id)));
    }
    state
        .review_chain_mut(&d.nomination)
        .unwrap()
        .accepted_nominations
        .insert(d.nomination.clone());
    Ok(())
}

/// `decline`/`withdraw`/`reassign` are the exclusive-transition trio "from
/// one nomination" (AGENT_BUS.md section 10): unlike `review.changes_requested`
/// (which the spec gives a *stronger*, hard current-nomination precondition),
/// two of these racing on the very same nomination link must be able to both
/// remain valid and reduce to a lifecycle conflict, not have the second
/// arrival hard-fail because the first already advanced `current_nomination`.
/// So authority here is checked against the *named* nomination link, not
/// against whatever the chain now considers current.
fn apply_review_closing(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    commit_idx: usize,
    nomination: &EventId,
    label: &'static str,
) -> AbResult<()> {
    let chain = state
        .review_chain(nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {nomination}", env.id)))?;
    let link_reviewer = chain
        .nomination_reviewer
        .get(nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination link {nomination}", env.id)))?
        .clone();
    let ok_actor = match label {
        "declined" => env.agent == link_reviewer,
        "withdrawn" => chain.current_request.authors.iter().any(|a| a == &env.agent),
        _ => false,
    };
    if !ok_actor {
        return Err(invalid(format!("{}: {label} emitted by unauthorized agent", env.id)));
    }
    if predecessor_is_contested(state, nomination) {
        return Err(invalid(format!(
            "{}: nomination {nomination} is itself part of an unresolved lifecycle conflict",
            env.id
        )));
    }
    // AGENT_BUS_SCHEMA.md section 8: decline is valid "before authorization"
    // — not merely before acceptance (AGENT_REVIEW.md section 6 explicitly
    // allows declining after taking review, e.g. "the reviewer may request a
    // narrower branch or decline"). Withdraw uses the identical bound.
    if (label == "declined" || label == "withdrawn") && !chain.authorizations.is_empty() {
        return Err(invalid(format!("{}: cannot {label} after authorization", env.id)));
    }
    let idx = observed_index(state, env)?;
    let outcome = record_exclusive(state, review_key(nomination), &env.id, commit_idx, idx)?;
    let root = state.review_chain_by_nomination.get(nomination).unwrap().clone();
    match outcome {
        Exclusivity::Apply => apply_review_closing_effect(state, &root, label),
        Exclusivity::Concurrent => {
            if let Some(chain) = state.reviews.get_mut(&root) {
                chain.decline_or_withdraw_or_reassign_status = ItemStatus::LifecycleConflict;
            }
        }
    }
    Ok(())
}

fn apply_review_closing_effect(state: &mut BusState, root: &EventId, label: &'static str) {
    if let Some(chain) = state.reviews.get_mut(root) {
        chain.decline_or_withdraw_or_reassign_status = ItemStatus::Terminal(label);
    }
}

fn apply_review_changes(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    d: &ReviewChangesRequested,
) -> AbResult<()> {
    let chain = state
        .review_chain(&d.nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {}", env.id, d.nomination)))?;
    if chain.current_nomination != d.nomination {
        return Err(invalid(format!(
            "{}: nomination is no longer current (stale after reassignment)",
            env.id
        )));
    }
    if !chain.accepted() || chain.current_request.reviewer != env.agent {
        return Err(invalid(format!("{}: only the accepting reviewer may request changes", env.id)));
    }
    if d.findings.is_empty() {
        return Err(invalid(format!("{}: findings must be nonempty", env.id)));
    }
    let mut ids = std::collections::BTreeSet::new();
    for f in &d.findings {
        if !ids.insert(f.id.as_str().to_string()) {
            return Err(invalid(format!("{}: duplicate finding id {}", env.id, f.id)));
        }
    }
    let chain = state.review_chain_mut(&d.nomination).unwrap();
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
    env: &crate::envelope::Envelope,
    data: &EventData,
    commit_idx: usize,
    nomination: &EventId,
    changes_event: &EventId,
    finding_id: &crate::scalars::Short,
) -> AbResult<()> {
    let chain = state
        .review_chain(nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {nomination}", env.id)))?;
    if chain.current_nomination != *nomination {
        return Err(invalid(format!("{}: nomination is no longer current", env.id)));
    }
    if !chain.accepted() || chain.current_request.reviewer != env.agent {
        return Err(invalid(format!(
            "{}: only the accepting reviewer may dispose of findings",
            env.id
        )));
    }
    let fkey = (changes_event.clone(), finding_id.as_str().to_string());
    let finding = chain
        .findings
        .get(&fkey)
        .ok_or_else(|| invalid(format!("{}: unknown finding {}", env.id, finding_id)))?;
    if finding.disposition != FindingDisposition::Open {
        return Err(invalid(format!("{}: finding is already disposed", env.id)));
    }
    let idx = observed_index(state, env)?;
    let outcome = record_exclusive(state, finding_key(changes_event, finding_id), &env.id, commit_idx, idx)?;
    let root = state.review_chain_by_nomination.get(nomination).unwrap().clone();
    // On genuine concurrency, the finding simply stays `Open` (its existing
    // default) rather than either racer's disposition — no explicit revert
    // needed, and `authorize`'s "no open finding" check already blocks
    // authorization while it remains unresolved.
    if let Exclusivity::Apply = outcome {
        apply_finding_disposition_effect(state, &root, &fkey, &env.id, data);
    }
    Ok(())
}

fn apply_finding_disposition_effect(
    state: &mut BusState,
    root: &EventId,
    fkey: &(EventId, String),
    event_id: &EventId,
    data: &EventData,
) {
    let (disp, rationale) = match data {
        EventData::ReviewFindingsCleared(_) => (FindingDispositionKind::Cleared, None),
        EventData::ReviewFindingsSuperseded(d) => (FindingDispositionKind::Superseded, Some(d.rationale.clone())),
        _ => return,
    };
    if let Some(chain) = state.reviews.get_mut(root) {
        if let Some(f) = chain.findings.get_mut(fkey) {
            f.disposition = match disp {
                FindingDispositionKind::Cleared => FindingDisposition::Cleared {
                    by_event: event_id.clone(),
                },
                FindingDispositionKind::Superseded => FindingDisposition::Superseded {
                    by_event: event_id.clone(),
                    rationale: rationale.unwrap(),
                },
            };
        }
    }
}

fn apply_review_reassigned(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    commit_idx: usize,
    d: &ReviewReassigned,
) -> AbResult<()> {
    let chain = state
        .review_chain(&d.replaces)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {}", env.id, d.replaces)))?;
    let replaced_reviewer = chain
        .nomination_reviewer
        .get(&d.replaces)
        .ok_or_else(|| invalid(format!("{}: unknown nomination link {}", env.id, d.replaces)))?
        .clone();
    if predecessor_is_contested(state, &d.replaces) {
        return Err(invalid(format!(
            "{}: replaces {} is itself part of an unresolved lifecycle conflict",
            env.id, d.replaces
        )));
    }
    // The request is identical across the whole chain except `reviewer`
    // (AGENT_BUS_SCHEMA.md section 8), so compare against `current_request`'s
    // invariant fields regardless of which link this reassignment replaces.
    let same_except_reviewer = chain.current_request.authors == d.authors
        && chain.current_request.product_branch == d.product_branch
        && chain.current_request.required_checks == d.required_checks
        && chain.current_request.review_scope == d.review_scope
        && chain.current_request.summary == d.summary
        && chain.current_request.target_branch == d.target_branch
        && chain.current_request.evidence == d.evidence;
    if !same_except_reviewer {
        return Err(invalid(format!(
            "{}: reassignment must copy the request exactly except reviewer",
            env.id
        )));
    }
    if d.reviewer == replaced_reviewer {
        return Err(invalid(format!("{}: replacement reviewer must differ", env.id)));
    }
    require_active_role(state, &d.reviewer, Role::Reviewer)?;
    if d.authors.iter().any(|a| a == &d.reviewer) {
        return Err(invalid(format!("{}: replacement reviewer cannot be an author", env.id)));
    }
    if !(d.authors.iter().any(|a| a == &env.agent) || state.is_bootstrap_coordinator(&env.agent)) {
        return Err(invalid(format!(
            "{}: only a request author or bootstrap coordinator may reassign",
            env.id
        )));
    }
    let open_findings: std::collections::BTreeSet<(EventId, String)> = chain
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
    if inherited.len() != d.inherited_findings.len() {
        return Err(invalid(format!("{}: inherited_findings has duplicates", env.id)));
    }
    if inherited != open_findings {
        return Err(invalid(format!(
            "{}: inherited_findings must equal every still-open finding exactly once",
            env.id
        )));
    }
    let idx = observed_index(state, env)?;
    let outcome = record_exclusive(state, review_key(&d.replaces), &env.id, commit_idx, idx)?;
    let root = state.review_chain_by_nomination.get(&d.replaces).unwrap().clone();
    let this_event_id = env.id.clone();
    // The new link is always registered/referenceable (e.g. so its named
    // reviewer can `take` or `decline` it, or a later reassignment can name
    // it as *its* `replaces`) regardless of whether this reassignment turns
    // out to be the chain's confirmed winner.
    state.review_chain_by_nomination.insert(this_event_id.clone(), root.clone());
    if let Some(chain) = state.reviews.get_mut(&root) {
        chain.nomination_reviewer.insert(this_event_id.clone(), d.reviewer.clone());
    }
    match outcome {
        Exclusivity::Apply => {
            apply_review_reassigned_effect(state, &root, &this_event_id, &EventData::ReviewReassigned(d.clone()))
        }
        Exclusivity::Concurrent => {
            let replaces = d.replaces.clone();
            let replaced_reviewer = replaced_reviewer.clone();
            if let Some(chain) = state.reviews.get_mut(&root) {
                chain.current_nomination = replaces;
                chain.current_request.reviewer = replaced_reviewer;
                chain.decline_or_withdraw_or_reassign_status = ItemStatus::LifecycleConflict;
            }
        }
    }
    Ok(())
}

fn apply_review_reassigned_effect(state: &mut BusState, root: &EventId, event_id: &EventId, data: &EventData) {
    let d = match data {
        EventData::ReviewReassigned(d) => d,
        _ => return,
    };
    if let Some(chain) = state.reviews.get_mut(root) {
        chain.nomination_events.push(event_id.clone());
        chain.current_nomination = event_id.clone();
        chain.current_request = d.request();
        // A confirmed reassignment (uncontested, or the winner of a resolved
        // race) moves the chain to a fresh nomination link with a clean
        // slate: it must not stay stuck showing a stale `LifecycleConflict`/
        // `Terminal` marker from whatever happened to the *old* link.
        chain.decline_or_withdraw_or_reassign_status = ItemStatus::Open;
    }
}

fn apply_review_authorized(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    d: &ReviewMergeAuthorized,
) -> AbResult<()> {
    let chain = state
        .review_chain(&d.nomination)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {}", env.id, d.nomination)))?;
    if chain.current_nomination != d.nomination {
        return Err(invalid(format!("{}: nomination is no longer current", env.id)));
    }
    if !chain.accepted() || chain.current_request.reviewer != env.agent {
        return Err(invalid(format!("{}: only the accepting reviewer may authorize", env.id)));
    }
    // AGENT_BUS.md section 10: decline/withdraw/reassign are the nomination's
    // own exclusive set; a declined/withdrawn nomination (or one still in an
    // unresolved race between them) must not be able to authorize a merge.
    // `current_nomination == d.nomination` above already rules out a
    // *confirmed* reassignment away from this link, but not a decline,
    // withdrawal, or a still-unresolved race on this exact link.
    if !matches!(chain.decline_or_withdraw_or_reassign_status, ItemStatus::Open) {
        return Err(invalid(format!(
            "{}: nomination has a decline/withdraw/reassign disposition and cannot authorize",
            env.id
        )));
    }
    if chain.is_closed() {
        return Err(invalid(format!("{}: nomination already merged/reconciled", env.id)));
    }
    require_active_role(state, &env.agent, Role::Reviewer)?;
    let chain = state.review_chain(&d.nomination).unwrap();
    // AGENT_BUS_SCHEMA.md section 8 (2026-09 update): "reviewed_scope equals
    // the active nomination's review_scope exactly; an authorization cannot
    // widen, narrow, or otherwise rewrite the author's review request."
    if d.reviewed_scope != chain.current_request.review_scope {
        return Err(invalid(format!(
            "{}: reviewed_scope must exactly equal the nomination's review_scope",
            env.id
        )));
    }
    if d.product_branch != chain.current_request.product_branch {
        return Err(invalid(format!(
            "{}: product_branch must exactly equal the nomination's product_branch",
            env.id
        )));
    }
    let mut expected_dispositions: std::collections::BTreeSet<(EventId, String, FindingDispositionKind)> =
        std::collections::BTreeSet::new();
    for (key, f) in chain.findings.iter() {
        match &f.disposition {
            FindingDisposition::Open => {
                return Err(invalid(format!("{}: unresolved finding {}", env.id, f.finding_id)))
            }
            FindingDisposition::Cleared { .. } => {
                expected_dispositions.insert((key.0.clone(), key.1.clone(), FindingDispositionKind::Cleared));
            }
            FindingDisposition::Superseded { .. } => {
                expected_dispositions.insert((key.0.clone(), key.1.clone(), FindingDispositionKind::Superseded));
            }
        }
    }
    let actual_dispositions: std::collections::BTreeSet<(EventId, String, FindingDispositionKind)> = d
        .finding_dispositions
        .iter()
        .map(|fd| (fd.changes_event.clone(), fd.finding_id.as_str().to_string(), fd.disposition))
        .collect();
    if actual_dispositions.len() != d.finding_dispositions.len() {
        return Err(invalid(format!("{}: duplicate finding_dispositions entry", env.id)));
    }
    if actual_dispositions != expected_dispositions {
        return Err(invalid(format!(
            "{}: finding_dispositions must exactly match every finding's actual terminal disposition",
            env.id
        )));
    }
    if let Some(blocking) = blocking_issue_for_chain(state, chain) {
        return Err(invalid(format!(
            "{}: issue {blocking} explicitly blocks this nomination chain",
            env.id
        )));
    }
    // AGENT_BUS_SCHEMA.md section 8: "merge_engine_epoch is the selected
    // engine epoch visible in the authorization's observed state" — not
    // merely *a* known epoch; a superseded one may not be used (section 4:
    // "no candidate may use either until a coordinator selects one").
    if d.merge_engine_epoch != state.current_merge_engine_epoch {
        return Err(invalid(format!(
            "{}: merge_engine_epoch {} is not the currently selected epoch {}",
            env.id, d.merge_engine_epoch, state.current_merge_engine_epoch
        )));
    }
    for required in &chain.current_request.required_checks {
        if !d.checks.iter().any(|c| &c.command == required) {
            return Err(invalid(format!("{}: missing required check {:?}", env.id, required)));
        }
    }
    for c in &d.checks {
        if c.result != crate::common::CheckOutcome::Passed {
            return Err(invalid(format!("{}: check {:?} did not pass", env.id, c.command)));
        }
    }
    state.review_chain_mut(&d.nomination).unwrap().authorizations.push(env.id.clone());
    Ok(())
}

/// AGENT_BUS.md section 10: "Only unresolved issues whose `blocks` set names
/// an event in the active nomination chain block authorization." Applies at
/// authorization time (previously this was only checked by the separate
/// `merge-ready` gate, which a reviewer could simply not run).
pub fn blocking_issue_for_chain(state: &BusState, chain: &ReviewChain) -> Option<EventId> {
    let chain_members: std::collections::BTreeSet<&EventId> = chain.nomination_events.iter().collect();
    for issue in state.issues.values() {
        // "Unresolved" means not yet terminally resolved/rejected — an issue
        // sitting in `LifecycleConflict` (a race whose winner hasn't been
        // picked yet) is still unresolved and must still block, not just a
        // plain `Open` one.
        if !matches!(issue.status, ItemStatus::Terminal(_)) {
            for b in issue.data.blocks.iter() {
                if chain_members.contains(b) {
                    return Some(issue.id.clone());
                }
            }
        }
    }
    None
}

/// Load and type-check the `review.merge_authorized` event named by `auth_id`.
fn authorization_data(state: &BusState, auth_id: &EventId) -> AbResult<ReviewMergeAuthorized> {
    let env = state
        .events
        .get(auth_id)
        .ok_or_else(|| invalid(format!("unknown authorization {auth_id}")))?;
    match env.typed_data()? {
        EventData::ReviewMergeAuthorized(d) => Ok(d),
        _ => Err(invalid(format!("{auth_id} is not a review.merge_authorized event"))),
    }
}

/// AGENT_BUS_SCHEMA.md section 8: "Values equal the authorization and
/// `main_commit = candidate`." Checking every receipt against the
/// authorization it cites (rather than only checking receipts pairwise) is
/// exactly what makes "a concurrently published reviewer receipt with
/// identical authorization-derived values is a valid redundant receipt" true
/// by construction: any two receipts citing the *same* authorization are
/// forced to carry identical values by this check, so no separate identity
/// comparison between receipts is needed.
fn apply_review_merged(state: &mut BusState, env: &crate::envelope::Envelope, d: &ReviewMerged) -> AbResult<()> {
    let root = find_authorization_root(state, &d.authorization)
        .ok_or_else(|| invalid(format!("{}: unknown authorization {}", env.id, d.authorization)))?;
    if d.authorization.agent() != env.agent {
        return Err(invalid(format!("{}: only the authorizing reviewer may emit review.merged", env.id)));
    }
    let auth = authorization_data(state, &d.authorization)?;
    if d.previous_main != auth.previous_main
        || d.main_commit != auth.candidate
        || d.product_branch != auth.product_branch
        || d.reviewed_commit != auth.reviewed_commit
    {
        return Err(invalid(format!(
            "{}: receipt values do not match the cited authorization",
            env.id
        )));
    }
    state.reviews.get_mut(&root).unwrap().merged.push(env.id.clone());
    Ok(())
}

fn apply_review_reconciled(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    d: &ReviewMergeReconciled,
) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    let root = find_authorization_root(state, &d.authorization)
        .ok_or_else(|| invalid(format!("{}: unknown authorization {}", env.id, d.authorization)))?;
    let auth = authorization_data(state, &d.authorization)?;
    if d.previous_main != auth.previous_main
        || d.main_commit != auth.candidate
        || d.product_branch != auth.product_branch
        || d.reviewed_commit != auth.reviewed_commit
    {
        return Err(invalid(format!(
            "{}: receipt values do not match the cited authorization",
            env.id
        )));
    }
    // Every reconcile/merged receipt is independently checked above against
    // the *same cited authorization*, so any two receipts citing it are
    // forced to carry identical values — "a concurrently published reviewer
    // receipt with identical authorization-derived values is a valid
    // redundant receipt, not a lifecycle conflict" (AGENT_BUS_SCHEMA.md
    // section 8), regardless of which kind or order the receipts arrive in.
    state.reviews.get_mut(&root).unwrap().reconciled.push(env.id.clone());
    Ok(())
}

fn find_authorization_root(state: &BusState, auth_id: &EventId) -> Option<EventId> {
    state
        .reviews
        .iter()
        .find(|(_, chain)| chain.authorizations.iter().any(|a| a == auth_id))
        .map(|(root, _)| root.clone())
}

fn apply_conflict_resolved(
    state: &mut BusState,
    env: &crate::envelope::Envelope,
    d: &LifecycleConflictResolved,
) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    let is_open = |state: &BusState, k: &String| {
        state
            .exclusive
            .get(k)
            .map(|t| t.resolved.is_none() && t.transitions.len() >= 2)
            .unwrap_or(false)
    };
    let simple_key = ["issue", "dependency", "handoff", "review", "engine_epoch"]
        .iter()
        .map(|prefix| format!("{prefix}:{}", d.root))
        .find(|k| is_open(state, k));
    // A finding conflict is keyed `finding:<changes_event>:<finding_id>`,
    // which `root: EventId` alone cannot fully name; treat `root` as the
    // finding's `changes_event` and require the prefix to be unambiguous.
    let finding_prefix = format!("finding:{}:", d.root);
    let finding_matches: Vec<String> = state
        .exclusive
        .keys()
        .filter(|k| k.starts_with(&finding_prefix) && is_open(state, k))
        .cloned()
        .collect();
    let key = match (simple_key, finding_matches.as_slice()) {
        (Some(k), _) => k,
        (None, [only]) => only.clone(),
        (None, []) => {
            return Err(invalid(format!("{}: no unresolved conflict found for root {}", env.id, d.root)))
        }
        (None, _) => {
            return Err(invalid(format!(
                "{}: root {} names multiple ambiguous finding conflicts",
                env.id, d.root
            )))
        }
    };

    let tracker = state.exclusive.get(&key).unwrap();
    let members: std::collections::BTreeSet<EventId> = tracker.transitions.iter().map(|(id, _)| id.clone()).collect();
    let competing: std::collections::BTreeSet<EventId> = d.competing.iter().cloned().collect();
    if members != competing {
        return Err(invalid(format!(
            "{}: competing set does not match the recorded conflict set",
            env.id
        )));
    }
    if !competing.contains(&d.selected) {
        return Err(invalid(format!("{}: selected must be a member of competing", env.id)));
    }
    state.exclusive.get_mut(&key).unwrap().resolved = Some(d.selected.clone());
    apply_selected_transition_effect(state, &d.selected)?;
    Ok(())
}

/// Re-derives and applies the winning transition's effect now that a
/// coordinator has picked it (AGENT_BUS_SCHEMA.md section 9: "The selected
/// transition becomes current and the others remain visible but inert").
/// Every exclusive-transition kind was refactored so its mutation lives in a
/// standalone `apply_*_effect(state, ..., data)` function, both for its
/// normal (non-conflicting) call site and for reuse here.
fn apply_selected_transition_effect(state: &mut BusState, selected: &EventId) -> AbResult<()> {
    let env = state
        .events
        .get(selected)
        .ok_or_else(|| invalid(format!("selected transition {selected} not found")))?
        .clone();
    let data = env.typed_data()?;
    match &data {
        EventData::IssueResolved(d) => apply_issue_terminal_effect(state, &EventData::IssueResolved(d.clone()), "resolved"),
        EventData::IssueRejected(d) => apply_issue_terminal_effect(state, &EventData::IssueRejected(d.clone()), "rejected"),
        EventData::IssueReassigned(_) => apply_issue_reassigned_effect(state, selected, &data),
        EventData::DependencyResolved(d) => {
            apply_dependency_terminal_effect(state, &EventData::DependencyResolved(d.clone()), "resolved")
        }
        EventData::DependencyRejected(d) => {
            apply_dependency_terminal_effect(state, &EventData::DependencyRejected(d.clone()), "rejected")
        }
        EventData::DependencyReassigned(_) => apply_dependency_reassigned_effect(state, selected, &data),
        EventData::HandoffAccepted(d) => apply_handoff_terminal_effect(state, &d.handoff, "accepted"),
        EventData::HandoffDeclined(d) => apply_handoff_terminal_effect(state, &d.handoff, "declined"),
        EventData::HandoffWithdrawn(d) => apply_handoff_terminal_effect(state, &d.handoff, "withdrawn"),
        EventData::ReviewNominationDeclined(d) => {
            let root = state
                .review_chain_by_nomination
                .get(&d.nomination)
                .ok_or_else(|| invalid(format!("unknown nomination {}", d.nomination)))?
                .clone();
            apply_review_closing_effect(state, &root, "declined");
        }
        EventData::ReviewWithdrawn(d) => {
            let root = state
                .review_chain_by_nomination
                .get(&d.nomination)
                .ok_or_else(|| invalid(format!("unknown nomination {}", d.nomination)))?
                .clone();
            apply_review_closing_effect(state, &root, "withdrawn");
        }
        EventData::ReviewReassigned(d) => {
            let root = state
                .review_chain_by_nomination
                .get(&d.replaces)
                .ok_or_else(|| invalid(format!("unknown nomination {}", d.replaces)))?
                .clone();
            apply_review_reassigned_effect(state, &root, selected, &data);
        }
        EventData::ReviewFindingsCleared(d) => {
            let root = state
                .review_chain_by_nomination
                .get(&d.nomination)
                .ok_or_else(|| invalid(format!("unknown nomination {}", d.nomination)))?
                .clone();
            let fkey = (d.changes_event.clone(), d.finding_id.as_str().to_string());
            apply_finding_disposition_effect(state, &root, &fkey, selected, &data);
        }
        EventData::ReviewFindingsSuperseded(d) => {
            let root = state
                .review_chain_by_nomination
                .get(&d.nomination)
                .ok_or_else(|| invalid(format!("unknown nomination {}", d.nomination)))?
                .clone();
            let fkey = (d.changes_event.clone(), d.finding_id.as_str().to_string());
            apply_finding_disposition_effect(state, &root, &fkey, selected, &data);
        }
        EventData::MergeEngineActivated(_) => apply_merge_engine_activated_effect(state, selected, &data),
        _ => return Err(invalid(format!("{selected} is not an exclusive-transition event"))),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bootstrap::BusJson;
    use crate::common::Priority;
    use crate::history::{Walk, WalkedCommit};
    use crate::scalars::{ObjectId, Short, StringSet, Text};

    fn hash(n: u64) -> String {
        format!("{n:040x}")
    }

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn oid(n: u64) -> ObjectId {
        ObjectId::parse(hash(n)).unwrap()
    }

    fn wc(commit: &str, index: usize, agent: &Agent, events: Vec<crate::envelope::Envelope>) -> WalkedCommit {
        WalkedCommit {
            commit: commit.to_string(),
            index,
            is_bootstrap_root: false,
            is_repair: false,
            agent: Some(agent.clone()),
            new_events: events,
        }
    }

    fn env(
        agent: &Agent,
        seq: u64,
        observed: Option<ObjectId>,
        data: &EventData,
        refs: impl IntoIterator<Item = EventId>,
    ) -> crate::envelope::Envelope {
        crate::envelope::Envelope::new(agent, seq, observed, data, refs)
    }

    /// Builds a minimal valid bootstrap commit (one coordinator) plus
    /// alice/bob registrations, both observing the bootstrap commit.
    fn base_walk() -> (Walk, String) {
        let coord = a("coord1");
        let alice = a("alice");
        let bob = a("bob");
        let bus_json = BusJson::new("sha1".to_string(), vec![coord.clone()], oid(999)).unwrap();

        let coord_reg = EventData::AgentRegistered(AgentRegistered {
            display_name: Short::parse("coord1".into()).unwrap(),
            primary_role: Role::Coordinator,
            purpose: Text::parse("x".into()).unwrap(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        let root_commit = hash(0);
        let root = WalkedCommit {
            commit: root_commit.clone(),
            index: 0,
            is_bootstrap_root: true,
            is_repair: false,
            agent: None,
            new_events: vec![env(&coord, 0, None, &coord_reg, [])],
        };
        let root_oid = ObjectId::parse(root_commit.clone()).unwrap();

        let alice_reg = EventData::AgentRegistered(AgentRegistered {
            display_name: Short::parse("alice".into()).unwrap(),
            primary_role: Role::Implementor,
            purpose: Text::parse("x".into()).unwrap(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        let bob_reg = EventData::AgentRegistered(AgentRegistered {
            display_name: Short::parse("bob".into()).unwrap(),
            primary_role: Role::Implementor,
            purpose: Text::parse("x".into()).unwrap(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        let c1 = wc(&hash(1), 1, &alice, vec![env(&alice, 0, Some(root_oid.clone()), &alice_reg, [])]);
        let c2 = wc(&hash(2), 2, &bob, vec![env(&bob, 0, Some(root_oid), &bob_reg, [])]);

        (
            Walk {
                commits: vec![root, c1, c2],
                bus_json,
            },
            hash(2),
        )
    }

    /// Sequentially appends one commit per event, threading `observed` and
    /// per-agent `seq`/commit-index bookkeeping automatically, so tests for
    /// ordinary (non-concurrent) multi-step scenarios don't have to compute
    /// hashes/indices by hand.
    struct SeqBuilder {
        walk: Walk,
        tip: String,
        next_index: usize,
        next_seq: std::collections::BTreeMap<Agent, u64>,
    }

    impl SeqBuilder {
        fn new(base: (Walk, String), seeded_agents: &[Agent]) -> Self {
            let (walk, tip) = base;
            let next_index = walk.commits.len();
            let mut next_seq = std::collections::BTreeMap::new();
            for a in seeded_agents {
                next_seq.insert(a.clone(), 1);
            }
            SeqBuilder { walk, tip, next_index, next_seq }
        }

        fn register(&mut self, agent: &Agent, role: Role) -> EventId {
            let data = EventData::AgentRegistered(AgentRegistered {
                display_name: Short::parse(agent.to_string()).unwrap(),
                primary_role: role,
                purpose: Text::parse("x".into()).unwrap(),
                product_base: None,
                product_branch: None,
                provider: None,
                model: None,
            });
            let id = self.push_with_seq(agent, 0, &data, []);
            self.next_seq.insert(agent.clone(), 1);
            id
        }

        fn push(&mut self, agent: &Agent, data: &EventData, refs: impl IntoIterator<Item = EventId>) -> EventId {
            let seq = *self.next_seq.get(agent).unwrap_or(&0);
            let id = self.push_with_seq(agent, seq, data, refs);
            self.next_seq.insert(agent.clone(), seq + 1);
            id
        }

        fn push_with_seq(
            &mut self,
            agent: &Agent,
            seq: u64,
            data: &EventData,
            refs: impl IntoIterator<Item = EventId>,
        ) -> EventId {
            let observed = ObjectId::parse(self.tip.clone()).unwrap();
            let e = env(agent, seq, Some(observed), data, refs);
            let id = e.id.clone();
            let commit = hash(1000 + self.next_index as u64);
            self.walk.commits.push(wc(&commit, self.next_index, agent, vec![e]));
            self.next_index += 1;
            self.tip = commit;
            id
        }

        fn replay(self) -> AbResult<BusState> {
            replay(&self.walk)
        }

        /// Current tip as an ObjectId, so a test can capture a point in
        /// history and later publish several events all *racing* off it.
        fn tip_oid(&self) -> ObjectId {
            ObjectId::parse(self.tip.clone()).unwrap()
        }

        /// Like `push`, but with an explicit `observed` (so genuinely
        /// concurrent events can be built without hand-computing hashes).
        fn push_observing(
            &mut self,
            agent: &Agent,
            observed: &ObjectId,
            data: &EventData,
            refs: impl IntoIterator<Item = EventId>,
        ) -> EventId {
            let seq = *self.next_seq.get(agent).unwrap_or(&0);
            let e = env(agent, seq, Some(observed.clone()), data, refs);
            let id = e.id.clone();
            let commit = hash(1000 + self.next_index as u64);
            self.walk.commits.push(wc(&commit, self.next_index, agent, vec![e]));
            self.next_index += 1;
            self.tip = commit;
            self.next_seq.insert(agent.clone(), seq + 1);
            id
        }

        fn state(&self) -> AbResult<BusState> {
            replay(&self.walk)
        }

        /// Build (but do not append) an envelope, for `dry_run` tests.
        fn trial(&self, agent: &Agent, data: &EventData, refs: impl IntoIterator<Item = EventId>) -> crate::envelope::Envelope {
            let seq = *self.next_seq.get(agent).unwrap_or(&0);
            env(agent, seq, Some(self.tip_oid()), data, refs)
        }
    }

    fn simple_issue(target: &Agent, blocks: StringSet<EventId>) -> EventData {
        EventData::IssueOpened(IssueOpened {
            target: target.clone(),
            issue_kind: IssueKind::Bug,
            severity: Priority::High,
            summary: Text::parse("bug".into()).unwrap(),
            code_commit: None,
            locations: vec![],
            expected: None,
            observed_behavior: None,
            reproduction: vec![],
            blocks,
            evidence: StringSet::default(),
        })
    }

    fn reassign(issue: &EventId, prev_assignment: &EventId, prev_target: &Agent, new_target: &Agent) -> EventData {
        EventData::IssueReassigned(IssueReassigned {
            issue: issue.clone(),
            previous_assignment: prev_assignment.clone(),
            previous_target: prev_target.clone(),
            new_target: new_target.clone(),
            reason: Text::parse("r".into()).unwrap(),
        })
    }

    fn resolve(issue: &EventId, assignment: &EventId) -> EventData {
        EventData::IssueResolved(IssueResolved {
            issue: issue.clone(),
            assignment: assignment.clone(),
            summary: Text::parse("fixed".into()).unwrap(),
            fix_commit: None,
            verification: vec![],
        })
    }

    fn reject(issue: &EventId, assignment: &EventId) -> EventData {
        EventData::IssueRejected(IssueRejected {
            issue: issue.clone(),
            assignment: assignment.clone(),
            reason: Text::parse("nope".into()).unwrap(),
            normative_refs: vec![],
        })
    }

    /// An ordinary, uncontested reassign-then-act sequence must replay
    /// cleanly and leave the new target able to act, even though it all
    /// happens within one linear replay (no real race).
    #[test]
    fn uncontested_reassign_then_resolve_by_new_target() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&carol, Role::Implementor);

        let issue_data = EventData::IssueOpened(IssueOpened {
            target: bob.clone(),
            issue_kind: IssueKind::Bug,
            severity: Priority::High,
            summary: Text::parse("bug".into()).unwrap(),
            code_commit: None,
            locations: vec![],
            expected: None,
            observed_behavior: None,
            reproduction: vec![],
            blocks: StringSet::default(),
            evidence: StringSet::default(),
        });
        let issue_id = b.push(&alice, &issue_data, []);

        let reassign_data = EventData::IssueReassigned(IssueReassigned {
            issue: issue_id.clone(),
            previous_assignment: issue_id.clone(),
            previous_target: bob.clone(),
            new_target: carol.clone(),
            reason: Text::parse("handoff".into()).unwrap(),
        });
        let reassign_id = b.push(&alice, &reassign_data, [issue_id.clone(), issue_id.clone()]);

        let resolve_data = EventData::IssueResolved(IssueResolved {
            issue: issue_id.clone(),
            assignment: reassign_id.clone(),
            summary: Text::parse("fixed".into()).unwrap(),
            fix_commit: None,
            verification: vec![],
        });
        b.push(&carol, &resolve_data, [issue_id.clone(), reassign_id.clone()]);

        let state = b.replay().expect("an ordinary reassign-then-resolve sequence must replay");
        let issue = state.issues.get(&issue_id).unwrap();
        assert_eq!(issue.status, ItemStatus::Terminal("resolved"));
        assert_eq!(issue.current_target, carol);
    }

    /// An ordinary review reassignment followed by the new reviewer accepting
    /// must replay cleanly.
    #[test]
    fn uncontested_review_reassign_then_new_reviewer_accepts() {
        let alice = a("alice");
        let bob = a("bob");
        let rev1 = a("rev1");
        let rev2 = a("rev2");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&rev1, Role::Reviewer);
        b.register(&rev2, Role::Reviewer);

        let nom = ReviewNominated {
            authors: StringSet::from_iter(vec![alice.clone()]),
            product_branch: crate::scalars::Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewer: rev1.clone(),
            required_checks: vec![],
            review_scope: StringSet::default(),
            summary: Text::parse("s".into()).unwrap(),
            target_branch: crate::scalars::Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
        };
        let nom_id = b.push(&alice, &EventData::ReviewNominated(nom), []);

        let reassign = ReviewReassigned {
            authors: StringSet::from_iter(vec![alice.clone()]),
            product_branch: crate::scalars::Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewer: rev2.clone(),
            required_checks: vec![],
            review_scope: StringSet::default(),
            summary: Text::parse("s".into()).unwrap(),
            target_branch: crate::scalars::Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
            replaces: nom_id.clone(),
            reason: Text::parse("bob unavailable".into()).unwrap(),
            inherited_findings: vec![],
        };
        let reassign_id = b.push(&alice, &EventData::ReviewReassigned(reassign), [nom_id.clone()]);

        let accept = ReviewNominationAccepted {
            nomination: reassign_id.clone(),
            note: Text::parse("ok".into()).unwrap(),
        };
        b.push(&rev2, &EventData::ReviewNominationAccepted(accept), [reassign_id.clone()]);

        let state = b.replay().expect("the successor reviewer must be able to accept");
        let chain = state.review_chain(&reassign_id).unwrap();
        assert_eq!(chain.current_nomination, reassign_id);
        assert!(chain.accepted());
    }

    /// A reviewer superseded by `review.reassigned` must not retain authority
    /// to file findings under the now-stale nomination
    /// (AGENT_REVIEW.md section 4).
    #[test]
    fn superseded_reviewer_cannot_still_request_changes() {
        let alice = a("alice");
        let bob = a("bob");
        let rev1 = a("rev1");
        let rev2 = a("rev2");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&rev1, Role::Reviewer);
        b.register(&rev2, Role::Reviewer);

        let nom = ReviewNominated {
            authors: StringSet::from_iter(vec![alice.clone()]),
            product_branch: crate::scalars::Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewer: rev1.clone(),
            required_checks: vec![],
            review_scope: StringSet::default(),
            summary: Text::parse("s".into()).unwrap(),
            target_branch: crate::scalars::Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
        };
        let nom_id = b.push(&alice, &EventData::ReviewNominated(nom), []);
        let accept = ReviewNominationAccepted { nomination: nom_id.clone(), note: Text::parse("".into()).unwrap() };
        b.push(&rev1, &EventData::ReviewNominationAccepted(accept), [nom_id.clone()]);

        let reassign = ReviewReassigned {
            authors: StringSet::from_iter(vec![alice.clone()]),
            product_branch: crate::scalars::Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewer: rev2.clone(),
            required_checks: vec![],
            review_scope: StringSet::default(),
            summary: Text::parse("s".into()).unwrap(),
            target_branch: crate::scalars::Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
            replaces: nom_id.clone(),
            reason: Text::parse("bob unavailable".into()).unwrap(),
            inherited_findings: vec![],
        };
        b.push(&alice, &EventData::ReviewReassigned(reassign), [nom_id.clone()]);

        // rev1, superseded, tries to file a finding under the stale nomination.
        let changes = ReviewChangesRequested {
            nomination: nom_id.clone(),
            reviewed_commit: oid(42),
            findings: vec![crate::common::Finding {
                id: Short::parse("f1".into()).unwrap(),
                priority: Priority::High,
                locations: vec![],
                rationale: Text::parse("r".into()).unwrap(),
                closure_conditions: Text::parse("c".into()).unwrap(),
            }],
            evidence: StringSet::default(),
        };
        b.push(&rev1, &EventData::ReviewChangesRequested(changes), [nom_id.clone()]);

        let result = b.replay();
        assert!(
            result.is_err(),
            "a superseded reviewer's post-reassignment finding must be rejected as stale, but replay accepted it"
        );
    }

    /// Chained (sequential, non-concurrent) merge-engine epoch activations
    /// must replay cleanly.
    #[test]
    fn chained_merge_engine_activations() {
        let mut b = SeqBuilder::new(base_walk(), &[a("alice"), a("bob"), a("coord1")]);
        let coord = a("coord1");
        let bootstrap_epoch = EventId::new(&coord, 0);

        let first = MergeEngineActivated {
            previous_epoch: bootstrap_epoch.clone(),
            merge_engine: Short::parse("git-ort".into()).unwrap(),
            merge_engine_version: Short::parse("2.53.0".into()).unwrap(),
            design_commit: oid(10),
            helper_commit: oid(11),
        };
        let first_id = b.push(&coord, &EventData::MergeEngineActivated(first), [bootstrap_epoch]);

        let second = MergeEngineActivated {
            previous_epoch: first_id.clone(),
            merge_engine: Short::parse("git-ort".into()).unwrap(),
            merge_engine_version: Short::parse("2.53.0".into()).unwrap(),
            design_commit: oid(12),
            helper_commit: oid(13),
        };
        b.push(&coord, &EventData::MergeEngineActivated(second), [first_id]);

        let state = b.replay().expect("a chained engine activation must replay");
        assert_eq!(state.current_merge_engine_epoch, EventId::new(&coord, 2));
    }

    /// Reproduces the scenario the review flagged: alice opens an issue
    /// targeting bob; bob resolves it and (separately) alice reassigns it,
    /// both racing off the *same* observed state. Both must remain valid
    /// (AGENT_BUS.md section 10) and reduce to a lifecycle conflict, not
    /// have the second one hard-fail the whole replay.
    #[test]
    fn concurrent_resolve_and_reassign_become_a_lifecycle_conflict_not_a_hard_error() {
        let (mut walk, tip) = base_walk();
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let tip_oid = ObjectId::parse(tip.clone()).unwrap();

        let issue_data = EventData::IssueOpened(IssueOpened {
            target: bob.clone(),
            issue_kind: IssueKind::Bug,
            severity: Priority::High,
            summary: Text::parse("bug".into()).unwrap(),
            code_commit: None,
            locations: vec![],
            expected: None,
            observed_behavior: None,
            reproduction: vec![],
            blocks: StringSet::default(),
            evidence: StringSet::default(),
        });
        let issue_env = env(&alice, 1, Some(tip_oid), &issue_data, []);
        let issue_id = issue_env.id.clone();
        let c3 = wc(&hash(3), 3, &alice, vec![issue_env]);
        walk.commits.push(c3);
        let observed_after_issue = ObjectId::parse(hash(3)).unwrap();

        // carol registers too, so she can be reassigned the issue.
        let carol_reg = EventData::AgentRegistered(AgentRegistered {
            display_name: Short::parse("carol".into()).unwrap(),
            primary_role: Role::Implementor,
            purpose: Text::parse("x".into()).unwrap(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        let c4 = wc(
            &hash(4),
            4,
            &carol,
            vec![env(&carol, 0, Some(observed_after_issue.clone()), &carol_reg, [])],
        );
        walk.commits.push(c4);

        // Both race off the state right after the issue was opened (index 3),
        // *not* off each other or off carol's registration.
        let resolve_data = EventData::IssueResolved(IssueResolved {
            issue: issue_id.clone(),
            assignment: issue_id.clone(),
            summary: Text::parse("fixed".into()).unwrap(),
            fix_commit: None,
            verification: vec![],
        });
        let resolve_env = env(
            &bob,
            1,
            Some(observed_after_issue.clone()),
            &resolve_data,
            [issue_id.clone(), issue_id.clone()],
        );
        let c5 = wc(&hash(5), 5, &bob, vec![resolve_env]);

        let reassign_data = EventData::IssueReassigned(IssueReassigned {
            issue: issue_id.clone(),
            previous_assignment: issue_id.clone(),
            previous_target: bob.clone(),
            new_target: carol.clone(),
            reason: Text::parse("bob is unavailable".into()).unwrap(),
        });
        let reassign_env = env(
            &alice,
            2,
            Some(observed_after_issue),
            &reassign_data,
            [issue_id.clone(), issue_id.clone()],
        );
        let c6 = wc(&hash(6), 6, &alice, vec![reassign_env]);

        walk.commits.push(c5);
        walk.commits.push(c6);

        let state = replay(&walk).expect("both concurrent transitions must remain valid, not hard-fail replay");

        let issue = state.issues.get(&issue_id).unwrap();
        // Neither transition's effect wins outright: whichever was walked
        // first (bob's resolve) gets reverted back to neutral the moment the
        // genuinely concurrent sibling (alice's reassignment) is detected, so
        // the issue reads as an explicit lifecycle conflict rather than
        // either candidate's guess, and current_target stays at its
        // pre-conflict value.
        assert_eq!(issue.status, ItemStatus::LifecycleConflict);
        assert_eq!(issue.current_target, bob, "reassignment must not have applied unilaterally");

        let tracker = state
            .exclusive
            .get(&issue_key(&issue_id))
            .expect("a conflict tracker must exist for the raced predecessor");
        assert!(tracker.resolved.is_none());
        assert_eq!(tracker.transitions.len(), 2, "both racing transitions must be recorded");

        // Now a coordinator resolves the conflict in favor of the reassignment.
        let selected = tracker.transitions[1].0.clone(); // the reassignment (published second)
        let competing: Vec<EventId> = tracker.transitions.iter().map(|(id, _)| id.clone()).collect();
        let resolved_data = EventData::LifecycleConflictResolved(LifecycleConflictResolved {
            root: issue_id.clone(),
            competing: StringSet::from_sorted_unique(competing).unwrap(),
            selected: selected.clone(),
            reason: Text::parse("bob confirmed unavailable".into()).unwrap(),
            user_authority: Text::parse("user".into()).unwrap(),
        });
        let coord = a("coord1");
        let coord_next_seq = state.agents.get(&coord).unwrap().next_seq;
        let resolve_conflict_env = env(
            &coord,
            coord_next_seq,
            Some(ObjectId::parse(hash(6)).unwrap()),
            &resolved_data,
            [issue_id.clone(), selected.clone(), tracker.transitions[0].0.clone()],
        );
        let mut walk2 = walk;
        walk2.commits.push(wc(&hash(7), 7, &coord, vec![resolve_conflict_env]));

        let state2 = replay(&walk2).expect("conflict resolution must replay cleanly");
        let issue2 = state2.issues.get(&issue_id).unwrap();
        assert_eq!(
            issue2.current_target, carol,
            "the selected reassignment's effect must actually apply once resolved"
        );
        assert_eq!(issue2.status, ItemStatus::Open);
    }

    /// Round-3 adversarial regressions, layered onto the eager-apply-with-
    /// revert design: three-way races, causally-aware rejection, resumed
    /// action by a conflict-selected winner's target, dry_run agreement, and
    /// (after the `predecessor_is_contested` fix) that dependent mutations
    /// off an *unconfirmed* predecessor are rejected rather than silently
    /// laundering the predecessor into authoritative state.
    #[test]
    fn r3_three_way_race_records_all_three_and_resolves_to_exactly_one() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let coord = a("coord1");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone(), coord.clone()]);
        b.register(&carol, Role::Implementor);

        let issue_id = b.push(&alice, &simple_issue(&bob, StringSet::default()), []);
        let race_point = b.tip_oid();

        let r_resolve = b.push_observing(&bob, &race_point, &resolve(&issue_id, &issue_id), []);
        let r_reassign_alice =
            b.push_observing(&alice, &race_point, &reassign(&issue_id, &issue_id, &bob, &carol), []);
        let r_reassign_coord =
            b.push_observing(&coord, &race_point, &reassign(&issue_id, &issue_id, &bob, &alice), []);

        let state = b.state().expect("three concurrent transitions must all remain valid");
        let tracker = state.exclusive.get(&issue_key(&issue_id)).expect("tracker");
        assert_eq!(tracker.transitions.len(), 3, "all three racers must be recorded");
        assert!(tracker.resolved.is_none());
        let issue = state.issues.get(&issue_id).unwrap();
        assert_eq!(issue.status, ItemStatus::LifecycleConflict);
        assert_eq!(issue.current_target, bob, "no racer may unilaterally win");

        let competing: Vec<EventId> = vec![r_resolve.clone(), r_reassign_alice.clone(), r_reassign_coord.clone()];
        let resolved = EventData::LifecycleConflictResolved(LifecycleConflictResolved {
            root: issue_id.clone(),
            competing: StringSet::from_sorted_unique(competing).unwrap(),
            selected: r_reassign_coord.clone(),
            reason: Text::parse("user picked".into()).unwrap(),
            user_authority: Text::parse("user".into()).unwrap(),
        });
        b.push(&coord, &resolved, []);
        let state2 = b.state().expect("3-way conflict resolution must replay");
        let issue2 = state2.issues.get(&issue_id).unwrap();
        assert_eq!(issue2.current_target, alice, "exactly the selected transition must apply");
        assert_eq!(issue2.current_assignment, r_reassign_coord);
        assert_eq!(issue2.status, ItemStatus::Open);
        assert_eq!(state2.exclusive.get(&issue_key(&issue_id)).unwrap().resolved, Some(r_reassign_coord));
    }

    #[test]
    fn r3_causally_aware_second_transition_is_rejected() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&carol, Role::Implementor);
        let issue_id = b.push(&alice, &simple_issue(&bob, StringSet::default()), []);
        let race_point = b.tip_oid();
        b.push_observing(&bob, &race_point, &resolve(&issue_id, &issue_id), []);

        let state_before = b.state().expect("resolve alone replays");
        assert_eq!(state_before.exclusive.get(&issue_key(&issue_id)).unwrap().transitions.len(), 1);
        let trial = b.trial(&alice, &reassign(&issue_id, &issue_id, &bob, &carol), []);
        let err = dry_run(&state_before, &trial).expect_err("causally-aware transition must be rejected");
        assert!(format!("{err}").contains("already causally observed"), "unexpected error: {err}");

        assert_eq!(
            state_before.exclusive.get(&issue_key(&issue_id)).unwrap().transitions.len(),
            1,
            "a rejected dry-run must not mutate the real tracker"
        );
        b.push_observing(&alice, &race_point, &reassign(&issue_id, &issue_id, &bob, &carol), []);
        let state_after = b.state().expect("a genuinely concurrent racer must still be accepted");
        assert_eq!(state_after.exclusive.get(&issue_key(&issue_id)).unwrap().transitions.len(), 2);
    }

    #[test]
    fn r3_ack_by_target_of_conflict_selected_reassignment() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let coord = a("coord1");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone(), coord.clone()]);
        b.register(&carol, Role::Implementor);
        let issue_id = b.push(&alice, &simple_issue(&bob, StringSet::default()), []);
        let race_point = b.tip_oid();
        let r_resolve = b.push_observing(&bob, &race_point, &resolve(&issue_id, &issue_id), []);
        let r_reassign = b.push_observing(&alice, &race_point, &reassign(&issue_id, &issue_id, &bob, &carol), []);

        let resolved = EventData::LifecycleConflictResolved(LifecycleConflictResolved {
            root: issue_id.clone(),
            competing: StringSet::from_sorted_unique(vec![r_resolve, r_reassign.clone()]).unwrap(),
            selected: r_reassign.clone(),
            reason: Text::parse("x".into()).unwrap(),
            user_authority: Text::parse("user".into()).unwrap(),
        });
        b.push(&coord, &resolved, []);

        let ack = EventData::IssueAcknowledged(IssueAcknowledged {
            issue: issue_id.clone(),
            assignment: r_reassign.clone(),
            note: Text::parse("on it".into()).unwrap(),
        });
        let state_pre = b.state().expect("pre-ack replay");
        let trial = b.trial(&carol, &ack, []);
        dry_run(&state_pre, &trial).expect("dry_run must accept the confirmed target's ack");

        b.push(&carol, &ack, []);
        let state = b.state().expect("the confirmed target must be able to act");
        assert!(state.issues.get(&issue_id).unwrap().acknowledged);
    }

    #[test]
    fn r3_dry_run_sees_eagerly_applied_reassignment() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&carol, Role::Implementor);
        let issue_id = b.push(&alice, &simple_issue(&bob, StringSet::default()), []);
        let reassign_id = b.push(&alice, &reassign(&issue_id, &issue_id, &bob, &carol), []);
        let state = b.state().unwrap();

        let ack = EventData::IssueAcknowledged(IssueAcknowledged {
            issue: issue_id.clone(),
            assignment: reassign_id.clone(),
            note: Text::parse("on it".into()).unwrap(),
        });
        dry_run(&state, &b.trial(&carol, &ack, [])).expect("dry_run must see the eager reassignment");
        let bad_ack = EventData::IssueAcknowledged(IssueAcknowledged {
            issue: issue_id.clone(),
            assignment: reassign_id.clone(),
            note: Text::parse("mine".into()).unwrap(),
        });
        dry_run(&state, &b.trial(&bob, &bad_ack, [])).expect_err("only the named target may ack");
    }

    /// The `predecessor_is_contested` fix: the target of a reassignment that
    /// is itself part of an unresolved conflict must NOT be able to dispose
    /// of the issue by naming that unconfirmed assignment id.
    #[test]
    fn r3_unconfirmed_reassignment_target_cannot_dispose_of_the_issue() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&carol, Role::Implementor);
        let issue_id = b.push(&alice, &simple_issue(&bob, StringSet::default()), []);
        let race_point = b.tip_oid();
        let r_reassign = b.push_observing(&alice, &race_point, &reassign(&issue_id, &issue_id, &bob, &carol), []);
        b.push_observing(&bob, &race_point, &reject(&issue_id, &issue_id), []);
        let mid = b.state().unwrap();
        assert_eq!(mid.issues.get(&issue_id).unwrap().status, ItemStatus::LifecycleConflict);
        assert_eq!(mid.exclusive.get(&issue_key(&issue_id)).unwrap().transitions.len(), 2);

        // carol -- target of a reassignment that has NOT been confirmed --
        // must not be able to resolve the issue off that unconfirmed id.
        let trial = b.trial(&carol, &resolve(&issue_id, &r_reassign), []);
        let err = dry_run(&mid, &trial)
            .expect_err("resolving off an unconfirmed, still-contested reassignment must be rejected");
        assert!(format!("{err}").contains("unresolved lifecycle conflict"), "unexpected error: {err}");
    }

    #[test]
    fn r3_conflicted_blocking_issue_stops_blocking_authorization() {
        let alice = a("alice");
        let bob = a("bob");
        let rev1 = a("rev1");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&rev1, Role::Reviewer);

        let branch = crate::scalars::Branch::parse("refs/heads/agent/alice/x".into()).unwrap();
        let main = crate::scalars::Branch::parse("refs/heads/main".into()).unwrap();
        let nom = ReviewNominated {
            authors: StringSet::from_iter(vec![alice.clone()]),
            product_branch: branch.clone(),
            reviewer: rev1.clone(),
            required_checks: vec![],
            review_scope: StringSet::default(),
            summary: Text::parse("s".into()).unwrap(),
            target_branch: main,
            evidence: StringSet::default(),
        };
        let nom_id = b.push(&alice, &EventData::ReviewNominated(nom), []);
        b.push(
            &rev1,
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: nom_id.clone(),
                note: Text::parse("".into()).unwrap(),
            }),
            [],
        );

        let blocks = StringSet::from_sorted_unique(vec![nom_id.clone()]).unwrap();
        let issue_id = b.push(&alice, &simple_issue(&bob, blocks), []);

        let authorize = EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
            nomination: nom_id.clone(),
            product_branch: branch.clone(),
            previous_main: oid(1),
            reviewed_commit: oid(2),
            candidate: oid(3),
            merge_engine_epoch: EventId::new(&a("coord1"), 0),
            checks: vec![],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::default(),
            limitations: vec![],
            summary: Text::parse("ok".into()).unwrap(),
        });

        let st = b.state().unwrap();
        let err = dry_run(&st, &b.trial(&rev1, &authorize, [])).expect_err("open blocking issue must block");
        assert!(format!("{err}").contains("blocks this nomination chain"), "unexpected: {err}");

        let race_point = b.tip_oid();
        b.push_observing(&bob, &race_point, &resolve(&issue_id, &issue_id), []);
        b.push_observing(&alice, &race_point, &reassign(&issue_id, &issue_id, &bob, &rev1), []);
        let st2 = b.state().unwrap();
        assert_eq!(st2.issues.get(&issue_id).unwrap().status, ItemStatus::LifecycleConflict);
        assert!(st2.exclusive.get(&issue_key(&issue_id)).unwrap().resolved.is_none());

        dry_run(&st2, &b.trial(&rev1, &authorize, []))
            .expect_err("an unresolved lifecycle-conflicted blocking issue must still block authorization");
    }

    #[test]
    fn r3_conflicted_review_chain_stops_authorization() {
        let alice = a("alice");
        let bob = a("bob");
        let rev1 = a("rev1");
        let rev2 = a("rev2");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&rev1, Role::Reviewer);
        b.register(&rev2, Role::Reviewer);

        let branch = crate::scalars::Branch::parse("refs/heads/agent/alice/x".into()).unwrap();
        let main = crate::scalars::Branch::parse("refs/heads/main".into()).unwrap();
        let nom = ReviewNominated {
            authors: StringSet::from_iter(vec![alice.clone()]),
            product_branch: branch.clone(),
            reviewer: rev1.clone(),
            required_checks: vec![],
            review_scope: StringSet::default(),
            summary: Text::parse("s".into()).unwrap(),
            target_branch: main.clone(),
            evidence: StringSet::default(),
        };
        let nom_id = b.push(&alice, &EventData::ReviewNominated(nom), []);
        b.push(
            &rev1,
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: nom_id.clone(),
                note: Text::parse("".into()).unwrap(),
            }),
            [],
        );

        let race_point = b.tip_oid();
        b.push_observing(
            &rev1,
            &race_point,
            &EventData::ReviewNominationDeclined(ReviewNominationDeclined {
                nomination: nom_id.clone(),
                reason: Text::parse("too big".into()).unwrap(),
            }),
            [],
        );
        b.push_observing(
            &alice,
            &race_point,
            &EventData::ReviewReassigned(ReviewReassigned {
                authors: StringSet::from_iter(vec![alice.clone()]),
                product_branch: branch.clone(),
                reviewer: rev2.clone(),
                required_checks: vec![],
                review_scope: StringSet::default(),
                summary: Text::parse("s".into()).unwrap(),
                target_branch: main,
                evidence: StringSet::default(),
                replaces: nom_id.clone(),
                reason: Text::parse("unavailable".into()).unwrap(),
                inherited_findings: vec![],
            }),
            [],
        );

        let st = b.state().unwrap();
        assert_eq!(st.exclusive.get(&review_key(&nom_id)).unwrap().transitions.len(), 2);
        assert!(st.exclusive.get(&review_key(&nom_id)).unwrap().resolved.is_none());

        let authorize = EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
            nomination: nom_id.clone(),
            product_branch: branch,
            previous_main: oid(1),
            reviewed_commit: oid(2),
            candidate: oid(3),
            merge_engine_epoch: EventId::new(&a("coord1"), 0),
            checks: vec![],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::default(),
            limitations: vec![],
            summary: Text::parse("ok".into()).unwrap(),
        });
        dry_run(&st, &b.trial(&rev1, &authorize, []))
            .expect_err("a chain with an unresolved decline/reassign conflict must not authorize a merge");
    }

    #[test]
    fn r3_declined_nomination_cannot_still_authorize_a_merge() {
        let alice = a("alice");
        let bob = a("bob");
        let rev1 = a("rev1");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&rev1, Role::Reviewer);

        let branch = crate::scalars::Branch::parse("refs/heads/agent/alice/x".into()).unwrap();
        let main = crate::scalars::Branch::parse("refs/heads/main".into()).unwrap();
        let nom_id = b.push(
            &alice,
            &EventData::ReviewNominated(ReviewNominated {
                authors: StringSet::from_iter(vec![alice.clone()]),
                product_branch: branch.clone(),
                reviewer: rev1.clone(),
                required_checks: vec![],
                review_scope: StringSet::default(),
                summary: Text::parse("s".into()).unwrap(),
                target_branch: main,
                evidence: StringSet::default(),
            }),
            [],
        );
        b.push(
            &rev1,
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: nom_id.clone(),
                note: Text::parse("".into()).unwrap(),
            }),
            [],
        );
        b.push(
            &rev1,
            &EventData::ReviewNominationDeclined(ReviewNominationDeclined {
                nomination: nom_id.clone(),
                reason: Text::parse("too big".into()).unwrap(),
            }),
            [],
        );
        let st = b.state().unwrap();
        assert_eq!(
            st.review_chain(&nom_id).unwrap().decline_or_withdraw_or_reassign_status,
            ItemStatus::Terminal("declined")
        );

        let authorize = EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
            nomination: nom_id.clone(),
            product_branch: branch,
            previous_main: oid(1),
            reviewed_commit: oid(2),
            candidate: oid(3),
            merge_engine_epoch: EventId::new(&a("coord1"), 0),
            checks: vec![],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::default(),
            limitations: vec![],
            summary: Text::parse("ok".into()).unwrap(),
        });
        dry_run(&st, &b.trial(&rev1, &authorize, []))
            .expect_err("a declined nomination must not still authorize a merge");
    }

    #[test]
    fn r3_uncontested_review_reassign_can_still_authorize() {
        let alice = a("alice");
        let bob = a("bob");
        let rev1 = a("rev1");
        let rev2 = a("rev2");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&rev1, Role::Reviewer);
        b.register(&rev2, Role::Reviewer);
        let branch = crate::scalars::Branch::parse("refs/heads/agent/alice/x".into()).unwrap();
        let main = crate::scalars::Branch::parse("refs/heads/main".into()).unwrap();
        let nom_id = b.push(
            &alice,
            &EventData::ReviewNominated(ReviewNominated {
                authors: StringSet::from_iter(vec![alice.clone()]),
                product_branch: branch.clone(),
                reviewer: rev1.clone(),
                required_checks: vec![],
                review_scope: StringSet::default(),
                summary: Text::parse("s".into()).unwrap(),
                target_branch: main.clone(),
                evidence: StringSet::default(),
            }),
            [],
        );
        let re_id = b.push(
            &alice,
            &EventData::ReviewReassigned(ReviewReassigned {
                authors: StringSet::from_iter(vec![alice.clone()]),
                product_branch: branch.clone(),
                reviewer: rev2.clone(),
                required_checks: vec![],
                review_scope: StringSet::default(),
                summary: Text::parse("s".into()).unwrap(),
                target_branch: main,
                evidence: StringSet::default(),
                replaces: nom_id.clone(),
                reason: Text::parse("unavailable".into()).unwrap(),
                inherited_findings: vec![],
            }),
            [],
        );
        b.push(
            &rev2,
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: re_id.clone(),
                note: Text::parse("".into()).unwrap(),
            }),
            [],
        );
        let st = b.state().unwrap();
        let authorize = EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
            nomination: re_id.clone(),
            product_branch: branch,
            previous_main: oid(1),
            reviewed_commit: oid(2),
            candidate: oid(3),
            merge_engine_epoch: EventId::new(&a("coord1"), 0),
            checks: vec![],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::default(),
            limitations: vec![],
            summary: Text::parse("ok".into()).unwrap(),
        });
        dry_run(&st, &b.trial(&rev2, &authorize, []))
            .expect("an ordinary reassignment's new reviewer must still be able to authorize");
    }

    #[test]
    fn r3_resolved_review_conflict_unblocks_authorization() {
        let alice = a("alice");
        let bob = a("bob");
        let rev1 = a("rev1");
        let rev2 = a("rev2");
        let coord = a("coord1");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone(), coord.clone()]);
        b.register(&rev1, Role::Reviewer);
        b.register(&rev2, Role::Reviewer);
        let branch = crate::scalars::Branch::parse("refs/heads/agent/alice/x".into()).unwrap();
        let main = crate::scalars::Branch::parse("refs/heads/main".into()).unwrap();
        let nom_id = b.push(
            &alice,
            &EventData::ReviewNominated(ReviewNominated {
                authors: StringSet::from_iter(vec![alice.clone()]),
                product_branch: branch.clone(),
                reviewer: rev1.clone(),
                required_checks: vec![],
                review_scope: StringSet::default(),
                summary: Text::parse("s".into()).unwrap(),
                target_branch: main.clone(),
                evidence: StringSet::default(),
            }),
            [],
        );
        b.push(
            &rev1,
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: nom_id.clone(),
                note: Text::parse("".into()).unwrap(),
            }),
            [],
        );
        let race = b.tip_oid();
        let decline_id = b.push_observing(
            &rev1,
            &race,
            &EventData::ReviewNominationDeclined(ReviewNominationDeclined {
                nomination: nom_id.clone(),
                reason: Text::parse("too big".into()).unwrap(),
            }),
            [],
        );
        let re_id = b.push_observing(
            &alice,
            &race,
            &EventData::ReviewReassigned(ReviewReassigned {
                authors: StringSet::from_iter(vec![alice.clone()]),
                product_branch: branch.clone(),
                reviewer: rev2.clone(),
                required_checks: vec![],
                review_scope: StringSet::default(),
                summary: Text::parse("s".into()).unwrap(),
                target_branch: main,
                evidence: StringSet::default(),
                replaces: nom_id.clone(),
                reason: Text::parse("unavailable".into()).unwrap(),
                inherited_findings: vec![],
            }),
            [],
        );
        b.push(
            &coord,
            &EventData::LifecycleConflictResolved(LifecycleConflictResolved {
                root: nom_id.clone(),
                competing: StringSet::from_sorted_unique(vec![decline_id, re_id.clone()]).unwrap(),
                selected: re_id.clone(),
                reason: Text::parse("rev1 stands down".into()).unwrap(),
                user_authority: Text::parse("user".into()).unwrap(),
            }),
            [],
        );
        b.push(
            &rev2,
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: re_id.clone(),
                note: Text::parse("".into()).unwrap(),
            }),
            [],
        );
        let st = b.state().expect("resolution replays");
        assert_eq!(st.review_chain(&re_id).unwrap().current_nomination, re_id);
        let authorize = EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
            nomination: re_id.clone(),
            product_branch: branch,
            previous_main: oid(1),
            reviewed_commit: oid(2),
            candidate: oid(3),
            merge_engine_epoch: EventId::new(&coord, 0),
            checks: vec![],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::default(),
            limitations: vec![],
            summary: Text::parse("ok".into()).unwrap(),
        });
        dry_run(&st, &b.trial(&rev2, &authorize, []))
            .expect("a RESOLVED lifecycle conflict must not permanently block authorization");
    }

    /// The `blocking_issue_for_chain` fix (conflicted issues still block)
    /// combined with the `predecessor_is_contested` fix on issue disposal:
    /// the target of a losing/unconfirmed reassignment can no longer drive
    /// the blocking issue to Terminal to unblock the merge out from under an
    /// unresolved conflict.
    #[test]
    fn r3_blocking_fix_cannot_be_bypassed_via_unconfirmed_reassignment() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let rev1 = a("rev1");
        let mut b = SeqBuilder::new(base_walk(), &[alice.clone(), bob.clone()]);
        b.register(&carol, Role::Implementor);
        b.register(&rev1, Role::Reviewer);
        let branch = crate::scalars::Branch::parse("refs/heads/agent/alice/x".into()).unwrap();
        let main = crate::scalars::Branch::parse("refs/heads/main".into()).unwrap();
        let nom_id = b.push(
            &alice,
            &EventData::ReviewNominated(ReviewNominated {
                authors: StringSet::from_iter(vec![alice.clone()]),
                product_branch: branch.clone(),
                reviewer: rev1.clone(),
                required_checks: vec![],
                review_scope: StringSet::default(),
                summary: Text::parse("s".into()).unwrap(),
                target_branch: main,
                evidence: StringSet::default(),
            }),
            [],
        );
        b.push(
            &rev1,
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: nom_id.clone(),
                note: Text::parse("".into()).unwrap(),
            }),
            [],
        );
        let blocks = StringSet::from_sorted_unique(vec![nom_id.clone()]).unwrap();
        let issue_id = b.push(&alice, &simple_issue(&bob, blocks), []);

        let authorize = EventData::ReviewMergeAuthorized(ReviewMergeAuthorized {
            nomination: nom_id.clone(),
            product_branch: branch,
            previous_main: oid(1),
            reviewed_commit: oid(2),
            candidate: oid(3),
            merge_engine_epoch: EventId::new(&a("coord1"), 0),
            checks: vec![],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::default(),
            limitations: vec![],
            summary: Text::parse("ok".into()).unwrap(),
        });

        let race = b.tip_oid();
        let r_reassign = b.push_observing(&alice, &race, &reassign(&issue_id, &issue_id, &bob, &carol), []);
        b.push_observing(&bob, &race, &reject(&issue_id, &issue_id), []);
        let st = b.state().unwrap();
        assert_eq!(st.issues.get(&issue_id).unwrap().status, ItemStatus::LifecycleConflict);
        dry_run(&st, &b.trial(&rev1, &authorize, []))
            .expect_err("conflicted blocking issue must block (this part now works)");

        // carol, target of the UNCONFIRMED reassignment, must not be able to
        // resolve the issue off that unconfirmed id either.
        let resolve_trial = b.trial(&carol, &resolve(&issue_id, &r_reassign), []);
        dry_run(&st, &resolve_trial)
            .expect_err("resolving off an unconfirmed reassignment must be rejected outright");
    }

    /// AGENT_BUS_SCHEMA.md section 4: concurrent activations off one
    /// `previous_epoch` conflict and "no candidate may use either until a
    /// coordinator selects one". Chaining a third activation off a *losing*
    /// racer must be rejected outright by `predecessor_is_contested`, not
    /// laundered into the selected epoch.
    #[test]
    fn r3_chaining_off_an_unresolved_engine_racer_is_rejected() {
        let coord = a("coord1");
        let mut b = SeqBuilder::new(base_walk(), &[a("alice"), a("bob"), coord.clone()]);
        let bootstrap = EventId::new(&coord, 0);
        let race_point = b.tip_oid();

        let mk = |prev: &EventId, n: u64| {
            EventData::MergeEngineActivated(MergeEngineActivated {
                previous_epoch: prev.clone(),
                merge_engine: Short::parse("git-ort".into()).unwrap(),
                merge_engine_version: Short::parse("2.53.0".into()).unwrap(),
                design_commit: oid(n),
                helper_commit: oid(n + 1),
            })
        };
        let e1 = b.push_observing(&coord, &race_point, &mk(&bootstrap, 10), []);
        b.push_observing(&coord, &race_point, &mk(&bootstrap, 20), []);
        let st = b.state().unwrap();
        assert_eq!(st.exclusive.get(&format!("engine_epoch:{bootstrap}")).unwrap().transitions.len(), 2);
        assert_eq!(st.current_merge_engine_epoch, bootstrap, "conflict reverts to the pre-race epoch");

        // Chain a third activation off the *unresolved* racer e1: must be
        // rejected, not accepted.
        let trial = b.trial(&coord, &mk(&e1, 30), []);
        let err = dry_run(&st, &trial)
            .expect_err("an epoch chained off an unresolved racer must be rejected outright");
        assert!(format!("{err}").contains("unresolved lifecycle conflict"), "unexpected error: {err}");
    }
}
