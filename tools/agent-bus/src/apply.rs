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
use crate::exclusive::Disposition;
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
///
/// This is the *only* place in the crate that validates an `Envelope` built
/// directly via `Envelope::new` rather than one already read back through
/// `Envelope::parse_line` (`reduce`/`reduce_onto` only ever see envelopes
/// `stream::read_stream`/`storage::read_stream_log` already parsed that
/// way). `parse_line` enforces two structural invariants `apply_event` alone
/// does not, so both are re-checked here explicitly:
///
///  - `refs` must equal *exactly* `data.referenced_ids()` -- not merely a
///    superset. `Envelope::new` sets `refs` to `data.referenced_ids() ∪
///    extra_refs`, so a caller passing an `--observes`/`extra_refs` id the
///    payload doesn't itself reference produces an envelope `parse_line`
///    will reject on every future read, forever, even though nothing here
///    stopped it from being committed and pushed first (round-6 adversarial
///    review, reproduced live: `submit ... --observes <unrelated-id>`
///    durably corrupted a stream fleet-wide the same way an *omitted*
///    `--observes` did before the fix below it).
///  - gate 4: every cross-agent id in `refs` must have frontier coverage in
///    `observed` (round-5 adversarial review, reproduced live: a `review.
///    nomination_accepted` submitted without the operator remembering
///    `--observes` for the nomination it names durably corrupted that
///    stream fleet-wide the same way). `coordinator::build_frontier` is
///    fixed to derive coverage from `data.referenced_ids()` automatically,
///    closing that gap at its source -- this check is the defense-in-depth
///    backstop for any other path that might one day construct an envelope
///    the same way.
///
/// Without either check, a self-inconsistent envelope would sail through
/// dry-run, get committed and pushed, and then permanently fail to reduce
/// for every host that ever fetches it.
pub fn dry_run(state: &BusState, env: &Envelope) -> AbResult<()> {
    let data = env.typed_data()?;
    let expected: BTreeSet<EventId> = data.referenced_ids();
    let actual: BTreeSet<EventId> = env.refs.iter().cloned().collect();
    if expected != actual {
        return Err(invalid(format!(
            "{}: refs mismatch: envelope has {actual:?}, data references {expected:?} -- \
             --observes may only repeat an id the event's own payload already references, never \
             add one beyond it",
            env.id
        )));
    }
    for r in env.refs.iter() {
        if r.agent() != env.agent {
            env.observed
                .validate_reference(r)
                .map_err(|e| invalid(format!("{}: {e}", env.id)))?;
        }
    }
    let mut trial = state.clone();
    apply_event(&mut trial, env)
}

/// A valid linear extension of the causal partial order: each event only
/// after its own stream's immediately preceding event and after every
/// cross-agent event it references. Ties are broken by `EventId` purely for
/// deterministic, reproducible test behavior -- correctness does not depend
/// on which valid order is chosen (gate 16) -- with one deliberate
/// exception: among several simultaneously-ready events, every remaining
/// `seq == 0` (an agent's own `agent.registered`) is preferred over every
/// `seq > 0` event, regardless of which sorts lower by id.
///
/// This exception exists because most event kinds that name another agent
/// by identity (e.g. `IssueOpened.target`, `DependencyRequested.target`,
/// `HandoffOffered.receiver`, `ReviewRequest.reviewer`/`authors`) do not
/// include that agent's registration in `EventData::referenced_ids()` --
/// only fields that already carry an `EventId` naturally do (`blocks`,
/// `evidence`, and similar). Without this exception, a plain lexicographic
/// tie-break has no notion that "the named agent must already be
/// registered" is a real dependency at all, and -- since ties are broken by
/// *agent name*, not real causality -- it would deterministically place
/// e.g. `alice:1` (an issue alice opens targeting `bob`) before `bob:0`
/// (bob's own registration) on *every* cold reduce whenever `alice` sorts
/// before `bob`, permanently failing with "unregistered agent: bob" even
/// though bob is definitely registered. Every agent's own `seq == 0` event
/// always has zero dependencies by construction (the very first event on
/// any stream), so it is always in the initial `ready` set from the start
/// of this algorithm; preferring it whenever it's available guarantees
/// every registration in the batch is applied before any event that merely
/// *names* that agent, without requiring a wire-format change to add those
/// references explicitly everywhere.
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

    // Ordered `(is_not_registration, id)` so a `seq == 0` event (false)
    // always sorts before a `seq > 0` event (true), and ties within each
    // tier still fall back to plain `EventId` order.
    let ready_key = |id: &EventId| (id.seq() != 0, id.clone());

    let mut remaining_deps = deps.clone();
    let mut ready: std::collections::BTreeSet<(bool, EventId)> = remaining_deps
        .iter()
        .filter(|(_, d)| d.is_empty())
        .map(|(id, _)| ready_key(id))
        .collect();
    let mut dependents: BTreeMap<EventId, Vec<EventId>> = BTreeMap::new();
    for (id, d) in &deps {
        for dep in d {
            dependents.entry(dep.clone()).or_default().push(id.clone());
        }
    }

    let mut order = Vec::new();
    while let Some((_, id)) = ready.iter().next().cloned() {
        ready.remove(&(id.seq() != 0, id.clone()));
        remaining_deps.remove(&id);
        order.push(id.clone());
        if let Some(children) = dependents.get(&id) {
            for child in children {
                if let Some(d) = remaining_deps.get_mut(child) {
                    d.retain(|x| x != &id);
                    if d.is_empty() {
                        ready.insert(ready_key(child));
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
        EventData::AuditReported(d) => apply_audit_reported(state, env, d)?,
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

/// `a` is registered with `role` and is still active, reading both halves
/// of `active()`.
///
/// **Sound only outside reduction**, and it now has exactly one caller:
/// `merge_ready::check_merge_ready`, which is a gate. A gate runs against a
/// fully-reduced view at the moment of the push and *should* ask the live
/// question, so reading `retired` there is right.
///
/// It is not right during replay, which is why no handler calls it any
/// more. See `require_self_active_role` for the half that is safe there,
/// and `coordinator::verify_author_active` for where the other half went.
pub(crate) fn require_active_role<'a>(
    state: &'a BusState,
    a: &Agent,
    role: Role,
) -> AbResult<&'a AgentState> {
    let ag = require_role(state, a, role)?;
    if !ag.active() {
        return Err(invalid(format!("{a} is not active")));
    }
    Ok(ag)
}

/// `a` is registered with `role` and has not itself stood down -- the most
/// a handler can soundly ask about its own publisher's liveness.
///
/// `active()` is two questions wearing one name, and only one of them is
/// answerable during replay:
///
///  - `status.deactivates()` comes from the agent's own `agent.status`.
///    Streams are single-writer and `topological_order` gives each one a
///    predecessor edge, so an agent's status is ordered against its later
///    events on every host. Safe, and checked here.
///  - `retired` comes from `agent.retired`, which `apply_retired` requires
///    a *coordinator* to publish, and which forbids retiring yourself. It
///    therefore always lives on someone else's stream, causally unordered
///    against anything the target published. Not safe, and not read here.
///
/// The old code read both. A coordinator retiring an agent then made every
/// one of that agent's own already-published `scope.set`, `audit.reported`,
/// `handoff.offered` and `review.nominated` events fail on any host that
/// had fetched the retirement -- and `reduce` has no per-event isolation,
/// so that is the entire bus, permanently, from an ordinary administrative
/// action.
///
/// `coordinator::verify_author_active` asks the `retired` half at
/// publication, against a fully-reduced view, where it has one answer.
pub(crate) fn require_self_active_role<'a>(
    state: &'a BusState,
    a: &Agent,
    role: Role,
) -> AbResult<&'a AgentState> {
    let ag = require_role(state, a, role)?;
    if ag.status.deactivates() {
        return Err(invalid(format!(
            "{a} has stood down ({:?}) and cannot publish this",
            ag.status
        )));
    }
    Ok(ag)
}

/// `a` is registered with `role`, saying nothing about whether it is still
/// active.
///
/// The role half is safe to ask during replay where the liveness half is
/// not. `primary_role` is fixed by `agent.registered` at sequence zero and
/// never changes, and `topological_order` sorts every sequence-zero event
/// into a tier ahead of all others, so an agent's registration is applied
/// before any event that could name it, on every host.
pub(crate) fn require_role<'a>(
    state: &'a BusState,
    a: &Agent,
    role: Role,
) -> AbResult<&'a AgentState> {
    let ag = require_agent(state, a)?;
    if ag.primary_role != role {
        return Err(invalid(format!("{a} does not have role {role}")));
    }
    Ok(ag)
}

/// Coordinator authority, asked the only way replay can soundly ask it:
/// "was this identity registered with `Role::Coordinator`?"
///
/// This used to ask two further questions, and both were fatal to the whole
/// fleet rather than to one event (`reduce`/`reduce_onto` propagate with a
/// bare `?` and have no per-event isolation):
///
///  - **"is it a coordinator in the *current* roster epoch?"** -- read off
///    `state.roster_epoch`, i.e. whatever epoch the registry tip happens to
///    name at *reduction* time, not the epoch that was current when the
///    event was authored. `sync::reduce_local` re-reduces every event on
///    every read, so the first registry epoch that dropped a coordinator
///    made every coordinator-authored event in history permanently
///    unreducible, on every host, forever. Retirement and coordinator
///    succession are ordinary administrative acts (section 2.1 names them
///    as epoch transitions), and adding or moving a host is exactly such an
///    act -- so this was a total, unrecoverable outage one routine roster
///    change away. It is the same defect `require_complete_frontier` was
///    already fixed for, in the same file, for the same reason (gate 5: "a
///    later registration does not invalidate it"); it simply survived here.
///
///  - **"is it still active?"** -- `AgentState::active()` reads `retired`,
///    which is set by *someone else's* `agent.retired` on a *different*
///    stream. That event is causally unordered against this one, so which
///    of the two a given host applied first decided whether the bus
///    reduced at all: a confluence violation of exactly the kind gates
///    15/16 forbid (`require_active_role`'s own doc claims it is "sound
///    where `a` is the publisher itself", which holds for `agent.status`
///    -- same stream -- but not for `agent.retired`).
///
/// Neither is replaced by looking the epoch up from `env.observed.
/// roster_epoch` instead of from `state.roster_epoch`. For a *sparse*
/// frontier -- which is what every coordinator kind here except
/// `schema.activated`/`merge_engine.activated` carries -- nothing validates
/// that field against anything, so it is the author's own unchecked choice
/// of which epoch to be judged by: an author could always name whichever
/// epoch grants it authority. Since primary roles are immutable (section
/// 2.2: "Primary roles remain immutable"), the best that self-selection can
/// ever prove is "this identity was a coordinator in *some* epoch" -- which
/// is precisely `primary_role`, already checked below, minus the new
/// failure mode of an event naming an epoch this host has not fetched yet.
///
/// What is genuinely lost is the *membership and liveness* half, and that
/// half moves to publication time, where the codebase already puts every
/// question whose answer a concurrent event can change (`coordinator::
/// verify_participants_active`, `verify_predecessor_not_contested`,
/// `verify_broadcast_published`):
///
///  - membership was already enforced there, for every event and not just
///    these -- `drain_outbox` calls `registry::authorize_stream_write`,
///    which refuses to advance the stream of an agent that is not an active
///    member of the *current* epoch holding the claimed custody. A dropped
///    coordinator therefore cannot publish anything new; only its already
///    -published history keeps the authority it genuinely had, which is
///    section 2.3's "an event consumes the exact historical state it
///    observed; later events do not rewrite that verdict."
///  - liveness moves to `coordinator::verify_author_active`, added for this
///    change, so a retired-but-still-bound coordinator is still refused at
///    the gate where the question has one answer.
fn require_bootstrap_coordinator(state: &BusState, a: &Agent) -> AbResult<()> {
    let ag = require_agent(state, a)?;
    if ag.primary_role != Role::Coordinator {
        // Deliberately not `require_role`'s generic wording: this is the
        // one refusal an operator is most likely to hit by hand, and the
        // actionable part is that no registry edit can fix it -- primary
        // roles are immutable (section 2.2), so the answer is always
        // "publish this from a coordinator identity instead."
        return Err(invalid(format!(
            "{a} is not a coordinator: it registered as {}, and primary roles are immutable -- \
             publish this from a coordinator identity instead",
            ag.primary_role
        )));
    }
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
    // The role the agent declares must be the role the registry binds it to.
    //
    // Every authority check in this crate reads `AgentState::primary_role`,
    // which comes solely from this payload, while `cli::status` prints the
    // registry's `MemberBinding::role` -- so a divergence is invisible in the
    // one place an operator would look, and the declared value is the one
    // that decides what the identity may do. An identity the roster binds as
    // `auditor` could declare itself an implementor and hold every authority
    // gates 20 and 21 deny it.
    //
    // Reachable without malice: `cli::register` lands the registry transition
    // before draining the registration event, and refuses to run again once
    // the member exists, so a failed drain leaves a hand-written `submit
    // --kind agent.registered` as the only way forward -- and that payload
    // may name any role.
    if let Some(binding) = state
        .roster_epoch
        .as_ref()
        .and_then(|e| e.active_members.get(&env.agent))
    {
        if binding.role != d.primary_role {
            return Err(invalid(format!(
                "{}: registers as {} but the roster epoch binds {} as {} -- the declared role must match the registry, since it is the declared one that grants authority",
                env.id, d.primary_role, env.agent, binding.role
            )));
        }
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
        // `previous_lifecycle` named a predecessor that is no longer this
        // agent's latest lifecycle event -- ordinarily, or because a
        // concurrent lifecycle event this event's author never observed
        // (e.g. a coordinator's `agent.retired`, independently published
        // from a different host -- AGENT_COORDINATION_EVOLUTION.md section
        // 2.1: per-agent streams are single-writer and published without
        // cross-observing each other) landed first. A no-op, not an `Err`:
        // `reduce()`/`reduce_onto()` propagate any `Err` here via a bare
        // `?` with no per-event isolation, so a hard failure would
        // permanently break reduction of the *entire* bus for every host
        // that has fetched both streams, not just this one agent's record
        // (round-4 adversarial review, same bug class already fixed for
        // review.* events -- see `apply_review_accept`'s identical
        // reasoning).
        return Ok(());
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
        // See the identical comment in `apply_resumed`: a no-op, not an
        // `Err`. Two coordinators on different hosts can each validly
        // retire the same silent target, each citing the same
        // `previous_lifecycle`, without observing each other -- exactly
        // the "silent death" scenario `agent.retired` exists for. Whichever
        // reduces first must not poison reduction of the entire bus for
        // the second.
        return Ok(());
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
    // AGENT_BUS_SCHEMA.md section 4's "`version` is greater than all
    // previously activated versions" is deliberately *not* asked here, and
    // the complete-frontier requirement above buys nothing towards it.
    // `SchemaActivated::referenced_ids` is empty (this event names no
    // predecessor at all), so two activations from different coordinators
    // get no edge between them in `topological_order` -- which builds edges
    // from `refs` and each stream's own predecessor, never from `observed`.
    // Replaying v3 then v2 therefore hit "not greater than the currently
    // activated 3" while v2-then-v3 was fine, and two coordinators
    // activating the *same* version were fatal in both orders. With
    // `reduce`'s bare `?` and an append-only log that is every host unable
    // to reduce the bus at all, permanently (round-9 sweep, C3).
    //
    // What replaces it is the operation this field's own definition already
    // describes -- "highest version seen so far". A maximum over a set is
    // commutative and idempotent, so every linear extension of the same
    // events lands on the identical value, and no ordering is ever fatal.
    // A concurrent lower activation is simply subsumed by the higher one
    // rather than being a fleet-wide error, which is also the only answer
    // that is stable: nothing in the event records a predecessor, so there
    // is no baseline for the `ExclusiveTracker` "contested, reset to the
    // shared pre-race value" treatment `apply_merge_engine_activated` gets
    // just below -- that treatment needs a `previous_epoch` field, which is
    // a normative schema change, not a fix (see this task's report).
    //
    // `coordinator::verify_schema_activation_advances` asks the advancement
    // question at publication instead, against the publishing host's
    // fully-reduced view, where there is no replay order to be at the mercy
    // of -- the same relocation `verify_predecessor_not_contested` and
    // `verify_author_active` already are.
    state.activated_schema_version = state.activated_schema_version.max(d.version);
    Ok(())
}

fn apply_merge_engine_activated(
    state: &mut BusState,
    env: &Envelope,
    d: &MergeEngineActivated,
) -> AbResult<()> {
    require_bootstrap_coordinator(state, &env.agent)?;
    require_complete_frontier(state, env)?;
    // Bootstrap exception: `bootstrap::genesis` never itself emits a
    // `merge_engine.activated` event (it only records `merge_engine`/
    // `merge_engine_version` as static `BusConfig` metadata, a supported
    // -version check, not a real prior activation) -- so a fresh bus has no
    // production path that ever seeds a first `merge_engine_info` entry.
    // Without this exception, the very first activation on any real bus can
    // never name a previous_epoch that passes the "known prior activation"
    // check below, current_merge_engine_epoch can never become `Some`, and
    // review.merge_authorized (which requires its own merge_engine_epoch to
    // equal the currently selected one) can therefore never be validly
    // published at all: a bootstrap deadlock in the crate's own core
    // feature, found by adversarial review while porting v1's merge
    // -authorization checks. The one legitimate case with nothing real to
    // reference is the genesis activation itself: `merge_engine_info` is
    // still completely empty, and the caller names their own registration
    // event as the synthetic anchor -- the same convention this file's own
    // tests already assumed (`default_merge_engine_epoch`), just never
    // wired to an actual production path until now.
    let is_genesis_activation =
        state.merge_engine_info.is_empty() && d.previous_epoch == EventId::new(&env.agent, 0);
    if !is_genesis_activation && !state.merge_engine_info.contains_key(&d.previous_epoch) {
        return Err(invalid(format!(
            "{}: previous_epoch {} is not a known prior engine activation",
            env.id, d.previous_epoch
        )));
    }
    // Whether the predecessor is itself contested is deliberately not asked
    // here. `is_contested` reads `ExclusiveTracker` group membership, which
    // *grows* as concurrent candidates reduce, and the candidate that makes a
    // predecessor contested is referenced by nothing this event carries.
    // Reduce that candidate first and this event was fatal; reduce it second
    // and this event succeeded -- the same two events, one host wedged and
    // one not, with no per-event isolation in `reduce` to contain it.
    //
    // `coordinator::verify_predecessor_not_contested` asks it at publication
    // instead, against this host's fully-reduced view, where there is no
    // replay order to be at the mercy of. Recording is confluent: this event
    // joins its own key's group, which is a set, and whether its effect
    // applies is `ExclusiveTracker::disposition`, a pure function of that
    // group's final membership.
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
    state.exclusive.record(&key, &env.id)?;
    state.merge_engine_info.insert(
        env.id.clone(),
        (d.merge_engine.clone(), d.merge_engine_version.clone()),
    );
    match state.exclusive.disposition(&key, &env.id) {
        Disposition::Applies => {
            state.current_merge_engine_epoch = Some(env.id.clone());
        }
        Disposition::Contested => {
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
        // A coordinator already picked someone else. The effect must
        // not apply, and resetting to contested here would undo the
        // resolution this candidate simply arrived too late for.
        Disposition::Superseded => {}
    }
    Ok(())
}

// ------------------------------------------------------------ scope/plan/progress

fn apply_scope_set(state: &mut BusState, env: &Envelope, d: &ScopeSet) -> AbResult<()> {
    require_self_active_role(state, &env.agent, Role::Implementor)?;
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

/// docs/AGENT_COORDINATION_EVOLUTION.md section 2.2, gates 20 and 22.
///
/// Two rules, and the second is the one worth being careful about.
///
/// Gate 20: only an auditor publishes this. The role is what the design
/// gives fleet-wide audit authority to; an implementor or reviewer with an
/// opinion about the fleet raises issues, which they already may.
///
/// Gate 22: "an audit report cannot resolve its referenced issues or satisfy
/// any merge finding disposition merely by describing them as closed". That
/// is enforced by this function doing *nothing* to the issues it names --
/// deliberately, and the emptiness is the enforcement. It validates that
/// each referenced issue exists, so a report cannot cite a fiction, and then
/// touches no issue, no review chain, and no finding disposition.
///
/// `an_audit_report_disturbs_no_issue_and_no_review_chain` holds that to
/// account by comparing `state.issues` and `state.reviews` *wholesale* across
/// the report. An earlier version of this comment claimed a four-field
/// comparison would catch any mutation here; it would not, and an adversarial
/// review demonstrated it by making the report silently reassign every issue
/// it named and clear every finding on every chain, both of which passed.
fn apply_audit_reported(
    state: &mut BusState,
    env: &Envelope,
    d: &crate::events::AuditReported,
) -> AbResult<()> {
    require_self_active_role(state, &env.agent, Role::Auditor)?;
    // The frontier is the only place the report records what it observed, so
    // it has to name every active member rather than only whoever it happened
    // to reference. See `coordinator::requires_complete_frontier`.
    require_complete_frontier(state, env)?;
    // A report that names no area, states no method, and says nothing is
    // durable evidence of nothing, and `methods` exists precisely so a reader
    // can judge what the absence of a finding is worth.
    //
    // Emptiness is measured after trimming, per entry: a length check alone
    // accepted `areas: [""]` and `methods: ["   "]`, which is the same
    // contentless report wearing a list. `limitations` is deliberately *not*
    // required -- an audit may genuinely have no blind spot worth naming --
    // and `inspected_commits`/`issues` may be empty because the schema
    // licenses both: an audit of coordination history inspects no product
    // commit, and a clean surface files no issue.
    let has_content = |v: &[crate::scalars::Text]| v.iter().any(|t| !t.as_str().trim().is_empty());
    for (field, empty) in [
        ("areas", !has_content(&d.areas)),
        ("methods", !has_content(&d.methods)),
        ("summary", d.summary.as_str().trim().is_empty()),
    ] {
        if empty {
            return Err(invalid(format!(
                "{}: an audit report must state its {field}",
                env.id
            )));
        }
    }
    for issue in d.issues.iter() {
        if !state.issues.contains_key(issue) {
            return Err(invalid(format!(
                "{}: audit report references unknown issue {issue}",
                env.id
            )));
        }
    }
    // Recorded verbatim as durable evidence, exactly like `friction.reported`
    // -- readable, referenceable, and carrying no obligation of its own.
    state.audits.insert(env.id.clone(), d.clone());
    Ok(())
}

fn apply_issue_opened(state: &mut BusState, env: &Envelope, d: &IssueOpened) -> AbResult<()> {
    let opener = require_agent(state, &env.agent)?;
    // AGENT_COORDINATION_EVOLUTION.md section 2.2: "An auditor-opened
    // `issue.opened` must carry an empty `blocks` set. The checked writer
    // rejects a nonempty set from an auditor identity." Gate 21 restates it
    // as an activation condition.
    //
    // Without this an auditor has exactly the authority the role table denies
    // it. `blocks` makes an issue refuse the named reviewer's own
    // `review.merge_authorized` through `blocking_issue_for_chain`, and only
    // the issue's *target* may dispose of it -- so an auditor could block a
    // candidate at will and could not be made to unblock it. The design calls
    // that "a unilateral or indefinite candidate veto that the named reviewer
    // cannot dispose", and routes urgent findings to the reviewer instead:
    // audit "can demand attention without silently acquiring candidate
    // authority".
    //
    // Deliberately keyed on the opener's role, not on who the issue targets:
    // the rule is about what an auditor identity may author.
    if opener.primary_role == Role::Auditor && !d.blocks.is_empty() {
        return Err(invalid(format!(
            "{}: an auditor-opened issue must carry an empty blocks set. An auditor's finding is evidence for the nominated reviewer to assess, not a merge verdict it can impose (AGENT_COORDINATION_EVOLUTION.md section 2.2). Route the evidence to the reviewer and coordinator urgently instead; the reviewer decides whether to publish a merge-blocking finding.",
            env.id
        )));
    }
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
    // A no-op, not an `Err`. This is the identical situation
    // `apply_review_accept` and `apply_finding_disposition` already handle
    // that way, for the identical reason recorded there: a hard failure here
    // "would permanently break reduction of the entire bus, not just this
    // chain".
    //
    // It is a plain causal race and nobody is at fault. The target
    // acknowledges the assignment it holds; concurrently the item is
    // reassigned away by someone whose event it has not yet observed. The
    // acknowledgement is honest, correctly authorized, and simply
    // inapplicable by the time it is reduced -- and because reduction
    // propagates with `?` and has no per-event isolation, rejecting it makes
    // every host unable to reduce the bus at all, forever, from one
    // well-formed event.
    //
    // That is not hypothetical: it took the whole fleet down. `g-build:4` was
    // opened against `g-foundation`, reassigned to `g-build` by `g-build:17`,
    // acknowledged and resolved there -- and `g-foundation:68` acknowledged
    // the original assignment, its own frontier showing it had never observed
    // the reassignment. Every `status` and `tail` on every host then failed.
    //
    // Recorded against the assignment it *names*, not against whatever is
    // current -- deliberately, and this is the part that took two attempts to
    // get right. Dropping a superseded acknowledgement outright also unblocks
    // reduction, but it makes the result depend on arrival order: whether the
    // ack is recorded would hinge on whether the racing reassignment happened
    // to reduce first, and `state.rs` documents `acknowledged_assignments` as
    // "a pure function of history". Two hosts fetching the same two streams
    // in different orders would then disagree permanently, with no error to
    // signal it -- and after a later conflict rolls `current_assignment` back
    // to the baseline, one host would report the issue acknowledged and the
    // other not. Recording it keeps the field a pure function of history and
    // satisfies gates 15/16.
    //
    // It grants nothing: `IssueState::acknowledged()` keys on
    // `current_assignment`, so a superseded entry never makes the *current*
    // assignment look acknowledged. The duplicate check below keys on the
    // named assignment for the same reason.
    let issue = state.issues.get_mut(&d.issue).expect("just checked");
    if issue.acknowledged_assignments.contains(&d.assignment) {
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
    // Not asked here -- see `apply_merge_engine_activated` for why the
    // contested-predecessor question cannot be answered during replay,
    // and `coordinator::verify_predecessor_not_contested` for where it
    // is answered instead.
    let key = issue_key(assignment);
    state.exclusive.record(&key, &env.id)?;
    let expected_target = expected_target.clone();
    match state.exclusive.disposition(&key, &env.id) {
        Disposition::Applies => {
            apply_issue_terminal_effect(state, data, label);
        }
        Disposition::Contested => {
            reset_issue_to_conflict(state, issue_id, assignment, &expected_target);
        }
        // A coordinator already picked someone else. The effect must
        // not apply, and resetting to contested here would undo the
        // resolution this candidate simply arrived too late for.
        Disposition::Superseded => {}
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
    // Not asked here -- see `apply_merge_engine_activated` for why the
    // contested-predecessor question cannot be answered during replay,
    // and `coordinator::verify_predecessor_not_contested` for where it
    // is answered instead.
    let key = issue_key(&d.previous_assignment);
    state.exclusive.record(&key, &env.id)?;
    match state.exclusive.disposition(&key, &env.id) {
        Disposition::Applies => {
            issue_reassign_effect(state, &env.id, d);
        }
        Disposition::Contested => {
            reset_issue_to_conflict(state, &d.issue, &d.previous_assignment, &d.previous_target);
        }
        // A coordinator already picked someone else. The effect must
        // not apply, and resetting to contested here would undo the
        // resolution this candidate simply arrived too late for.
        Disposition::Superseded => {}
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
    // The dependency twin of the issue case above -- same race, same
    // fleet-wide consequence, same order-independent resolution.
    let dep = state
        .dependencies
        .get_mut(&d.dependency)
        .expect("just checked");
    if dep.acknowledged_assignments.contains(&d.assignment) {
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
    // Not asked here -- see `apply_merge_engine_activated` for why the
    // contested-predecessor question cannot be answered during replay,
    // and `coordinator::verify_predecessor_not_contested` for where it
    // is answered instead.
    let expected_target = expected_target.clone();
    let key = dependency_key(assignment);
    state.exclusive.record(&key, &env.id)?;
    match state.exclusive.disposition(&key, &env.id) {
        Disposition::Applies => {
            dependency_terminal_effect(state, data, dependency_id, label);
        }
        Disposition::Contested => {
            reset_dependency_to_conflict(state, dependency_id, assignment, &expected_target);
        }
        // A coordinator already picked someone else. The effect must
        // not apply, and resetting to contested here would undo the
        // resolution this candidate simply arrived too late for.
        Disposition::Superseded => {}
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
    // Not asked here -- see `apply_merge_engine_activated` for why the
    // contested-predecessor question cannot be answered during replay,
    // and `coordinator::verify_predecessor_not_contested` for where it
    // is answered instead.
    let key = dependency_key(&d.previous_assignment);
    state.exclusive.record(&key, &env.id)?;
    match state.exclusive.disposition(&key, &env.id) {
        Disposition::Applies => {
            dependency_reassign_effect(state, &env.id, d);
        }
        Disposition::Contested => {
            reset_dependency_to_conflict(
                state,
                &d.dependency,
                &d.previous_assignment,
                &d.previous_target,
            );
        }
        // A coordinator already picked someone else. The effect must
        // not apply, and resetting to contested here would undo the
        // resolution this candidate simply arrived too late for.
        Disposition::Superseded => {}
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
    require_self_active_role(state, &env.agent, Role::Implementor)?;
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
    // Not asked here -- see `apply_merge_engine_activated` for why the
    // contested-predecessor question cannot be answered during replay,
    // and `coordinator::verify_predecessor_not_contested` for where it
    // is answered instead.
    let key = handoff_key(handoff_id);
    state.exclusive.record(&key, &env.id)?;
    match state.exclusive.disposition(&key, &env.id) {
        Disposition::Applies => {
            handoff_terminal_effect(state, handoff_id, label);
        }
        Disposition::Contested => {
            reset_handoff_to_conflict(state, handoff_id);
        }
        // A coordinator already picked someone else. The effect must
        // not apply, and resetting to contested here would undo the
        // resolution this candidate simply arrived too late for.
        Disposition::Superseded => {}
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
    // The publisher is one of the authors (just checked), so its own
    // liveness is sound to ask here: a stream is single-writer and
    // `topological_order` gives it a predecessor edge, so this agent's own
    // status events are ordered against this one on every host.
    require_self_active_role(state, &env.agent, Role::Implementor)?;
    for author in d.authors.iter() {
        // Every *other* author gets the role check only. Their
        // `agent.status`/`agent.retired` is on their own stream, which this
        // nomination neither references nor need have observed, so charging
        // the nominator for it made reduction depend on which a host
        // replayed first. `coordinator::verify_participants_active` asks
        // about liveness at publication instead.
        require_role(state, author, Role::Implementor)?;
    }
    if d.authors.iter().any(|a| a == &d.reviewer) {
        return Err(invalid(format!(
            "{}: reviewer must not be one of the authors",
            env.id
        )));
    }
    require_role(state, &d.reviewer, Role::Reviewer)?;
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
            authorizations: Default::default(),
            merged: Default::default(),
            reconciled: Default::default(),
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
        // `d.nomination` was once this chain's current link but has since
        // been superseded -- ordinarily, or by a concurrent reassignment
        // this event's independently-published author could not have
        // observed (AGENT_COORDINATION_EVOLUTION.md section 2.1: per-agent
        // streams are single-writer and published without cross-observing
        // each other). AGENT_BUS_SCHEMA.md section 8 says such an
        // acceptance "never becomes an orphaned concurrent successor of a
        // published reassignment" -- the fix is a no-op, not an `Err`:
        // `reduce()`/`reduce_onto()` propagate any `Err` here via a bare
        // `?` with no per-event isolation, so a hard failure would
        // permanently break reduction of the *entire* bus for every host
        // that has fetched both streams, not just this one chain
        // (round-3 adversarial review, confirmed fleet-wide DoS).
        return Ok(());
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
                // A no-op, not an `Err`: an author's withdrawal built
                // without observing a just-landed `review.merge_authorized`
                // (the two are independently published and never
                // cross-observe each other before publication --
                // AGENT_COORDINATION_EVOLUTION.md section 2.1) must not
                // poison reduction of the entire bus the way a hard `Err`
                // here would (`reduce()`'s bare `?` has no per-event
                // isolation). The policy outcome is unchanged -- withdrawal
                // after authorization still never takes effect -- only the
                // enforcement mechanism changes (round-4 adversarial
                // review, same bug class already fixed for the sibling
                // `chain.current_nomination` checks in this file).
                return Ok(());
            }
        }
        _ => unreachable!(),
    }
    let key = review_key(nomination);
    state.exclusive.record(&key, &env.id)?;
    match state.exclusive.disposition(&key, &env.id) {
        Disposition::Applies => {
            confirm_review_closing(state, nomination, label);
        }
        Disposition::Contested => {
            reset_review_to_conflict(state, nomination);
        }
        // A coordinator already picked someone else. The effect must
        // not apply, and resetting to contested here would undo the
        // resolution this candidate simply arrived too late for.
        Disposition::Superseded => {}
    }
    Ok(())
}

/// The winner-confirmed effect of a decline/withdraw: shared between the
/// normal reduction path above and `apply_conflict_resolved`, which applies
/// this same effect once a coordinator has explicitly picked a winner out
/// of an already-contested decline/withdraw/reassign group.
fn confirm_review_closing(state: &mut BusState, nomination: &EventId, label: &'static str) {
    if let Some(chain) = state.review_chain_mut(nomination) {
        chain.decline_or_withdraw_or_reassign_status = ItemStatus::Terminal(label);
    }
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
        // See the identical comment in `apply_review_accept`: a no-op, not
        // an `Err` -- a hard failure here would permanently break reduction
        // of the entire bus, not just this chain.
        return Ok(());
    }
    let reviewer = chain.nomination_reviewer.get(&d.nomination).unwrap();
    if reviewer != &env.agent {
        return Err(invalid(format!(
            "{}: only the accepting reviewer may request changes",
            env.id
        )));
    }
    if !chain.accepted() {
        return Err(invalid(format!(
            "{}: the named reviewer must accept the nomination before requesting changes",
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
    // Authority belongs to the reviewer of the link this event *names*, and
    // whether the chain has since moved past that link is deliberately not
    // asked here.
    //
    // It used to be, as a no-op ("a superseded reviewer must not retain
    // disposal authority by citing a now-stale nomination id"). A no-op is
    // total, which is what round 3 needed, but it is not confluent, which is
    // the other half of the same requirement: `current_nomination` moves
    // under a concurrent `review.reassigned`, and `topological_order` builds
    // edges from `refs` and each stream's own predecessor, never from
    // `observed` -- so a disposal and a reassignment that both merely
    // reference the same nomination have no edge between them. Reduce the
    // disposal first and the finding is disposed; reduce the reassignment
    // first and the disposal silently evaporates. Two hosts that fetched the
    // same streams in a different order then hold permanently different
    // state, which is gates 15/16 broken exactly where the round-3 fix
    // looked correct in isolation (round-9 sweep, found while making C5's
    // own event pair converge rather than merely reduce).
    //
    // What remains is the half that is sound in every order: the reviewer
    // recorded for the *named* link, written once when that link was created
    // and never rewritten, and reachable because this event references the
    // nomination. `coordinator::verify_disposition_targets_the_current_
    // nomination` asks the superseded-reviewer question at publication
    // instead, against the publishing host's fully-reduced view.
    let reviewer = chain.nomination_reviewer.get(nomination).cloned();
    if reviewer.as_ref() != Some(&env.agent) {
        return Err(invalid(format!(
            "{}: only the named nomination's accepting reviewer may dispose of findings",
            env.id
        )));
    }
    // `accepted_nominations.contains(nomination)`, not `chain.accepted()`:
    // the latter tests the *current* link, which is the mutable fact just
    // discussed. This one is stable -- the acceptance can only have come
    // from `env.agent` (the check above), so it sits earlier on this very
    // stream and a predecessor edge orders it before this event in every
    // linear extension.
    if !chain.accepted_nominations.contains(nomination) {
        return Err(invalid(format!(
            "{}: the named reviewer must accept the nomination before disposing of findings",
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
    // competing candidate. The policy is a hard block; the *mechanism* is
    // a no-op rather than an `Err`, though -- a reassignment built without
    // observing a just-landed `review.merged`/`review.merge_reconciled`
    // (independently published, never cross-observed before publication --
    // AGENT_COORDINATION_EVOLUTION.md section 2.1) must not poison
    // reduction of the entire bus via `reduce()`'s bare `?` (round-4
    // adversarial review, same bug class already fixed for the sibling
    // `chain.current_nomination` checks in this file).
    let chain = state
        .review_chain(&d.replaces)
        .ok_or_else(|| invalid(format!("{}: unknown nomination {}", env.id, d.replaces)))?;
    if !chain.merged.is_empty() || !chain.reconciled.is_empty() {
        return Ok(());
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
    // Compared against the reviewer of the link this event actually
    // *replaces*, never against whoever is currently in force. `chain.
    // current_request.reviewer` moves the moment a first, genuinely
    // concurrent reassignment from the same predecessor is reduced
    // (`confirm_review_reassigned` overwrites `current_request` whole), and
    // nothing this event carries references that competitor -- so two
    // reassignments naming the same replacement reviewer, which is what an
    // author and a coordinator independently picking the same alternate
    // looks like, were fatal in *both* orders, and with `reduce`'s bare `?`
    // that is every host permanently unable to reduce the bus (round-9
    // sweep, C4).
    //
    // `nomination_reviewer[d.replaces]` is the sound reading of the same
    // rule, and the more faithful one: `d.replaces` is in `refs`, so its
    // link is ordered before this event in every linear extension, and its
    // entry is written once when that link is created and never rewritten
    // afterwards (`reset_review_to_conflict` only ever removes a
    // *provisional* link's entry, and removes it from
    // `review_chain_by_nomination` in the same breath -- so the chain
    // lookup above has already failed by then). The rule it enforces is
    // "replacing link X with X's own reviewer is a no-op nobody meant to
    // publish", which is what the message says and what the check was for;
    // in the sequential case the two readings are the same value, because
    // `current_nomination == d.replaces`.
    //
    // `.get`, not `.unwrap`: totality here is the whole point, and a
    // missing entry is the pre-race baseline being absent, not a rule this
    // event broke.
    if chain.nomination_reviewer.get(&d.replaces) == Some(&d.reviewer) {
        return Err(invalid(format!(
            "{}: replacement reviewer must differ from the replaced nomination's reviewer",
            env.id
        )));
    }
    require_role(state, &d.reviewer, Role::Reviewer)?;
    let is_author = chain
        .current_request
        .authors
        .iter()
        .any(|a| a == &env.agent);
    if !is_author {
        require_bootstrap_coordinator(state, &env.agent)?;
    }
    // AGENT_BUS_SCHEMA.md section 8's "inherited_findings equals every
    // still-open finding exactly once" is deliberately *not* asked here.
    // Both sides of that equality move under events this one references
    // nothing of: the open set shrinks under a concurrent `review.findings_
    // cleared`/`_superseded` (which this event references only the
    // *changes* event behind, never the disposition itself) and grows under
    // a concurrent `review.changes_requested`. Reduce a clear first and the
    // sets no longer match, so the reassignment was fatal; reduce it second
    // and the identical pair was fine -- one host wedged and one not, with
    // no per-event isolation in `reduce` to contain it (round-9 sweep, C5).
    //
    // Dropping it costs no reduced state: `inherited_findings` is a
    // declaration about the author's view, not an input to reduction --
    // `confirm_review_reassigned` carries `chain.findings` across the new
    // link whole and never reads this field -- so the two orders now agree
    // byte for byte rather than one of them failing.
    // `coordinator::verify_review_reassignment_inherits_open_findings` asks
    // the equality at publication instead, against the publishing host's
    // fully-reduced view, which is the only place that view exists.
    //
    // What survives is the half that is a pure function of the event
    // itself, and so gives the same answer in every order: the same finding
    // may not be inherited twice.
    let mut inherited = std::collections::BTreeSet::new();
    for f in &d.inherited_findings {
        if !inherited.insert((f.changes_event.clone(), f.finding_id.as_str().to_string())) {
            return Err(invalid(format!(
                "{}: duplicate inherited finding {}",
                env.id, f.finding_id
            )));
        }
    }

    let root = chain.root.clone();
    let key = review_key(&d.replaces);
    state.exclusive.record(&key, &env.id)?;
    match state.exclusive.disposition(&key, &env.id) {
        Disposition::Applies => {
            confirm_review_reassigned(state, &env.id, &root, d);
        }
        Disposition::Contested => {
            reset_review_to_conflict(state, &d.replaces);
        }
        // A coordinator already picked someone else. The effect must
        // not apply, and resetting to contested here would undo the
        // resolution this candidate simply arrived too late for.
        Disposition::Superseded => {}
    }
    Ok(())
}

/// The winner-confirmed effect of a reassignment: shared between the normal
/// reduction path above and `apply_conflict_resolved` (see
/// `confirm_review_closing`'s doc comment for the general rationale).
fn confirm_review_reassigned(
    state: &mut BusState,
    winner_id: &EventId,
    root: &EventId,
    d: &ReviewReassigned,
) {
    let Some(chain_mut) = state.reviews.get_mut(root) else {
        return;
    };
    chain_mut.nomination_events.push(winner_id.clone());
    chain_mut.current_nomination = winner_id.clone();
    chain_mut.current_request = d.request();
    chain_mut
        .nomination_reviewer
        .insert(winner_id.clone(), d.reviewer.clone());
    chain_mut.decline_or_withdraw_or_reassign_status = ItemStatus::Open;
    state
        .review_chain_by_nomination
        .insert(winner_id.clone(), root.clone());
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
        // See the identical comment in `apply_review_accept`: a no-op, not
        // an `Err`. Same reasoning applies here -- an authorization against
        // a nomination link the chain has since moved past from under it
        // (ordinarily, or via a reassignment this event's
        // independently-published author never observed) is inapplicable,
        // not fleet-wide-fatal.
        return Ok(());
    }
    let reviewer = chain.nomination_reviewer.get(&d.nomination).unwrap();
    if reviewer != &env.agent {
        return Err(invalid(format!(
            "{}: only the accepting reviewer may authorize a merge",
            env.id
        )));
    }
    if !chain.accepted() {
        return Err(invalid(format!(
            "{}: the named reviewer must accept the nomination before authorizing a merge",
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
    //
    // Reduction can only carry half of that. The half it can: the epoch must
    // name a real activation, and `ReviewMergeAuthorized::referenced_ids`
    // includes `merge_engine_epoch`, so `topological_order` gives it a
    // genuine dependency edge and the activation is applied before this
    // event on every host. That check is sound.
    //
    // The half it cannot: whether the epoch is still *current*.
    // `current_merge_engine_epoch` is moved by any later
    // `merge_engine.activated`, which this authorization does not reference
    // and need not have observed. Comparing against it made
    // authorization-first reduce and activation-first return `Err` for the
    // same two events -- one host wedged, one not, decided by replay order.
    // `coordinator::verify_review_merge_authorized` asks the currency
    // question at publication, against a fully-reduced state.
    if !state.merge_engine_info.contains_key(&d.merge_engine_epoch) {
        return Err(invalid(format!(
            "{}: merge_engine_epoch {} is not a known merge engine activation",
            env.id, d.merge_engine_epoch
        )));
    }
    // Extra checks beyond required are fine; required checks must all be
    // present, verified below.
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
    //
    // A blocking issue is deliberately not consulted *here*. Reduction is
    // the wrong place for the question, and not merely because the naive
    // form was fatal: `topological_order` derives its edges from `refs`
    // alone, never from `observed`, so an authorization is routinely applied
    // *before* the very issue its frontier says it saw. A causal test asked
    // during replay therefore fires or not according to the lexicographic
    // accident of the two agents' names -- and where it does fire, a host
    // that has fetched the issue cannot reduce the bus while a host that has
    // not reduces it fine, which is the outage this whole class describes.
    // `probe_ordering_decides_whether_the_observed_blocker_check_fires`
    // pins both halves of that.
    //
    // Section 10's verdict is not lost, it is asked where the question is
    // well-posed: `coordinator::verify_review_merge_authorized` refuses to
    // *publish* an authorization against a chain this host can already see
    // is blocked, and `merge_ready::check_merge_ready` re-reads it live
    // immediately before the push. Both run against a fully-reduced state
    // with no replay order to be at the mercy of. Reduction's own job is to
    // say what happened, and the authorization did happen.
    let chain_mut = state
        .review_chain_mut(&d.nomination)
        .expect("checked above");
    chain_mut.authorizations.insert(env.id.clone());
    Ok(())
}

/// AGENT_BUS_SCHEMA.md section 10: the first unresolved issue (not
/// `ItemStatus::Terminal`) whose `blocks` set names any event in `chain`'s
/// nomination chain, if any.
///
/// Asked by the two places that have a fully-reduced state and no replay
/// order to worry about: `coordinator::verify_review_merge_authorized`
/// (publication time -- may this be published at all?) and
/// `merge_ready::check_merge_ready` (AGENT_REVIEW.md section 8's pre-merge
/// gate -- may the push proceed right now?). Reduction deliberately does
/// not ask it; see `apply_review_merge_authorized` for why.
pub(crate) fn blocking_issue_for_chain(state: &BusState, chain: &ReviewChain) -> Option<EventId> {
    first_blocking_issue(state, chain)
}

/// `state.issues` is a `BTreeMap`, so "first" is a deterministic choice of
/// witness rather than whichever one a hash order happened to yield.
fn first_blocking_issue(state: &BusState, chain: &ReviewChain) -> Option<EventId> {
    let chain_members: BTreeSet<&EventId> = chain.nomination_events.iter().collect();
    for issue in state.issues.values() {
        // "Unresolved" means not yet terminally resolved/rejected -- an issue
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
    chain.merged.insert(env.id.clone());
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
    // Recorded even when a receipt already exists, rather than rejected.
    //
    // Reconciliation exists precisely for a reviewer that has gone quiet, so
    // the coordinator doing it and the reviewer publishing its own
    // `review.merged` have by construction not observed each other. Both
    // reference the authorization; neither references the other. They are
    // concurrent, both orders are valid linear extensions, and rejecting
    // whichever arrives second returned `Err` -- which, with no per-event
    // isolation in `reduce`, is every host unable to reduce the bus at all,
    // decided by fetch order.
    //
    // Recording both is the only outcome that is total *and* confluent. A
    // no-op is not: it would keep whichever receipt happened to reduce first,
    // so two hosts fetching in different orders would disagree about which
    // receipt the chain carries. And recording both is simply true -- both
    // events were published, and reduction's job is to say what happened.
    //
    // Nothing downstream is confused by two: `audit_main` asks whether *any*
    // receipt names the commit, which is exactly the question it should ask.
    // Whether a second receipt indicates something worth a human looking at
    // is an audit question, not a reduction one.
    //
    // The author's *own* prior receipt is a different thing entirely and
    // stays a hard error: publishing a second receipt while already knowing
    // about the first is not a race anybody lost, it is a caller doing
    // something incoherent, and refusing it costs nothing fleet-wide because
    // `topological_order` gives every stream its own predecessor edge -- an
    // agent's events are ordered against each other in every extension, so
    // this answer is the same on every host.
    //
    // The test is authorship, not `validate_reference`. It is tempting to
    // write "a receipt this event observed", but `coordinator::build_frontier`
    // skips the author when building a frontier (`ref_agent == *author`), and
    // `dry_run` forbids adding refs beyond `referenced_ids()`, so a real
    // envelope never carries an entry for its own stream and the frontier
    // test would silently never fire. A cross-agent duplicate is exactly the
    // concurrent case that must stay recordable; publication-time
    // `coordinator::verify_review_merge_reconciled` is where that one is
    // refused.
    let chain = state.reviews.get(&root).expect("chain exists");
    if let Some(observed) = chain
        .merged
        .iter()
        .chain(chain.reconciled.iter())
        .find(|existing| existing.agent() == env.agent)
    {
        return Err(invalid(format!(
            "{}: this agent already published receipt {observed} for this chain",
            env.id
        )));
    }
    let chain = state.reviews.get_mut(&root).expect("chain exists");
    chain.reconciled.insert(env.id.clone());
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
    // Find the exclusive-tracker key whose group contains `competing`.
    // Containment rather than equality: a further candidate may be published
    // concurrently with this very resolution, and requiring an exact match
    // made the resolution unfindable on any host that had already reduced
    // the newcomer -- see `ExclusiveTracker::key_for_competing`.
    let key = state
        .exclusive
        .key_for_competing(&d.competing.iter().cloned().collect())
        .ok_or_else(|| {
            invalid(format!(
                "{}: no unresolved conflict covers this competing set",
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
        EventData::ReviewNominationDeclined(rd) => {
            confirm_review_closing(state, &rd.nomination, "declined")
        }
        EventData::ReviewWithdrawn(rd) => {
            confirm_review_closing(state, &rd.nomination, "withdrawn")
        }
        EventData::ReviewReassigned(rd) => {
            let root = state
                .review_chain(&rd.replaces)
                .map(|c| c.root.clone())
                .ok_or_else(|| {
                    invalid(format!(
                        "{}: reassignment replaces unknown nomination {}",
                        env.id, rd.replaces
                    ))
                })?;
            confirm_review_reassigned(state, &d.selected, &root, rd);
        }
        EventData::MergeEngineActivated(_) => {
            // Mirrors `apply_merge_engine_activated`'s own winner branch: an
            // explicitly confirmed winner becomes the current epoch outright,
            // superseding the provisional reset-to-baseline every candidate
            // in the contested group applied while the race was unresolved.
            state.current_merge_engine_epoch = Some(d.selected.clone());
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
    // Gate 12's audience exactness is *not* checked here, and cannot be.
    //
    // `TopicSubscribers` and `InterfaceDependents` resolve against
    // `subscribed_topics`/`scope`, which any agent may change at any time.
    // Nothing pins them: `audience_epoch` fixes the member set, and even a
    // complete frontier fixes only that set, never where each member's
    // stream had got to. A `subscription.set` published concurrently with
    // this broadcast therefore changes the resolved answer, and rejecting on
    // that made whether the bus reduces *at all* depend on replay order.
    //
    // Nor can the disagreement be charged causally, the way it first
    // appeared it could. Reduction orders events by `refs`, never by
    // `observed`, so the deciding `subscription.set` is routinely applied
    // *after* this broadcast -- and a broadcast cannot even name it:
    // `BroadcastPublished::referenced_ids` is `supersedes` alone, so
    // `coordinator::build_frontier` produces an empty frontier for an
    // informational broadcast and `dry_run` forbids adding to it. An honest
    // publisher naming a first-time subscriber would be refused on every
    // host, permanently, while the case that is genuinely the publisher's
    // fault could never be distinguished.
    //
    // So exactness is asked at publication, by
    // `coordinator::verify_broadcast_published`, against this host's
    // fully-reduced state with no replay order in play.
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

    /// `coordinator` retires `target`, citing `previous_lifecycle` (the
    /// target's registration in these fixtures). Sequence 1 throughout:
    /// every fixture using this gives its coordinator exactly one event
    /// after its own registration.
    fn retire_env(coordinator: &Agent, target: &Agent, previous_lifecycle: &EventId) -> Envelope {
        Envelope::new(
            coordinator,
            1,
            frontier_seeing(&[previous_lifecycle]),
            &EventData::AgentRetired(AgentRetired {
                target: target.clone(),
                previous_lifecycle: previous_lifecycle.clone(),
                reason: text("no longer reachable"),
                user_authority: text("operator"),
            }),
            [],
        )
    }

    fn apply_ok(state: &mut BusState, env: &Envelope) {
        apply_event(state, env).unwrap_or_else(|e| panic!("{}: {e}", env.id));
        state.kind_of_event_insert(env.id.clone(), &env.kind);
        state.events.insert(env.id.clone(), env.clone());
        if let Some(ag) = state.agents.get_mut(&env.agent) {
            ag.next_seq = ag.next_seq.max(env.seq + 1);
        }
    }

    // ------------------------------------------------ auditor role (2.2)
    //
    // AGENT_COORDINATION_EVOLUTION.md section 2.2 and its activation gates
    // 20-23. The role's whole point is that it has *less* authority than the
    // roles around it, so most of what follows asserts refusals.

    /// A complete frontier for `state`'s current epoch that also observes
    /// `ids` -- what an `audit.reported` needs, since the report's only
    /// record of what it examined is its frontier.
    fn complete_seeing(state: &BusState, ids: &[&EventId]) -> ObservedFrontier {
        let epoch = state.roster_epoch.as_ref().expect("a roster epoch").clone();
        let entries = epoch.active_members.keys().map(|agent| {
            let through = ids
                .iter()
                .find(|id| id.agent() == *agent)
                .map(|id| (*id).clone())
                .unwrap_or_else(|| EventId::new(agent, 0));
            FrontierEntry {
                agent: agent.clone(),
                stream_tip: hash(1),
                through,
            }
        });
        ObservedFrontier::complete(&epoch, entries).expect("a complete frontier")
    }

    fn audit(state: &BusState, auditor: &Agent, seq: u64, issues: &[&EventId]) -> Envelope {
        let data = EventData::AuditReported(crate::events::AuditReported {
            inspected_commits: StringSet::from_iter([hash(7)]),
            areas: vec![text("coordination history")],
            methods: vec![text("replayed every stream against the registry")],
            limitations: vec![text("did not examine the proof surface")],
            issues: StringSet::from_iter(issues.iter().map(|i| (*i).clone())),
            summary: text("one drift found, filed as an issue"),
        });
        Envelope::new(
            auditor,
            seq,
            complete_seeing(state, issues),
            &data,
            issues.iter().map(|i| (*i).clone()),
        )
    }

    fn open_issue(opener: &Agent, seq: u64, target: &Agent) -> Envelope {
        let data = EventData::IssueOpened(IssueOpened {
            target: target.clone(),
            issue_kind: IssueKind::Bug,
            severity: Priority::Normal,
            summary: text("cross-cutting drift no workstream-local review would see"),
            code_commit: None,
            locations: vec![],
            expected: None,
            observed_behavior: None,
            reproduction: vec![],
            blocks: StringSet::default(),
            evidence: StringSet::default(),
        });
        Envelope::new(opener, seq, no_frontier(), &data, [])
    }

    /// Gate 21's `blocks` clause, and the reason it exists.
    ///
    /// `blocks` makes an issue refuse the named reviewer's own
    /// `review.merge_authorized`, and only the issue's *target* may dispose of
    /// it -- so an auditor could halt a candidate at will and could not be
    /// made to release it. Section 2.2 calls that "a unilateral or indefinite
    /// candidate veto that the named reviewer cannot dispose".
    ///
    /// Asserted from three sides, because the rule is about *who authored the
    /// issue* rather than about `blocks` in general: an auditor with a
    /// nonempty set is refused, the same auditor with an empty set is
    /// accepted, and an implementor with the identical nonempty set is
    /// accepted -- otherwise a check that simply banned `blocks` outright
    /// would pass.
    #[test]
    fn an_auditor_may_not_open_an_issue_that_blocks_a_candidate() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Reviewer),
            ("aud", Role::Auditor),
        ]);
        let (alice, bob, aud) = (a("alice"), a("bob"), a("aud"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&aud, Role::Auditor));
        let (nominate_env, _accept) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        let blocking = |opener: &Agent, seq: u64| {
            let mut d = match open_issue(opener, seq, &alice).typed_data().unwrap() {
                EventData::IssueOpened(d) => d,
                _ => unreachable!(),
            };
            d.blocks = StringSet::from_iter([nominate_env.id.clone()]);
            Envelope::new(
                opener,
                seq,
                frontier_seeing(&[&nominate_env.id]),
                &EventData::IssueOpened(d),
                [nominate_env.id.clone()],
            )
        };

        let err = apply_event(&mut state.clone(), &blocking(&aud, 1)).unwrap_err();
        assert!(
            err.to_string()
                .contains("an auditor-opened issue must carry an empty blocks set"),
            "expected the auditor blocks refusal, got: {err}"
        );

        // The same auditor, without the veto, is fine.
        apply_ok(&mut state.clone(), &open_issue(&aud, 1, &alice));

        // And an implementor may still block -- the rule is about the
        // author's role, not about `blocks`.
        apply_ok(&mut state.clone(), &blocking(&alice, 2));
    }

    /// Gate 21: "an auditor is rejected when it attempts to claim product
    /// scope, nominate or accept a candidate review, authorize or perform a
    /// merge, or attach product commit state to its identity."
    ///
    /// Each refusal already followed from an existing role check, but nothing
    /// demonstrated it, and the design states the gate as an acceptance
    /// condition rather than an implementation detail. Driven as one table so
    /// a future role change that quietly widens auditor authority fails here
    /// rather than in whichever single case someone happened to cover.
    #[test]
    fn an_auditor_is_refused_every_authority_the_design_denies_it() {
        let aud = a("aud");
        let alice = a("alice");
        let bob = a("bob");

        let fresh = || {
            let mut state = empty_state(&[
                ("aud", Role::Auditor),
                ("alice", Role::Implementor),
                ("bob", Role::Reviewer),
            ]);
            apply_ok(&mut state, &register(&aud, Role::Auditor));
            apply_ok(&mut state, &register(&alice, Role::Implementor));
            apply_ok(&mut state, &register(&bob, Role::Reviewer));
            state
        };

        // Claiming product scope.
        let scope = Envelope::new(
            &aud,
            1,
            no_frontier(),
            &EventData::ScopeSet(ScopeSet {
                base_code_commit: hash(1),
                exclusive: StringSet::from_iter([crate::scalars::PathClaim::parse(
                    "src/**".into(),
                )
                .unwrap()]),
                shared: StringSet::default(),
                exports: StringSet::default(),
                depends_on: vec![],
                note: text("auditors do not own paths"),
            }),
            [],
        );
        let err = apply_event(&mut fresh(), &scope).unwrap_err();
        assert!(
            err.to_string().contains("does not have role implementor"),
            "an auditor must not claim product scope, got: {err}"
        );

        // Attaching product commit state to its own identity, by either
        // route. `agent.status` and `progress.reported` carry separate checks
        // and only the first was covered; disabling the second survived the
        // whole suite.
        let progress_with_commit = Envelope::new(
            &aud,
            1,
            no_frontier(),
            &EventData::ProgressReported(ProgressReported {
                product_commit: Some(hash(2)),
                completed: vec![],
                current: vec![],
                next: vec![],
                blockers: vec![],
                verification: vec![],
            }),
            [],
        );
        let err = apply_event(&mut fresh(), &progress_with_commit).unwrap_err();
        assert!(
            err.to_string()
                .contains("product_commit is permitted only for an implementor"),
            "an auditor must not attach a product commit to progress, got: {err}"
        );

        // Attaching product commit state to its own identity.
        let product_state = Envelope::new(
            &aud,
            1,
            no_frontier(),
            &EventData::AgentStatus(AgentStatusEvent {
                status: LifecycleStatus::Active,
                note: text("hi"),
                product_branch: None,
                product_commit: Some(hash(2)),
            }),
            [],
        );
        let err = apply_event(&mut fresh(), &product_state).unwrap_err();
        assert!(
            err.to_string()
                .contains("product fields are permitted only for an implementor"),
            "an auditor must not carry product commit state, got: {err}"
        );

        // Nominating a candidate for review.
        let nominate = Envelope::new(
            &aud,
            1,
            no_frontier(),
            &EventData::ReviewNominated(ReviewNominated {
                authors: StringSet::from_iter([aud.clone()]),
                product_branch: Branch::parse("refs/heads/agent/aud/x".into()).unwrap(),
                reviewer: bob.clone(),
                required_checks: vec![],
                review_scope: StringSet::from_iter([crate::scalars::PathClaim::parse(
                    "src/**".into(),
                )
                .unwrap()]),
                summary: text("s"),
                target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
                evidence: StringSet::default(),
            }),
            [],
        );
        let err = apply_event(&mut fresh(), &nominate).unwrap_err();
        assert!(
            err.to_string().contains("does not have role implementor"),
            "an auditor must not nominate, got: {err}"
        );

        // Being named as the reviewer of one.
        let named_as_reviewer = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::ReviewNominated(ReviewNominated {
                authors: StringSet::from_iter([alice.clone()]),
                product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                reviewer: aud.clone(),
                required_checks: vec![],
                review_scope: StringSet::from_iter([crate::scalars::PathClaim::parse(
                    "src/**".into(),
                )
                .unwrap()]),
                summary: text("s"),
                target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
                evidence: StringSet::default(),
            }),
            [],
        );
        let err = apply_event(&mut fresh(), &named_as_reviewer).unwrap_err();
        assert!(
            err.to_string().contains("does not have role reviewer"),
            "an auditor must not be nominated as a reviewer, got: {err}"
        );

        // The remaining half of gate 21 -- accepting, authorizing, merging,
        // reconciling, and requesting changes -- needs a *live* chain, since
        // each of those checks keys off the chain's accepting reviewer rather
        // than off a role. Without a real chain these events are refused for
        // the wrong reason (unknown nomination), which would prove nothing.
        let mut with_chain = fresh();
        let (nominate_env, _accept) = nominate_and_accept(&mut with_chain, &alice, 1, &bob, 1);
        let nomination = nominate_env.id.clone();
        let seeing = frontier_seeing(&[&nomination]);
        // Some of these events demand a *complete* frontier, and would
        // otherwise be refused for that instead of for the rule under test --
        // the same way the accept row was being refused by "already
        // accepted". This one names every active member and puts alice at the
        // nomination, so it is both complete and causally sufficient.
        let epoch = with_chain.roster_epoch.as_ref().unwrap().clone();
        let complete_seeing = ObservedFrontier::complete(
            &epoch,
            epoch.active_members.keys().map(|agent| FrontierEntry {
                agent: agent.clone(),
                stream_tip: hash(1),
                through: if *agent == alice {
                    nomination.clone()
                } else {
                    EventId::new(agent, 0)
                },
            }),
        )
        .expect("a complete frontier for this epoch");

        // `review.merged` and `review.merge_reconciled` both name an
        // *authorization*, so the fixture needs a real one or they are
        // refused for citing the wrong kind of event rather than for who
        // emitted them. Bob, the legitimate reviewer, publishes it.
        let bob_auth = Envelope::new(
            &bob,
            2,
            complete_seeing.clone(),
            &EventData::ReviewMergeAuthorized(merge_authorized(
                &nomination,
                StringSet::default(),
                &[],
            )),
            [nomination.clone()],
        );
        apply_ok(&mut with_chain, &bob_auth);
        let authorization = bob_auth.id.clone();

        // Each row names the refusal it expects, not merely that *some*
        // refusal happened. Asserting `is_err()` alone was not enough: with
        // the reviewer check disabled, an auditor's `review.nomination_
        // accepted` is still refused -- by the unrelated "already accepted"
        // check further down -- so the test passed while the rule it exists
        // for was gone. An adversarial review found exactly that.
        let intrusions: Vec<(bool, &str, &str, EventData)> = vec![
            (
                false,
                "accept a review",
                "only the named reviewer may accept this nomination",
                EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                    nomination: nomination.clone(),
                    note: text(""),
                }),
            ),
            (
                false,
                "request changes on one",
                "only the accepting reviewer may request changes",
                EventData::ReviewChangesRequested(ReviewChangesRequested {
                    nomination: nomination.clone(),
                    reviewed_commit: hash(3),
                    findings: vec![finding("f1")],
                    evidence: StringSet::default(),
                }),
            ),
            (
                true,
                "authorize a merge",
                "only the accepting reviewer may authorize a merge",
                EventData::ReviewMergeAuthorized(merge_authorized(
                    &nomination,
                    StringSet::default(),
                    &[],
                )),
            ),
            (
                true,
                "record a merge",
                "only the authorizing reviewer may emit review.merged",
                EventData::ReviewMerged(ReviewMerged {
                    authorization: authorization.clone(),
                    previous_main: hash(1),
                    main_commit: hash(2),
                    product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                    reviewed_commit: hash(3),
                    summary: text("s"),
                }),
            ),
            (
                true,
                "reconcile a merge",
                // Refused on the auditor's own immutable primary role, not
                // on its roster binding -- see `require_bootstrap_
                // coordinator` for why replay may not read the live epoch.
                // Gate 21 is unaffected either way: an auditor can never
                // have registered as a coordinator.
                "aud is not a coordinator",
                EventData::ReviewMergeReconciled(ReviewMergeReconciled {
                    authorization: authorization.clone(),
                    previous_main: hash(1),
                    main_commit: hash(2),
                    product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                    reviewed_commit: hash(3),
                    reason: text("r"),
                    user_authority: text("u"),
                }),
            ),
        ];

        for (needs_complete, what, expected, data) in intrusions {
            let frontier = if needs_complete {
                complete_seeing.clone()
            } else {
                seeing.clone()
            };
            let refs: Vec<EventId> = data.referenced_ids().into_iter().collect();
            let env = Envelope::new(&aud, 1, frontier, &data, refs);
            // Each intrusion runs against its own copy, so an earlier
            // refusal cannot be what makes a later one fail.
            let err = apply_event(&mut with_chain.clone(), &env)
                .expect_err(&format!("an auditor must not {what}"))
                .to_string();
            assert!(
                err.contains(expected),
                "an auditor must not {what}, and must be refused for that reason;                  expected {expected:?}, got: {err}"
            );
        }
    }

    /// Gate 20: "an auditor can publish `audit.reported` and open issues
    /// without product scope, product authorship, nomination acceptance, or
    /// merge authority."
    #[test]
    fn an_auditor_may_open_issues_and_publish_an_audit_report() {
        let mut state = empty_state(&[("alice", Role::Implementor), ("aud", Role::Auditor)]);
        let (alice, aud) = (a("alice"), a("aud"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&aud, Role::Auditor));

        let issue = open_issue(&aud, 1, &alice);
        let issue_id = issue.id.clone();
        apply_ok(&mut state, &issue);

        let report = audit(&state, &aud, 2, &[&issue_id]);
        let report_id = report.id.clone();
        apply_ok(&mut state, &report);
        assert!(
            state.audits.contains_key(&report_id),
            "the report must be recorded as durable evidence"
        );
    }

    /// The same event from any other role is refused: the design gives
    /// fleet-wide audit authority to this role specifically. An implementor
    /// or reviewer with a fleet-wide concern raises an issue, which both
    /// already may.
    #[test]
    fn only_an_auditor_may_publish_an_audit_report() {
        for role in [Role::Implementor, Role::Reviewer, Role::Coordinator] {
            let mut state = empty_state(&[("someone", role)]);
            let someone = a("someone");
            apply_ok(&mut state, &register(&someone, role));
            let env = audit(&state, &someone, 1, &[]);
            let err = apply_event(&mut state, &env).unwrap_err();
            assert!(
                err.to_string().contains("does not have role auditor"),
                "{role} must not publish an audit report, got: {err}"
            );
        }
    }

    /// Gate 23: "a nominated reviewer can consume auditor evidence but must
    /// publish its own finding dispositions and authorization judgment."
    ///
    /// The consuming half is easy to get right by accident and easy to lose
    /// silently, so it is asserted from both sides: the reviewer *may* cite
    /// an audit report as evidence, and doing so changes nothing about what
    /// it still owes. An open finding still blocks the authorization with the
    /// audit cited; clearing it -- by the reviewer, in its own event -- is
    /// what unblocks it.
    #[test]
    fn citing_an_audit_as_evidence_does_not_discharge_a_reviewers_own_disposition() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Reviewer),
            ("aud", Role::Auditor),
        ]);
        let (alice, bob, aud) = (a("alice"), a("bob"), a("aud"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&aud, Role::Auditor));

        let report = audit(&state, &aud, 1, &[]);
        let report_id = report.id.clone();
        apply_ok(&mut state, &report);

        let (nominate_env, _accept) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let changes = Envelope::new(
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
        apply_ok(&mut state, &changes);

        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let complete = ObservedFrontier::complete(
            &epoch,
            epoch.active_members.keys().map(|agent| FrontierEntry {
                agent: agent.clone(),
                stream_tip: hash(1),
                through: if *agent == alice {
                    nominate_env.id.clone()
                } else if *agent == aud {
                    report_id.clone()
                } else {
                    EventId::new(agent, 0)
                },
            }),
        )
        .expect("a complete frontier for this epoch");

        // The reviewer authorizes, citing the audit as evidence.
        let mut authorized = merge_authorized(&nominate_env.id, StringSet::default(), &[]);
        authorized.evidence = StringSet::from_iter([report_id.clone()]);
        let env = Envelope::new(
            &bob,
            3,
            complete,
            &EventData::ReviewMergeAuthorized(authorized),
            [nominate_env.id.clone(), report_id.clone()],
        );

        let err = apply_event(&mut state, &env)
            .expect_err("an open finding must still block, audit or no audit");
        assert!(
            err.to_string().contains("finding"),
            "the reviewer still owes its own disposition, got: {err}"
        );
    }

    /// Gate 20's positive half, beyond the two events the first test covers.
    ///
    /// Over-restriction is a defect too: section 2.2 says an auditor "may
    /// read every product and event stream without claiming those paths, run
    /// analyses and validation probes, publish an audit report, and open or
    /// reassign issues". If the role were accidentally locked out of ordinary
    /// participation it would be unable to do the job the design gives it,
    /// and nothing here would have said so.
    #[test]
    fn an_auditor_retains_ordinary_participation() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Reviewer),
            ("aud", Role::Auditor),
        ]);
        let (alice, bob, aud) = (a("alice"), a("bob"), a("aud"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&aud, Role::Auditor));

        // Choose what it listens to.
        apply_ok(
            &mut state,
            &Envelope::new(
                &aud,
                1,
                no_frontier(),
                &EventData::SubscriptionSet(crate::events::SubscriptionSet {
                    topics: StringSet::from_iter([crate::scalars::CoordinationTopic::parse(
                        "release.main".into(),
                    )
                    .unwrap()]),
                }),
                [],
            ),
        );

        // Report progress -- carrying no product commit. That line is drawn
        // by `progress.reported`'s own check, which the refusal table pins
        // separately from `agent.status`'s; they are two checks, and an
        // earlier version of this comment claimed one test covered both.
        apply_ok(
            &mut state,
            &Envelope::new(
                &aud,
                2,
                no_frontier(),
                &EventData::ProgressReported(ProgressReported {
                    product_commit: None,
                    completed: vec![text("swept the coordination history")],
                    current: vec![],
                    next: vec![],
                    blockers: vec![],
                    verification: vec![text("replayed every stream")],
                }),
                [],
            ),
        );

        // Open an issue, then reassign it -- section 2.2 names both.
        //
        // The reassignment here is by the *opener*. Ordinary issue-lifecycle
        // authority (`apply.rs`'s opener-or-coordinator rule) means an
        // auditor cannot reassign an issue someone else opened, while section
        // 2.2 says "open or reassign issues" without qualification. Whether
        // the design means "issues it opened" or intends something wider is
        // unresolved; this test pins only the case both readings agree on.
        let issue = open_issue(&aud, 3, &alice);
        let issue_id = issue.id.clone();
        apply_ok(&mut state, &issue);
        apply_ok(
            &mut state,
            &Envelope::new(
                &aud,
                4,
                frontier_seeing(&[&issue_id]),
                &EventData::IssueReassigned(IssueReassigned {
                    issue: issue_id.clone(),
                    previous_assignment: issue_id.clone(),
                    previous_target: alice.clone(),
                    new_target: bob.clone(),
                    reason: text("belongs with the reviewer"),
                }),
                [issue_id.clone()],
            ),
        );
        assert_eq!(
            state.issues[&issue_id].current_target, bob,
            "an auditor may reassign an issue it opened"
        );
    }

    /// `methods` and `limitations` exist so a reader can judge what the
    /// absence of a finding is worth; a report that states neither, names no
    /// area and says nothing is durable evidence of nothing. `inspected_
    /// commits` and `issues` stay legitimately empty -- an audit of
    /// coordination history inspects no product commit, and a clean surface
    /// files no issue.
    #[test]
    fn an_audit_report_must_actually_say_something() {
        let mut state = empty_state(&[("aud", Role::Auditor)]);
        let aud = a("aud");
        apply_ok(&mut state, &register(&aud, Role::Auditor));

        let frontier = complete_seeing(&state, &[]);
        let report = |areas: Vec<Text>, methods: Vec<Text>, summary: Text| {
            Envelope::new(
                &aud,
                1,
                frontier.clone(),
                &EventData::AuditReported(crate::events::AuditReported {
                    inspected_commits: StringSet::default(),
                    areas,
                    methods,
                    limitations: vec![],
                    issues: StringSet::default(),
                    summary,
                }),
                [],
            )
        };

        for (field, env) in [
            ("areas", report(vec![], vec![text("m")], text("s"))),
            ("methods", report(vec![text("a")], vec![], text("s"))),
            (
                "summary",
                report(vec![text("a")], vec![text("m")], text("   ")),
            ),
        ] {
            let err = apply_event(&mut state.clone(), &env).unwrap_err();
            assert!(
                err.to_string().contains(&format!("must state its {field}")),
                "an empty {field} must be refused, got: {err}"
            );
        }

        // Everything stated, nothing inspected and nothing filed: a clean
        // report, and legitimate.
        apply_ok(
            &mut state,
            &report(
                vec![text("coordination history")],
                vec![text("replay")],
                text("clean"),
            ),
        );
    }

    /// Section 2.2: the report "pins the inspected product revisions and
    /// observed event frontier". The frontier is the only place it records
    /// what it observed, and a *sparse* one names just the agents the payload
    /// happens to reference -- so a clean report on a sparse frontier would
    /// pin nothing at all about the streams it claims to have examined.
    ///
    /// Every other test here builds a complete frontier, which means none of
    /// them could see the requirement being removed; this one refuses the
    /// sparse case directly.
    #[test]
    fn an_audit_report_on_a_sparse_frontier_is_refused() {
        let mut state = empty_state(&[("alice", Role::Implementor), ("aud", Role::Auditor)]);
        let (alice, aud) = (a("alice"), a("aud"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&aud, Role::Auditor));

        let sparse = Envelope::new(
            &aud,
            1,
            no_frontier(),
            &EventData::AuditReported(crate::events::AuditReported {
                inspected_commits: StringSet::default(),
                areas: vec![text("coordination history")],
                methods: vec![text("replayed every stream")],
                limitations: vec![],
                issues: StringSet::default(),
                summary: text("clean"),
            }),
            [],
        );
        let err = apply_event(&mut state, &sparse).unwrap_err();
        assert!(
            err.to_string().contains("complete frontier"),
            "a report must pin what it observed, got: {err}"
        );
    }

    /// Gate 20, at its full width: "an auditor can publish `audit.reported`
    /// and open issues without product scope, product authorship, nomination
    /// acceptance, or merge authority", and section 2.2's prose "open or
    /// reassign issues to the appropriate design steward or implementor".
    ///
    /// The narrow test above covers `issue.opened` and `audit.reported`. The
    /// rest of what an auditor must be able to do to be useful -- work an
    /// issue through its lifecycle, report progress, subscribe, acknowledge a
    /// broadcast -- was only ever confirmed by a reviewer's throwaway probe
    /// that was reverted afterwards. Over-restriction is as much a defect as
    /// over-permission, and nothing here would have caught it.
    ///
    /// Deliberately one test over one auditor: these are the operations a
    /// real auditing session performs in sequence, and running them against a
    /// single evolving state is what would expose an ordering or lifecycle
    /// restriction that each operation in isolation would miss.
    #[test]
    fn an_auditor_can_survey_report_and_work_its_own_findings() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Implementor),
            ("aud", Role::Auditor),
        ]);
        let (alice, bob, aud) = (a("alice"), a("bob"), a("aud"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&aud, Role::Auditor));

        // Report a bug against an implementor.
        let issue = open_issue(&aud, 1, &alice);
        let issue_id = issue.id.clone();
        apply_ok(&mut state, &issue);

        // Reassign it -- section 2.2 names this explicitly. Legitimate here
        // because the auditor is the opener; ordinary issue-lifecycle
        // authority (opener-or-coordinator) still applies to everyone.
        let reassign = Envelope::new(
            &aud,
            2,
            frontier_seeing(&[&issue_id]),
            &EventData::IssueReassigned(IssueReassigned {
                issue: issue_id.clone(),
                previous_assignment: issue_id.clone(),
                previous_target: alice.clone(),
                new_target: bob.clone(),
                reason: text("bob owns this surface"),
            }),
            [issue_id.clone()],
        );
        apply_ok(&mut state, &reassign);

        // Report progress, carrying no product commit -- that line is drawn
        // by `progress.reported`'s own check, pinned separately in the
        // refusal table.
        apply_ok(
            &mut state,
            &Envelope::new(
                &aud,
                3,
                no_frontier(),
                &EventData::ProgressReported(ProgressReported {
                    product_commit: None,
                    completed: vec![text("swept every stream")],
                    current: vec![],
                    next: vec![],
                    blockers: vec![],
                    verification: vec![],
                }),
                [],
            ),
        );

        // Subscribe to a coordination topic.
        apply_ok(
            &mut state,
            &Envelope::new(
                &aud,
                4,
                no_frontier(),
                &EventData::SubscriptionSet(crate::events::SubscriptionSet {
                    topics: StringSet::from_iter([crate::scalars::CoordinationTopic::parse(
                        "proof.rebuild".into(),
                    )
                    .unwrap()]),
                }),
                [],
            ),
        );

        // Work an issue that someone else targeted *at* the auditor.
        let inbound = open_issue(&alice, 1, &aud);
        let inbound_id = inbound.id.clone();
        apply_ok(&mut state, &inbound);
        apply_ok(
            &mut state,
            &Envelope::new(
                &aud,
                5,
                frontier_seeing(&[&inbound_id]),
                &EventData::IssueAcknowledged(IssueAcknowledged {
                    issue: inbound_id.clone(),
                    assignment: inbound_id.clone(),
                    note: text("looking"),
                }),
                [inbound_id.clone()],
            ),
        );
        apply_ok(
            &mut state,
            &Envelope::new(
                &aud,
                6,
                frontier_seeing(&[&inbound_id]),
                &EventData::IssueResolved(IssueResolved {
                    issue: inbound_id.clone(),
                    assignment: inbound_id.clone(),
                    summary: text("not a defect; measured and explained"),
                    fix_commit: None,
                    verification: vec![],
                }),
                [inbound_id.clone()],
            ),
        );

        // And publish the summary that ties it together.
        let env = audit(&state, &aud, 7, &[&issue_id]);
        apply_ok(&mut state, &env);
        assert!(
            state.audits.contains_key(&EventId::new(&aud, 7)),
            "the report must be recorded"
        );
    }

    /// M3: the frontier must be *validated*, not merely labelled complete.
    ///
    /// Replacing `require_complete_frontier` with a bare `FrontierKind::
    /// Complete` check left the whole suite green, so a frontier naming an
    /// unknown epoch, or omitting a member, was accepted -- pinning as little
    /// as the sparse frontier round 2 rejected. `validate_complete` exists
    /// precisely because the frontier "was constructed elsewhere and must be
    /// re-checked rather than trusted", and this is the read-time
    /// revalidation that matters for a foreign or hand-crafted envelope.
    #[test]
    fn an_audit_reports_complete_frontier_is_validated_not_merely_labelled() {
        let mut state = empty_state(&[("alice", Role::Implementor), ("aud", Role::Auditor)]);
        let (alice, aud) = (a("alice"), a("aud"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&aud, Role::Auditor));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();

        let report = |observed: ObservedFrontier| {
            Envelope::new(
                &aud,
                1,
                observed,
                &EventData::AuditReported(crate::events::AuditReported {
                    inspected_commits: StringSet::default(),
                    areas: vec![text("coordination history")],
                    methods: vec![text("replayed every stream")],
                    limitations: vec![],
                    issues: StringSet::default(),
                    summary: text("clean"),
                }),
                [],
            )
        };

        // Labelled complete, but omitting a member: rejected.
        // Built field-by-field rather than through `complete()`, which
        // validates -- the point is a frontier that only *claims* to be
        // complete, exactly what a foreign or hand-crafted envelope can carry.
        let missing_member = ObservedFrontier {
            kind: crate::frontier::FrontierKind::Complete,
            roster_epoch: epoch.id.clone(),
            entries: BTreeMap::from([(
                aud.clone(),
                FrontierEntry {
                    agent: aud.clone(),
                    stream_tip: hash(1),
                    through: EventId::new(&aud, 0),
                },
            )]),
        };
        let err = apply_event(&mut state.clone(), &report(missing_member)).unwrap_err();
        assert!(
            !err.to_string().is_empty(),
            "a frontier omitting a member must be refused"
        );

        // Labelled complete, naming an epoch nobody knows: rejected.
        let unknown_epoch = ObservedFrontier {
            kind: crate::frontier::FrontierKind::Complete,
            roster_epoch: hash(9999),
            entries: epoch
                .active_members
                .keys()
                .map(|agent| {
                    (
                        agent.clone(),
                        FrontierEntry {
                            agent: agent.clone(),
                            stream_tip: hash(1),
                            through: EventId::new(agent, 0),
                        },
                    )
                })
                .collect(),
        };
        let err = apply_event(&mut state.clone(), &report(unknown_epoch)).unwrap_err();
        assert!(
            err.to_string().contains("not a known epoch"),
            "a frontier naming an unknown epoch must be refused, got: {err}"
        );
    }

    /// M5: a list of blank strings is not content. A length-only check
    /// accepted `areas: [""]`, which is the contentless report the rule was
    /// added to refuse, wearing a list.
    #[test]
    fn an_audit_report_of_blank_entries_is_still_contentless() {
        let mut state = empty_state(&[("aud", Role::Auditor)]);
        let aud = a("aud");
        apply_ok(&mut state, &register(&aud, Role::Auditor));
        let frontier = complete_seeing(&state, &[]);

        for (field, areas, methods) in [
            ("areas", vec![text("")], vec![text("m")]),
            ("methods", vec![text("a")], vec![text("   ")]),
        ] {
            let env = Envelope::new(
                &aud,
                1,
                frontier.clone(),
                &EventData::AuditReported(crate::events::AuditReported {
                    inspected_commits: StringSet::default(),
                    areas,
                    methods,
                    limitations: vec![],
                    issues: StringSet::default(),
                    summary: text("s"),
                }),
                [],
            );
            let err = apply_event(&mut state.clone(), &env).unwrap_err();
            assert!(
                err.to_string().contains(&format!("must state its {field}")),
                "blank {field} must be refused, got: {err}"
            );
        }
    }

    /// M4: the role an agent declares must be the role the registry binds it
    /// to. Every authority check reads the declared value, while `status`
    /// prints the registry's -- so a divergence grants authority invisibly.
    #[test]
    fn a_registration_may_not_declare_a_role_the_registry_does_not_bind() {
        let mut state = empty_state(&[("aud", Role::Auditor)]);
        let aud = a("aud");
        let err = apply_event(&mut state, &register(&aud, Role::Implementor)).unwrap_err();
        assert!(
            err.to_string().contains("must match the registry"),
            "an auditor may not register as an implementor, got: {err}"
        );
        // The honest declaration still works.
        apply_ok(&mut state, &register(&aud, Role::Auditor));
    }

    /// The check is `require_self_active_role`, not merely a role
    /// comparison, and that distinction needs its own case: replacing it
    /// with a bare `primary_role` check survived the entire suite. Same
    /// failure mode `merge_ready` documents at length for reviewers -- an
    /// identity that has declared itself unavailable going on working.
    ///
    /// Note which half this exercises. The auditor stands itself down with
    /// its own `agent.status`, on its own stream, so `topological_order`'s
    /// predecessor edge orders it ahead of the later report on every host
    /// and reduction can refuse it. Being *retired* by a coordinator is the
    /// other half and is deliberately not asked here -- see
    /// `an_agent_retired_by_a_coordinator_can_still_have_its_own_history_reduced`.
    #[test]
    fn an_auditor_that_stood_itself_down_may_not_publish_a_report() {
        let mut state = empty_state(&[("aud", Role::Auditor)]);
        let aud = a("aud");
        apply_ok(&mut state, &register(&aud, Role::Auditor));
        let env = audit(&state, &aud, 1, &[]);
        apply_ok(&mut state, &env);

        apply_ok(
            &mut state,
            &Envelope::new(
                &aud,
                2,
                no_frontier(),
                &EventData::AgentStatus(AgentStatusEvent {
                    status: LifecycleStatus::Done,
                    note: text("audit complete"),
                    product_branch: None,
                    product_commit: None,
                }),
                [],
            ),
        );

        let env = audit(&state, &aud, 3, &[]);
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("has stood down"),
            "an auditor that stood itself down must not publish, got: {err}"
        );
    }

    /// The other half: an agent a *coordinator* retired must still have its
    /// own already-published history reduce.
    ///
    /// `apply_retired` requires a coordinator and forbids retiring yourself,
    /// so `retired` always arrives on somebody else's stream, causally
    /// unordered against anything the target published. Reading it during
    /// replay meant a host that had fetched the retirement failed on every
    /// one of the target's own `scope.set`, `audit.reported`,
    /// `handoff.offered` and `review.nominated` events -- and with no
    /// per-event isolation in `reduce`, that is the whole bus, permanently,
    /// from an ordinary administrative action.
    ///
    /// Both orders are asserted, because the point is that the outcome must
    /// not depend on which the host replayed first. The `retired` question
    /// is asked at publication instead
    /// (`coordinator::verify_author_active`), which
    /// `the_publication_gate_refuses_a_retired_author` pins.
    #[test]
    fn an_agent_retired_by_a_coordinator_can_still_have_its_own_history_reduced() {
        let build = |retire_first: bool| {
            let mut state = empty_state(&[("aud", Role::Auditor), ("coord1", Role::Coordinator)]);
            let (aud, coord1) = (a("aud"), a("coord1"));
            apply_ok(&mut state, &register(&aud, Role::Auditor));
            apply_ok(&mut state, &register(&coord1, Role::Coordinator));

            let report = audit(&state, &aud, 1, &[]);
            let retire = Envelope::new(
                &coord1,
                1,
                no_frontier(),
                &EventData::AgentRetired(AgentRetired {
                    target: aud.clone(),
                    previous_lifecycle: EventId::new(&aud, 0),
                    reason: text("engagement over"),
                    user_authority: text("operator"),
                }),
                [],
            );

            let order: Vec<Envelope> = if retire_first {
                vec![retire.clone(), report.clone()]
            } else {
                vec![report.clone(), retire.clone()]
            };
            reduce_onto(state, &order)
                .unwrap_or_else(|e| panic!("retire_first={retire_first} must still reduce: {e}"))
        };

        let report_first = build(false);
        let retire_first = build(true);
        assert_eq!(
            report_first.audits.len(),
            1,
            "the report must be recorded, not silently skipped"
        );
        assert_eq!(
            format!("{report_first:#?}"),
            format!("{retire_first:#?}"),
            "GATE 15/16: both valid orders must reduce to identical state"
        );
    }

    /// A report may not cite a finding that does not exist -- otherwise an
    /// audit could manufacture the appearance of filed work.
    #[test]
    fn an_audit_report_may_not_reference_an_issue_that_does_not_exist() {
        let mut state = empty_state(&[("aud", Role::Auditor)]);
        let aud = a("aud");
        apply_ok(&mut state, &register(&aud, Role::Auditor));
        let env = audit(&state, &aud, 1, &[&EventId::new(&a("alice"), 9)]);
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("unknown issue"),
            "expected an unknown-issue refusal, got: {err}"
        );

        // And an id that *is* a real event but is not an issue. Without this
        // case the existence check could look in `state.events` instead of
        // `state.issues` and no test would notice -- an adversarial review
        // made exactly that substitution and the whole suite stayed green.
        // The schema promises `issues` names `issue.opened` events; without
        // this, a report could pass off a progress note, a broadcast, or a
        // previous audit report as a filed finding.
        let not_an_issue = register(&aud, Role::Auditor).id.clone();
        assert!(
            state.events.contains_key(&not_an_issue) && !state.issues.contains_key(&not_an_issue),
            "fixture must name an id that is an event but not an issue"
        );
        let env = audit(&state, &aud, 1, &[&not_an_issue]);
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string().contains("unknown issue"),
            "a real non-issue event must not pass as a finding, got: {err}"
        );
    }

    /// AGENT_BUS_SCHEMA.md section 2: "`refs` equals exactly the unique event
    /// IDs contained in `data`."
    ///
    /// A report's issue references are event ids, so they must appear in
    /// `refs`; its inspected commits are *object* ids and must not. Pinned
    /// through `dry_run`, which is the check a self-inconsistent envelope
    /// would otherwise sail past before being committed, pushed, and then
    /// failing to reduce on every host that fetches it -- and asserted on
    /// `referenced_ids` directly as well, because the apply-level tests above
    /// never reach `dry_run` and so could not see this.
    #[test]
    fn an_audit_report_references_exactly_the_issues_it_names() {
        let mut state = empty_state(&[("alice", Role::Implementor), ("aud", Role::Auditor)]);
        let (alice, aud) = (a("alice"), a("aud"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&aud, Role::Auditor));
        let issue = open_issue(&aud, 1, &alice);
        let issue_id = issue.id.clone();
        apply_ok(&mut state, &issue);

        let report = audit(&state, &aud, 2, &[&issue_id]);
        assert_eq!(
            report.typed_data().unwrap().referenced_ids(),
            [issue_id.clone()]
                .into_iter()
                .collect::<BTreeSet<EventId>>(),
            "the named issues, and nothing else -- inspected commits are object ids"
        );
        dry_run(&state, &report).expect("a well-formed report must pass dry-run");

        // And a report naming nothing references nothing. Same sequence as
        // above: neither report is applied here, only dry-run, so the
        // auditor's next expected sequence has not moved.
        let clean = audit(&state, &aud, 2, &[]);
        assert!(
            clean.typed_data().unwrap().referenced_ids().is_empty(),
            "a clean report references no events"
        );
        dry_run(&state, &clean).expect("a clean report is still well-formed");
    }

    /// Gate 22: "an audit report cannot resolve its referenced issues or
    /// satisfy any merge finding disposition merely by describing them as
    /// closed."
    ///
    /// Both halves, and asserted *wholesale* rather than field by field. An
    /// earlier version of this test compared four hand-picked fields of the
    /// referenced issue, and an adversarial review broke it twice without
    /// failing it: once by making the report reassign every issue it named to
    /// the auditor, and once by making it clear every finding on every review
    /// chain in the fleet. Neither field was in the four.
    ///
    /// Comparing derived `Debug` is deliberate. `IssueState` and `ReviewChain`
    /// are not `PartialEq`, and widening production types for a test's
    /// convenience is the wrong trade; `Debug` covers every field, and both
    /// containers are `BTreeMap`s so the rendering is ordered and stable.
    #[test]
    fn an_audit_report_disturbs_no_issue_and_no_review_chain() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Reviewer),
            ("aud", Role::Auditor),
        ]);
        let (alice, bob, aud) = (a("alice"), a("bob"), a("aud"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&aud, Role::Auditor));

        // An issue the report will name ...
        let issue = open_issue(&aud, 1, &alice);
        let issue_id = issue.id.clone();
        apply_ok(&mut state, &issue);

        // ... and a live review chain carrying an *open* finding, which is
        // the half gate 22 calls "satisfy any merge finding disposition".
        let (nominate_env, _accept) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let changes = Envelope::new(
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
        apply_ok(&mut state, &changes);
        assert!(
            state.reviews.values().any(|c| c
                .findings
                .values()
                .any(|f| f.disposition == FindingDisposition::Open)),
            "fixture must carry an open finding, or the second half proves nothing"
        );

        let issues_before = format!("{:#?}", state.issues);
        let reviews_before = format!("{:#?}", state.reviews);

        let env = audit(&state, &aud, 2, &[&issue_id]);
        apply_ok(&mut state, &env);

        assert_eq!(
            issues_before,
            format!("{:#?}", state.issues),
            "an audit report must leave every issue exactly as it found it"
        );
        assert_eq!(
            reviews_before,
            format!("{:#?}", state.reviews),
            "an audit report must not touch a review chain or dispose of a finding"
        );
    }

    #[test]
    fn registers_an_implementor() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        assert!(state.agents.contains_key(&alice));
        assert!(state.agents[&alice].active());
    }

    /// `dry_run`'s gate-4 recheck (round-5 adversarial review): a
    /// self-inconsistent envelope -- `refs` naming a cross-agent event
    /// `observed` does not cover -- must be rejected by `dry_run` even
    /// though `apply_event` alone has no opinion on frontier coverage at
    /// all. Proves the check genuinely lives at the `dry_run` boundary
    /// (the only place a not-yet-`parse_line`-validated envelope is ever
    /// checked), not merely that some other rule happens to also reject
    /// this particular envelope.
    #[test]
    fn dry_run_rejects_a_self_inconsistent_envelope_apply_event_alone_would_accept() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));

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

        let ack = EventData::IssueAcknowledged(IssueAcknowledged {
            issue: issue_env.id.clone(),
            assignment: issue_env.id.clone(),
            note: text("on it"),
        });
        // References alice's issue cross-agent, but `observed` is empty --
        // exactly the shape `coordinator::build_frontier` could produce
        // before its own fix, and what `Envelope::parse_line` would reject
        // on any later read-back.
        let ack_env = Envelope::new(&bob, 1, no_frontier(), &ack, [issue_env.id.clone()]);

        let mut trial = state.clone();
        apply_event(&mut trial, &ack_env).expect("apply_event alone does not check gate 4");

        let err = dry_run(&state, &ack_env).unwrap_err();
        assert!(
            err.to_string()
                .contains("names an agent absent from the declared frontier"),
            "{err}"
        );
    }

    /// Round-6 adversarial review, reproduced live: `--observes`/`extra_refs`
    /// naming an id the event's own payload does not reference at all
    /// produces an envelope `Envelope::parse_line` would reject on every
    /// future read (its `refs mismatch` check requires `refs == data.
    /// referenced_ids()` exactly), even though the frontier itself has real
    /// coverage for that id -- so gate 4 alone (the previous fix) does not
    /// catch it. Before this fix a plain `agent.status` submitted with an
    /// unrelated `--observes` id committed and pushed successfully, then
    /// permanently corrupted that stream for every future reader.
    #[test]
    fn dry_run_rejects_extra_refs_the_payload_does_not_itself_reference() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        let bob_reg = register(&bob, Role::Implementor);
        apply_ok(&mut state, &bob_reg);

        let status_data = EventData::AgentStatus(AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: text("hi"),
            product_branch: None,
            product_commit: None,
        });
        // A real, existing, in-frontier cross-agent id -- gate 4 alone would
        // happily accept this -- but `agent.status` doesn't reference
        // anything at all, so this is still a structural mismatch.
        let observed = frontier_seeing(&[&bob_reg.id]);
        let status_env = Envelope::new(&alice, 1, observed, &status_data, [bob_reg.id.clone()]);

        let mut trial = state.clone();
        apply_event(&mut trial, &status_env)
            .expect("apply_event alone has no opinion on refs equality");

        let err = dry_run(&state, &status_env).unwrap_err();
        assert!(err.to_string().contains("refs mismatch"), "{err}");
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

    /// Round-4 adversarial review, Critical finding: two coordinators on
    /// different hosts, neither observing the other, can each validly
    /// retire the same silently-vanished target, each citing the same
    /// `previous_lifecycle` -- exactly the "silent death" scenario
    /// `agent.retired` exists for. The second one to reduce must be a
    /// no-op, not a hard `Err` that (via `reduce()`'s bare `?`) would
    /// permanently break reduction of the entire bus.
    #[test]
    fn ignores_a_second_retirement_racing_against_the_first() {
        let coord_a = a("coord-a");
        let coord_b = a("coord-b");
        let worker = a("worker1");
        let mut state = empty_state(&[
            ("coord-a", Role::Coordinator),
            ("coord-b", Role::Coordinator),
        ]);
        apply_ok(&mut state, &register(&coord_a, Role::Coordinator));
        apply_ok(&mut state, &register(&coord_b, Role::Coordinator));
        apply_ok(&mut state, &register(&worker, Role::Implementor));
        let previous_lifecycle = EventId::new(&worker, 0);

        let retire_data = |reason: &str| {
            EventData::AgentRetired(AgentRetired {
                target: worker.clone(),
                previous_lifecycle: previous_lifecycle.clone(),
                reason: text(reason),
                user_authority: text("the user"),
            })
        };
        let first_env = Envelope::new(&coord_a, 1, no_frontier(), &retire_data("silent"), []);
        apply_ok(&mut state, &first_env);
        assert!(state.agents[&worker].retired);
        assert_eq!(state.agents[&worker].last_lifecycle_event, first_env.id);

        let second_env = Envelope::new(&coord_b, 1, no_frontier(), &retire_data("silent"), []);
        apply_ok(&mut state, &second_env);
        // The second, stale retirement must not have overwritten the
        // already-recorded lifecycle event.
        assert_eq!(state.agents[&worker].last_lifecycle_event, first_env.id);
    }

    /// Companion to the above for `agent.resumed`: a returning agent's
    /// self-published resumption, built against a `previous_lifecycle` that
    /// a concurrent (unobserved) coordinator retirement has since moved
    /// past, must be a no-op rather than fleet-wide-fatal.
    #[test]
    fn ignores_a_resumption_against_a_stale_previous_lifecycle() {
        let coord1 = a("coord1");
        let worker = a("worker1");
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        apply_ok(&mut state, &register(&worker, Role::Implementor));

        let retire_env = Envelope::new(
            &coord1,
            1,
            no_frontier(),
            &EventData::AgentRetired(AgentRetired {
                target: worker.clone(),
                previous_lifecycle: EventId::new(&worker, 0),
                reason: text("silent"),
                user_authority: text("the user"),
            }),
            [],
        );
        apply_ok(&mut state, &retire_env);
        assert!(state.agents[&worker].retired);

        // worker never observed the retirement and resumes against its own
        // stale last-known lifecycle event.
        let resume_env = Envelope::new(
            &worker,
            1,
            no_frontier(),
            &EventData::AgentResumed(AgentResumed {
                previous_lifecycle: EventId::new(&worker, 0),
                reason: text("back online"),
                user_authority: text("the user"),
            }),
            [],
        );
        apply_ok(&mut state, &resume_env);
        assert!(
            state.agents[&worker].retired,
            "the stale resumption must not have undone the real retirement"
        );
        assert_eq!(state.agents[&worker].last_lifecycle_event, retire_env.id);
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
        // Round-4 adversarial review: `reset_issue_to_conflict` clears
        // `resolution_summary` alongside `status` -- the provisionally-
        // applied resolve's summary must not linger once the race resets
        // the issue back to neutral.
        assert_eq!(state.issues[&issue_env.id].resolution_summary, None);
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

    /// A reviewer retiring concurrently with a nomination naming it must not
    /// make the bus unreducible.
    ///
    /// `active()` reads `status` and `retired`, both moved by events on the
    /// reviewer's *own* stream. A nomination references neither and need not
    /// have observed either, so charging the nominator for them made the
    /// nomination fatal on a host that had fetched the retirement and
    /// harmless on one that had not -- the same two events, one host unable
    /// to read the bus.
    ///
    /// The role half is still checked here, and is sound: `primary_role` is
    /// fixed by `agent.registered` at sequence zero, and `topological_order`
    /// sorts every sequence-zero event ahead of all others.
    ///
    /// Pairs with `the_publication_gate_refuses_an_inactive_participant`,
    /// which is where the liveness rule now lives.
    #[test]
    fn a_reviewer_retiring_concurrently_with_a_nomination_still_reduces() {
        let build = |retire_first: bool| {
            let mut state = empty_state(&[("alice", Role::Implementor), ("bob", Role::Reviewer)]);
            let (alice, bob) = (a("alice"), a("bob"));
            apply_ok(&mut state, &register(&alice, Role::Implementor));
            apply_ok(&mut state, &register(&bob, Role::Reviewer));

            let retire = Envelope::new(
                &bob,
                1,
                no_frontier(),
                &EventData::AgentStatus(AgentStatusEvent {
                    status: LifecycleStatus::Done,
                    note: text("handing over"),
                    product_branch: None,
                    product_commit: None,
                }),
                [],
            );
            let nominate = Envelope::new(
                &alice,
                1,
                no_frontier(),
                &EventData::ReviewNominated(review_request(&[&alice], &bob)),
                [],
            );

            let order: Vec<Envelope> = if retire_first {
                vec![retire.clone(), nominate.clone()]
            } else {
                vec![nominate.clone(), retire.clone()]
            };
            reduce_onto(state, &order)
                .unwrap_or_else(|e| panic!("retire_first={retire_first} must still reduce: {e}"))
        };

        let nominate_first = build(false);
        let retire_first = build(true);
        assert_eq!(
            nominate_first.reviews.len(),
            1,
            "the nomination must be recorded, not silently skipped"
        );
        assert_eq!(
            format!("{nominate_first:#?}"),
            format!("{retire_first:#?}"),
            "GATE 15/16: both valid orders must reduce to identical state"
        );
    }

    /// The role half of the same check is not weakened: naming an agent that
    /// is registered as something else is still refused during replay,
    /// because `primary_role` cannot move.
    #[test]
    fn a_nomination_naming_a_non_reviewer_is_still_refused() {
        let mut state = empty_state(&[("alice", Role::Implementor), ("bob", Role::Implementor)]);
        let (alice, bob) = (a("alice"), a("bob"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        let err = apply_event(
            &mut state,
            &Envelope::new(
                &alice,
                1,
                no_frontier(),
                &EventData::ReviewNominated(review_request(&[&alice], &bob)),
                [],
            ),
        )
        .expect_err("an implementor cannot be nominated as the reviewer");
        assert!(err.to_string().contains("does not have role"), "{err}");
    }

    /// A third claim published concurrently with a `lifecycle.conflict_
    /// resolved` must not wedge the bus -- in either order.
    ///
    /// This pair was the worst of the reduction-DoS class because it was
    /// fatal *both* ways round, not merely order-dependent:
    ///
    ///   resolution first -> `ExclusiveTracker::record` refused the newcomer,
    ///                       because the key already had a resolved
    ///                       disposition it had not observed;
    ///   newcomer first   -> `key_with_exact_group` required the tracker's
    ///                       group to equal the coordinator's `competing` set
    ///                       exactly, and the newcomer had grown it, so the
    ///                       resolution could not find its own key.
    ///
    /// So whichever order a host replayed, some host somewhere returned
    /// `Err` from `reduce` and could not read the bus at all. The coordinator
    /// naming only the racers it could see is not a defect on its part --
    /// the newcomer is concurrent with the resolution itself, and no amount
    /// of care lets the coordinator name an event that does not exist yet.
    #[test]
    fn a_third_claim_racing_a_conflict_resolution_reduces_in_either_order() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let dave = a("dave");
        let coord1 = a("coord1");
        let coord2 = a("coord2");

        let issue_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::IssueOpened(IssueOpened {
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
            }),
            [],
        );

        let reassign = |who: &Agent, seq: u64, to: &Agent, why: &str| {
            Envelope::new(
                who,
                seq,
                no_frontier(),
                &EventData::IssueReassigned(IssueReassigned {
                    issue: issue_env.id.clone(),
                    previous_assignment: issue_env.id.clone(),
                    previous_target: bob.clone(),
                    new_target: to.clone(),
                    reason: text(why),
                }),
                [issue_env.id.clone()],
            )
        };
        // Three agents entitled to reassign this issue: its opener and two
        // coordinators. None has observed the others.
        let by_alice = reassign(&alice, 2, &carol, "r1");
        let by_coord1 = reassign(&coord1, 1, &dave, "r2");
        let by_coord2 = reassign(&coord2, 1, &bob, "r3");

        // coord1 resolves, naming only the two racers it could see. `by_coord2`
        // is concurrent with this event.
        let resolve_env = Envelope::new(
            &coord1,
            2,
            frontier_seeing(&[&by_alice.id]),
            &EventData::LifecycleConflictResolved(LifecycleConflictResolved {
                root: by_alice.id.clone(),
                competing: StringSet::from_iter([by_alice.id.clone(), by_coord1.id.clone()]),
                selected: by_alice.id.clone(),
                reason: text("alice opened it and picked first"),
                user_authority: text("operator"),
            }),
            [by_alice.id.clone(), by_coord1.id.clone()],
        );

        let run = |newcomer_first: bool| {
            let mut state = empty_state(&[
                ("alice", Role::Implementor),
                ("bob", Role::Implementor),
                ("carol", Role::Implementor),
                ("coord1", Role::Coordinator),
                ("coord2", Role::Coordinator),
                ("dave", Role::Implementor),
            ]);
            for (name, role) in [
                ("alice", Role::Implementor),
                ("bob", Role::Implementor),
                ("carol", Role::Implementor),
                ("dave", Role::Implementor),
                ("coord1", Role::Coordinator),
                ("coord2", Role::Coordinator),
            ] {
                apply_ok(&mut state, &register(&a(name), role));
            }
            apply_ok(&mut state, &issue_env);
            apply_ok(&mut state, &by_alice);
            apply_ok(&mut state, &by_coord1);

            let tail: Vec<Envelope> = if newcomer_first {
                vec![by_coord2.clone(), resolve_env.clone()]
            } else {
                vec![resolve_env.clone(), by_coord2.clone()]
            };
            reduce_onto(state, &tail).unwrap_or_else(|e| {
                panic!("newcomer_first={newcomer_first} must still reduce: {e}")
            })
        };

        let resolution_first = run(false);
        let newcomer_first = run(true);

        // The resolution stands in both, and the late claim did not drag the
        // issue back into conflict.
        for (label, state) in [
            ("resolution first", &resolution_first),
            ("newcomer first", &newcomer_first),
        ] {
            let issue = &state.issues[&issue_env.id];
            assert_eq!(
                issue.current_target, carol,
                "{label}: the coordinator's selected winner must hold"
            );
            assert_ne!(
                issue.status,
                ItemStatus::LifecycleConflict,
                "{label}: a claim that arrived after the resolution must not reopen the conflict"
            );
        }
        assert_eq!(
            format!("{resolution_first:#?}"),
            format!("{newcomer_first:#?}"),
            "GATE 15/16: both valid orders must reduce to identical state"
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

    /// Shared fixture for the `apply_conflict_resolved` input-validation
    /// tests below: a real, currently-contested issue.resolved vs.
    /// issue.reassigned race, with `coord1` registered and ready to author
    /// a `lifecycle.conflict_resolved`. Returns `(state, resolve_env.id,
    /// reassign_env.id, coord1)`.
    fn contested_issue_race() -> (BusState, EventId, EventId, Agent) {
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
        (state, resolve_env.id, reassign_env.id, coord1)
    }

    /// Round-3 adversarial review, Significant finding: `apply_conflict_
    /// resolved`'s four input-validation guards had no negative tests at
    /// all -- only the happy path was ever exercised. A wrong
    /// implementation of any one of them (e.g. `key_with_exact_group`
    /// matching on a subset instead of the exact set) would let a
    /// coordinator "resolve" a conflict that doesn't structurally exist,
    /// with zero test failures.
    #[test]
    fn conflict_resolved_rejects_a_competing_set_with_fewer_than_two_members() {
        let (mut state, resolve_id, _reassign_id, coord1) = contested_issue_race();
        let resolved_data = EventData::LifecycleConflictResolved(LifecycleConflictResolved {
            root: resolve_id.clone(),
            competing: StringSet::from_iter([resolve_id.clone()]),
            selected: resolve_id.clone(),
            reason: text("user said so"),
            user_authority: text("the user"),
        });
        let env = Envelope::new(
            &coord1,
            1,
            frontier_seeing(&[&resolve_id]),
            &resolved_data,
            [resolve_id],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("competing must have at least two members"),
            "{err}"
        );
    }

    #[test]
    fn conflict_resolved_rejects_a_selected_id_not_in_competing() {
        let (mut state, resolve_id, reassign_id, coord1) = contested_issue_race();
        let bogus = EventId::new(&a("nobody"), 99);
        let resolved_data = EventData::LifecycleConflictResolved(LifecycleConflictResolved {
            root: resolve_id.clone(),
            competing: StringSet::from_iter([resolve_id.clone(), reassign_id.clone()]),
            selected: bogus,
            reason: text("user said so"),
            user_authority: text("the user"),
        });
        let env = Envelope::new(
            &coord1,
            1,
            frontier_seeing(&[&resolve_id, &reassign_id]),
            &resolved_data,
            [resolve_id, reassign_id],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("selected must be a member of competing"),
            "{err}"
        );
    }

    #[test]
    fn conflict_resolved_rejects_a_competing_set_that_matches_no_unresolved_conflict() {
        let (mut state, resolve_id, _reassign_id, coord1) = contested_issue_race();
        // A syntactically valid two-member competing set (satisfies the
        // first two guards) that no real conflict's group covers --
        // `resolve_id` paired with an unrelated, never-contested event id.
        // Containment is what the lookup asks now, and an id that was never
        // a candidate at all is not contained in any group, so naming one
        // still fails. Only a *concurrent* candidate widening a group is
        // tolerated, and that one is a genuine member of it.
        let unrelated = EventId::new(&a("nobody"), 0);
        let resolved_data = EventData::LifecycleConflictResolved(LifecycleConflictResolved {
            root: resolve_id.clone(),
            competing: StringSet::from_iter([resolve_id.clone(), unrelated.clone()]),
            selected: resolve_id.clone(),
            reason: text("user said so"),
            user_authority: text("the user"),
        });
        let env = Envelope::new(
            &coord1,
            1,
            frontier_seeing(&[&resolve_id]),
            &resolved_data,
            [resolve_id, unrelated],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("no unresolved conflict covers this competing set"),
            "{err}"
        );
    }

    // Note: `apply_conflict_resolved`'s fourth guard --
    // `state.events.get(&d.selected)` being `None` -- has no reachable test
    // construction given the current invariants: `selected` must pass the
    // "member of `competing`" guard, and `competing` must exactly match a
    // real `state.exclusive` group (guard three) for reduction to reach
    // this point at all. Every `exclusive.record(...)` call site in this
    // file (grep `exclusive.record`) is immediately followed only by an
    // infallible `winner()`/effect step before returning `Ok(())`, so any
    // event id ever recorded into an exclusive group is unconditionally
    // also inserted into `state.events` by the same `reduce()`/
    // `reduce_onto()` iteration. `selected` therefore cannot simultaneously
    // be a real group member and an unknown event under any input this
    // guard could actually see; it is defensive-only, matching the
    // `Some`/never-`None` pattern the round-3 test-attacking review judged
    // acceptable to leave uncovered elsewhere in this file.

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
            std::collections::BTreeSet::from([authorize_env.id.clone()])
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

    /// Regression test for round-2 adversarial review's Significant finding:
    /// `apply_conflict_resolved`'s match had no arm for the review
    /// decline/withdraw/reassign exclusive set, so a chain stuck in
    /// `LifecycleConflict` (see
    /// `review_decline_and_reassign_race_produces_a_lifecycle_conflict`
    /// above) could never actually be resolved -- a coordinator's
    /// `lifecycle.conflict_resolved` naming a winner would hit the
    /// catch-all "not an exclusive-transition winner this helper knows how
    /// to confirm" error, a permanent dead end.
    #[test]
    fn lifecycle_conflict_resolved_confirms_a_review_reassign_winner() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let coord1 = a("coord1");

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

        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&carol, Role::Reviewer));
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        apply_ok(&mut state, &nominate_env);
        apply_ok(&mut state, &decline_env);
        apply_ok(&mut state, &reassign_env);
        assert_eq!(
            state
                .review_chain(&nominate_env.id)
                .unwrap()
                .decline_or_withdraw_or_reassign_status,
            ItemStatus::LifecycleConflict
        );

        let resolved_data = EventData::LifecycleConflictResolved(LifecycleConflictResolved {
            root: decline_env.id.clone(),
            competing: StringSet::from_iter([decline_env.id.clone(), reassign_env.id.clone()]),
            selected: reassign_env.id.clone(),
            reason: text("user said so"),
            user_authority: text("the user"),
        });
        let resolved_env = Envelope::new(
            &coord1,
            1,
            frontier_seeing(&[&decline_env.id, &reassign_env.id]),
            &resolved_data,
            [decline_env.id.clone(), reassign_env.id.clone()],
        );
        apply_ok(&mut state, &resolved_env);

        let chain = state.review_chain(&nominate_env.id).unwrap();
        assert_eq!(
            chain.decline_or_withdraw_or_reassign_status,
            ItemStatus::Open
        );
        assert_eq!(chain.current_nomination, reassign_env.id);
        assert_eq!(chain.nomination_reviewer[&reassign_env.id], carol);
        assert!(!state.exclusive.is_contested(&reassign_env.id));
    }

    /// Companion to the above for the merge-engine-epoch exclusive group:
    /// once a race has left `current_merge_engine_epoch` at the provisional
    /// pre-race baseline (see
    /// `merge_engine_race_resets_current_epoch_to_the_pre_race_baseline`),
    /// an explicit `lifecycle.conflict_resolved` must be able to select a
    /// definitive winner rather than hitting the same catch-all dead end.
    #[test]
    fn lifecycle_conflict_resolved_confirms_a_merge_engine_epoch_winner() {
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
        let candidate_b = Envelope::new(
            &coord2,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(merge_engine_activated(&genesis)),
            [],
        );
        apply_ok(&mut state, &candidate_b);
        assert_eq!(state.current_merge_engine_epoch, Some(genesis.clone()));
        assert!(state.exclusive.is_contested(&candidate_a.id));

        let resolved_data = EventData::LifecycleConflictResolved(LifecycleConflictResolved {
            root: candidate_a.id.clone(),
            competing: StringSet::from_iter([candidate_a.id.clone(), candidate_b.id.clone()]),
            selected: candidate_b.id.clone(),
            reason: text("user said so"),
            user_authority: text("the user"),
        });
        let resolved_env = Envelope::new(
            &coord1,
            2,
            frontier_seeing(&[&candidate_a.id, &candidate_b.id]),
            &resolved_data,
            [candidate_a.id.clone(), candidate_b.id.clone()],
        );
        apply_ok(&mut state, &resolved_env);

        assert_eq!(
            state.current_merge_engine_epoch,
            Some(candidate_b.id.clone())
        );
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
    /// disposal attempt by the agent that already made one: `apply_handoff_
    /// terminal` routes every disposal through the same `ExclusiveTracker`
    /// used for issue/dependency/review terminal transitions, and a second
    /// claim from the same agent is hard-rejected outright by
    /// `ExclusiveTracker::record` -- it never gets the chance to become a
    /// second, genuinely concurrent candidate the way an
    /// unaware-of-each-other race would.
    ///
    /// Only the receiver may accept or decline, so both disposals here are
    /// necessarily bob's. That is what keeps this rejection sound: a stream
    /// is single-writer, so bob's two events are ordered against each other
    /// on every host. The tracker no longer refuses a *cross-agent* claim on
    /// the frontier, because reduction cannot ask that question -- see
    /// `ExclusiveTracker::record`.
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
            err.to_string()
                .contains("already claimed the same predecessor"),
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

    /// A coordinator-authored event, reduced against a later roster epoch
    /// that no longer lists its author.
    ///
    /// This is the whole-fleet outage `require_bootstrap_coordinator`'s doc
    /// describes, reproduced before it was fixed: the *identical* envelope
    /// reduced `Ok(())` under the epoch that was live when it was published
    /// and `Err("coord1 is not a coordinator in the current roster epoch")`
    /// under a later one. Since `sync::reduce_local` re-reduces every event
    /// from scratch on every read against the registry *tip*, "a later
    /// epoch" is what every host has within moments of any retirement,
    /// succession, or host move -- and `reduce` propagates with a bare `?`,
    /// so one such epoch would have made the entire bus permanently
    /// unreadable everywhere, from an ordinary administrative act.
    ///
    /// Falsification: restoring the `state.is_bootstrap_coordinator(a)`
    /// check in `require_bootstrap_coordinator` fails the second assertion
    /// with exactly that message.
    #[test]
    fn a_later_epoch_dropping_a_coordinator_cannot_unreduce_its_history() {
        let reduce_under_epoch_dropping_coord1 = |drop_coord1: bool| -> AbResult<()> {
            let mut state =
                empty_state(&[("coord1", Role::Coordinator), ("dave", Role::Implementor)]);
            let coord1 = a("coord1");
            let dave = a("dave");
            apply_ok(&mut state, &register(&coord1, Role::Coordinator));
            let dave_reg = register(&dave, Role::Implementor);
            apply_ok(&mut state, &dave_reg);
            if drop_coord1 {
                // Exactly what `registry::propose_transition` writes when a
                // coordinator is retired out of the roster: a child epoch
                // without it. Nothing rewrites the event below, which keeps
                // naming (and was authored under) the parent epoch.
                let old = state.roster_epoch.as_ref().unwrap().clone();
                let mut members = old.active_members.clone();
                members.remove(&coord1);
                let new_epoch = old.child(hash(1000), members);
                state
                    .known_epochs
                    .insert(new_epoch.id.clone(), new_epoch.clone());
                state.roster_epoch = Some(new_epoch);
            }
            apply_event(&mut state, &retire_env(&coord1, &dave, &dave_reg.id))
        };
        reduce_under_epoch_dropping_coord1(false)
            .expect("the epoch that was live at publication reduces it");
        reduce_under_epoch_dropping_coord1(true)
            .expect("a later epoch that dropped coord1 must reduce it identically");
    }

    /// The same event, reduced after its author was retired by *another*
    /// coordinator.
    ///
    /// Distinct from the sibling above because it needs no registry change
    /// at all: `agent.retired` is an ordinary event on someone else's
    /// stream, causally unordered against this one, so asking `active()`
    /// during replay made the answer a function of fetch order. See
    /// `the_order_of_a_retirement_against_its_targets_own_events_does_not_matter`
    /// for the confluence half, which is what makes this a gate-15/16
    /// violation and not merely a policy choice.
    #[test]
    fn a_coordinator_retired_by_another_cannot_unreduce_its_own_history() {
        let mut state = empty_state(&[("coord1", Role::Coordinator), ("dave", Role::Implementor)]);
        let coord1 = a("coord1");
        let dave = a("dave");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let dave_reg = register(&dave, Role::Implementor);
        apply_ok(&mut state, &dave_reg);
        state.agents.get_mut(&coord1).expect("registered").retired = true;
        apply_event(&mut state, &retire_env(&coord1, &dave, &dave_reg.id))
            .expect("a retired author's already-published event still reduces");
    }

    /// The confluence half of the two tests above, and the reason this is a
    /// gate-15/16 violation rather than a policy choice: `coord2` retires
    /// `coord1` while `coord1` independently retires `dave`, neither having
    /// observed the other (they are on separate single-writer streams,
    /// published without cross-observation -- section 2.1). Both orderings
    /// are valid linear extensions of the same causal partial order, so
    /// both must reduce, and to byte-identical state.
    ///
    /// Driven through `reduce_onto`, the real incremental path two hosts
    /// actually take when they fetch the two streams in opposite orders --
    /// which is the only way to *pick* an order, since `reduce` picks its
    /// own. Before the fix, `retire_coord1`-first reduced to `Err` and the
    /// other order to `Ok`: one host's bus became unreadable and the
    /// other's did not, decided purely by fetch order.
    #[test]
    fn a_retirement_racing_its_targets_own_coordinator_event_reduces_in_either_order() {
        let reduce_in_order = |retire_coord1_first: bool| -> AbResult<BusState> {
            let mut state = empty_state(&[
                ("coord1", Role::Coordinator),
                ("coord2", Role::Coordinator),
                ("dave", Role::Implementor),
            ]);
            let (coord1, coord2, dave) = (a("coord1"), a("coord2"), a("dave"));
            let coord1_reg = register(&coord1, Role::Coordinator);
            apply_ok(&mut state, &coord1_reg);
            apply_ok(&mut state, &register(&coord2, Role::Coordinator));
            let dave_reg = register(&dave, Role::Implementor);
            apply_ok(&mut state, &dave_reg);

            let retire_coord1 = retire_env(&coord2, &coord1, &coord1_reg.id);
            let retire_dave = retire_env(&coord1, &dave, &dave_reg.id);
            let order: Vec<Envelope> = if retire_coord1_first {
                vec![retire_coord1, retire_dave]
            } else {
                vec![retire_dave, retire_coord1]
            };
            reduce_onto(state, &order)
        };
        let retire_first = reduce_in_order(true).expect("the bus must still reduce");
        let retire_last = reduce_in_order(false).expect("the bus must still reduce");
        assert!(
            retire_first.agents[&a("dave")].retired,
            "the retired coordinator's own already-published retirement still took effect"
        );
        // `events`/`kind_of_event` are keyed by event id and `next_seq` by
        // agent, so the whole reduced state is order-insensitive here and
        // the wide comparison is the honest one (see
        // `two_coordinators_reconciling_the_same_authorization_converge`
        // for why a narrow one hides real order-dependence).
        assert_eq!(
            format!("{retire_first:#?}"),
            format!("{retire_last:#?}"),
            "both valid orders must converge on the same state"
        );
    }

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

    /// The reduction half of the pair that replaced
    /// `schema_activated_requires_a_strictly_increasing_version`: a
    /// non-advancing activation is *accepted* by `apply` and subsumed by the
    /// higher version, rather than being an `Err` that `reduce`'s bare `?`
    /// turns into a permanently unreducible bus. The refusal half moved to
    /// `coordinator::verify_schema_activation_advances`, pinned by
    /// `drain_outbox_rejects_a_schema_activation_that_does_not_advance`
    /// -- see `probe3`'s regression tests below for why (round-9 sweep, C3).
    #[test]
    fn schema_activated_takes_the_maximum_rather_than_refusing_a_lower_version() {
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
        let first_env = Envelope::new(&coord1, 1, complete_frontier(&epoch), &activate(3), []);
        apply_ok(&mut state, &first_env);
        assert_eq!(state.activated_schema_version, 3);

        let same_version_env =
            Envelope::new(&coord1, 2, complete_frontier(&epoch), &activate(3), []);
        apply_ok(&mut state, &same_version_env);
        assert_eq!(state.activated_schema_version, 3);

        let lower_version_env =
            Envelope::new(&coord1, 3, complete_frontier(&epoch), &activate(1), []);
        apply_ok(&mut state, &lower_version_env);
        assert_eq!(
            state.activated_schema_version, 3,
            "a lower activation is subsumed, never applied and never fatal"
        );

        let higher_version_env =
            Envelope::new(&coord1, 4, complete_frontier(&epoch), &activate(4), []);
        apply_ok(&mut state, &higher_version_env);
        assert_eq!(
            state.activated_schema_version, 4,
            "and the handler still actually records a genuine advance"
        );
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
        // Not `coord1:0` (coord1's own registration): that is the
        // legitimate genesis-activation anchor (see `apply_merge_engine_
        // activated`'s bootstrap exception) and must succeed, not fail --
        // covered separately by
        // `merge_engine_activated_genesis_bootstraps_from_a_real_registration`.
        // A bogus, entirely unrelated id is a genuinely unknown epoch.
        let bogus = EventId::new(&a("nobody"), 5);
        let env = Envelope::new(
            &coord1,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(merge_engine_activated(&bogus)),
            [],
        );
        let err = apply_event(&mut state, &env).unwrap_err();
        assert!(
            err.to_string()
                .contains("is not a known prior engine activation"),
            "{err}"
        );
    }

    /// Round-4-follow-up Critical finding: `bootstrap::genesis` never
    /// itself emits a `merge_engine.activated` event (it only records
    /// `merge_engine`/`merge_engine_version` as static config metadata), so
    /// a fresh bus had no production path that could ever seed a first
    /// `merge_engine_info` entry -- every existing test reached one only
    /// via a test-only seeding helper (`seed_merge_engine_genesis`) that
    /// has no real-world equivalent. Without the bootstrap exception this
    /// test proves, `current_merge_engine_epoch` could never become `Some`
    /// on any real bus, and `review.merge_authorized` (which requires its
    /// own `merge_engine_epoch` to match the currently selected one) could
    /// therefore never be validly published at all: the crate's own core
    /// feature was unreachable from a genuine cold start.
    #[test]
    fn merge_engine_activated_genesis_bootstraps_from_a_real_registration() {
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        assert!(state.merge_engine_info.is_empty());

        let env = Envelope::new(
            &coord1,
            1,
            complete_frontier(&epoch),
            &EventData::MergeEngineActivated(merge_engine_activated(&EventId::new(&coord1, 0))),
            [],
        );
        apply_ok(&mut state, &env);
        assert_eq!(state.current_merge_engine_epoch, Some(env.id.clone()));
        assert!(state.merge_engine_info.contains_key(&env.id));
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

    /// Building on a contested predecessor must not be fatal to reduction.
    ///
    /// `is_contested` reads `ExclusiveTracker` group membership, which grows
    /// as concurrent candidates reduce. Nothing `downstream` carries
    /// references `candidate_b` -- the event that makes its predecessor
    /// contested -- so reducing `candidate_b` first made `downstream` fatal
    /// while reducing it second let `downstream` through. Same events, one
    /// host unable to read the bus and one not.
    ///
    /// The rule itself is sound and is not dropped: it is asked at
    /// publication by `coordinator::verify_predecessor_not_contested`, where
    /// the state is the publishing host's own fully-reduced view. See
    /// `the_publication_gate_refuses_a_contested_predecessor` for that half;
    /// this test and that one are a pair, and either alone reads like a
    /// regression.
    #[test]
    fn building_on_a_contested_predecessor_still_reduces() {
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
        apply_event(&mut state, &downstream)
            .expect("a contested predecessor must not make the bus unreducible");
        // And it is recorded, rather than quietly dropped.
        assert!(
            state.exclusive.is_contested(&candidate_a.id),
            "the underlying race is untouched by the downstream event"
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
    fn a_dependency_ack_against_a_superseded_assignment_reduces_and_is_recorded() {
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
        // It reduces -- which is the property that failed on the live bus --
        // and it is *recorded against the assignment it names*, which is what
        // keeps the field a pure function of history. It must not touch the
        // current assignment, and must not make the current assignment look
        // acknowledged.
        let before_current = state.dependencies[&dep_env.id].current_assignment.clone();
        apply_event(&mut state, &ack_env).expect("a superseded ack is inapplicable, not invalid");
        let dep = &state.dependencies[&dep_env.id];
        assert!(
            dep.acknowledged_assignments.contains(&dep_env.id),
            "the historical acknowledgement must be recorded"
        );
        assert_eq!(
            dep.current_assignment, before_current,
            "a superseded acknowledgement must not move the current assignment"
        );
        assert!(
            !dep.acknowledged(),
            "the current assignment must still read unacknowledged"
        );
    }

    /// The issue twin, reproducing the shape that actually broke the fleet:
    /// `g-build:4` opened against `g-foundation`, reassigned away by
    /// `g-build:17`, and `g-foundation:68` acknowledging the original
    /// assignment with a frontier that had never seen the reassignment.
    #[test]
    fn an_issue_ack_against_a_superseded_assignment_reduces_and_is_recorded() {
        let mut state = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Implementor),
            ("carol", Role::Implementor),
        ]);
        let (alice, bob, carol) = (a("alice"), a("bob"), a("carol"));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Implementor));
        apply_ok(&mut state, &register(&carol, Role::Implementor));

        let issue = open_issue(&alice, 1, &bob);
        let issue_id = issue.id.clone();
        apply_ok(&mut state, &issue);

        let reassign = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&issue_id]),
            &EventData::IssueReassigned(IssueReassigned {
                issue: issue_id.clone(),
                previous_assignment: issue_id.clone(),
                previous_target: bob.clone(),
                new_target: carol.clone(),
                reason: text("carol owns this now"),
            }),
            [issue_id.clone()],
        );
        apply_ok(&mut state, &reassign);

        // bob acknowledges the assignment it held, never having observed the
        // reassignment -- its frontier stops at the issue itself.
        let ack = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&issue_id]),
            &EventData::IssueAcknowledged(IssueAcknowledged {
                issue: issue_id.clone(),
                assignment: issue_id.clone(),
                note: text("on it"),
            }),
            [issue_id.clone()],
        );
        let before_current = state.issues[&issue_id].current_assignment.clone();
        apply_event(&mut state, &ack).expect("a superseded ack is inapplicable, not invalid");
        let reduced = &state.issues[&issue_id];
        assert!(
            reduced.acknowledged_assignments.contains(&issue_id),
            "the historical acknowledgement must be recorded, so the field stays a pure              function of history"
        );
        assert_eq!(
            reduced.current_assignment, before_current,
            "a superseded acknowledgement must not move the current assignment"
        );
        assert!(
            !reduced.acknowledged(),
            "the current assignment must still read unacknowledged -- recording history              grants nothing"
        );

        // And the whole stream still reduces -- the property that failed.
        let mut fresh = empty_state(&[
            ("alice", Role::Implementor),
            ("bob", Role::Implementor),
            ("carol", Role::Implementor),
        ]);
        // `apply_ok` rather than raw `apply_event`: it carries the per-agent
        // sequence bookkeeping a real reduction does, and it panics on error,
        // which is the assertion -- the property that failed on the live bus
        // was that reducing this sequence at all was impossible.
        for env in [
            register(&alice, Role::Implementor),
            register(&bob, Role::Implementor),
            register(&carol, Role::Implementor),
            issue.clone(),
            reassign.clone(),
            ack.clone(),
        ] {
            apply_ok(&mut fresh, &env);
        }
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
    fn review_merge_authorized_ignores_a_stale_nomination_after_reassignment() {
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
        apply_ok(&mut state, &env);
        let chain = state.review_chain(&reassign_env.id).unwrap();
        assert!(
            chain.authorizations.is_empty(),
            "bob's stale authorization must not have taken effect"
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
    ///
    /// That rule is enforced by `merge_ready::check_merge_ready` -- see
    /// `merge_ready::tests::rejects_a_blocking_issue` -- and deliberately not
    /// by reduction. This test used to assert reduction rejected it, which is
    /// the behaviour that made a blocking issue opened concurrently with an
    /// authorization able to render the whole bus unreducible, decided by
    /// fetch order. Reduction now records what happened; the gate decides
    /// what may be acted on.
    #[test]
    fn review_merge_authorized_is_recorded_even_when_an_open_issue_blocks_the_chain() {
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
        apply_ok(&mut state, &env);
        assert!(
            state
                .review_chain(&nominate_env.id)
                .expect("the chain exists")
                .authorizations
                .contains(&env.id),
            "reduction records the authorization that was published"
        );
        // And the blocking issue is still open, so the gate that consults it
        // will still refuse the merge.
        assert!(
            blocking_issue_for_chain(&state, state.review_chain(&nominate_env.id).unwrap())
                .is_some(),
            "the issue must still block at the gate"
        );
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
            std::collections::BTreeSet::from([env.id])
        );
    }

    /// A fabricated `merge_engine_epoch` is refused here; a merely *stale*
    /// one is refused at publication instead.
    ///
    /// AGENT_BUS_SCHEMA.md asks for "the selected engine epoch visible in
    /// the authorization's observed state", and reduction can only carry
    /// half of that. `ReviewMergeAuthorized::referenced_ids` includes
    /// `merge_engine_epoch`, so `topological_order` gives it a real
    /// dependency edge and the named activation is applied first on every
    /// host -- checking it exists is sound. Whether it is still *current* is
    /// not: any later `merge_engine.activated` moves the selection, this
    /// event neither references nor need have observed it, and comparing
    /// against it made authorization-first reduce while activation-first
    /// returned `Err` for the same two events. That half now lives in
    /// `coordinator::verify_review_merge_authorized`, pinned by
    /// `the_authorization_gate_refuses_a_stale_merge_engine_epoch`.
    #[test]
    fn review_merge_authorized_rejects_an_unknown_merge_engine_epoch() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        let mut authorize = merge_authorized(&nominate_env.id, StringSet::default(), &[]);
        // Not merely stale -- no `merge_engine.activated` ever named this, so
        // no ordering of any event set could make it valid.
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
                .contains("is not a known merge engine activation"),
            "{err}"
        );
    }

    /// The counterpart to the above: a *known but superseded* epoch reduces
    /// fine, because refusing it would depend on whether the later
    /// activation had been replayed yet.
    #[test]
    fn a_superseded_merge_engine_epoch_still_reduces() {
        let mut state = empty_state(&[]);
        let alice = a("alice");
        let bob = a("bob");
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

        // The authorization names the epoch that was current when it was
        // written; something else has since been selected.
        let authorize = merge_authorized(&nominate_env.id, StringSet::default(), &[]);
        let superseded = authorize.merge_engine_epoch.clone();
        state.current_merge_engine_epoch = Some(EventId::new(&a("coord1"), 99));
        state
            .merge_engine_info
            .insert(EventId::new(&a("coord1"), 99), (short("ort"), short("2")));
        assert!(state.merge_engine_info.contains_key(&superseded));

        let env = Envelope::new(
            &bob,
            2,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(authorize),
            [],
        );
        apply_event(&mut state, &env)
            .expect("a superseded but real epoch must not make the bus unreducible");
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

    /// Round-4 adversarial review, Significant finding: `apply_review_
    /// reassigned`'s eager "already merged" precheck was a hard `Err`, not
    /// subject to the graceful winner/loser machinery the surrounding
    /// decline/withdraw/reassign race already uses. A reassignment built
    /// without observing a just-landed `review.merged` (independently
    /// published, never cross-observed before publication) must not poison
    /// reduction of the entire bus.
    #[test]
    fn ignores_a_reassignment_racing_against_an_already_merged_review() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let mut state = empty_state(&[]);
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&carol, Role::Reviewer));
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

        let merged_env = Envelope::new(
            &bob,
            3,
            frontier_seeing(&[&authorize_env.id]),
            &EventData::ReviewMerged(ReviewMerged {
                authorization: authorize_env.id.clone(),
                previous_main: authorize.previous_main,
                main_commit: authorize.candidate,
                product_branch: authorize.product_branch.clone(),
                reviewed_commit: authorize.reviewed_commit,
                summary: text("merged"),
            }),
            [],
        );
        apply_ok(&mut state, &merged_env);
        assert!(!state
            .review_chain(&nominate_env.id)
            .unwrap()
            .merged
            .is_empty());

        // alice, unaware the review already merged, tries to reassign it.
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
                reason: text("bob went quiet"),
                inherited_findings: vec![],
            }),
            [],
        );
        apply_ok(&mut state, &reassign_env);

        let chain = state.review_chain(&nominate_env.id).unwrap();
        assert_eq!(
            chain.current_nomination, nominate_env.id,
            "the stale reassignment must not have taken effect"
        );
    }

    /// Round-4 adversarial review, Critical finding: `apply_review_closing`'s
    /// "withdrawn" arm hard-`Err`ed on `!chain.authorizations.is_empty()`,
    /// unconditionally and before the exclusive tracker is even consulted --
    /// unlike every other check in the same function, which is subject to
    /// the graceful winner/loser machinery. An author's withdrawal built
    /// without observing a just-landed `review.merge_authorized`
    /// (independently published, never cross-observed before publication)
    /// must not poison reduction of the entire bus.
    #[test]
    fn ignores_a_withdrawal_racing_against_an_already_authorized_review() {
        let alice = a("alice");
        let bob = a("bob");
        let mut state = empty_state(&[]);
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let (nominate_env, _accept_env) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
        let authorize_env = Envelope::new(
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
        apply_ok(&mut state, &authorize_env);
        assert!(!state
            .review_chain(&nominate_env.id)
            .unwrap()
            .authorizations
            .is_empty());

        // alice, unaware of the authorization, withdraws the nomination.
        let withdraw_env = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewWithdrawn(ReviewWithdrawn {
                nomination: nominate_env.id.clone(),
                reason: text("changed plans"),
            }),
            [],
        );
        apply_ok(&mut state, &withdraw_env);

        let chain = state.review_chain(&nominate_env.id).unwrap();
        assert_ne!(
            chain.decline_or_withdraw_or_reassign_status,
            ItemStatus::Terminal("withdrawn"),
            "the stale withdrawal must not have taken effect"
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

        // Deliberately the frontier `coordinator::build_frontier` would
        // really produce: it skips the author's own stream, so there is no
        // self-entry here. An earlier version of this test hand-built one
        // and so passed against an envelope shape production cannot emit,
        // which hid that the rule it was checking never fired.
        let second_env = Envelope::new(
            &coord1,
            2,
            frontier_seeing(&[&authorize_env.id]),
            &reconciled_data(),
            [],
        );
        // Still refused, and for the reason that makes it a caller error
        // rather than a race: it is this same coordinator's second receipt.
        // Streams get a predecessor edge in `topological_order`, so an
        // agent's own events are ordered against each other on every host
        // and this answer cannot vary. A *cross-agent* second receipt is
        // recorded instead (see
        // `a_merged_receipt_racing_a_reconciliation_reduces_in_either_order`),
        // with publication-time verification refusing it there.
        let err = apply_event(&mut state, &second_env).unwrap_err();
        assert!(
            err.to_string()
                .contains(&format!("already published receipt {}", first_env.id)),
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
                .contains("only the named nomination's accepting reviewer may dispose"),
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

    /// Round-3 adversarial review, Critical finding: an `Err` here would
    /// propagate via `reduce()`'s bare `?` with no per-event isolation,
    /// permanently breaking reduction of the *entire* bus for every host
    /// that has fetched both streams -- not merely this one review chain --
    /// the moment a genuinely concurrent disposal and reassignment (two
    /// independently-published, single-writer streams, neither observing
    /// the other) are reduced together.
    ///
    /// Round-9 sweep: that fix was a no-op, which is total but *not*
    /// confluent. Nothing orders the disposal against the reassignment (see
    /// `apply_finding_disposition`), so "does bob's disposal apply" was
    /// decided by replay order -- a silent permanent divergence between
    /// hosts. The disposal is now recorded in either order, with its own
    /// provenance, and `coordinator::verify_disposition_targets_the_current_
    /// nomination` refuses it at publication for any host that can actually
    /// see the reassignment. This test's name and shape are kept so the
    /// round-3 scenario stays pinned; what changed is the answer.
    #[test]
    fn records_finding_disposal_against_a_stale_nomination_rather_than_dropping_it() {
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
        apply_ok(&mut state, &cleared_env);
        let root = state.review_chain_by_nomination[&nominate_env.id].clone();
        let key = (changes_env.id.clone(), "f1".to_string());
        assert_eq!(
            state.reviews[&root].findings[&key].disposition,
            FindingDisposition::Cleared {
                by_event: cleared_env.id.clone()
            },
            "bob's concurrent disposal is recorded, with provenance, in whichever order it is \
             replayed -- the policy refusal lives at publication now"
        );
    }

    /// Companion to `ignores_finding_disposal_against_a_stale_nomination`
    /// for `apply_review_accept`: bob never gets a chance to accept before
    /// alice reassigns the nomination away from him. His late acceptance
    /// must be a no-op, not a fatal `Err`.
    #[test]
    fn ignores_review_accept_against_a_stale_nomination() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let mut state = empty_state(&[]);
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&carol, Role::Reviewer));

        let request = review_request(&[&alice], &bob);
        let nominate_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::ReviewNominated(request.clone()),
            [],
        );
        apply_ok(&mut state, &nominate_env);

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
                reason: text("bob went quiet"),
                inherited_findings: vec![],
            }),
            [],
        );
        apply_ok(&mut state, &reassign_env);

        // bob, unaware his nomination was already reassigned, accepts it
        // anyway under its now-stale id.
        let accept_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: nominate_env.id.clone(),
                note: text(""),
            }),
            [],
        );
        apply_ok(&mut state, &accept_env);

        let chain = state.review_chain(&reassign_env.id).unwrap();
        assert_eq!(chain.current_nomination, reassign_env.id);
        assert!(
            !chain.accepted_nominations.contains(&nominate_env.id),
            "bob's stale acceptance must not have taken effect"
        );
        assert!(!chain.accepted());
    }

    /// Companion to `ignores_finding_disposal_against_a_stale_nomination`
    /// for `apply_review_changes`: bob accepts, then loses a genuinely
    /// concurrent reassignment race he never observed. His changes-request
    /// against the stale nomination must be a no-op, not a fatal `Err` that
    /// would (via `reduce()`'s bare `?` propagation) break reduction of the
    /// entire bus for any host that later fetches both streams.
    #[test]
    fn ignores_review_changes_requested_against_a_stale_nomination() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let mut state = empty_state(&[]);
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        apply_ok(&mut state, &register(&carol, Role::Reviewer));
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
                reason: text("bob went quiet"),
                inherited_findings: vec![],
            }),
            [],
        );
        apply_ok(&mut state, &reassign_env);

        // bob, unaware of the reassignment, requests changes against the
        // now-stale nomination.
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

        let root = state.review_chain_by_nomination[&nominate_env.id].clone();
        assert!(
            state.reviews[&root].findings.is_empty(),
            "bob's stale changes-request must not have recorded any finding"
        );
    }

    /// Round-3 adversarial review, Significant finding: AGENT_BUS.md section
    /// 6.6 / AGENT_BUS_SCHEMA.md section 8 say only the agent who *accepted*
    /// a nomination may emit review.changes_requested, review.findings_
    /// cleared/superseded, or review.merge_authorized -- being merely the
    /// *named* reviewer is not enough. Previously only reviewer identity was
    /// checked, so a nominated-but-never-accepted reviewer could still
    /// validly request changes.
    #[test]
    fn rejects_review_changes_requested_before_the_reviewer_has_accepted() {
        let alice = a("alice");
        let bob = a("bob");
        let mut state = empty_state(&[]);
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let request = review_request(&[&alice], &bob);
        let nominate_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::ReviewNominated(request),
            [],
        );
        apply_ok(&mut state, &nominate_env);

        let changes_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewChangesRequested(ReviewChangesRequested {
                nomination: nominate_env.id.clone(),
                reviewed_commit: hash(3),
                findings: vec![finding("f1")],
                evidence: StringSet::default(),
            }),
            [],
        );
        let err = apply_event(&mut state, &changes_env).unwrap_err();
        assert!(
            err.to_string().contains("must accept the nomination"),
            "{err}"
        );
    }

    /// Companion to the above for `review.merge_authorized`.
    #[test]
    fn rejects_review_merge_authorized_before_the_reviewer_has_accepted() {
        let alice = a("alice");
        let bob = a("bob");
        let mut state = empty_state(&[("coord1", Role::Coordinator)]);
        let coord1 = a("coord1");
        apply_ok(&mut state, &register(&coord1, Role::Coordinator));
        apply_ok(&mut state, &register(&alice, Role::Implementor));
        apply_ok(&mut state, &register(&bob, Role::Reviewer));
        let epoch = state.roster_epoch.as_ref().unwrap().clone();
        let engine_epoch = default_merge_engine_epoch();
        state.merge_engine_info.insert(
            engine_epoch.clone(),
            (
                short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
                short(crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION),
            ),
        );
        state.current_merge_engine_epoch = Some(engine_epoch);
        let request = review_request(&[&alice], &bob);
        let nominate_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::ReviewNominated(request),
            [],
        );
        apply_ok(&mut state, &nominate_env);

        let authorize_env = Envelope::new(
            &bob,
            1,
            complete_frontier(&epoch),
            &EventData::ReviewMergeAuthorized(merge_authorized(
                &nominate_env.id,
                StringSet::default(),
                &[],
            )),
            [],
        );
        let err = apply_event(&mut state, &authorize_env).unwrap_err();
        assert!(
            err.to_string().contains("must accept the nomination"),
            "{err}"
        );
    }

    /// Companion to the above for finding disposal -- this one needs an
    /// *already-open* finding under a reassignment whose new reviewer has
    /// not yet accepted, since a finding cannot exist at all without a
    /// prior accepted changes-request. Findings persist chain-wide across
    /// reassignment (they are inherited, not per-link), so the still-open
    /// finding is exactly what the new, not-yet-accepted reviewer would
    /// otherwise be able to dispose of.
    #[test]
    fn rejects_finding_disposal_before_the_new_reviewer_has_accepted() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let mut state = empty_state(&[]);
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

        // carol, the new reviewer, has not accepted yet.
        let cleared_env = Envelope::new(
            &carol,
            1,
            frontier_seeing(&[&reassign_env.id]),
            &EventData::ReviewFindingsCleared(ReviewFindingsCleared {
                nomination: reassign_env.id.clone(),
                changes_event: changes_env.id.clone(),
                finding_id: short("f1"),
                resolved_commit: hash(4),
                summary: text("fixed"),
            }),
            [],
        );
        let err = apply_event(&mut state, &cleared_env).unwrap_err();
        assert!(
            err.to_string().contains("must accept the nomination"),
            "{err}"
        );
    }

    /// Round-4 adversarial review, Significant finding: a set comparison
    /// alone silently accepts a reassignment that cites the one open finding
    /// twice, because the duplicate collapses under the comparison. The
    /// round-9 sweep (C5) moved the "equals every still-open finding" half
    /// of that rule to `coordinator::verify_review_reassignment_inherits_
    /// open_findings` -- the open set is concurrently mutable, so reduction
    /// cannot ask it -- but the no-duplicates half is a pure function of the
    /// event's own payload, gives the same answer in every replay order, and
    /// so stays here. This pins that surviving half.
    #[test]
    fn rejects_a_reassignment_that_cites_the_same_open_finding_twice() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let mut state = empty_state(&[]);
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
        let duplicate_ref = crate::common::FindingRef {
            changes_event: changes_env.id.clone(),
            finding_id: short("f1"),
        };
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
                inherited_findings: vec![duplicate_ref.clone(), duplicate_ref],
            }),
            [],
        );
        let err = apply_event(&mut state, &reassign_env).unwrap_err();
        assert!(
            err.to_string().contains("duplicate inherited finding f1"),
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

    // --------------------------------------------------- reduce()/reduce_onto()

    /// Regression test for a Critical finding surfaced while building the
    /// gate-15 test below: `IssueOpened::referenced_ids()` (like most
    /// event kinds naming another agent by identity rather than by
    /// `EventId`) does not include `target`, so nothing in the dependency
    /// graph `topological_order` builds forces that agent's own
    /// registration to be ordered first. Before the fix in this same
    /// function, the plain lexicographic tie-break would deterministically
    /// place an alphabetically-earlier author's event ahead of an
    /// alphabetically-later target's registration whenever both were
    /// simultaneously ready and nothing else constrained them -- here,
    /// `alice` opening an ordinary issue against `bob`, with no other
    /// cross-reference between their streams at all (the exact shape a
    /// real submission takes when the author doesn't separately
    /// `--observes` the target's registration, which nothing requires).
    /// This is not a race or an adversarial construction: it is the
    /// ordinary, single-host, fully-synced cold-replay path every `status`/
    /// `tail`/`coordinate` call goes through, and it would have
    /// permanently failed with "unregistered agent: bob" -- exactly the
    /// fleet-wide-DoS shape already fixed elsewhere in this file, just via
    /// a different mechanism (ordering, not a hard `Err` on an otherwise
    /// -valid event).
    #[test]
    fn cold_reduce_orders_every_registration_before_any_event_merely_naming_that_agent() {
        let coord1 = a("coord1");
        let alice = a("alice");
        let bob = a("bob");
        let epoch = epoch_with(&[
            ("coord1", Role::Coordinator),
            ("alice", Role::Implementor),
            ("bob", Role::Implementor),
        ]);
        let mut known_epochs = BTreeMap::new();
        known_epochs.insert(epoch.id.clone(), epoch.clone());

        let coord1_reg = register(&coord1, Role::Coordinator);
        let alice_reg = register(&alice, Role::Implementor);
        let bob_reg = register(&bob, Role::Implementor);

        // Deliberately no reference to bob at all -- `alice` sorts before
        // `bob`, so a plain lexicographic tie-break would place this event
        // before `bob:0` the moment both are simultaneously ready.
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

        let streams: BTreeMap<Agent, Vec<Envelope>> = BTreeMap::from([
            (coord1.clone(), vec![coord1_reg]),
            (alice.clone(), vec![alice_reg, issue_env.clone()]),
            (bob.clone(), vec![bob_reg]),
        ]);
        let state = reduce(config(), Some(epoch), known_epochs, &streams)
            .expect("bob's registration must be ordered before alice's issue targeting him");
        assert_eq!(state.issues[&issue_env.id].current_target, bob);
    }

    /// Gate 15 ("cold replay and incremental replay produce exactly the
    /// same reduced state"), exercised at the actual public entry points
    /// for the first time -- every other test in this module drives
    /// `apply_event` directly against a hand-built `BusState`, never
    /// `reduce()`/`topological_order` (the real cold-replay path
    /// `sync::reduce_local` uses) or `reduce_onto()` (the real incremental
    /// path `coordinator::drain_outbox` uses to fold newly-validated
    /// candidates onto an already-reduced state). Builds one real,
    /// multi-agent, multi-kind event history, reduces it two ways -- fully
    /// cold in one `reduce()` call, versus cold over a prefix followed by
    /// `reduce_onto()` for the rest, mirroring exactly how a coordinator
    /// batch actually gets folded onto a prior snapshot in production --
    /// and asserts the two resulting `BusState`s are identical via their
    /// `Debug` representation (every field is a `BTreeMap`/`BTreeSet` or
    /// similarly order-independent, so this is a reliable deep-equality
    /// check without adding `PartialEq` to `BusState`'s full field graph
    /// just for one test).
    #[test]
    fn cold_replay_and_incremental_replay_produce_identical_state() {
        let coord1 = a("coord1");
        let alice = a("alice");
        let bob = a("bob");
        let aud = a("aud");
        let epoch = epoch_with(&[
            ("coord1", Role::Coordinator),
            ("alice", Role::Implementor),
            ("bob", Role::Implementor),
            ("aud", Role::Auditor),
        ]);
        let mut known_epochs = BTreeMap::new();
        known_epochs.insert(epoch.id.clone(), epoch.clone());

        let coord1_reg = register(&coord1, Role::Coordinator);
        let alice_reg = register(&alice, Role::Implementor);
        let bob_reg = register(&bob, Role::Implementor);
        let aud_reg = register(&aud, Role::Auditor);

        // `IssueOpened::referenced_ids()` does not include `target` (only
        // `blocks`/`evidence`), so `target`'s registration has no causal
        // edge in `topological_order` unless the submitter's own refs
        // supply one -- citing it as evidence here is a test-construction
        // workaround for that (a real, separate finding -- see the
        // `agent-bus-v2-target-agent-topological-ordering` memory note --
        // not something this test is trying to exercise).
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
            evidence: StringSet::from_iter([bob_reg.id.clone()]),
        });
        let issue_env = Envelope::new(
            &alice,
            1,
            frontier_seeing(&[&bob_reg.id]),
            &issue_data,
            [bob_reg.id.clone()],
        );

        let resolve_data = EventData::IssueResolved(IssueResolved {
            issue: issue_env.id.clone(),
            assignment: issue_env.id.clone(),
            summary: text("done"),
            fix_commit: None,
            verification: vec![],
        });
        let resolve_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&issue_env.id]),
            &resolve_data,
            [issue_env.id.clone()],
        );

        let status_data = EventData::AgentStatus(AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: text("all done"),
            product_branch: None,
            product_commit: None,
        });
        let status_env = Envelope::new(&bob, 2, no_frontier(), &status_data, []);

        // An `audit.reported` too, so `state.audits` is non-empty on both
        // sides of the comparison below rather than trivially equal. It is
        // also the only kind here that requires a *complete* frontier, so
        // this covers that path through replay as well.
        let audit_data = EventData::AuditReported(crate::events::AuditReported {
            inspected_commits: StringSet::default(),
            areas: vec![text("coordination history")],
            methods: vec![text("replayed every stream")],
            limitations: vec![text("product surface not examined")],
            issues: StringSet::from_iter([issue_env.id.clone()]),
            summary: text("one finding, already filed"),
        });
        let audit_env = Envelope::new(
            &aud,
            1,
            ObservedFrontier::complete(
                &epoch,
                epoch.active_members.keys().map(|agent| FrontierEntry {
                    agent: agent.clone(),
                    stream_tip: hash(1),
                    through: if *agent == alice {
                        issue_env.id.clone()
                    } else {
                        EventId::new(agent, 0)
                    },
                }),
            )
            .expect("a complete frontier"),
            &audit_data,
            [issue_env.id.clone()],
        );

        let streams_full: BTreeMap<Agent, Vec<Envelope>> = BTreeMap::from([
            (coord1.clone(), vec![coord1_reg.clone()]),
            (alice.clone(), vec![alice_reg.clone(), issue_env.clone()]),
            (
                bob.clone(),
                vec![bob_reg.clone(), resolve_env.clone(), status_env.clone()],
            ),
            (aud.clone(), vec![aud_reg.clone(), audit_env.clone()]),
        ]);

        let cold = reduce(
            config(),
            Some(epoch.clone()),
            known_epochs.clone(),
            &streams_full,
        )
        .expect("full cold reduce succeeds");

        // Split: reduce a prefix cold (everything except bob's last two
        // events), then fold the rest on incrementally, in dependency
        // order -- exactly `coordinator::drain_outbox`'s own shape.
        let streams_prefix: BTreeMap<Agent, Vec<Envelope>> = BTreeMap::from([
            (coord1.clone(), vec![coord1_reg.clone()]),
            (alice.clone(), vec![alice_reg.clone(), issue_env.clone()]),
            (bob.clone(), vec![bob_reg.clone()]),
            (aud.clone(), vec![aud_reg.clone()]),
        ]);
        let incremental = reduce(config(), Some(epoch), known_epochs, &streams_prefix)
            .expect("prefix cold reduce succeeds");
        let incremental = reduce_onto(incremental, &[resolve_env, status_env, audit_env])
            .expect("incremental reduce_onto succeeds");

        assert_eq!(
            format!("{cold:?}"),
            format!("{incremental:?}"),
            "cold replay and cold-plus-incremental replay of the identical event set must \
             produce byte-identical state"
        );
    }

    /// A subscription change racing a broadcast must not make the bus
    /// unreducible.
    ///
    /// `resolve_audience` for `TopicSubscribers` reads
    /// `AgentState::subscribed_topics`, which is mutable derived state set by
    /// `subscription.set`. A complete frontier does not pin it --
    /// `validate_complete` checks that the frontier names the epoch's exact
    /// active-member *set*, never their stream positions -- and an
    /// informational broadcast needs only a sparse frontier anyway. So a
    /// publisher resolves the audience against the view it had, someone
    /// subscribes concurrently, and whether the snapshot "matches" depends
    /// entirely on which event a host reduced first.
    #[test]
    fn a_subscription_racing_a_broadcast_reduces_in_either_order() {
        let build = |subscribe_first: bool| {
            let mut state = empty_state(&[
                ("alice", Role::Implementor),
                ("bob", Role::Implementor),
                ("carol", Role::Implementor),
            ]);
            let (alice, bob, carol) = (a("alice"), a("bob"), a("carol"));
            apply_ok(&mut state, &register(&alice, Role::Implementor));
            apply_ok(&mut state, &register(&bob, Role::Implementor));
            apply_ok(&mut state, &register(&carol, Role::Implementor));
            let epoch = state.roster_epoch.as_ref().unwrap().clone();

            // carol is already subscribed, and alice has seen that.
            apply_ok(
                &mut state,
                &Envelope::new(
                    &carol,
                    1,
                    no_frontier(),
                    &EventData::SubscriptionSet(crate::events::SubscriptionSet {
                        topics: StringSet::from_iter([topic("release.main")]),
                    }),
                    [],
                ),
            );

            // bob subscribes too, concurrently with alice's broadcast.
            let subscribe = Envelope::new(
                &bob,
                1,
                no_frontier(),
                &EventData::SubscriptionSet(crate::events::SubscriptionSet {
                    topics: StringSet::from_iter([topic("release.main")]),
                }),
                [],
            );
            // alice publishes to that topic's subscribers, having resolved the
            // audience before bob subscribed -- so the snapshot is empty.
            let published = Envelope::new(
                &alice,
                1,
                no_frontier(),
                &EventData::BroadcastPublished(broadcast(
                    epoch.id.clone(),
                    crate::common::AudienceSelector::TopicSubscribers(topic("release.main")),
                    &[&carol],
                    crate::common::AckRequirement::None,
                )),
                [],
            );

            let order: Vec<&Envelope> = if subscribe_first {
                vec![&subscribe, &published]
            } else {
                vec![&published, &subscribe]
            };
            // The real incremental path, not a hand-rolled copy of it.
            // These fixtures model exactly what `reduce_onto` does on a host
            // that fetched one stream before the other, so anything else
            // leaves the production path untested -- and the loop that stood
            // here differed from it, assigning `next_seq` where `reduce_onto`
            // takes a `max`.
            let owned: Vec<Envelope> = order.into_iter().cloned().collect();
            reduce_onto(state, &owned)
                .expect("both orders are valid linear extensions and must reduce")
        };

        let publish_first = build(false);
        let subscribe_first = build(true);
        // Converging on "the handler quietly did nothing" would satisfy any
        // comparison, so pin that the broadcast was actually recorded first.
        assert_eq!(
            publish_first.broadcasts.len(),
            1,
            "the broadcast must be recorded, not silently skipped"
        );
        // Compare the *whole* state, not one map. Gates 15/16 are about
        // state, and an adversarial test review demonstrated the narrower
        // form's cost: a deliberate order-dependent write into `state.issues`
        // from inside `apply_review_merge_authorized` -- the very handler this
        // work rewrote -- survived the entire suite, proptests included,
        // because every convergence test here compared only `reviews` or only
        // `broadcasts`. The events in each pair come from different agents, so
        // `events`, `kind_of_event` and `next_seq` are order-insensitive too
        // and the wider compare is just as valid.
        assert_eq!(
            format!("{publish_first:#?}"),
            format!("{subscribe_first:#?}"),
            "both valid orders must converge on the same broadcast state"
        );
    }

    /// Two coordinators reconciling the same authorization must converge.
    ///
    /// The sibling test races a `review.merged` against a
    /// `review.merge_reconciled`, and those land in two *different*
    /// containers, each receiving exactly one entry -- the one pairing where
    /// arrival order cannot show through. This races two events into the
    /// *same* container, which is what actually exercises the ordering, and
    /// what caught `reconciled` still being a `Vec` after concurrent
    /// receipts started being recorded rather than refused.
    ///
    /// `require_bootstrap_coordinator` admits any active member bound as
    /// `Coordinator`, so two of them is a real configuration, not a
    /// contrivance.
    #[test]
    fn two_coordinators_reconciling_the_same_authorization_converge() {
        let build = |second_first: bool| {
            let mut state = empty_state(&[
                ("alice", Role::Implementor),
                ("bob", Role::Reviewer),
                ("coord1", Role::Coordinator),
                ("coord2", Role::Coordinator),
            ]);
            let (alice, bob) = (a("alice"), a("bob"));
            let (coord1, coord2) = (a("coord1"), a("coord2"));
            apply_ok(&mut state, &register(&alice, Role::Implementor));
            apply_ok(&mut state, &register(&bob, Role::Reviewer));
            apply_ok(&mut state, &register(&coord1, Role::Coordinator));
            apply_ok(&mut state, &register(&coord2, Role::Coordinator));
            let epoch = state.roster_epoch.as_ref().unwrap().clone();
            let (nominate_env, _accept) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
            let authorize = merge_authorized(&nominate_env.id, StringSet::default(), &[]);
            let authorize_env = Envelope::new(
                &bob,
                2,
                complete_frontier(&epoch),
                &EventData::ReviewMergeAuthorized(authorize.clone()),
                [],
            );
            apply_ok(&mut state, &authorize_env);

            let reconciled_by = |who: &Agent| {
                Envelope::new(
                    who,
                    1,
                    frontier_seeing(&[&authorize_env.id]),
                    &EventData::ReviewMergeReconciled(ReviewMergeReconciled {
                        authorization: authorize_env.id.clone(),
                        previous_main: authorize.previous_main.clone(),
                        main_commit: authorize.candidate.clone(),
                        product_branch: authorize.product_branch.clone(),
                        reviewed_commit: authorize.reviewed_commit.clone(),
                        reason: text("r"),
                        user_authority: text("operator"),
                    }),
                    [],
                )
            };
            let first = reconciled_by(&coord1);
            let second = reconciled_by(&coord2);

            let order: Vec<&Envelope> = if second_first {
                vec![&second, &first]
            } else {
                vec![&first, &second]
            };
            // The real incremental path, not a hand-rolled copy of it.
            // These fixtures model exactly what `reduce_onto` does on a host
            // that fetched one stream before the other, so anything else
            // leaves the production path untested -- and the loop that stood
            // here differed from it, assigning `next_seq` where `reduce_onto`
            // takes a `max`.
            let owned: Vec<Envelope> = order.into_iter().cloned().collect();
            reduce_onto(state, &owned)
                .expect("both orders are valid linear extensions and must reduce")
        };

        let coord1_first = build(false);
        let coord2_first = build(true);
        // Both receipts recorded -- this is the commit message's own claim,
        // and without it the test passes just as well against a handler that
        // dropped one.
        let chain = coord1_first.reviews.values().next().expect("a chain");
        assert_eq!(chain.reconciled.len(), 2, "both receipts must be recorded");
        // Compare the *whole* state, not one map. Gates 15/16 are about
        // state, and an adversarial test review demonstrated the narrower
        // form's cost: a deliberate order-dependent write into `state.issues`
        // from inside `apply_review_merge_authorized` -- the very handler this
        // work rewrote -- survived the entire suite, proptests included,
        // because every convergence test here compared only `reviews` or only
        // `broadcasts`. The events in each pair come from different agents, so
        // `events`, `kind_of_event` and `next_seq` are order-insensitive too
        // and the wider compare is just as valid.
        assert_eq!(
            format!("{coord1_first:#?}"),
            format!("{coord2_first:#?}"),
            "GATE 15/16: both receipts are recorded, and in an order-independent container"
        );
    }

    /// A reviewer's own `review.merged` racing a coordinator's
    /// `review.merge_reconciled` for the same authorization must not make the
    /// bus unreducible.
    ///
    /// Reconciliation exists precisely for a reviewer that went quiet, so the
    /// two are published by different agents who have not observed each other.
    /// Both reference the authorization; neither references the other. They
    /// are concurrent, both orders are valid, and rejecting the second one is
    /// fatal to reduction on every host.
    #[test]
    fn a_merged_receipt_racing_a_reconciliation_reduces_in_either_order() {
        let build = |reconcile_first: bool| {
            let mut state = empty_state(&[
                ("alice", Role::Implementor),
                ("bob", Role::Reviewer),
                ("coord1", Role::Coordinator),
            ]);
            let (alice, bob, coord1) = (a("alice"), a("bob"), a("coord1"));
            apply_ok(&mut state, &register(&alice, Role::Implementor));
            apply_ok(&mut state, &register(&bob, Role::Reviewer));
            apply_ok(&mut state, &register(&coord1, Role::Coordinator));
            let (nominate_env, _accept) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);

            let engine_epoch = EventId::new(&coord1, 0);
            state.merge_engine_info.insert(
                engine_epoch.clone(),
                (
                    short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
                    short(crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION),
                ),
            );
            state.current_merge_engine_epoch = Some(engine_epoch.clone());
            let epoch = state.roster_epoch.as_ref().unwrap().clone();

            let authorize = Envelope::new(
                &bob,
                2,
                complete_frontier(&epoch),
                &EventData::ReviewMergeAuthorized(merge_authorized(
                    &nominate_env.id,
                    StringSet::default(),
                    &[],
                )),
                [nominate_env.id.clone(), engine_epoch.clone()],
            );
            apply_ok(&mut state, &authorize);

            let merged = Envelope::new(
                &bob,
                3,
                frontier_seeing(&[&authorize.id]),
                &EventData::ReviewMerged(ReviewMerged {
                    authorization: authorize.id.clone(),
                    previous_main: hash(2),
                    main_commit: hash(4),
                    product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                    reviewed_commit: hash(3),
                    summary: text("merged"),
                }),
                [authorize.id.clone()],
            );
            let reconciled = Envelope::new(
                &coord1,
                1,
                frontier_seeing(&[&authorize.id]),
                &EventData::ReviewMergeReconciled(ReviewMergeReconciled {
                    authorization: authorize.id.clone(),
                    previous_main: hash(2),
                    main_commit: hash(4),
                    product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
                    reviewed_commit: hash(3),
                    reason: text("reviewer went quiet"),
                    user_authority: text("operator"),
                }),
                [authorize.id.clone()],
            );

            let order: Vec<&Envelope> = if reconcile_first {
                vec![&reconciled, &merged]
            } else {
                vec![&merged, &reconciled]
            };
            // The real incremental path, not a hand-rolled copy of it.
            // These fixtures model exactly what `reduce_onto` does on a host
            // that fetched one stream before the other, so anything else
            // leaves the production path untested -- and the loop that stood
            // here differed from it, assigning `next_seq` where `reduce_onto`
            // takes a `max`.
            let owned: Vec<Envelope> = order.into_iter().cloned().collect();
            reduce_onto(state, &owned)
                .expect("both orders are valid linear extensions and must reduce")
        };

        let merged_first = build(false);
        let reconciled_first = build(true);
        let chain = merged_first.reviews.values().next().expect("a chain");
        assert_eq!(chain.merged.len(), 1, "the merge receipt must be recorded");
        assert_eq!(
            chain.reconciled.len(),
            1,
            "and so must the reconciliation -- recording both is the whole claim"
        );
        // Compare the *whole* state, not one map. Gates 15/16 are about
        // state, and an adversarial test review demonstrated the narrower
        // form's cost: a deliberate order-dependent write into `state.issues`
        // from inside `apply_review_merge_authorized` -- the very handler this
        // work rewrote -- survived the entire suite, proptests included,
        // because every convergence test here compared only `reviews` or only
        // `broadcasts`. The events in each pair come from different agents, so
        // `events`, `kind_of_event` and `next_seq` are order-insensitive too
        // and the wider compare is just as valid.
        assert_eq!(
            format!("{merged_first:#?}"),
            format!("{reconciled_first:#?}"),
            "both valid orders must converge on the same chain state"
        );
    }

    /// A blocking issue opened concurrently with an authorization must not
    /// make the bus unreducible.
    ///
    /// An `issue.opened` carrying `blocks` need have no causal edge to a
    /// `review.merge_authorized`: the issue references the chain event, the
    /// authorization does not reference the issue. Where there is no edge
    /// both orders are valid linear extensions, and a rule that scanned
    /// *every* issue made them disagree -- authorization-first succeeded,
    /// issue-first returned `Err`. With no per-event isolation in `reduce`,
    /// that `Err` is every host unable to reduce the bus at all.
    ///
    /// Section 10's policy is not weakened, it is asked where it can be
    /// answered honestly -- at publication
    /// (`coordinator::verify_review_merge_authorized`) and at the gate
    /// (`merge_ready::check_merge_ready`), both against a fully-reduced
    /// state. See
    /// `reduction_never_consults_a_blocking_issue_whatever_the_names_or_fetch_state`
    /// for why reduction itself cannot.
    #[test]
    fn an_issue_blocking_a_chain_does_not_make_a_published_authorization_fatal() {
        let build = |issue_first: bool| {
            let mut state = empty_state(&[
                ("alice", Role::Implementor),
                ("bob", Role::Reviewer),
                ("carol", Role::Implementor),
            ]);
            let (alice, bob, carol) = (a("alice"), a("bob"), a("carol"));
            apply_ok(&mut state, &register(&alice, Role::Implementor));
            apply_ok(&mut state, &register(&bob, Role::Reviewer));
            apply_ok(&mut state, &register(&carol, Role::Implementor));
            let (nominate_env, accept) = nominate_and_accept(&mut state, &alice, 1, &bob, 1);
            let epoch = state.roster_epoch.as_ref().unwrap().clone();

            // carol opens an issue that blocks the chain, having observed only
            // the nomination -- never bob's authorization.
            let mut issue_data = match open_issue(&carol, 1, &alice).typed_data().unwrap() {
                EventData::IssueOpened(d) => d,
                _ => unreachable!(),
            };
            issue_data.blocks = StringSet::from_iter([nominate_env.id.clone()]);
            let issue = Envelope::new(
                &carol,
                1,
                frontier_seeing(&[&nominate_env.id]),
                &EventData::IssueOpened(issue_data),
                [nominate_env.id.clone()],
            );

            // bob authorizes, having observed only the nomination.
            let auth = Envelope::new(
                &bob,
                2,
                ObservedFrontier::complete(
                    &epoch,
                    epoch.active_members.keys().map(|agent| FrontierEntry {
                        agent: agent.clone(),
                        stream_tip: hash(1),
                        // bob's own entry runs through bob's real tip. Streams
                        // are single-writer, so an agent has always observed
                        // its own prior events; a frontier claiming otherwise
                        // is an envelope production cannot emit, and
                        // `validate_complete` would not catch it because it
                        // checks the member set, not the positions.
                        through: if *agent == alice {
                            nominate_env.id.clone()
                        } else if *agent == bob {
                            accept.id.clone()
                        } else {
                            EventId::new(agent, 0)
                        },
                    }),
                )
                .expect("a complete frontier"),
                &EventData::ReviewMergeAuthorized(merge_authorized(
                    &nominate_env.id,
                    StringSet::default(),
                    &[],
                )),
                [nominate_env.id.clone()],
            );

            let order: Vec<&Envelope> = if issue_first {
                vec![&issue, &auth]
            } else {
                vec![&auth, &issue]
            };
            // The real incremental path, not a hand-rolled copy of it.
            // These fixtures model exactly what `reduce_onto` does on a host
            // that fetched one stream before the other, so anything else
            // leaves the production path untested -- and the loop that stood
            // here differed from it, assigning `next_seq` where `reduce_onto`
            // takes a `max`.
            let owned: Vec<Envelope> = order.into_iter().cloned().collect();
            reduce_onto(state, &owned)
                .expect("both orders are valid linear extensions and must reduce")
        };

        // Both orders must reduce, and must agree (gates 15/16).
        let auth_first = build(false);
        let issue_first = build(true);
        // `apply_review_merge_authorized` has a live silent-`Ok(())` path for
        // a stale nomination link; a refactor that widened it would turn this
        // test green and meaningless without this assertion.
        let chain = auth_first.reviews.values().next().expect("a chain");
        assert_eq!(
            chain.authorizations.len(),
            1,
            "the authorization must be recorded, not silently skipped"
        );
        // Compare the *whole* state, not one map. Gates 15/16 are about
        // state, and an adversarial test review demonstrated the narrower
        // form's cost: a deliberate order-dependent write into `state.issues`
        // from inside `apply_review_merge_authorized` -- the very handler this
        // work rewrote -- survived the entire suite, proptests included,
        // because every convergence test here compared only `reviews` or only
        // `broadcasts`. The events in each pair come from different agents, so
        // `events`, `kind_of_event` and `next_seq` are order-insensitive too
        // and the wider compare is just as valid.
        assert_eq!(
            format!("{auth_first:#?}"),
            format!("{issue_first:#?}"),
            "the two valid orders must converge on the same review state"
        );
    }

    /// Gates 15/16 for the acknowledge-versus-reassign race: two valid,
    /// dependency-respecting orders of the same events must reduce to
    /// identical state.
    ///
    /// This is the test that rejects the tempting version of the fix. Simply
    /// dropping a superseded acknowledgement unblocks reduction and looks
    /// correct in isolation, but leaves `acknowledged_assignments` dependent
    /// on arrival order -- so two hosts that fetched the same streams in
    /// different orders diverge silently and permanently.
    #[test]
    fn an_ack_racing_a_reassignment_converges_in_either_order() {
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");
        let epoch = epoch_with(&[
            ("alice", Role::Implementor),
            ("bob", Role::Implementor),
            ("carol", Role::Implementor),
        ]);
        let mut known_epochs = BTreeMap::new();
        known_epochs.insert(epoch.id.clone(), epoch.clone());

        let alice_reg = register(&alice, Role::Implementor);
        let bob_reg = register(&bob, Role::Implementor);
        let carol_reg = register(&carol, Role::Implementor);

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
            evidence: StringSet::from_iter([bob_reg.id.clone()]),
        });
        let issue_env = Envelope::new(
            &alice,
            1,
            frontier_seeing(&[&bob_reg.id]),
            &issue_data,
            [bob_reg.id.clone()],
        );

        let reassign = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&bob_reg.id]),
            &EventData::IssueReassigned(IssueReassigned {
                issue: issue_env.id.clone(),
                previous_assignment: issue_env.id.clone(),
                previous_target: bob.clone(),
                new_target: carol.clone(),
                reason: text("carol owns this now"),
            }),
            [],
        );

        let ack = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&issue_env.id]),
            &EventData::IssueAcknowledged(IssueAcknowledged {
                issue: issue_env.id.clone(),
                assignment: issue_env.id.clone(),
                note: text("on it"),
            }),
            [issue_env.id.clone()],
        );

        let streams_prefix: BTreeMap<Agent, Vec<Envelope>> = BTreeMap::from([
            (alice.clone(), vec![alice_reg.clone(), issue_env.clone()]),
            (bob.clone(), vec![bob_reg.clone()]),
            (carol.clone(), vec![carol_reg.clone()]),
        ]);
        let base = reduce(
            config(),
            Some(epoch.clone()),
            known_epochs.clone(),
            &streams_prefix,
        )
        .expect("prefix cold reduce succeeds");

        let ack_first = reduce_onto(base.clone(), &[ack.clone(), reassign.clone()])
            .expect("ack-then-reassign reduces");
        let reassign_first = reduce_onto(base.clone(), &[reassign.clone(), ack.clone()])
            .expect("reassign-then-ack reduces");

        assert_eq!(
            format!("{ack_first:?}"),
            format!("{reassign_first:?}"),
            "GATE 15/16: two valid dependency-respecting orders of the same event set must \
             produce identical state"
        );
    }

    /// Reduction must not consult a blocking issue, because during replay it
    /// cannot ask the question honestly.
    ///
    /// `topological_order` derives its edges from `refs` alone and never
    /// from `observed`. An authorization references the nomination, not the
    /// issue that blocks it, so the two are ordered against each other by
    /// nothing but `EventId`'s lexicographic order -- that is, by the
    /// agents' *names*. This runs one fixed scenario under two reviewer
    /// names and both fetch states, and asserts all four reduce.
    ///
    /// Before the check moved to publication time, the four rows read:
    ///   reviewer `bob`, issue fetched     -> Ok  (auth sorts first, never fires)
    ///   reviewer `bob`, issue not fetched -> Ok
    ///   reviewer `zed`, issue fetched     -> Err (issue sorts first, fires)
    ///   reviewer `zed`, issue not fetched -> Ok
    /// which is the whole outage in one table: a rule that enforced itself
    /// only for some spellings of an agent's name, and that wedged exactly
    /// those hosts which had fetched the most.
    #[test]
    fn reduction_never_consults_a_blocking_issue_whatever_the_names_or_fetch_state() {
        // Faithfully reproduces `reduce`'s loop (same `topological_order`,
        // same apply sequence) but on a state that already has a merge
        // engine epoch, which only a test shortcut can install.
        let run = |reviewer_name: &str, include_issue: bool| -> Result<String, String> {
            let alice = a("alice");
            let rev = a(reviewer_name);
            let carol = a("carol");
            let members: Vec<(&str, Role)> = vec![
                ("alice", Role::Implementor),
                (reviewer_name, Role::Reviewer),
                ("carol", Role::Implementor),
                ("coord1", Role::Coordinator),
            ];
            let mut st = empty_state(&members);
            let coord1 = a("coord1");
            let coord1_reg = register(&coord1, Role::Coordinator);
            let alice_reg = register(&alice, Role::Implementor);
            let rev_reg = register(&rev, Role::Reviewer);
            let carol_reg = register(&carol, Role::Implementor);
            apply_ok(&mut st, &coord1_reg);
            apply_ok(&mut st, &alice_reg);
            apply_ok(&mut st, &rev_reg);
            apply_ok(&mut st, &carol_reg);
            let (nominate_env, accept_env) = nominate_and_accept(&mut st, &alice, 1, &rev, 1);
            let epoch = st.roster_epoch.as_ref().unwrap().clone();

            let mut issue_data = match open_issue(&carol, 1, &alice).typed_data().unwrap() {
                EventData::IssueOpened(d) => d,
                _ => unreachable!(),
            };
            issue_data.blocks = StringSet::from_iter([nominate_env.id.clone()]);
            let issue = Envelope::new(
                &carol,
                1,
                frontier_seeing(&[&nominate_env.id]),
                &EventData::IssueOpened(issue_data),
                [nominate_env.id.clone()],
            );
            let auth = Envelope::new(
                &rev,
                2,
                ObservedFrontier::complete(
                    &epoch,
                    epoch.active_members.keys().map(|agent| FrontierEntry {
                        agent: agent.clone(),
                        stream_tip: hash(1),
                        through: if *agent == alice {
                            nominate_env.id.clone()
                        } else if *agent == carol {
                            issue.id.clone()
                        } else {
                            EventId::new(agent, 0)
                        },
                    }),
                )
                .expect("a complete frontier"),
                &EventData::ReviewMergeAuthorized(merge_authorized(
                    &nominate_env.id,
                    StringSet::default(),
                    &[],
                )),
                [nominate_env.id.clone()],
            );

            let mut carol_stream = vec![carol_reg.clone()];
            if include_issue {
                carol_stream.push(issue.clone());
            }
            let streams: BTreeMap<Agent, Vec<Envelope>> = BTreeMap::from([
                (alice.clone(), vec![alice_reg.clone(), nominate_env.clone()]),
                (
                    rev.clone(),
                    vec![rev_reg.clone(), accept_env.clone(), auth.clone()],
                ),
                (carol.clone(), carol_stream),
                (coord1.clone(), vec![coord1_reg.clone()]),
            ]);
            let order = topological_order(&streams).expect("topo order");
            let order_str = order
                .iter()
                .map(|e| e.id.to_string())
                .collect::<Vec<_>>()
                .join(" ");

            // Replay onto a state carrying only the merge-engine setup.
            let mut replay = empty_state(&members);
            replay.current_merge_engine_epoch = st.current_merge_engine_epoch.clone();
            replay.merge_engine_info = st.merge_engine_info.clone();
            for env in order {
                if let Err(e) = apply_event(&mut replay, env) {
                    return Err(format!("[{order_str}] FAILED at {}: {e}", env.id));
                }
                replay.kind_of_event_insert(env.id.clone(), &env.kind);
                replay.events.insert(env.id.clone(), env.clone());
                if let Some(ag) = replay.agents.get_mut(&env.agent) {
                    ag.next_seq = ag.next_seq.max(env.seq + 1);
                }
            }
            Ok(format!("[{order_str}] OK"))
        };

        for name in ["bob", "zed"] {
            for include in [true, false] {
                if let Err(m) = run(name, include) {
                    panic!("reduction must not depend on agent naming or fetch state (reviewer={name}, issue fetched={include}): {m}");
                }
            }
        }
    }

    /// Round-9 sweep, C3: two coordinators activating a schema without
    /// having observed each other.
    ///
    /// `schema.activated` names no predecessor, so `topological_order` -- which
    /// builds edges from `refs` and each stream's own predecessor, never from
    /// `observed` -- puts no edge between the two, and the complete-frontier
    /// requirement buys nothing towards ordering them. Replaying the higher
    /// version first hit "schema version 2 is not greater than the currently
    /// activated 3"; `reduce`'s bare `?` turns that into every host on the
    /// fleet permanently unable to reduce an append-only log.
    ///
    /// Both halves are asserted here because the second is the one that shows
    /// this was never merely an ordering nuisance: two coordinators activating
    /// the *same* version -- an ordinary duplicate, not misuse -- were fatal
    /// in *both* orders. See `coordinator::drain_outbox_rejects_a_schema_
    /// activation_that_does_not_advance` for the paired half: the advancement
    /// rule itself is still enforced, at publication, where the question has
    /// one answer.
    #[test]
    fn two_concurrent_schema_activations_reduce_and_converge_in_either_order() {
        let c1 = a("c-one");
        let c2 = a("c-two");
        let epoch = epoch_with(&[("c-one", Role::Coordinator), ("c-two", Role::Coordinator)]);
        let mut known_epochs = BTreeMap::new();
        known_epochs.insert(epoch.id.clone(), epoch.clone());
        let c1_reg = register(&c1, Role::Coordinator);
        let c2_reg = register(&c2, Role::Coordinator);
        let base = reduce(
            config(),
            Some(epoch.clone()),
            known_epochs,
            &BTreeMap::from([
                (c1.clone(), vec![c1_reg.clone()]),
                (c2.clone(), vec![c2_reg.clone()]),
            ]),
        )
        .expect("the registration prefix reduces");

        let activate = |who: &Agent, version: u32| {
            Envelope::new(
                who,
                1,
                complete_seeing(&base, &[]),
                &EventData::SchemaActivated(SchemaActivated {
                    version,
                    design_commit: hash(11),
                    helper_commit: hash(12),
                }),
                [],
            )
        };

        // Different versions: the descending order used to be fatal.
        let v2 = activate(&c1, 2);
        let v3 = activate(&c2, 3);
        let ascending = reduce_onto(base.clone(), &[v2.clone(), v3.clone()])
            .expect("v2-then-v3 reduces (it always did)");
        let descending = reduce_onto(base.clone(), &[v3.clone(), v2.clone()])
            .expect("v3-then-v2 must reduce too, or every host that fetched c-two first wedges");
        for (label, state) in [("ascending", &ascending), ("descending", &descending)] {
            assert_eq!(
                state.activated_schema_version, 3,
                "{label}: the higher activation must actually be recorded, not skipped"
            );
            assert!(
                state.events.contains_key(&v2.id) && state.events.contains_key(&v3.id),
                "{label}: both activations must be reduced, not dropped"
            );
        }
        // The whole state, not one field. A narrow compare has already let a
        // real order-dependent write through in this file -- see
        // `an_authorization_racing_a_blocking_issue_converges_in_either_order`.
        assert_eq!(
            format!("{ascending:#?}"),
            format!("{descending:#?}"),
            "the two valid orders must converge on identical state"
        );

        // Same version from both coordinators: this pair was fatal in *both*
        // orders, so neither host could reduce at all.
        let same_a = activate(&c1, 2);
        let same_b = activate(&c2, 2);
        let forward = reduce_onto(base.clone(), &[same_a.clone(), same_b.clone()])
            .expect("c-one-then-c-two reduces");
        let reverse = reduce_onto(base.clone(), &[same_b.clone(), same_a.clone()])
            .expect("c-two-then-c-one reduces");
        for (label, state) in [("forward", &forward), ("reverse", &reverse)] {
            assert_eq!(
                state.activated_schema_version, 2,
                "{label}: the activation must actually be recorded"
            );
            assert!(
                state.events.contains_key(&same_a.id) && state.events.contains_key(&same_b.id),
                "{label}: both activations must be reduced, not dropped"
            );
        }
        assert_eq!(
            format!("{forward:#?}"),
            format!("{reverse:#?}"),
            "two coordinators activating the same version must converge"
        );
    }

    /// Round-9 sweep, C4: an author and a coordinator independently picking
    /// the same alternate reviewer.
    ///
    /// The replacement-reviewer check used to compare against `chain.
    /// current_request.reviewer`, which the first of two concurrent
    /// candidates has already moved by the time the second is applied --
    /// and nothing either event carries references the other, so
    /// `topological_order` is free to pick either. Both orders therefore hit
    /// "replacement reviewer must differ from the current reviewer" and the
    /// whole bus stopped reducing on every host.
    ///
    /// Comparing against the *replaced* link's own reviewer is the sound
    /// reading: `d.replaces` is in `refs`, so its entry is already applied,
    /// and it is written once and never rewritten. The last block asserts the
    /// rule still bites, so this is a re-pointing rather than a deletion.
    #[test]
    fn two_reassignments_naming_the_same_replacement_reviewer_reduce_and_converge() {
        let alice = a("alice");
        let bob = a("bob");
        let zed = a("zed");
        let coord1 = a("coord1");
        let epoch = epoch_with(&[
            ("alice", Role::Implementor),
            ("bob", Role::Reviewer),
            ("zed", Role::Reviewer),
            ("coord1", Role::Coordinator),
        ]);
        let mut known_epochs = BTreeMap::new();
        known_epochs.insert(epoch.id.clone(), epoch.clone());

        let alice_reg = register(&alice, Role::Implementor);
        let bob_reg = register(&bob, Role::Reviewer);
        let zed_reg = register(&zed, Role::Reviewer);
        let coord1_reg = register(&coord1, Role::Coordinator);
        let request = review_request(&[&alice], &bob);
        let nominate_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::ReviewNominated(request.clone()),
            [],
        );
        let base = reduce(
            config(),
            Some(epoch.clone()),
            known_epochs,
            &BTreeMap::from([
                (alice.clone(), vec![alice_reg, nominate_env.clone()]),
                (bob.clone(), vec![bob_reg]),
                (zed.clone(), vec![zed_reg]),
                (coord1.clone(), vec![coord1_reg]),
            ]),
        )
        .expect("the nomination prefix reduces");

        let reassign_to = |who: &Agent, seq: u64, reviewer: &Agent, reason: &str| {
            Envelope::new(
                who,
                seq,
                frontier_seeing(&[&nominate_env.id]),
                &EventData::ReviewReassigned(ReviewReassigned {
                    authors: request.authors.clone(),
                    product_branch: request.product_branch.clone(),
                    reviewer: reviewer.clone(),
                    required_checks: request.required_checks.clone(),
                    review_scope: request.review_scope.clone(),
                    summary: request.summary.clone(),
                    target_branch: request.target_branch.clone(),
                    evidence: request.evidence.clone(),
                    replaces: nominate_env.id.clone(),
                    reason: text(reason),
                    inherited_findings: vec![],
                }),
                [],
            )
        };
        let by_author = reassign_to(&alice, 2, &zed, "author picked zed");
        let by_coord = reassign_to(&coord1, 1, &zed, "coordinator also picked zed");

        let author_first = reduce_onto(base.clone(), &[by_author.clone(), by_coord.clone()])
            .expect("author-then-coordinator must reduce");
        let coord_first = reduce_onto(base.clone(), &[by_coord.clone(), by_author.clone()])
            .expect("coordinator-then-author must reduce");
        for (label, state) in [
            ("author_first", &author_first),
            ("coord_first", &coord_first),
        ] {
            // Both candidates must have been *recorded* as competing claims,
            // not quietly skipped: that is what turns the race into the
            // documented lifecycle conflict a coordinator can then resolve.
            assert!(
                state.exclusive.is_contested(&by_author.id)
                    && state.exclusive.is_contested(&by_coord.id),
                "{label}: both reassignments must join the same exclusive group"
            );
            let chain = state
                .review_chain(&nominate_env.id)
                .expect("the chain still resolves");
            assert_eq!(
                chain.decline_or_withdraw_or_reassign_status,
                ItemStatus::LifecycleConflict,
                "{label}: the chain must be left contested, awaiting a resolution"
            );
        }
        assert_eq!(
            format!("{author_first:#?}"),
            format!("{coord_first:#?}"),
            "the two valid orders must converge on identical state"
        );

        // The rule itself is intact: naming the replaced link's own reviewer
        // is still refused, in the one reading that gives the same answer in
        // every order.
        let to_the_same_reviewer = reassign_to(&alice, 2, &bob, "pointless");
        let err = reduce_onto(base, &[to_the_same_reviewer])
            .expect_err("replacing bob's link with bob again is still refused");
        assert!(
            err.to_string().contains(
                "replacement reviewer must differ from the replaced nomination's reviewer"
            ),
            "{err}"
        );
    }

    /// Round-9 sweep, C5: a reassignment racing the reviewer's own clearing
    /// of a finding it inherits.
    ///
    /// The reassignment references the `review.changes_requested` its
    /// inherited findings came from, but nothing references the
    /// `review.findings_cleared` that closes one -- so `topological_order`
    /// may put the clear either side of it. Clear-first shrank the open set
    /// out from under "inherited_findings must equal every still-open finding
    /// exactly once" and the whole bus stopped reducing; reassign-first was
    /// fine. See `coordinator::drain_outbox_rejects_a_reassignment_that_drops
    /// _an_open_finding` for the paired half: the equality is still enforced,
    /// at publication, against a view that actually exists.
    #[test]
    fn a_reassignment_racing_a_finding_clear_reduces_and_converges_in_either_order() {
        let alice = a("alice");
        let bob = a("bob");
        let zed = a("zed");
        let epoch = epoch_with(&[
            ("alice", Role::Implementor),
            ("bob", Role::Reviewer),
            ("zed", Role::Reviewer),
        ]);
        let mut known_epochs = BTreeMap::new();
        known_epochs.insert(epoch.id.clone(), epoch.clone());

        let alice_reg = register(&alice, Role::Implementor);
        let bob_reg = register(&bob, Role::Reviewer);
        let zed_reg = register(&zed, Role::Reviewer);
        let request = review_request(&[&alice], &bob);
        let nominate_env = Envelope::new(
            &alice,
            1,
            no_frontier(),
            &EventData::ReviewNominated(request.clone()),
            [],
        );
        let accept_env = Envelope::new(
            &bob,
            1,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                nomination: nominate_env.id.clone(),
                note: text(""),
            }),
            [],
        );
        let changes_env = Envelope::new(
            &bob,
            2,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewChangesRequested(ReviewChangesRequested {
                nomination: nominate_env.id.clone(),
                reviewed_commit: hash(5),
                findings: vec![finding("f1")],
                evidence: StringSet::default(),
            }),
            [],
        );
        let base = reduce(
            config(),
            Some(epoch.clone()),
            known_epochs,
            &BTreeMap::from([
                (alice.clone(), vec![alice_reg, nominate_env.clone()]),
                (
                    bob.clone(),
                    vec![bob_reg, accept_env.clone(), changes_env.clone()],
                ),
                (zed.clone(), vec![zed_reg]),
            ]),
        )
        .expect("the changes-requested prefix reduces");

        let clear_env = Envelope::new(
            &bob,
            3,
            frontier_seeing(&[&nominate_env.id]),
            &EventData::ReviewFindingsCleared(ReviewFindingsCleared {
                nomination: nominate_env.id.clone(),
                changes_event: changes_env.id.clone(),
                finding_id: short("f1"),
                resolved_commit: hash(6),
                summary: text("fixed"),
            }),
            [],
        );
        let reassign_env = Envelope::new(
            &alice,
            2,
            frontier_seeing(&[&nominate_env.id, &changes_env.id]),
            &EventData::ReviewReassigned(ReviewReassigned {
                authors: request.authors.clone(),
                product_branch: request.product_branch.clone(),
                reviewer: zed.clone(),
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

        let reassign_first = reduce_onto(base.clone(), &[reassign_env.clone(), clear_env.clone()])
            .expect("reassign-then-clear must reduce (it always did)");
        let clear_first = reduce_onto(base.clone(), &[clear_env.clone(), reassign_env.clone()])
            .expect(
                "clear-then-reassign must reduce too, or every host that fetched bob first wedges",
            );
        for (label, state) in [
            ("reassign_first", &reassign_first),
            ("clear_first", &clear_first),
        ] {
            let chain = state
                .review_chain(&reassign_env.id)
                .expect("the reassignment must extend the chain, not be skipped");
            assert_eq!(
                chain.current_nomination, reassign_env.id,
                "{label}: the reassignment must actually take effect"
            );
            assert_eq!(
                chain.nomination_reviewer.get(&reassign_env.id),
                Some(&zed),
                "{label}: the new link must name the replacement reviewer"
            );
            let disposed = chain
                .findings
                .get(&(changes_env.id.clone(), "f1".to_string()))
                .expect("the finding survives the transfer");
            assert_eq!(
                disposed.disposition,
                FindingDisposition::Cleared {
                    by_event: clear_env.id.clone()
                },
                "{label}: the clear must actually be recorded, not silently skipped"
            );
        }
        assert_eq!(
            format!("{reassign_first:#?}"),
            format!("{clear_first:#?}"),
            "the two valid orders must converge on identical state"
        );
    }
}
