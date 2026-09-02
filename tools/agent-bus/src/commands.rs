//! CLI command handlers for everything except review/merge (see
//! `review_cmds.rs`) and validation (see `validate_cmd.rs`).

use crate::bus::{self, BusCtx};
use crate::error::{invalid, AbResult};
use crate::events::*;
use crate::scalars::*;
use crate::state::{AgentState, BusState, ItemStatus};
use serde_json::Value;

fn inject(mut v: Value, fields: &[(&str, Value)]) -> Value {
    if let Value::Object(map) = &mut v {
        for (k, val) in fields {
            map.insert(k.to_string(), val.clone());
        }
    }
    v
}

fn from_value<T: serde::de::DeserializeOwned>(v: Value) -> AbResult<T> {
    serde_json::from_value(v).map_err(|e| invalid(format!("invalid payload: {e}")))
}

// -------------------------------------------------------------- lifecycle

pub fn register(ctx: &BusCtx, args: &crate::cli::RegisterArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let role = parse_role(&args.role)?;
    let data = EventData::AgentRegistered(AgentRegistered {
        display_name: Short::parse(args.display_name.clone())?,
        primary_role: role,
        purpose: Text::parse(args.purpose.clone())?,
        product_base: args.product_base.clone().map(ObjectId::parse).transpose()?,
        product_branch: args.product_branch.clone().map(Branch::parse).transpose()?,
        provider: args.provider.clone().map(Short::parse).transpose()?,
        model: args.model.clone().map(Short::parse).transpose()?,
    });
    if role == Role::Coordinator {
        return Err(invalid("coordinators register only via bootstrap-init"));
    }
    // A fresh registration is its own agent.registered event with seq 0; the
    // helper does not yet know the agent, so publish_event's state lookup
    // (which requires an existing AgentState) cannot be reused verbatim.
    register_new_agent(ctx, &agent, data)
}

pub(crate) fn register_new_agent(ctx: &BusCtx, agent: &Agent, data: EventData) -> AbResult<()> {
    let _lock = ctx.lock()?;
    ctx.fetch_remote()?;
    let wt = ctx.ensure_worktree(agent)?;

    let target = crate::gitrepo::rev_parse(&ctx.repo_root, bus::BUS_BRANCH)?;
    let head = crate::gitrepo::rev_parse(&wt, "HEAD")?;
    if head != target {
        crate::gitrepo::checkout_detach(&wt, &target)?;
    }
    let state = ctx.load_state_at(&target)?;
    if state.agents.contains_key(agent) {
        return Err(invalid(format!("{agent} is already registered")));
    }
    let observed = Some(ObjectId::parse(target.clone())?);
    let env = crate::envelope::Envelope::new(agent, 0, observed, &data, []);
    crate::apply::dry_run(&state, &env)?;
    crate::storage::append_event(&wt, &env)?;
    crate::gitrepo::add_all(&wt)?;
    crate::gitrepo::commit(&wt, &format!("agent-bus: {agent} agent.registered"))?;

    let mut attempts = 0;
    loop {
        attempts += 1;
        let push = crate::gitrepo::push(&wt, ".", &format!("HEAD:{}", bus::BUS_BRANCH))?;
        if push.success {
            ctx.push_remote()?;
            println!("registered {agent} at {}", env.id);
            return Ok(());
        }
        if attempts >= 10 {
            return Err(invalid("push failed after repeated retries"));
        }
        ctx.fetch_remote()?;
        let new_target = crate::gitrepo::rev_parse(&ctx.repo_root, bus::BUS_BRANCH)?;
        let rebase = crate::gitrepo::rebase_onto(&wt, &new_target)?;
        if !rebase.success {
            crate::gitrepo::rebase_abort(&wt)?;
            return Err(invalid(format!(
                "rebasing {agent}'s registration onto {new_target} conflicted: {}",
                rebase.stderr
            )));
        }
    }
}

fn parse_role(s: &str) -> AbResult<Role> {
    match s {
        "implementor" => Ok(Role::Implementor),
        "reviewer" => Ok(Role::Reviewer),
        "coordinator" => Ok(Role::Coordinator),
        "observer" => Ok(Role::Observer),
        other => Err(invalid(format!("unknown role: {other}"))),
    }
}

fn parse_status(s: &str) -> AbResult<LifecycleStatus> {
    match s {
        "active" => Ok(LifecycleStatus::Active),
        "blocked" => Ok(LifecycleStatus::Blocked),
        "paused" => Ok(LifecycleStatus::Paused),
        "done" => Ok(LifecycleStatus::Done),
        "abandoned" => Ok(LifecycleStatus::Abandoned),
        other => Err(invalid(format!("unknown status: {other}"))),
    }
}

pub fn status_set(ctx: &BusCtx, args: &crate::cli::StatusSetArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let data = EventData::AgentStatus(AgentStatusEvent {
        status: parse_status(&args.status)?,
        note: Text::parse(args.note.clone())?,
        product_branch: args.product_branch.clone().map(Branch::parse).transpose()?,
        product_commit: args.product_commit.clone().map(ObjectId::parse).transpose()?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn resume(ctx: &BusCtx, args: &crate::cli::ResumeArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let state = ctx.load_state()?;
    let (data, refs) = build_resume(&state, &agent, &args.reason, &args.user_authority)?;
    let env = bus::publish_event(ctx, &agent, data, refs)?;
    println!("published {}", env.id);
    Ok(())
}

fn build_resume(state: &BusState, agent: &Agent, reason: &str, user_authority: &str) -> AbResult<(EventData, Vec<EventId>)> {
    let ag = state
        .agent(agent)
        .ok_or_else(|| invalid(format!("{agent} is not registered")))?;
    let previous = ag.last_lifecycle_event.clone();
    let data = EventData::AgentResumed(AgentResumed {
        previous_lifecycle: previous.clone(),
        reason: Text::parse(reason.to_string())?,
        user_authority: Text::parse(user_authority.to_string())?,
    });
    Ok((data, vec![previous]))
}

pub fn retire(ctx: &BusCtx, args: &crate::cli::RetireArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let target = Agent::parse(args.target.clone())?;
    let state = ctx.load_state()?;
    let (data, refs) = build_retire(&state, &target, &args.reason, &args.user_authority)?;
    let env = bus::publish_event(ctx, &agent, data, refs)?;
    println!("published {}", env.id);
    Ok(())
}

fn build_retire(state: &BusState, target: &Agent, reason: &str, user_authority: &str) -> AbResult<(EventData, Vec<EventId>)> {
    let tgt = state
        .agent(target)
        .ok_or_else(|| invalid(format!("{target} is not registered")))?;
    let previous = tgt.last_lifecycle_event.clone();
    let data = EventData::AgentRetired(AgentRetired {
        target: target.clone(),
        previous_lifecycle: previous.clone(),
        reason: Text::parse(reason.to_string())?,
        user_authority: Text::parse(user_authority.to_string())?,
    });
    Ok((data, vec![previous]))
}

pub fn schema_activate(ctx: &BusCtx, args: &crate::cli::SchemaActivateArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let data = EventData::SchemaActivated(SchemaActivated {
        version: args.version,
        design_commit: ObjectId::parse(args.design_commit.clone())?,
        helper_commit: ObjectId::parse(args.helper_commit.clone())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn merge_engine_activate(ctx: &BusCtx, args: &crate::cli::MergeEngineActivateArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let previous_epoch = EventId::parse(args.previous_epoch.clone())?;
    let data = EventData::MergeEngineActivated(MergeEngineActivated {
        previous_epoch: previous_epoch.clone(),
        merge_engine: Short::parse(args.merge_engine.clone())?,
        merge_engine_version: Short::parse(args.merge_engine_version.clone())?,
        design_commit: ObjectId::parse(args.design_commit.clone())?,
        helper_commit: ObjectId::parse(args.helper_commit.clone())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![previous_epoch])?;
    println!("published {}", env.id);
    Ok(())
}

// -------------------------------------------------------- scope/plan/progress

pub fn scope_set(ctx: &BusCtx, args: &crate::cli::FileAgentArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let v = bus::read_json_file(std::path::Path::new(&args.file))?;
    let data: ScopeSet = from_value(v)?;
    let env = bus::publish_event(ctx, &agent, EventData::ScopeSet(data), vec![])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn plan_set(ctx: &BusCtx, args: &crate::cli::FileAgentArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let v = bus::read_json_file(std::path::Path::new(&args.file))?;
    let data: PlanSet = from_value(v)?;
    let env = bus::publish_event(ctx, &agent, EventData::PlanSet(data), vec![])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn progress(ctx: &BusCtx, args: &crate::cli::ProgressArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let v = bus::read_json_file(std::path::Path::new(&args.file))?;
    let data: ProgressReported = from_value(v)?;
    let env = bus::publish_event(ctx, &agent, EventData::ProgressReported(data), vec![])?;
    println!("published {}", env.id);
    Ok(())
}

// ------------------------------------------------------------------- issues

pub fn issue_open(ctx: &BusCtx, agent: &str, to: &str, file: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let v = inject(v, &[("target", Value::String(to.to_string()))]);
    let data: IssueOpened = from_value(v)?;
    let extra_refs: Vec<EventId> = data.blocks.iter().chain(data.evidence.iter()).cloned().collect();
    let env = bus::publish_event(ctx, &agent, EventData::IssueOpened(data), extra_refs)?;
    println!("opened {}", env.id);
    Ok(())
}

pub fn issue_acknowledge(ctx: &BusCtx, agent: &str, issue_id: &str, note: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let issue_id = EventId::parse(issue_id.to_string())?;
    let state = ctx.load_state()?;
    let (data, refs) = build_issue_ack(&state, &issue_id, note)?;
    let env = bus::publish_event(ctx, &agent, data, refs)?;
    println!("published {}", env.id);
    Ok(())
}

fn build_issue_ack(state: &BusState, issue_id: &EventId, note: &str) -> AbResult<(EventData, Vec<EventId>)> {
    let issue = state
        .issues
        .get(issue_id)
        .ok_or_else(|| invalid(format!("unknown issue {issue_id}")))?;
    let assignment = issue.current_assignment.clone();
    let data = EventData::IssueAcknowledged(IssueAcknowledged {
        issue: issue_id.clone(),
        assignment: assignment.clone(),
        note: Text::parse(note.to_string())?,
    });
    Ok((data, vec![issue_id.clone(), assignment]))
}

pub fn issue_resolve(ctx: &BusCtx, agent: &str, issue_id: &str, file: &str) -> AbResult<()> {
    issue_terminal(ctx, agent, issue_id, file, true)
}

pub fn issue_reject(ctx: &BusCtx, agent: &str, issue_id: &str, file: &str) -> AbResult<()> {
    issue_terminal(ctx, agent, issue_id, file, false)
}

fn issue_terminal(ctx: &BusCtx, agent: &str, issue_id: &str, file: &str, resolve: bool) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let issue_id = EventId::parse(issue_id.to_string())?;
    let state = ctx.load_state()?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let (data, refs) = build_issue_terminal(&state, &issue_id, v, resolve)?;
    let env = bus::publish_event(ctx, &agent, data, refs)?;
    println!("published {}", env.id);
    Ok(())
}

fn build_issue_terminal(state: &BusState, issue_id: &EventId, v: Value, resolve: bool) -> AbResult<(EventData, Vec<EventId>)> {
    let issue = state
        .issues
        .get(issue_id)
        .ok_or_else(|| invalid(format!("unknown issue {issue_id}")))?;
    let assignment = issue.current_assignment.clone();
    let v = inject(
        v,
        &[
            ("issue", Value::String(issue_id.to_string())),
            ("assignment", Value::String(assignment.to_string())),
        ],
    );
    if resolve {
        let d: IssueResolved = from_value(v)?;
        Ok((EventData::IssueResolved(d), vec![issue_id.clone(), assignment]))
    } else {
        let d: IssueRejected = from_value(v)?;
        Ok((EventData::IssueRejected(d), vec![issue_id.clone(), assignment]))
    }
}

pub fn issue_reassign(ctx: &BusCtx, agent: &str, issue_id: &str, new_target: &str, reason: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let issue_id = EventId::parse(issue_id.to_string())?;
    let new_target = Agent::parse(new_target.to_string())?;
    let state = ctx.load_state()?;
    let (data, refs) = build_issue_reassign(&state, &issue_id, new_target, reason)?;
    let env = bus::publish_event(ctx, &agent, data, refs)?;
    println!("published {}", env.id);
    Ok(())
}

fn build_issue_reassign(state: &BusState, issue_id: &EventId, new_target: Agent, reason: &str) -> AbResult<(EventData, Vec<EventId>)> {
    let issue = state
        .issues
        .get(issue_id)
        .ok_or_else(|| invalid(format!("unknown issue {issue_id}")))?;
    let previous_assignment = issue.current_assignment.clone();
    let previous_target = issue.current_target.clone();
    let data = EventData::IssueReassigned(IssueReassigned {
        issue: issue_id.clone(),
        previous_assignment: previous_assignment.clone(),
        previous_target,
        new_target,
        reason: Text::parse(reason.to_string())?,
    });
    Ok((data, vec![issue_id.clone(), previous_assignment]))
}

// -------------------------------------------------------------- dependencies

pub fn dependency_request(ctx: &BusCtx, agent: &str, to: &str, file: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let v = inject(v, &[("target", Value::String(to.to_string()))]);
    let data: DependencyRequested = from_value(v)?;
    let refs: Vec<EventId> = data.evidence.iter().cloned().collect();
    let env = bus::publish_event(ctx, &agent, EventData::DependencyRequested(data), refs)?;
    println!("opened {}", env.id);
    Ok(())
}

pub fn dependency_acknowledge(ctx: &BusCtx, agent: &str, dep_id: &str, note: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let dep_id = EventId::parse(dep_id.to_string())?;
    let state = ctx.load_state()?;
    let (data, refs) = build_dependency_ack(&state, &dep_id, note)?;
    let env = bus::publish_event(ctx, &agent, data, refs)?;
    println!("published {}", env.id);
    Ok(())
}

fn build_dependency_ack(state: &BusState, dep_id: &EventId, note: &str) -> AbResult<(EventData, Vec<EventId>)> {
    let dep = state
        .dependencies
        .get(dep_id)
        .ok_or_else(|| invalid(format!("unknown dependency {dep_id}")))?;
    let assignment = dep.current_assignment.clone();
    let data = EventData::DependencyAcknowledged(DependencyAcknowledged {
        dependency: dep_id.clone(),
        assignment: assignment.clone(),
        note: Text::parse(note.to_string())?,
    });
    Ok((data, vec![dep_id.clone(), assignment]))
}

pub fn dependency_resolve(ctx: &BusCtx, agent: &str, dep_id: &str, file: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let dep_id = EventId::parse(dep_id.to_string())?;
    let state = ctx.load_state()?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let (data, refs) = build_dependency_resolve(&state, &dep_id, v)?;
    let env = bus::publish_event(ctx, &agent, data, refs)?;
    println!("published {}", env.id);
    Ok(())
}

fn build_dependency_resolve(state: &BusState, dep_id: &EventId, v: Value) -> AbResult<(EventData, Vec<EventId>)> {
    let dep = state
        .dependencies
        .get(dep_id)
        .ok_or_else(|| invalid(format!("unknown dependency {dep_id}")))?;
    let assignment = dep.current_assignment.clone();
    let v = inject(
        v,
        &[
            ("dependency", Value::String(dep_id.to_string())),
            ("assignment", Value::String(assignment.to_string())),
        ],
    );
    let data: DependencyResolved = from_value(v)?;
    Ok((EventData::DependencyResolved(data), vec![dep_id.clone(), assignment]))
}

pub fn dependency_reject(ctx: &BusCtx, agent: &str, dep_id: &str, reason: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let dep_id = EventId::parse(dep_id.to_string())?;
    let state = ctx.load_state()?;
    let (data, refs) = build_dependency_reject(&state, &dep_id, reason)?;
    let env = bus::publish_event(ctx, &agent, data, refs)?;
    println!("published {}", env.id);
    Ok(())
}

fn build_dependency_reject(state: &BusState, dep_id: &EventId, reason: &str) -> AbResult<(EventData, Vec<EventId>)> {
    let dep = state
        .dependencies
        .get(dep_id)
        .ok_or_else(|| invalid(format!("unknown dependency {dep_id}")))?;
    let assignment = dep.current_assignment.clone();
    let data = EventData::DependencyRejected(DependencyRejected {
        dependency: dep_id.clone(),
        assignment: assignment.clone(),
        reason: Text::parse(reason.to_string())?,
    });
    Ok((data, vec![dep_id.clone(), assignment]))
}

pub fn dependency_reassign(ctx: &BusCtx, agent: &str, dep_id: &str, new_target: &str, reason: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let dep_id = EventId::parse(dep_id.to_string())?;
    let new_target = Agent::parse(new_target.to_string())?;
    let state = ctx.load_state()?;
    let (data, refs) = build_dependency_reassign(&state, &dep_id, new_target, reason)?;
    let env = bus::publish_event(ctx, &agent, data, refs)?;
    println!("published {}", env.id);
    Ok(())
}

fn build_dependency_reassign(
    state: &BusState,
    dep_id: &EventId,
    new_target: Agent,
    reason: &str,
) -> AbResult<(EventData, Vec<EventId>)> {
    let dep = state
        .dependencies
        .get(dep_id)
        .ok_or_else(|| invalid(format!("unknown dependency {dep_id}")))?;
    let previous_assignment = dep.current_assignment.clone();
    let previous_target = dep.current_target.clone();
    let data = EventData::DependencyReassigned(DependencyReassigned {
        dependency: dep_id.clone(),
        previous_assignment: previous_assignment.clone(),
        previous_target,
        new_target,
        reason: Text::parse(reason.to_string())?,
    });
    Ok((data, vec![dep_id.clone(), previous_assignment]))
}

// ---------------------------------------------------------------- handoffs

pub fn handoff_offer(ctx: &BusCtx, agent: &str, file: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let data: HandoffOffered = from_value(v)?;
    let refs: Vec<EventId> = data.known_issues.iter().chain(data.evidence.iter()).cloned().collect();
    let env = bus::publish_event(ctx, &agent, EventData::HandoffOffered(data), refs)?;
    println!("offered {}", env.id);
    Ok(())
}

pub fn handoff_accept(ctx: &BusCtx, agent: &str, handoff_id: &str, note: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let handoff_id = EventId::parse(handoff_id.to_string())?;
    let data = EventData::HandoffAccepted(HandoffAccepted {
        handoff: handoff_id.clone(),
        note: Text::parse(note.to_string())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![handoff_id])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn handoff_decline(ctx: &BusCtx, agent: &str, handoff_id: &str, reason: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let handoff_id = EventId::parse(handoff_id.to_string())?;
    let data = EventData::HandoffDeclined(HandoffDeclined {
        handoff: handoff_id.clone(),
        reason: Text::parse(reason.to_string())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![handoff_id])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn handoff_withdraw(ctx: &BusCtx, agent: &str, handoff_id: &str, reason: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let handoff_id = EventId::parse(handoff_id.to_string())?;
    let data = EventData::HandoffWithdrawn(HandoffWithdrawn {
        handoff: handoff_id.clone(),
        reason: Text::parse(reason.to_string())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![handoff_id])?;
    println!("published {}", env.id);
    Ok(())
}

// ------------------------------------------------------------- lifecycle-conflict

pub fn lifecycle_resolve(ctx: &BusCtx, args: &crate::cli::FileAgentArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let v = bus::read_json_file(std::path::Path::new(&args.file))?;
    let data: LifecycleConflictResolved = from_value(v)?;
    let mut refs = vec![data.root.clone()];
    refs.extend(data.competing.iter().cloned());
    let env = bus::publish_event(ctx, &agent, EventData::LifecycleConflictResolved(data), refs)?;
    println!("published {}", env.id);
    Ok(())
}

// -------------------------------------------------------------------- sync

pub fn sync(ctx: &BusCtx, args: &crate::cli::SyncArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let tip = ctx.sync(&agent)?;
    println!("synced {agent}, agent-bus at {tip}");
    Ok(())
}

// ------------------------------------------------------------------- queries

pub fn status(ctx: &BusCtx, args: &crate::cli::StatusArgs) -> AbResult<()> {
    let state = ctx.load_state()?;
    let agents = select_agents(&state, &args.agent)?;
    if args.json {
        let arr: Vec<Value> = agents.iter().map(|a| agent_summary(a)).collect();
        println!("{}", serde_json::to_string_pretty(&arr)?);
    } else {
        for a in agents {
            println!(
                "{:<24} role={:<12} status={:<10} active={} {}",
                a.agent.as_str(),
                a.primary_role.to_string(),
                format!("{:?}", a.status).to_lowercase(),
                a.active(),
                a.status_note.as_str()
            );
        }
    }
    Ok(())
}

fn select_agents<'a>(state: &'a BusState, agent: &Option<String>) -> AbResult<Vec<&'a AgentState>> {
    match agent {
        Some(a) => {
            let a = Agent::parse(a.clone())?;
            Ok(vec![state.agent(&a).ok_or_else(|| invalid(format!("unknown agent {a}")))?])
        }
        None => Ok(state.agents.values().collect()),
    }
}

fn agent_summary(a: &crate::state::AgentState) -> Value {
    serde_json::json!({
        "agent": a.agent.as_str(),
        "display_name": a.display_name.as_str(),
        "primary_role": a.primary_role.to_string(),
        "purpose": a.purpose.as_str(),
        "provider": a.provider.as_ref().map(|p| p.as_str()),
        "model": a.model.as_ref().map(|m| m.as_str()),
        "status": format!("{:?}", a.status).to_lowercase(),
        "active": a.active(),
        "retired": a.retired,
        "product_branch": a.product_branch.as_ref().map(|b| b.as_str().to_string()),
        "product_commit": a.product_commit.as_ref().map(|c| c.as_str().to_string()),
        "scope": a.scope.as_ref().map(|s| serde_json::to_value(s).unwrap()),
        "plan": a.plan.as_ref().map(|p| serde_json::to_value(p).unwrap()),
    })
}

pub fn inbox(ctx: &BusCtx, args: &crate::cli::InboxArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let state = ctx.load_state()?;
    let items = inbox_items(&state, &agent);
    if args.json {
        println!("{}", serde_json::to_string_pretty(&items)?);
    } else {
        for i in &items {
            println!("{i}");
        }
        if items.is_empty() {
            println!("(empty)");
        }
    }
    Ok(())
}

/// Not yet terminally resolved — includes `LifecycleConflict` items, which
/// still need attention (a coordinator's `lifecycle.conflict_resolved`),
/// not just plain `Open` ones.
fn still_open(s: &ItemStatus) -> bool {
    !matches!(s, ItemStatus::Terminal(_))
}

fn inbox_items(state: &BusState, agent: &Agent) -> Vec<Value> {
    let mut items = Vec::new();
    for issue in state.issues.values() {
        if issue.current_target == *agent && still_open(&issue.status) {
            items.push(serde_json::json!({"kind": "issue", "id": issue.id.to_string(), "summary": issue.data.summary.as_str()}));
        }
    }
    for dep in state.dependencies.values() {
        if dep.current_target == *agent && still_open(&dep.status) {
            items.push(serde_json::json!({"kind": "dependency", "id": dep.id.to_string(), "interface": dep.data.interface.as_str()}));
        }
    }
    for h in state.handoffs.values() {
        if h.data.receiver == *agent && still_open(&h.status) {
            items.push(serde_json::json!({"kind": "handoff", "id": h.id.to_string(), "summary": h.data.summary.as_str()}));
        }
    }
    for chain in state.reviews.values() {
        if chain.current_request.reviewer == *agent && !chain.is_closed() {
            items.push(serde_json::json!({
                "kind": "review",
                "id": chain.current_nomination.to_string(),
                "summary": chain.current_request.summary.as_str(),
            }));
        }
    }
    items
}

pub fn dependencies(ctx: &BusCtx, args: &crate::cli::DependenciesArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let state = ctx.load_state()?;
    let items = dependencies_items(&state, &agent);
    if args.json {
        println!("{}", serde_json::to_string_pretty(&items)?);
    } else {
        for i in &items {
            println!("{i}");
        }
    }
    Ok(())
}

fn dependencies_items(state: &BusState, agent: &Agent) -> Vec<Value> {
    state
        .dependencies
        .values()
        .filter(|d| d.requester == *agent || d.current_target == *agent)
        .map(|d| {
            serde_json::json!({
                "id": d.id.to_string(),
                "requester": d.requester.as_str(),
                "target": d.current_target.as_str(),
                "interface": d.data.interface.as_str(),
                "blocking": d.data.blocking,
                "status": format!("{:?}", d.status),
            })
        })
        .collect()
}

pub fn tail(ctx: &BusCtx, args: &crate::cli::TailArgs) -> AbResult<()> {
    let walk = crate::history::walk_full(&ctx.repo_root, bus::BUS_BRANCH)?;
    let tail = tail_events(&walk, args.agent.as_deref(), args.count);
    if args.json {
        let lines: Vec<String> = tail.iter().map(|e| e.to_canonical_line()).collect();
        println!("[{}]", lines.join(","));
    } else {
        for e in &tail {
            println!("{}", e.to_canonical_line());
        }
    }
    Ok(())
}

fn tail_events(walk: &crate::history::Walk, agent_filter: Option<&str>, count: usize) -> Vec<crate::envelope::Envelope> {
    let mut events = Vec::new();
    for c in &walk.commits {
        for e in &c.new_events {
            if let Some(a) = agent_filter {
                if e.agent.as_str() != a {
                    continue;
                }
            }
            events.push(e.clone());
        }
    }
    let start = events.len().saturating_sub(count);
    events[start..].to_vec()
}

pub fn conflicts(ctx: &BusCtx, args: &crate::cli::ConflictsArgs) -> AbResult<()> {
    let state = ctx.load_state()?;
    let out = conflicts_items(&state);
    if args.json {
        println!("{}", serde_json::to_string_pretty(&out)?);
    } else {
        for o in &out {
            println!("{o}");
        }
        if out.is_empty() {
            println!("(no conflicts)");
        }
    }
    Ok(())
}

fn conflicts_items(state: &BusState) -> Vec<Value> {
    let mut out = Vec::new();

    // Scope conflicts (AGENT_BUS.md section 6.2): exclusive/exclusive overlap
    // is a hard conflict; exclusive/shared overlap is merely reported.
    let actives: Vec<&crate::state::AgentState> = state.agents.values().filter(|a| a.active()).collect();
    for i in 0..actives.len() {
        for j in (i + 1)..actives.len() {
            let (a, b) = (actives[i], actives[j]);
            if let (Some(sa), Some(sb)) = (&a.scope, &b.scope) {
                for pa in sa.exclusive.iter() {
                    for pb in sb.exclusive.iter() {
                        if pa.overlaps(pb) {
                            out.push(serde_json::json!({
                                "kind": "scope",
                                "a": a.agent.as_str(),
                                "b": b.agent.as_str(),
                                "path_a": pa.as_str(),
                                "path_b": pb.as_str(),
                            }));
                        }
                    }
                }
                for (owner, claim, other_owner, other_shared) in [
                    (&a.agent, &sa.exclusive, &b.agent, &sb.shared),
                    (&b.agent, &sb.exclusive, &a.agent, &sa.shared),
                ] {
                    for pa in claim.iter() {
                        for pb in other_shared.iter() {
                            if pa.overlaps(pb) {
                                out.push(serde_json::json!({
                                    "kind": "scope_exclusive_shared",
                                    "exclusive_owner": owner.as_str(),
                                    "shared_owner": other_owner.as_str(),
                                    "path_exclusive": pa.as_str(),
                                    "path_shared": pb.as_str(),
                                }));
                            }
                        }
                    }
                }
            }
        }
    }

    for (key, tracker) in state.exclusive.iter() {
        if tracker.resolved.is_none() && tracker.transitions.len() >= 2 {
            out.push(serde_json::json!({
                "kind": "lifecycle_conflict",
                "predecessor": key,
                "competing": tracker.transitions.iter().map(|(id, _)| id.to_string()).collect::<Vec<_>>(),
            }));
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bootstrap::BusJson;
    use crate::common::Priority;
    use crate::history::{Walk, WalkedCommit};
    use crate::state::{DependencyState, ExclusiveTracker, HandoffState, IssueState, ReviewChain};
    use std::collections::{BTreeMap, BTreeSet};

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
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

    fn eid(agent: &Agent, seq: u64) -> EventId {
        EventId::new(agent, seq)
    }

    /// A `BusCtx` pointing at a fresh, empty temp directory: not a real git
    /// repository, so any code path that actually needs `ctx.load_state()`
    /// or `bus::publish_event` to *succeed* will fail here (real `git`
    /// invocations against a non-repository directory error out quickly and
    /// deterministically). Good enough for exercising every validation
    /// branch that runs *before* those calls, plus the fact that the calls
    /// themselves are reached and their errors propagate.
    fn dummy_ctx() -> (tempfile::TempDir, BusCtx) {
        let dir = tempfile::tempdir().unwrap();
        let ctx = BusCtx { repo_root: dir.path().to_path_buf(), has_origin: false };
        (dir, ctx)
    }

    fn temp_json(content: &str) -> (tempfile::TempDir, String) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("data.json");
        std::fs::write(&path, content).unwrap();
        (dir, path.to_string_lossy().to_string())
    }

    fn bus_json_fixture() -> BusJson {
        BusJson::new("sha1".to_string(), vec![a("coord1")], oid(999)).unwrap()
    }

    fn empty_state() -> BusState {
        BusState::new(bus_json_fixture())
    }

    fn mk_agent(name: &str, role: Role) -> AgentState {
        let agent = a(name);
        AgentState {
            agent: agent.clone(),
            display_name: short(name),
            primary_role: role,
            purpose: text("purpose"),
            provider: None,
            model: None,
            status: LifecycleStatus::Active,
            status_note: text(""),
            product_branch: None,
            product_commit: None,
            last_lifecycle_event: eid(&agent, 0),
            retired: false,
            scope: None,
            plan: None,
            progress_tail: Vec::new(),
            next_seq: 1,
            registered_commit_index: 0,
        }
    }

    fn insert_agent(state: &mut BusState, name: &str, role: Role) -> Agent {
        let ag = mk_agent(name, role);
        let agent = ag.agent.clone();
        state.agents.insert(agent.clone(), ag);
        agent
    }

    fn mk_issue(opener: &Agent, target: &Agent, id: &EventId, status: ItemStatus) -> IssueState {
        IssueState {
            id: id.clone(),
            opener: opener.clone(),
            data: IssueOpened {
                target: target.clone(),
                issue_kind: IssueKind::Bug,
                severity: Priority::Normal,
                summary: text("summary"),
                code_commit: None,
                locations: vec![],
                expected: None,
                observed_behavior: None,
                reproduction: vec![],
                blocks: StringSet::default(),
                evidence: StringSet::default(),
            },
            current_target: target.clone(),
            current_assignment: id.clone(),
            assignment_target: BTreeMap::new(),
            acknowledged: false,
            status,
            resolution_summary: None,
            reassignment_chain: vec![],
        }
    }

    fn mk_dependency(requester: &Agent, target: &Agent, id: &EventId, status: ItemStatus) -> DependencyState {
        DependencyState {
            id: id.clone(),
            requester: requester.clone(),
            data: DependencyRequested {
                target: target.clone(),
                interface: short("iface"),
                needed_by: text("asap"),
                blocking: true,
                summary: text("s"),
                evidence: StringSet::default(),
            },
            current_target: target.clone(),
            current_assignment: id.clone(),
            assignment_target: BTreeMap::new(),
            acknowledged: false,
            status,
            reassignment_chain: vec![],
        }
    }

    fn mk_handoff(offerer: &Agent, receiver: &Agent, id: &EventId, status: ItemStatus) -> HandoffState {
        HandoffState {
            id: id.clone(),
            offerer: offerer.clone(),
            data: HandoffOffered {
                receiver: receiver.clone(),
                scope: StringSet::default(),
                product_branch: branch("refs/heads/x"),
                product_commit: oid(1),
                verification: vec![],
                known_issues: StringSet::default(),
                evidence: StringSet::default(),
                summary: text("s"),
            },
            status,
        }
    }

    fn mk_review_chain(root: &EventId, reviewer: &Agent, closed: bool) -> ReviewChain {
        ReviewChain {
            root: root.clone(),
            nomination_events: vec![root.clone()],
            current_nomination: root.clone(),
            current_request: ReviewRequest {
                authors: StringSet::default(),
                product_branch: branch("refs/heads/x"),
                reviewer: reviewer.clone(),
                required_checks: vec![],
                review_scope: StringSet::default(),
                summary: text("review me"),
                target_branch: branch("refs/heads/main"),
                evidence: StringSet::default(),
            },
            nomination_reviewer: BTreeMap::new(),
            accepted_nominations: BTreeSet::new(),
            decline_or_withdraw_or_reassign_status: ItemStatus::Open,
            findings: BTreeMap::new(),
            authorizations: vec![],
            merged: if closed { vec![root.clone()] } else { vec![] },
            reconciled: vec![],
        }
    }

    fn mk_envelope(agent: &Agent, seq: u64) -> crate::envelope::Envelope {
        crate::envelope::Envelope {
            v: 1,
            id: eid(agent, seq),
            agent: agent.clone(),
            seq,
            time: Timestamp::parse("2024-01-01T00:00:00Z".to_string()).unwrap(),
            observed: None,
            kind: "agent.status".to_string(),
            refs: StringSet::default(),
            data: serde_json::json!({}),
        }
    }

    fn mk_walk(commits: Vec<(Agent, Vec<u64>)>) -> Walk {
        let bus_json = bus_json_fixture();
        let mut wcs = Vec::new();
        for (i, (agent, seqs)) in commits.into_iter().enumerate() {
            let events = seqs.into_iter().map(|s| mk_envelope(&agent, s)).collect();
            wcs.push(WalkedCommit {
                commit: hash(i as u64),
                index: i,
                is_bootstrap_root: false,
                is_repair: false,
                agent: Some(agent),
                new_events: events,
            });
        }
        Walk { commits: wcs, bus_json }
    }

    // ---------------------------------------------------------- register()

    fn base_register_args() -> crate::cli::RegisterArgs {
        crate::cli::RegisterArgs {
            agent: "alice".to_string(),
            display_name: "Alice".to_string(),
            role: "implementor".to_string(),
            purpose: "do things".to_string(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        }
    }

    #[test]
    fn register_rejects_invalid_agent_name() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_register_args();
        args.agent = "Alice".to_string();
        let err = register(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("invalid agent name"), "{err}");
    }

    #[test]
    fn register_rejects_invalid_role() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_register_args();
        args.role = "wizard".to_string();
        let err = register(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("unknown role"), "{err}");
    }

    #[test]
    fn register_rejects_invalid_display_name() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_register_args();
        args.display_name = "".to_string();
        let err = register(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("Short out of bounds"), "{err}");
    }

    #[test]
    fn register_rejects_purpose_too_long() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_register_args();
        args.purpose = "x".repeat(4097);
        let err = register(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("Text out of bounds"), "{err}");
    }

    #[test]
    fn register_rejects_invalid_product_base() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_register_args();
        args.product_base = Some("not-a-hash".to_string());
        let err = register(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("invalid object id"), "{err}");
    }

    #[test]
    fn register_rejects_invalid_product_branch() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_register_args();
        args.product_branch = Some("main".to_string());
        let err = register(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("branch must start with refs/"), "{err}");
    }

    #[test]
    fn register_rejects_invalid_provider() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_register_args();
        args.provider = Some("".to_string());
        let err = register(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("Short out of bounds"), "{err}");
    }

    #[test]
    fn register_rejects_invalid_model() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_register_args();
        args.model = Some("".to_string());
        let err = register(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("Short out of bounds"), "{err}");
    }

    #[test]
    fn register_rejects_coordinator_role() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_register_args();
        args.role = "coordinator".to_string();
        let err = register(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("coordinators register only via bootstrap-init"), "{err}");
    }

    #[test]
    fn parse_role_accepts_all_known_values() {
        for r in ["implementor", "reviewer", "coordinator", "observer"] {
            assert!(parse_role(r).is_ok());
        }
        assert!(parse_role("bogus").is_err());
    }

    // -------------------------------------------------------- status_set()

    fn base_status_set_args() -> crate::cli::StatusSetArgs {
        crate::cli::StatusSetArgs {
            agent: "alice".to_string(),
            status: "active".to_string(),
            note: "".to_string(),
            product_branch: None,
            product_commit: None,
        }
    }

    #[test]
    fn status_set_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_status_set_args();
        args.agent = "BAD".to_string();
        assert!(status_set(&ctx, &args).is_err());
    }

    #[test]
    fn status_set_rejects_invalid_status() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_status_set_args();
        args.status = "sleeping".to_string();
        let err = status_set(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("unknown status"), "{err}");
    }

    #[test]
    fn status_set_rejects_note_too_long() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_status_set_args();
        args.note = "x".repeat(4097);
        assert!(status_set(&ctx, &args).is_err());
    }

    #[test]
    fn status_set_rejects_invalid_product_branch() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_status_set_args();
        args.product_branch = Some("bad".to_string());
        assert!(status_set(&ctx, &args).is_err());
    }

    #[test]
    fn status_set_rejects_invalid_product_commit() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_status_set_args();
        args.product_commit = Some("nothex".to_string());
        assert!(status_set(&ctx, &args).is_err());
    }

    #[test]
    fn parse_status_accepts_all_known_values() {
        for s in ["active", "blocked", "paused", "done", "abandoned"] {
            assert!(parse_status(s).is_ok());
        }
        assert!(parse_status("bogus").is_err());
    }

    // ------------------------------------------------------------ resume/retire

    #[test]
    fn resume_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::ResumeArgs { agent: "BAD".to_string(), reason: "r".to_string(), user_authority: "u".to_string() };
        assert!(resume(&ctx, &args).is_err());
    }

    #[test]
    fn resume_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::ResumeArgs { agent: "alice".to_string(), reason: "r".to_string(), user_authority: "u".to_string() };
        assert!(resume(&ctx, &args).is_err());
    }

    #[test]
    fn build_resume_rejects_unregistered_agent() {
        let state = empty_state();
        let alice = a("alice");
        let err = build_resume(&state, &alice, "reason", "user").unwrap_err();
        assert!(err.to_string().contains("is not registered"), "{err}");
    }

    #[test]
    fn build_resume_builds_expected_event() {
        let mut state = empty_state();
        let alice = insert_agent(&mut state, "alice", Role::Implementor);
        let (data, refs) = build_resume(&state, &alice, "back", "user says so").unwrap();
        match data {
            EventData::AgentResumed(d) => {
                assert_eq!(d.reason.as_str(), "back");
                assert_eq!(d.user_authority.as_str(), "user says so");
            }
            _ => panic!("wrong event kind"),
        }
        assert_eq!(refs.len(), 1);
    }

    #[test]
    fn retire_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::RetireArgs {
            agent: "BAD".to_string(),
            target: "bob".to_string(),
            reason: "r".to_string(),
            user_authority: "u".to_string(),
        };
        assert!(retire(&ctx, &args).is_err());
    }

    #[test]
    fn retire_rejects_invalid_target() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::RetireArgs {
            agent: "alice".to_string(),
            target: "BAD".to_string(),
            reason: "r".to_string(),
            user_authority: "u".to_string(),
        };
        assert!(retire(&ctx, &args).is_err());
    }

    #[test]
    fn build_retire_rejects_unregistered_target() {
        let state = empty_state();
        let bob = a("bob");
        let err = build_retire(&state, &bob, "reason", "user").unwrap_err();
        assert!(err.to_string().contains("is not registered"), "{err}");
    }

    #[test]
    fn build_retire_builds_expected_event() {
        let mut state = empty_state();
        let bob = insert_agent(&mut state, "bob", Role::Implementor);
        let (data, refs) = build_retire(&state, &bob, "done", "user").unwrap();
        assert!(matches!(data, EventData::AgentRetired(ref d) if d.target == bob));
        assert_eq!(refs.len(), 1);
    }

    // ------------------------------------------------- schema/merge-engine

    fn base_schema_activate_args() -> crate::cli::SchemaActivateArgs {
        crate::cli::SchemaActivateArgs { agent: "alice".to_string(), version: 1, design_commit: hash(1), helper_commit: hash(2) }
    }

    #[test]
    fn schema_activate_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_schema_activate_args();
        args.agent = "BAD".to_string();
        assert!(schema_activate(&ctx, &args).is_err());
    }

    #[test]
    fn schema_activate_rejects_invalid_design_commit() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_schema_activate_args();
        args.design_commit = "bad".to_string();
        assert!(schema_activate(&ctx, &args).is_err());
    }

    #[test]
    fn schema_activate_rejects_invalid_helper_commit() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_schema_activate_args();
        args.helper_commit = "bad".to_string();
        assert!(schema_activate(&ctx, &args).is_err());
    }

    fn base_mea_args() -> crate::cli::MergeEngineActivateArgs {
        crate::cli::MergeEngineActivateArgs {
            agent: "alice".to_string(),
            previous_epoch: "coord1:0".to_string(),
            merge_engine: "git-ort".to_string(),
            merge_engine_version: "2.53.0".to_string(),
            design_commit: hash(1),
            helper_commit: hash(2),
        }
    }

    #[test]
    fn merge_engine_activate_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_mea_args();
        args.agent = "BAD".to_string();
        assert!(merge_engine_activate(&ctx, &args).is_err());
    }

    #[test]
    fn merge_engine_activate_rejects_invalid_previous_epoch() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_mea_args();
        args.previous_epoch = "not-an-id".to_string();
        assert!(merge_engine_activate(&ctx, &args).is_err());
    }

    #[test]
    fn merge_engine_activate_rejects_invalid_merge_engine() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_mea_args();
        args.merge_engine = "".to_string();
        assert!(merge_engine_activate(&ctx, &args).is_err());
    }

    #[test]
    fn merge_engine_activate_rejects_invalid_design_commit() {
        let (_d, ctx) = dummy_ctx();
        let mut args = base_mea_args();
        args.design_commit = "bad".to_string();
        assert!(merge_engine_activate(&ctx, &args).is_err());
    }

    // ------------------------------------------------- scope/plan/progress

    #[test]
    fn scope_set_rejects_missing_file() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::FileAgentArgs { agent: "alice".to_string(), file: "/no/such/file.json".to_string() };
        let err = scope_set(&ctx, &args).unwrap_err();
        assert!(matches!(err, crate::error::AbError::Io { .. }), "{err}");
    }

    #[test]
    fn scope_set_rejects_malformed_payload() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json("{}");
        let args = crate::cli::FileAgentArgs { agent: "alice".to_string(), file: path };
        let err = scope_set(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn scope_set_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json("{}");
        let args = crate::cli::FileAgentArgs { agent: "BAD".to_string(), file: path };
        assert!(scope_set(&ctx, &args).is_err());
    }

    #[test]
    fn plan_set_rejects_malformed_payload() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json("{}");
        let args = crate::cli::FileAgentArgs { agent: "alice".to_string(), file: path };
        let err = plan_set(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn progress_rejects_malformed_payload() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json("{}");
        let args = crate::cli::ProgressArgs { agent: "alice".to_string(), file: path };
        let err = progress(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn progress_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json("{}");
        let args = crate::cli::ProgressArgs { agent: "BAD".to_string(), file: path };
        assert!(progress(&ctx, &args).is_err());
    }

    // ------------------------------------------------------------- issues

    #[test]
    fn issue_open_rejects_missing_file() {
        let (_d, ctx) = dummy_ctx();
        let err = issue_open(&ctx, "alice", "bob", "/no/such.json").unwrap_err();
        assert!(matches!(err, crate::error::AbError::Io { .. }), "{err}");
    }

    #[test]
    fn issue_open_rejects_malformed_payload() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json("{}");
        let err = issue_open(&ctx, "alice", "bob", &path).unwrap_err();
        assert!(err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn issue_open_builds_refs_from_blocks_and_evidence_then_attempts_publish() {
        let (_d, ctx) = dummy_ctx();
        let body = r#"{"issue_kind":"bug","severity":"normal","summary":"s","locations":[],"reproduction":[],"blocks":["alice:0"],"evidence":["bob:0"]}"#;
        let (_t, path) = temp_json(body);
        // No real git repo behind `ctx.repo_root`, so `publish_event`
        // ultimately fails -- but only after `from_value`/extra-refs
        // construction has already run without error.
        let err = issue_open(&ctx, "alice", "bob", &path).unwrap_err();
        assert!(!err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn issue_acknowledge_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        assert!(issue_acknowledge(&ctx, "BAD", "alice:0", "note").is_err());
    }

    #[test]
    fn issue_acknowledge_rejects_invalid_issue_id() {
        let (_d, ctx) = dummy_ctx();
        assert!(issue_acknowledge(&ctx, "alice", "not-an-id", "note").is_err());
    }

    #[test]
    fn issue_acknowledge_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        assert!(issue_acknowledge(&ctx, "alice", "alice:0", "note").is_err());
    }

    #[test]
    fn build_issue_ack_rejects_unknown_issue() {
        let state = empty_state();
        let id = eid(&a("alice"), 0);
        let err = build_issue_ack(&state, &id, "note").unwrap_err();
        assert!(err.to_string().contains("unknown issue"), "{err}");
    }

    #[test]
    fn build_issue_ack_builds_expected_event() {
        let mut state = empty_state();
        let opener = a("alice");
        let target = a("bob");
        let assignment = eid(&opener, 0);
        state.issues.insert(assignment.clone(), mk_issue(&opener, &target, &assignment, ItemStatus::Open));
        let (data, refs) = build_issue_ack(&state, &assignment, "hi").unwrap();
        match data {
            EventData::IssueAcknowledged(d) => {
                assert_eq!(d.issue, assignment);
                assert_eq!(d.assignment, assignment);
                assert_eq!(d.note.as_str(), "hi");
            }
            _ => panic!("wrong event kind"),
        }
        assert_eq!(refs, vec![assignment.clone(), assignment]);
    }

    #[test]
    fn issue_resolve_rejects_invalid_issue_id() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json(r#"{"summary":"s","verification":[]}"#);
        assert!(issue_resolve(&ctx, "alice", "not-an-id", &path).is_err());
    }

    #[test]
    fn build_issue_terminal_rejects_unknown_issue() {
        let state = empty_state();
        let id = eid(&a("alice"), 0);
        let v = serde_json::json!({"summary": "s", "verification": []});
        let err = build_issue_terminal(&state, &id, v, true).unwrap_err();
        assert!(err.to_string().contains("unknown issue"), "{err}");
    }

    #[test]
    fn build_issue_terminal_resolve_builds_expected_event() {
        let mut state = empty_state();
        let opener = a("alice");
        let target = a("bob");
        let id = eid(&opener, 0);
        state.issues.insert(id.clone(), mk_issue(&opener, &target, &id, ItemStatus::Open));
        let v = serde_json::json!({"summary": "fixed it", "verification": ["checked"]});
        let (data, refs) = build_issue_terminal(&state, &id, v, true).unwrap();
        match data {
            EventData::IssueResolved(d) => {
                assert_eq!(d.issue, id);
                assert_eq!(d.summary.as_str(), "fixed it");
            }
            _ => panic!("wrong event kind"),
        }
        assert_eq!(refs, vec![id.clone(), id]);
    }

    #[test]
    fn build_issue_terminal_reject_builds_expected_event() {
        let mut state = empty_state();
        let opener = a("alice");
        let target = a("bob");
        let id = eid(&opener, 0);
        state.issues.insert(id.clone(), mk_issue(&opener, &target, &id, ItemStatus::Open));
        let v = serde_json::json!({"reason": "wontfix", "normative_refs": []});
        let (data, _refs) = build_issue_terminal(&state, &id, v, false).unwrap();
        assert!(matches!(data, EventData::IssueRejected(ref d) if d.reason.as_str() == "wontfix"));
    }

    #[test]
    fn build_issue_terminal_rejects_malformed_payload() {
        let mut state = empty_state();
        let opener = a("alice");
        let target = a("bob");
        let id = eid(&opener, 0);
        state.issues.insert(id.clone(), mk_issue(&opener, &target, &id, ItemStatus::Open));
        let err = build_issue_terminal(&state, &id, serde_json::json!({}), true).unwrap_err();
        assert!(err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn issue_reassign_rejects_invalid_new_target() {
        let (_d, ctx) = dummy_ctx();
        assert!(issue_reassign(&ctx, "alice", "alice:0", "BAD", "reason").is_err());
    }

    #[test]
    fn build_issue_reassign_rejects_unknown_issue() {
        let state = empty_state();
        let id = eid(&a("alice"), 0);
        let err = build_issue_reassign(&state, &id, a("carol"), "handoff").unwrap_err();
        assert!(err.to_string().contains("unknown issue"), "{err}");
    }

    #[test]
    fn build_issue_reassign_builds_expected_event() {
        let mut state = empty_state();
        let opener = a("alice");
        let target = a("bob");
        let carol = a("carol");
        let id = eid(&opener, 0);
        state.issues.insert(id.clone(), mk_issue(&opener, &target, &id, ItemStatus::Open));
        let (data, refs) = build_issue_reassign(&state, &id, carol.clone(), "handoff").unwrap();
        match data {
            EventData::IssueReassigned(d) => {
                assert_eq!(d.previous_target, target);
                assert_eq!(d.new_target, carol);
                assert_eq!(d.reason.as_str(), "handoff");
            }
            _ => panic!("wrong event kind"),
        }
        assert_eq!(refs, vec![id.clone(), id]);
    }

    // -------------------------------------------------------- dependencies

    #[test]
    fn dependency_request_rejects_malformed_payload() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json("{}");
        let err = dependency_request(&ctx, "alice", "bob", &path).unwrap_err();
        assert!(err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn dependency_request_builds_refs_from_evidence_then_attempts_publish() {
        let (_d, ctx) = dummy_ctx();
        let body = r#"{"interface":"i","needed_by":"asap","blocking":true,"summary":"s","evidence":["alice:0"]}"#;
        let (_t, path) = temp_json(body);
        let err = dependency_request(&ctx, "alice", "bob", &path).unwrap_err();
        assert!(!err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn dependency_acknowledge_rejects_invalid_dep_id() {
        let (_d, ctx) = dummy_ctx();
        assert!(dependency_acknowledge(&ctx, "alice", "not-an-id", "note").is_err());
    }

    #[test]
    fn build_dependency_ack_rejects_unknown_dependency() {
        let state = empty_state();
        let id = eid(&a("alice"), 0);
        let err = build_dependency_ack(&state, &id, "note").unwrap_err();
        assert!(err.to_string().contains("unknown dependency"), "{err}");
    }

    #[test]
    fn build_dependency_ack_builds_expected_event() {
        let mut state = empty_state();
        let requester = a("alice");
        let target = a("bob");
        let id = eid(&requester, 0);
        state.dependencies.insert(id.clone(), mk_dependency(&requester, &target, &id, ItemStatus::Open));
        let (data, refs) = build_dependency_ack(&state, &id, "hi").unwrap();
        assert!(matches!(data, EventData::DependencyAcknowledged(ref d) if d.note.as_str() == "hi"));
        assert_eq!(refs, vec![id.clone(), id]);
    }

    #[test]
    fn build_dependency_resolve_rejects_unknown_dependency() {
        let state = empty_state();
        let id = eid(&a("alice"), 0);
        let v = serde_json::json!({"summary": "s", "verification": []});
        let err = build_dependency_resolve(&state, &id, v).unwrap_err();
        assert!(err.to_string().contains("unknown dependency"), "{err}");
    }

    #[test]
    fn build_dependency_resolve_builds_expected_event() {
        let mut state = empty_state();
        let requester = a("alice");
        let target = a("bob");
        let id = eid(&requester, 0);
        state.dependencies.insert(id.clone(), mk_dependency(&requester, &target, &id, ItemStatus::Open));
        let v = serde_json::json!({"summary": "done", "verification": []});
        let (data, refs) = build_dependency_resolve(&state, &id, v).unwrap();
        assert!(matches!(data, EventData::DependencyResolved(ref d) if d.summary.as_str() == "done"));
        assert_eq!(refs, vec![id.clone(), id]);
    }

    #[test]
    fn build_dependency_resolve_rejects_malformed_payload() {
        let mut state = empty_state();
        let requester = a("alice");
        let target = a("bob");
        let id = eid(&requester, 0);
        state.dependencies.insert(id.clone(), mk_dependency(&requester, &target, &id, ItemStatus::Open));
        let err = build_dependency_resolve(&state, &id, serde_json::json!({})).unwrap_err();
        assert!(err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn build_dependency_reject_rejects_unknown_dependency() {
        let state = empty_state();
        let id = eid(&a("alice"), 0);
        let err = build_dependency_reject(&state, &id, "reason").unwrap_err();
        assert!(err.to_string().contains("unknown dependency"), "{err}");
    }

    #[test]
    fn build_dependency_reject_builds_expected_event() {
        let mut state = empty_state();
        let requester = a("alice");
        let target = a("bob");
        let id = eid(&requester, 0);
        state.dependencies.insert(id.clone(), mk_dependency(&requester, &target, &id, ItemStatus::Open));
        let (data, refs) = build_dependency_reject(&state, &id, "nope").unwrap();
        assert!(matches!(data, EventData::DependencyRejected(ref d) if d.reason.as_str() == "nope"));
        assert_eq!(refs, vec![id.clone(), id]);
    }

    #[test]
    fn build_dependency_reassign_rejects_unknown_dependency() {
        let state = empty_state();
        let id = eid(&a("alice"), 0);
        let err = build_dependency_reassign(&state, &id, a("carol"), "reason").unwrap_err();
        assert!(err.to_string().contains("unknown dependency"), "{err}");
    }

    #[test]
    fn build_dependency_reassign_builds_expected_event() {
        let mut state = empty_state();
        let requester = a("alice");
        let target = a("bob");
        let carol = a("carol");
        let id = eid(&requester, 0);
        state.dependencies.insert(id.clone(), mk_dependency(&requester, &target, &id, ItemStatus::Open));
        let (data, refs) = build_dependency_reassign(&state, &id, carol.clone(), "moving").unwrap();
        match data {
            EventData::DependencyReassigned(d) => {
                assert_eq!(d.previous_target, target);
                assert_eq!(d.new_target, carol);
            }
            _ => panic!("wrong event kind"),
        }
        assert_eq!(refs, vec![id.clone(), id]);
    }

    #[test]
    fn dependency_reassign_rejects_invalid_new_target() {
        let (_d, ctx) = dummy_ctx();
        assert!(dependency_reassign(&ctx, "alice", "alice:0", "BAD", "reason").is_err());
    }

    // ----------------------------------------------------------- handoffs

    #[test]
    fn handoff_offer_rejects_malformed_payload() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json("{}");
        let err = handoff_offer(&ctx, "alice", &path).unwrap_err();
        assert!(err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn handoff_offer_builds_refs_then_attempts_publish() {
        let (_d, ctx) = dummy_ctx();
        let body = r#"{"receiver":"bob","scope":[],"product_branch":"refs/heads/x","product_commit":""#.to_string()
            + &hash(1)
            + r#"","verification":[],"known_issues":["alice:0"],"evidence":["bob:1"],"summary":"s"}"#;
        let (_t, path) = temp_json(&body);
        let err = handoff_offer(&ctx, "alice", &path).unwrap_err();
        assert!(!err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn handoff_accept_rejects_invalid_handoff_id() {
        let (_d, ctx) = dummy_ctx();
        assert!(handoff_accept(&ctx, "alice", "not-an-id", "note").is_err());
    }

    #[test]
    fn handoff_decline_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        assert!(handoff_decline(&ctx, "BAD", "alice:0", "reason").is_err());
    }

    #[test]
    fn handoff_withdraw_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        assert!(handoff_withdraw(&ctx, "BAD", "alice:0", "reason").is_err());
    }

    // ------------------------------------------------------- lifecycle-conflict

    #[test]
    fn lifecycle_resolve_rejects_malformed_payload() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json("{}");
        let args = crate::cli::FileAgentArgs { agent: "alice".to_string(), file: path };
        let err = lifecycle_resolve(&ctx, &args).unwrap_err();
        assert!(err.to_string().contains("invalid payload"), "{err}");
    }

    #[test]
    fn lifecycle_resolve_builds_refs_then_attempts_publish() {
        let (_d, ctx) = dummy_ctx();
        let body = r#"{"root":"alice:0","competing":["alice:0","bob:0"],"selected":"alice:0","reason":"r","user_authority":"u"}"#;
        let (_t, path) = temp_json(body);
        let args = crate::cli::FileAgentArgs { agent: "alice".to_string(), file: path };
        let err = lifecycle_resolve(&ctx, &args).unwrap_err();
        assert!(!err.to_string().contains("invalid payload"), "{err}");
    }

    // -------------------------------------------------------------- sync()

    #[test]
    fn sync_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::SyncArgs { agent: "BAD".to_string() };
        assert!(sync(&ctx, &args).is_err());
    }

    // ------------------------------------------------------------ status()

    #[test]
    fn select_agents_rejects_unknown_agent() {
        let state = empty_state();
        let err = select_agents(&state, &Some("ghost".to_string())).unwrap_err();
        assert!(err.to_string().contains("unknown agent"), "{err}");
    }

    #[test]
    fn select_agents_returns_specific_agent() {
        let mut state = empty_state();
        insert_agent(&mut state, "alice", Role::Implementor);
        insert_agent(&mut state, "bob", Role::Reviewer);
        let got = select_agents(&state, &Some("bob".to_string())).unwrap();
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].agent.as_str(), "bob");
    }

    #[test]
    fn select_agents_returns_all_when_none() {
        let mut state = empty_state();
        insert_agent(&mut state, "alice", Role::Implementor);
        insert_agent(&mut state, "bob", Role::Reviewer);
        let got = select_agents(&state, &None).unwrap();
        assert_eq!(got.len(), 2);
    }

    #[test]
    fn agent_summary_snapshot() {
        let ag = mk_agent("alice", Role::Implementor);
        insta::assert_json_snapshot!(agent_summary(&ag));
    }

    /// The all-defaults snapshot above only ever exercises the `None` arm of
    /// every `Option`-typed field in `agent_summary` (provider, model,
    /// product_branch, product_commit, scope, plan) plus a single
    /// `LifecycleStatus` variant and `retired: false`. None of that would
    /// notice a bug in the `Some(...)` serialization branches (e.g. a
    /// mis-shaped `scope`/`plan` value, or a wrong `Debug`-derived `status`
    /// string). This snapshot populates every optional field and flips
    /// `status`/`retired` so the whole shape is actually pinned down.
    #[test]
    fn agent_summary_snapshot_with_populated_optional_fields() {
        // Implementor, not Reviewer: AGENT_BUS_SCHEMA.md section 4 permits
        // `product_branch`/`product_commit` only for an implementor, and the
        // fixture should stay a state real event application could produce.
        let mut ag = mk_agent("bob", Role::Implementor);
        ag.provider = Some(short("anthropic"));
        ag.model = Some(short("sonnet"));
        ag.status = LifecycleStatus::Blocked;
        ag.retired = true;
        ag.product_branch = Some(branch("refs/heads/agent/bob/x"));
        ag.product_commit = Some(oid(7));
        ag.scope = Some(scope_set_fixture(&["Grass/Bob/**"], &["Grass/Shared/**"]));
        ag.plan = Some(PlanSet {
            summary: text("ship it"),
            steps: vec![crate::common::PlanStep {
                id: short("s1"),
                state: crate::common::PlanStepState::Active,
                text: text("do the thing"),
            }],
            risks: vec![text("might be late")],
        });
        insta::assert_json_snapshot!(agent_summary(&ag));
    }

    #[test]
    fn status_rejects_invalid_agent_filter() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::StatusArgs { agent: Some("BAD".to_string()), json: true };
        assert!(status(&ctx, &args).is_err());
    }

    #[test]
    fn status_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::StatusArgs { agent: None, json: true };
        assert!(status(&ctx, &args).is_err());
    }

    // ------------------------------------------------------------- inbox()

    #[test]
    fn inbox_items_collects_open_items_targeting_agent() {
        let mut state = empty_state();
        let alice = a("alice");
        let bob = a("bob");

        let issue_open_id = eid(&bob, 0);
        state.issues.insert(issue_open_id.clone(), mk_issue(&bob, &alice, &issue_open_id, ItemStatus::Open));
        let issue_done_id = eid(&bob, 1);
        state.issues.insert(issue_done_id.clone(), mk_issue(&bob, &alice, &issue_done_id, ItemStatus::Terminal("resolved")));

        let dep_id = eid(&bob, 2);
        state.dependencies.insert(dep_id.clone(), mk_dependency(&bob, &alice, &dep_id, ItemStatus::Open));

        let handoff_id = eid(&bob, 3);
        state.handoffs.insert(handoff_id.clone(), mk_handoff(&bob, &alice, &handoff_id, ItemStatus::Open));

        let review_root = eid(&bob, 4);
        state.reviews.insert(review_root.clone(), mk_review_chain(&review_root, &alice, false));
        state.review_chain_by_nomination.insert(review_root.clone(), review_root.clone());

        let closed_review_root = eid(&bob, 5);
        state.reviews.insert(closed_review_root.clone(), mk_review_chain(&closed_review_root, &alice, true));
        state.review_chain_by_nomination.insert(closed_review_root.clone(), closed_review_root.clone());

        let items = inbox_items(&state, &alice);
        let kinds: Vec<&str> = items.iter().map(|v| v["kind"].as_str().unwrap()).collect();
        assert_eq!(kinds.len(), 4, "{items:?}");
        for expected in ["issue", "dependency", "handoff", "review"] {
            assert!(kinds.contains(&expected), "missing {expected} in {kinds:?}");
        }
    }

    #[test]
    fn inbox_items_empty_for_uninvolved_agent() {
        let state = empty_state();
        assert!(inbox_items(&state, &a("alice")).is_empty());
    }

    // ------------------------------------------------------- dependencies()

    #[test]
    fn dependencies_items_filters_by_requester_or_target() {
        let mut state = empty_state();
        let alice = a("alice");
        let bob = a("bob");
        let carol = a("carol");

        let d1 = eid(&alice, 0);
        state.dependencies.insert(d1.clone(), mk_dependency(&alice, &bob, &d1, ItemStatus::Open));
        let d2 = eid(&bob, 0);
        state.dependencies.insert(d2.clone(), mk_dependency(&bob, &alice, &d2, ItemStatus::Open));
        let d3 = eid(&bob, 1);
        state.dependencies.insert(d3.clone(), mk_dependency(&bob, &carol, &d3, ItemStatus::Open));

        let items = dependencies_items(&state, &alice);
        assert_eq!(items.len(), 2, "{items:?}");
    }

    // ----------------------------------------------------------- conflicts()

    fn scope_set_fixture(exclusive: &[&str], shared: &[&str]) -> ScopeSet {
        ScopeSet {
            base_code_commit: oid(1),
            exclusive: StringSet::from_iter(exclusive.iter().map(|s| PathClaim::parse(s.to_string()).unwrap())),
            shared: StringSet::from_iter(shared.iter().map(|s| PathClaim::parse(s.to_string()).unwrap())),
            exports: StringSet::default(),
            depends_on: vec![],
            note: text(""),
        }
    }

    #[test]
    fn conflicts_items_detects_exclusive_exclusive_overlap() {
        let mut state = empty_state();
        let mut alice_ag = mk_agent("alice", Role::Implementor);
        alice_ag.scope = Some(scope_set_fixture(&["Grass/X/**"], &[]));
        let mut bob_ag = mk_agent("bob", Role::Implementor);
        bob_ag.scope = Some(scope_set_fixture(&["Grass/X/Y.lean"], &[]));
        state.agents.insert(alice_ag.agent.clone(), alice_ag);
        state.agents.insert(bob_ag.agent.clone(), bob_ag);

        let out = conflicts_items(&state);
        assert!(out.iter().any(|v| v["kind"] == "scope"), "{out:?}");
    }

    #[test]
    fn conflicts_items_detects_exclusive_shared_overlap() {
        let mut state = empty_state();
        let mut alice_ag = mk_agent("alice", Role::Implementor);
        alice_ag.scope = Some(scope_set_fixture(&["Excl/**"], &[]));
        let mut bob_ag = mk_agent("bob", Role::Implementor);
        bob_ag.scope = Some(scope_set_fixture(&[], &["Excl/file.lean"]));
        state.agents.insert(alice_ag.agent.clone(), alice_ag);
        state.agents.insert(bob_ag.agent.clone(), bob_ag);

        let out = conflicts_items(&state);
        assert!(out.iter().any(|v| v["kind"] == "scope_exclusive_shared"), "{out:?}");
    }

    #[test]
    fn conflicts_items_ignores_inactive_agents() {
        let mut state = empty_state();
        let mut alice_ag = mk_agent("alice", Role::Implementor);
        alice_ag.scope = Some(scope_set_fixture(&["Grass/X/**"], &[]));
        alice_ag.retired = true;
        let mut bob_ag = mk_agent("bob", Role::Implementor);
        bob_ag.scope = Some(scope_set_fixture(&["Grass/X/Y.lean"], &[]));
        state.agents.insert(alice_ag.agent.clone(), alice_ag);
        state.agents.insert(bob_ag.agent.clone(), bob_ag);

        assert!(conflicts_items(&state).is_empty());
    }

    #[test]
    fn conflicts_items_detects_unresolved_lifecycle_conflict() {
        let mut state = empty_state();
        state.exclusive.insert(
            "issue:carol:0".to_string(),
            ExclusiveTracker { transitions: vec![(eid(&a("carol"), 1), 1), (eid(&a("dave"), 1), 2)], resolved: None },
        );
        let out = conflicts_items(&state);
        assert!(out.iter().any(|v| v["kind"] == "lifecycle_conflict"), "{out:?}");
    }

    #[test]
    fn conflicts_items_ignores_resolved_lifecycle_conflict() {
        let mut state = empty_state();
        state.exclusive.insert(
            "issue:carol:0".to_string(),
            ExclusiveTracker {
                transitions: vec![(eid(&a("carol"), 1), 1), (eid(&a("dave"), 1), 2)],
                resolved: Some(eid(&a("carol"), 1)),
            },
        );
        assert!(conflicts_items(&state).is_empty());
    }

    #[test]
    fn conflicts_items_empty_when_no_conflicts() {
        let state = empty_state();
        assert!(conflicts_items(&state).is_empty());
    }

    #[test]
    fn conflicts_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::ConflictsArgs { json: true };
        assert!(conflicts(&ctx, &args).is_err());
    }

    // ------------------------------------------------------------- tail()

    #[test]
    fn tail_events_filters_by_agent_and_truncates_to_count() {
        let alice = a("alice");
        let bob = a("bob");
        let walk = mk_walk(vec![(alice.clone(), vec![0, 1]), (bob.clone(), vec![0]), (alice.clone(), vec![2])]);

        let all = tail_events(&walk, None, 100);
        assert_eq!(all.len(), 4);

        let alice_only = tail_events(&walk, Some("alice"), 100);
        assert_eq!(alice_only.len(), 3);

        let truncated = tail_events(&walk, None, 2);
        assert_eq!(truncated.len(), 2);
        assert_eq!(truncated[0].seq, 0); // bob:0
        assert_eq!(truncated[1].seq, 2); // alice:2
    }

    #[test]
    fn tail_events_empty_walk_slice_when_count_zero() {
        let walk = mk_walk(vec![(a("alice"), vec![0, 1])]);
        assert!(tail_events(&walk, None, 0).is_empty());
    }

    #[test]
    fn tail_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::TailArgs { agent: None, count: 20, json: false };
        assert!(tail(&ctx, &args).is_err());
    }

    #[test]
    fn inbox_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::InboxArgs { agent: "BAD".to_string(), json: false };
        assert!(inbox(&ctx, &args).is_err());
    }

    #[test]
    fn inbox_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::InboxArgs { agent: "alice".to_string(), json: false };
        assert!(inbox(&ctx, &args).is_err());
    }

    #[test]
    fn dependencies_rejects_invalid_agent() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::DependenciesArgs { agent: "BAD".to_string(), json: false };
        assert!(dependencies(&ctx, &args).is_err());
    }

    #[test]
    fn dependencies_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        let args = crate::cli::DependenciesArgs { agent: "alice".to_string(), json: false };
        assert!(dependencies(&ctx, &args).is_err());
    }

    // --------------------------------------------------- remaining wrappers
    //
    // Every function below reaches `bus::publish_event`/`ctx.load_state()`
    // with otherwise-valid arguments, so it needs a `dummy_ctx()` whose
    // *parse-time* validation has already succeeded; the eventual failure
    // (no real git repository behind `ctx.repo_root`) still exercises the
    // full body of the wrapper up to that call.

    #[test]
    fn issue_reject_rejects_invalid_issue_id() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json(r#"{"reason":"no","normative_refs":[]}"#);
        assert!(issue_reject(&ctx, "alice", "not-an-id", &path).is_err());
    }

    #[test]
    fn issue_reject_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json(r#"{"reason":"no","normative_refs":[]}"#);
        assert!(issue_reject(&ctx, "alice", "alice:0", &path).is_err());
    }

    #[test]
    fn issue_reassign_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        assert!(issue_reassign(&ctx, "alice", "alice:0", "carol", "reason").is_err());
    }

    #[test]
    fn dependency_resolve_rejects_invalid_dep_id() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json(r#"{"summary":"s","verification":[]}"#);
        assert!(dependency_resolve(&ctx, "alice", "not-an-id", &path).is_err());
    }

    #[test]
    fn dependency_resolve_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json(r#"{"summary":"s","verification":[]}"#);
        assert!(dependency_resolve(&ctx, "alice", "alice:0", &path).is_err());
    }

    #[test]
    fn dependency_reject_rejects_invalid_dep_id() {
        let (_d, ctx) = dummy_ctx();
        assert!(dependency_reject(&ctx, "alice", "not-an-id", "reason").is_err());
    }

    #[test]
    fn dependency_reject_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        assert!(dependency_reject(&ctx, "alice", "alice:0", "reason").is_err());
    }

    #[test]
    fn dependency_reassign_propagates_state_load_failure() {
        let (_d, ctx) = dummy_ctx();
        assert!(dependency_reassign(&ctx, "alice", "alice:0", "carol", "reason").is_err());
    }

    #[test]
    fn status_set_reaches_publish_with_valid_args() {
        let (_d, ctx) = dummy_ctx();
        let args = base_status_set_args();
        assert!(status_set(&ctx, &args).is_err());
    }

    #[test]
    fn schema_activate_reaches_publish_with_valid_args() {
        let (_d, ctx) = dummy_ctx();
        let args = base_schema_activate_args();
        assert!(schema_activate(&ctx, &args).is_err());
    }

    #[test]
    fn merge_engine_activate_reaches_publish_with_valid_args() {
        let (_d, ctx) = dummy_ctx();
        let args = base_mea_args();
        assert!(merge_engine_activate(&ctx, &args).is_err());
    }

    #[test]
    fn plan_set_reaches_publish_with_valid_payload() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json(r#"{"summary":"s","steps":[],"risks":[]}"#);
        let args = crate::cli::FileAgentArgs { agent: "alice".to_string(), file: path };
        assert!(plan_set(&ctx, &args).is_err());
    }

    #[test]
    fn progress_reaches_publish_with_valid_payload() {
        let (_d, ctx) = dummy_ctx();
        let (_t, path) = temp_json(r#"{"completed":[],"current":[],"next":[],"blockers":[],"verification":[]}"#);
        let args = crate::cli::ProgressArgs { agent: "alice".to_string(), file: path };
        assert!(progress(&ctx, &args).is_err());
    }

    #[test]
    fn handoff_accept_reaches_publish_with_valid_args() {
        let (_d, ctx) = dummy_ctx();
        assert!(handoff_accept(&ctx, "alice", "alice:0", "note").is_err());
    }

    #[test]
    fn handoff_decline_reaches_publish_with_valid_args() {
        let (_d, ctx) = dummy_ctx();
        assert!(handoff_decline(&ctx, "alice", "alice:0", "reason").is_err());
    }

    #[test]
    fn handoff_withdraw_reaches_publish_with_valid_args() {
        let (_d, ctx) = dummy_ctx();
        assert!(handoff_withdraw(&ctx, "alice", "alice:0", "reason").is_err());
    }

    #[test]
    fn register_reaches_registration_for_valid_implementor() {
        let (_d, ctx) = dummy_ctx();
        let args = base_register_args();
        // Not a real bootstrap repo, so this fails deep inside
        // `register_new_agent`'s git plumbing -- but only after the
        // coordinator-role short circuit is skipped and the full body runs.
        assert!(register(&ctx, &args).is_err());
    }

    // ------------------------------------------------------- real-repo flow
    //
    // A minimal but genuine `git init` + `bootstrap-init` repository, driving
    // the public command functions directly (no `assert_cmd` subprocess, so
    // this stays fast). Unlike every `dummy_ctx()` test above, calls here can
    // actually reach `bus::publish_event`'s success path, exercising the
    // `println!`/`Ok(())` tail of each wrapper that a non-repository
    // `BusCtx` can never reach.

    fn init_real_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path();
        std::process::Command::new("git").args(["init", "--quiet", "-b", "main"]).arg(path).status().unwrap();
        std::process::Command::new("git")
            .arg("-C")
            .arg(path)
            .args(["config", "user.email", "test@example.com"])
            .status()
            .unwrap();
        std::process::Command::new("git")
            .arg("-C")
            .arg(path)
            .args(["config", "user.name", "Test"])
            .status()
            .unwrap();
        dir
    }

    #[test]
    fn report_and_lifecycle_commands_against_a_real_repo() {
        let dir = init_real_repo();
        let ctx = BusCtx { repo_root: dir.path().to_path_buf(), has_origin: false };
        let coord1 = a("coord1");
        bus::bootstrap_init(&ctx, &[coord1.clone()], &oid(1)).unwrap();

        // register(): full success path through `register_new_agent`.
        let mut reg_args = base_register_args();
        reg_args.agent = "alice".to_string();
        reg_args.display_name = "Alice".to_string();
        register(&ctx, &reg_args).unwrap();

        // status_set(): full success path.
        let mut ss_args = base_status_set_args();
        ss_args.agent = "alice".to_string();
        status_set(&ctx, &ss_args).unwrap();

        // scope/plan/progress: full success paths.
        let (_t1, scope_path) = temp_json(&format!(
            r#"{{"base_code_commit":"{}","exclusive":["Grass/Alice/**"],"shared":[],"exports":[],"depends_on":[],"note":""}}"#,
            hash(1)
        ));
        scope_set(&ctx, &crate::cli::FileAgentArgs { agent: "alice".to_string(), file: scope_path }).unwrap();

        let (_t2, plan_path) = temp_json(r#"{"summary":"s","steps":[],"risks":[]}"#);
        plan_set(&ctx, &crate::cli::FileAgentArgs { agent: "alice".to_string(), file: plan_path }).unwrap();

        let (_t3, progress_path) =
            temp_json(r#"{"completed":[],"current":[],"next":[],"blockers":[],"verification":[]}"#);
        progress(&ctx, &crate::cli::ProgressArgs { agent: "alice".to_string(), file: progress_path }).unwrap();

        // schema/merge-engine activation: full success paths.
        schema_activate(
            &ctx,
            &crate::cli::SchemaActivateArgs { agent: "coord1".to_string(), version: 1, design_commit: hash(2), helper_commit: hash(3) },
        )
        .unwrap();
        merge_engine_activate(
            &ctx,
            &crate::cli::MergeEngineActivateArgs {
                agent: "coord1".to_string(),
                previous_epoch: "coord1:0".to_string(),
                merge_engine: crate::bootstrap::SUPPORTED_MERGE_ENGINE.to_string(),
                merge_engine_version: crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION.to_string(),
                design_commit: hash(4),
                helper_commit: hash(5),
            },
        )
        .unwrap();

        // issue open/acknowledge/resolve: full success path.
        let (_t4, issue_path) =
            temp_json(r#"{"issue_kind":"bug","severity":"normal","summary":"s","locations":[],"reproduction":[],"blocks":[],"evidence":[]}"#);
        issue_open(&ctx, "coord1", "alice", &issue_path).unwrap();
        let issue_id = ctx.load_state().unwrap().issues.keys().next().cloned().unwrap();
        issue_acknowledge(&ctx, "alice", issue_id.as_str(), "on it").unwrap();
        let (_t5, resolve_path) = temp_json(r#"{"summary":"fixed","verification":[]}"#);
        issue_resolve(&ctx, "alice", issue_id.as_str(), &resolve_path).unwrap();

        // dependency request/acknowledge/resolve: full success path.
        let (_t6, dep_path) = temp_json(r#"{"interface":"i","needed_by":"asap","blocking":true,"summary":"s","evidence":[]}"#);
        dependency_request(&ctx, "alice", "coord1", &dep_path).unwrap();
        let dep_id = ctx.load_state().unwrap().dependencies.keys().next().cloned().unwrap();
        dependency_acknowledge(&ctx, "coord1", dep_id.as_str(), "on it").unwrap();
        let (_t7, dep_resolve_path) = temp_json(r#"{"summary":"done","verification":[]}"#);
        dependency_resolve(&ctx, "coord1", dep_id.as_str(), &dep_resolve_path).unwrap();

        // handoff offer/accept: full success path. `product_branch` must
        // match `refs/heads/agent/<offerer>/<topic>`.
        let (_t8, handoff_path) = temp_json(&format!(
            r#"{{"receiver":"coord1","scope":[],"product_branch":"refs/heads/agent/alice/x","product_commit":"{}","verification":[],"known_issues":[],"evidence":[],"summary":"s"}}"#,
            hash(6)
        ));
        handoff_offer(&ctx, "alice", &handoff_path).unwrap();
        let handoff_id = ctx.load_state().unwrap().handoffs.keys().next().cloned().unwrap();
        handoff_accept(&ctx, "coord1", handoff_id.as_str(), "got it").unwrap();

        // sync(): full success path.
        sync(&ctx, &crate::cli::SyncArgs { agent: "alice".to_string() }).unwrap();

        // Report commands: both json and non-json branches, now against a
        // real, populated (and, for coord1's inbox / scope conflicts, empty)
        // state -- exercising the `(empty)`/`(no conflicts)` branches too.
        status(&ctx, &crate::cli::StatusArgs { agent: None, json: true }).unwrap();
        status(&ctx, &crate::cli::StatusArgs { agent: Some("alice".to_string()), json: false }).unwrap();

        inbox(&ctx, &crate::cli::InboxArgs { agent: "coord1".to_string(), json: false }).unwrap();
        inbox(&ctx, &crate::cli::InboxArgs { agent: "alice".to_string(), json: true }).unwrap();

        dependencies(&ctx, &crate::cli::DependenciesArgs { agent: "alice".to_string(), json: false }).unwrap();
        dependencies(&ctx, &crate::cli::DependenciesArgs { agent: "alice".to_string(), json: true }).unwrap();

        conflicts(&ctx, &crate::cli::ConflictsArgs { json: false }).unwrap();
        conflicts(&ctx, &crate::cli::ConflictsArgs { json: true }).unwrap();

        tail(&ctx, &crate::cli::TailArgs { agent: None, count: 50, json: false }).unwrap();
        tail(&ctx, &crate::cli::TailArgs { agent: Some("alice".to_string()), count: 1, json: true }).unwrap();

        // resume/retire/lifecycle_resolve: reach `build_*`/refs-building and
        // attempt to publish; not asserted to succeed since satisfying
        // `apply::dry_run`'s preconditions exactly is not the point here --
        // the wrapper's own lines all execute either way.
        let _ = resume(&ctx, &crate::cli::ResumeArgs { agent: "alice".to_string(), reason: "back".to_string(), user_authority: "self".to_string() });
        let _ = retire(&ctx, &crate::cli::RetireArgs {
            agent: "coord1".to_string(),
            target: "alice".to_string(),
            reason: "done".to_string(),
            user_authority: "coordinator".to_string(),
        });
        let (_t9, lifecycle_path) = temp_json(&format!(
            r#"{{"root":"{issue_id}","competing":["{issue_id}"],"selected":"{issue_id}","reason":"r","user_authority":"u"}}"#
        ));
        let _ = lifecycle_resolve(&ctx, &crate::cli::FileAgentArgs { agent: "coord1".to_string(), file: lifecycle_path });
    }
}
