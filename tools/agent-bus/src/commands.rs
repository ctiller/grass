//! CLI command handlers for everything except review/merge (see
//! `review_cmds.rs`) and validation (see `validate_cmd.rs`).

use crate::bus::{self, BusCtx};
use crate::error::{invalid, AbResult};
use crate::events::*;
use crate::scalars::*;
use crate::state::ItemStatus;
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

fn register_new_agent(ctx: &BusCtx, agent: &Agent, data: EventData) -> AbResult<()> {
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
    let ag = state
        .agent(&agent)
        .ok_or_else(|| invalid(format!("{agent} is not registered")))?;
    let previous = ag.last_lifecycle_event.clone();
    let data = EventData::AgentResumed(AgentResumed {
        previous_lifecycle: previous.clone(),
        reason: Text::parse(args.reason.clone())?,
        user_authority: Text::parse(args.user_authority.clone())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![previous])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn retire(ctx: &BusCtx, args: &crate::cli::RetireArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let target = Agent::parse(args.target.clone())?;
    let state = ctx.load_state()?;
    let tgt = state
        .agent(&target)
        .ok_or_else(|| invalid(format!("{target} is not registered")))?;
    let previous = tgt.last_lifecycle_event.clone();
    let data = EventData::AgentRetired(AgentRetired {
        target: target.clone(),
        previous_lifecycle: previous.clone(),
        reason: Text::parse(args.reason.clone())?,
        user_authority: Text::parse(args.user_authority.clone())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![previous])?;
    println!("published {}", env.id);
    Ok(())
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
    let issue = state
        .issues
        .get(&issue_id)
        .ok_or_else(|| invalid(format!("unknown issue {issue_id}")))?;
    let assignment = issue.current_assignment.clone();
    let data = EventData::IssueAcknowledged(IssueAcknowledged {
        issue: issue_id.clone(),
        assignment: assignment.clone(),
        note: Text::parse(note.to_string())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![issue_id, assignment])?;
    println!("published {}", env.id);
    Ok(())
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
    let issue = state
        .issues
        .get(&issue_id)
        .ok_or_else(|| invalid(format!("unknown issue {issue_id}")))?;
    let assignment = issue.current_assignment.clone();
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let v = inject(
        v,
        &[
            ("issue", Value::String(issue_id.to_string())),
            ("assignment", Value::String(assignment.to_string())),
        ],
    );
    let (data, refs) = if resolve {
        let d: IssueResolved = from_value(v)?;
        (EventData::IssueResolved(d), vec![issue_id, assignment])
    } else {
        let d: IssueRejected = from_value(v)?;
        (EventData::IssueRejected(d), vec![issue_id, assignment])
    };
    let env = bus::publish_event(ctx, &agent, data, refs)?;
    println!("published {}", env.id);
    Ok(())
}

pub fn issue_reassign(ctx: &BusCtx, agent: &str, issue_id: &str, new_target: &str, reason: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let issue_id = EventId::parse(issue_id.to_string())?;
    let new_target = Agent::parse(new_target.to_string())?;
    let state = ctx.load_state()?;
    let issue = state
        .issues
        .get(&issue_id)
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
    let env = bus::publish_event(ctx, &agent, data, vec![issue_id, previous_assignment])?;
    println!("published {}", env.id);
    Ok(())
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
    let dep = state
        .dependencies
        .get(&dep_id)
        .ok_or_else(|| invalid(format!("unknown dependency {dep_id}")))?;
    let assignment = dep.current_assignment.clone();
    let data = EventData::DependencyAcknowledged(DependencyAcknowledged {
        dependency: dep_id.clone(),
        assignment: assignment.clone(),
        note: Text::parse(note.to_string())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![dep_id, assignment])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn dependency_resolve(ctx: &BusCtx, agent: &str, dep_id: &str, file: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let dep_id = EventId::parse(dep_id.to_string())?;
    let state = ctx.load_state()?;
    let dep = state
        .dependencies
        .get(&dep_id)
        .ok_or_else(|| invalid(format!("unknown dependency {dep_id}")))?;
    let assignment = dep.current_assignment.clone();
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let v = inject(
        v,
        &[
            ("dependency", Value::String(dep_id.to_string())),
            ("assignment", Value::String(assignment.to_string())),
        ],
    );
    let data: DependencyResolved = from_value(v)?;
    let env = bus::publish_event(ctx, &agent, EventData::DependencyResolved(data), vec![dep_id, assignment])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn dependency_reject(ctx: &BusCtx, agent: &str, dep_id: &str, reason: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let dep_id = EventId::parse(dep_id.to_string())?;
    let state = ctx.load_state()?;
    let dep = state
        .dependencies
        .get(&dep_id)
        .ok_or_else(|| invalid(format!("unknown dependency {dep_id}")))?;
    let assignment = dep.current_assignment.clone();
    let data = EventData::DependencyRejected(DependencyRejected {
        dependency: dep_id.clone(),
        assignment: assignment.clone(),
        reason: Text::parse(reason.to_string())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![dep_id, assignment])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn dependency_reassign(ctx: &BusCtx, agent: &str, dep_id: &str, new_target: &str, reason: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let dep_id = EventId::parse(dep_id.to_string())?;
    let new_target = Agent::parse(new_target.to_string())?;
    let state = ctx.load_state()?;
    let dep = state
        .dependencies
        .get(&dep_id)
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
    let env = bus::publish_event(ctx, &agent, data, vec![dep_id, previous_assignment])?;
    println!("published {}", env.id);
    Ok(())
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
    let agents: Vec<&crate::state::AgentState> = match &args.agent {
        Some(a) => {
            let a = Agent::parse(a.clone())?;
            vec![state.agent(&a).ok_or_else(|| invalid(format!("unknown agent {a}")))?]
        }
        None => state.agents.values().collect(),
    };
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
    let mut items = Vec::new();
    // Not yet terminally resolved — includes `LifecycleConflict` items, which
    // still need attention (a coordinator's `lifecycle.conflict_resolved`),
    // not just plain `Open` ones.
    let still_open = |s: &ItemStatus| !matches!(s, ItemStatus::Terminal(_));
    for issue in state.issues.values() {
        if issue.current_target == agent && still_open(&issue.status) {
            items.push(serde_json::json!({"kind": "issue", "id": issue.id.to_string(), "summary": issue.data.summary.as_str()}));
        }
    }
    for dep in state.dependencies.values() {
        if dep.current_target == agent && still_open(&dep.status) {
            items.push(serde_json::json!({"kind": "dependency", "id": dep.id.to_string(), "interface": dep.data.interface.as_str()}));
        }
    }
    for h in state.handoffs.values() {
        if h.data.receiver == agent && still_open(&h.status) {
            items.push(serde_json::json!({"kind": "handoff", "id": h.id.to_string(), "summary": h.data.summary.as_str()}));
        }
    }
    for chain in state.reviews.values() {
        if chain.current_request.reviewer == agent && !chain.is_closed() {
            items.push(serde_json::json!({
                "kind": "review",
                "id": chain.current_nomination.to_string(),
                "summary": chain.current_request.summary.as_str(),
            }));
        }
    }
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

pub fn dependencies(ctx: &BusCtx, args: &crate::cli::DependenciesArgs) -> AbResult<()> {
    let agent = Agent::parse(args.agent.clone())?;
    let state = ctx.load_state()?;
    let items: Vec<Value> = state
        .dependencies
        .values()
        .filter(|d| d.requester == agent || d.current_target == agent)
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
        .collect();
    if args.json {
        println!("{}", serde_json::to_string_pretty(&items)?);
    } else {
        for i in &items {
            println!("{i}");
        }
    }
    Ok(())
}

pub fn tail(ctx: &BusCtx, args: &crate::cli::TailArgs) -> AbResult<()> {
    let walk = crate::history::walk_full(&ctx.repo_root, bus::BUS_BRANCH)?;
    let mut events = Vec::new();
    for c in &walk.commits {
        for e in &c.new_events {
            if let Some(a) = &args.agent {
                if e.agent.as_str() != a {
                    continue;
                }
            }
            events.push(e.clone());
        }
    }
    let start = events.len().saturating_sub(args.count);
    let tail = &events[start..];
    if args.json {
        let lines: Vec<String> = tail.iter().map(|e| e.to_canonical_line()).collect();
        println!("[{}]", lines.join(","));
    } else {
        for e in tail {
            println!("{}", e.to_canonical_line());
        }
    }
    Ok(())
}

pub fn conflicts(ctx: &BusCtx, args: &crate::cli::ConflictsArgs) -> AbResult<()> {
    let state = ctx.load_state()?;
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
