//! The command surface: turns the library primitives built so far
//! (bootstrap/registry/outbox/coordinator/publish/sync) into an actual
//! runnable binary. Deliberately minimal -- enough to genesis a bus,
//! register further agents, submit and publish ordinary events, and read
//! back a stream or a roster/state summary. Not yet covered: per-kind
//! convenience commands for every one of `events.rs`'s ~34 kinds (`submit`
//! is generic over kind+JSON data instead), friction/broadcast commands,
//! and a `v1`-fleet migration command -- each is real further work.

use crate::error::{invalid, AbError, AbResult};
use crate::events::{AgentRegistered, EventData, Role};
use crate::outbox::Candidate;
use crate::publish::RefUpdate;
use crate::registry::MemberBinding;
use crate::scalars::{Agent, EventId, ObjectId, Short, Text};
use clap::{Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "agent-bus",
    version,
    about = "Grass agent coordination bus (v2)"
)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Subcommand)]
pub enum Command {
    /// Activates a brand-new bus: the registry's root epoch, naming one
    /// coordinator, plus that coordinator's own stream root.
    Genesis(GenesisArgs),
    /// Registers a further agent: a registry epoch transition adding it as
    /// an active member, plus its own stream root -- published together as
    /// one atomic multi-ref push.
    Register(RegisterArgs),
    /// Enqueues one event in `--agent`'s local outbox. Not yet visible to
    /// anyone until a `coordinate` call drains and publishes it.
    Submit(SubmitArgs),
    /// Drains `--agent`'s outbox and pushes the resulting stream commit to
    /// the remote.
    Coordinate(CoordinateArgs),
    /// Prints `--agent`'s full event log.
    Tail(TailArgs),
    /// Prints the current roster and every member's reduced lifecycle state.
    Status(StatusArgs),
    /// Takes over `--target`'s stream custody, moving it to this caller's
    /// own host (section 2.3, gate 19). Refused unless the caller is
    /// `--target`'s pre-authorized standby or an existing coordinator.
    Succeed(SucceedArgs),
    /// Prints `--agent`'s local outbox state: every candidate still
    /// pending (in urgent-first drain order) and every one a coordinator
    /// has rejected, with the durable reason. Purely local -- no network
    /// round trip -- so this is what "the last local receipt and
    /// coordinator health" (section 2.3) means concretely: whether an
    /// urgent candidate is still waiting is always answerable here even
    /// when no coordinator has run at all (gate 18).
    Outbox(OutboxArgs),
}

#[derive(clap::Args)]
pub struct GenesisArgs {
    #[arg(long)]
    agent: String,
    #[arg(long)]
    display_name: String,
    #[arg(long)]
    purpose: String,
    #[arg(long, default_value = "sha1")]
    object_format: String,
    /// The product commit exempt from the newly activated review protocol.
    /// Defaults to the repository's current `HEAD`.
    #[arg(long)]
    product_review_from: Option<String>,
    #[arg(long)]
    host: String,
    #[arg(long, default_value = "origin")]
    remote: String,
}

#[derive(clap::Args)]
pub struct RegisterArgs {
    #[arg(long)]
    agent: String,
    #[arg(long)]
    display_name: String,
    #[arg(long, default_value = "implementor")]
    role: String,
    #[arg(long)]
    purpose: String,
    #[arg(long)]
    host: String,
    #[arg(long, default_value_t = 0)]
    custody_epoch: u64,
    /// A pre-authorized standby for this agent's stream custody (section
    /// 2.3): the only non-coordinator who may later `succeed` it.
    #[arg(long)]
    standby: Option<String>,
    #[arg(long)]
    provider: Option<String>,
    #[arg(long)]
    model: Option<String>,
    #[arg(long, default_value = "origin")]
    remote: String,
    #[arg(long)]
    client_id: Option<String>,
}

#[derive(clap::Args)]
pub struct SubmitArgs {
    #[arg(long)]
    agent: String,
    /// Event kind, e.g. `agent.status`.
    #[arg(long)]
    kind: String,
    /// The event's own data payload, as a JSON object.
    #[arg(long)]
    data: String,
    /// Cross-agent event ids this event causally depends on, `agent:seq`
    /// each.
    #[arg(long = "observes")]
    observes: Vec<String>,
    /// Requests an urgent flush (section 2.3/2.4): a priority signal for
    /// the coordinator's batching policy, not a liveness guarantee -- an
    /// urgent candidate is drained ahead of ordinary ones once a
    /// coordinator does run, but remains just as locally pending as any
    /// other candidate until one does.
    #[arg(long)]
    urgent: bool,
    #[arg(long)]
    client_id: Option<String>,
}

#[derive(clap::Args)]
pub struct CoordinateArgs {
    #[arg(long)]
    agent: String,
    #[arg(long)]
    host: String,
    #[arg(long, default_value_t = 0)]
    custody_epoch: u64,
    #[arg(long, default_value = "origin")]
    remote: String,
}

#[derive(clap::Args)]
pub struct TailArgs {
    #[arg(long)]
    agent: String,
    /// Fetch `--agent`'s stream from the remote first, rather than reading
    /// whatever is already local.
    #[arg(long, default_value = "origin")]
    remote: String,
    #[arg(long)]
    sync: bool,
}

#[derive(clap::Args)]
pub struct StatusArgs {
    #[arg(long, default_value = "origin")]
    remote: String,
    /// Refuse a cached snapshot; always probe the remote first. Currency-
    /// sensitive callers should set this (AGENT_COORDINATION_EVOLUTION.md
    /// section 2.4).
    #[arg(long)]
    sync: bool,
}

#[derive(clap::Args)]
pub struct SucceedArgs {
    /// The proposer taking over custody -- must be the target's
    /// pre-authorized standby, or an existing coordinator.
    #[arg(long)]
    proposer: String,
    /// The agent whose stream custody is being taken over.
    #[arg(long)]
    target: String,
    /// The host the proposer runs on -- what the target's stream custody
    /// moves to.
    #[arg(long)]
    host: String,
    #[arg(long, default_value = "origin")]
    remote: String,
}

#[derive(clap::Args)]
pub struct OutboxArgs {
    #[arg(long)]
    agent: String,
}

struct RepoPaths {
    repo: PathBuf,
    common_dir: PathBuf,
    worktrees: PathBuf,
}

fn resolve_paths() -> AbResult<RepoPaths> {
    let cwd = std::env::current_dir().map_err(|e| AbError::Io {
        path: ".".to_string(),
        source: e,
    })?;
    let repo = crate::gitrepo::repo_root(&cwd)?;
    let common_dir = crate::gitrepo::common_dir(&cwd)?;
    let worktrees = common_dir.join("agent-bus").join("wt-v2");
    Ok(RepoPaths {
        repo,
        common_dir,
        worktrees,
    })
}

fn parse_agent(s: &str) -> AbResult<Agent> {
    Agent::parse(s.to_string())
}

fn parse_short(s: &str) -> AbResult<Short> {
    Short::parse(s.to_string())
}

fn parse_text(s: &str) -> AbResult<Text> {
    Text::parse(s.to_string())
}

fn parse_role(s: &str) -> AbResult<Role> {
    serde_json::from_value(serde_json::Value::String(s.to_string()))
        .map_err(|e| invalid(format!("invalid role {s:?}: {e}")))
}

/// A default idempotency key for a submission the caller didn't name one
/// for: process id plus wall-clock nanos, unique enough for one-shot CLI
/// invocations. A caller that wants a truly retriable submission should
/// pass `--client-id` explicitly and reuse it.
fn default_client_id() -> String {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    format!("cli-{}-{nanos}", std::process::id())
}

fn print_json(value: &serde_json::Value) {
    println!(
        "{}",
        serde_json::to_string_pretty(value).expect("value always serializable")
    );
}

pub fn run(cli: Cli) -> AbResult<()> {
    match cli.command {
        Command::Genesis(args) => genesis(args),
        Command::Register(args) => register(args),
        Command::Submit(args) => submit(args),
        Command::Coordinate(args) => coordinate(args),
        Command::Tail(args) => tail(args),
        Command::Status(args) => status(args),
        Command::Succeed(args) => succeed(args),
        Command::Outbox(args) => outbox(args),
    }
}

fn genesis(args: GenesisArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let agent = parse_agent(&args.agent)?;
    let review_from = match args.product_review_from {
        Some(rev) => crate::gitrepo::rev_parse(&paths.repo, &rev)?,
        None => crate::gitrepo::rev_parse(&paths.repo, "HEAD")?,
    };
    let (config, epoch, stream_commit) = crate::bootstrap::genesis(
        &paths.repo,
        &agent,
        parse_short(&args.display_name)?,
        parse_text(&args.purpose)?,
        args.object_format,
        ObjectId::parse(review_from)?,
        parse_short(&args.host)?,
        &paths.worktrees,
    )?;

    let updates = vec![
        RefUpdate::new(crate::registry::REGISTRY_REF, epoch.id.clone()),
        RefUpdate::new(
            crate::stream::stream_ref(&agent).into_string(),
            stream_commit.clone(),
        ),
    ];
    let receipt = crate::publish::publish(&paths.repo, &args.remote, &updates)?;

    print_json(&serde_json::json!({
        "registry_epoch": epoch.id.as_str(),
        "stream_commit": stream_commit.as_str(),
        "object_format": config.object_format,
        "published": receipt.published,
        "rejected": receipt.rejected,
    }));
    Ok(())
}

fn register(args: RegisterArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let new_agent = parse_agent(&args.agent)?;
    let host = parse_short(&args.host)?;
    let role = parse_role(&args.role)?;

    let registry_tip = crate::registry::read_registry_tip(&paths.repo)?
        .ok_or_else(|| invalid("no registry root exists yet -- run `genesis` first"))?;
    let epoch = crate::registry::read_epoch(
        &paths.repo,
        &registry_tip,
        &paths.worktrees.join("_register_epoch"),
    )?;
    if epoch.is_active_member(&new_agent) {
        return Err(invalid(format!(
            "{new_agent} is already an active member of roster epoch {} -- pick a different \
             agent name; changing an existing agent's binding is not what `register` does",
            epoch.id
        )));
    }

    let mut members = epoch.active_members.clone();
    members.insert(
        new_agent.clone(),
        MemberBinding {
            role,
            host: host.clone(),
            coordinator_custody_epoch: args.custody_epoch,
            standby: args.standby.map(|s| parse_agent(&s)).transpose()?,
        },
    );
    let new_epoch = crate::registry::propose_transition(
        &paths.repo,
        &epoch,
        members,
        &paths.worktrees.join("_register_transition"),
    )?;

    let candidate = Candidate::new(
        &new_agent,
        &EventData::AgentRegistered(AgentRegistered {
            display_name: parse_short(&args.display_name)?,
            primary_role: role,
            purpose: parse_text(&args.purpose)?,
            product_base: None,
            product_branch: None,
            provider: args.provider.map(|s| parse_short(&s)).transpose()?,
            model: args.model.map(|s| parse_short(&s)).transpose()?,
        }),
        vec![],
    );
    let client_id = args.client_id.unwrap_or_else(default_client_id);
    crate::outbox::submit(&paths.common_dir, &client_id, &candidate)?;

    let drained = crate::coordinator::drain_outbox(
        &paths.repo,
        &paths.common_dir,
        &new_agent,
        &host,
        args.custody_epoch,
        &paths.worktrees,
    )?;
    let new_stream_tip = crate::stream::read_stream_tip(&paths.repo, &new_agent)?
        .ok_or_else(|| invalid("just-drained agent has no stream tip"))?;

    // Published atomically together: a reader must never see the new
    // agent's stream root without the registry epoch that authorizes it,
    // nor the registry transition without being able to explain what that
    // new member's own stream root looks like.
    let updates = vec![
        RefUpdate::new(crate::registry::REGISTRY_REF, new_epoch.id.clone()),
        RefUpdate::new(
            crate::stream::stream_ref(&new_agent).into_string(),
            new_stream_tip,
        ),
    ];
    let receipt = crate::publish::publish(&paths.repo, &args.remote, &updates)?;

    print_json(&serde_json::json!({
        "registry_epoch": new_epoch.id.as_str(),
        "published_events": drained.published.iter().map(|e| e.as_str().to_string()).collect::<Vec<_>>(),
        "outbox_rejected": drained.rejected.iter().map(|r| serde_json::json!({"kind": r.kind, "reason": r.reason})).collect::<Vec<_>>(),
        "published": receipt.published,
        "rejected": receipt.rejected,
    }));
    Ok(())
}

fn submit(args: SubmitArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let agent = parse_agent(&args.agent)?;
    let data_value: serde_json::Value = serde_json::from_str(&args.data)?;
    let data = EventData::from_kind_and_value(&args.kind, data_value)?;
    let extra_refs: Vec<EventId> = args
        .observes
        .into_iter()
        .map(EventId::parse)
        .collect::<AbResult<_>>()?;
    let mut candidate = Candidate::new(&agent, &data, extra_refs);
    if args.urgent {
        candidate = candidate.urgent();
    }
    let client_id = args.client_id.unwrap_or_else(default_client_id);
    let path = crate::outbox::submit(&paths.common_dir, &client_id, &candidate)?;
    print_json(&serde_json::json!({
        "client_id": client_id,
        "urgent": candidate.urgent,
        "outbox_path": path.display().to_string(),
    }));
    Ok(())
}

fn coordinate(args: CoordinateArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let agent = parse_agent(&args.agent)?;
    let host = parse_short(&args.host)?;
    let (drained, receipt) = crate::coordinator::drain_and_publish(
        &paths.repo,
        &paths.common_dir,
        &agent,
        &host,
        args.custody_epoch,
        &paths.worktrees,
        &args.remote,
    )?;
    print_json(&serde_json::json!({
        "published_events": drained.published.iter().map(|e| e.as_str().to_string()).collect::<Vec<_>>(),
        "outbox_rejected": drained.rejected.iter().map(|r| serde_json::json!({"kind": r.kind, "reason": r.reason})).collect::<Vec<_>>(),
        "published": receipt.published,
        "rejected": receipt.rejected,
        "not_attempted": receipt.not_attempted,
    }));
    Ok(())
}

fn tail(args: TailArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let agent = parse_agent(&args.agent)?;
    if args.sync {
        let refspec = {
            let r = crate::stream::stream_ref(&agent).into_string();
            format!("{r}:{r}")
        };
        crate::gitrepo::fetch_refspecs(&paths.repo, &args.remote, &[refspec])?;
    }
    let (header, log) = crate::stream::read_stream(
        &paths.repo,
        &agent,
        &paths.worktrees.join(format!("_tail_{agent}")),
    )?;
    print_json(&serde_json::json!({
        "agent": agent.as_str(),
        "activation_event": header.activation_event.map(|e| e.as_str().to_string()),
        "events": log,
    }));
    Ok(())
}

fn status(args: StatusArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let snapshot = if args.sync {
        crate::sync::synced_snapshot(&paths.repo, &args.remote, &paths.worktrees)?
    } else {
        crate::sync::cached_snapshot(&paths.repo, &paths.worktrees)?
    };

    let agents: Vec<serde_json::Value> = snapshot
        .roster_epoch
        .active_members
        .iter()
        .map(|(agent, binding)| {
            let reduced = snapshot.state.agents.get(agent);
            serde_json::json!({
                "agent": agent.as_str(),
                "role": binding.role.to_string(),
                "host": binding.host.as_str(),
                "coordinator_custody_epoch": binding.coordinator_custody_epoch,
                "stream_tip": snapshot.stream_tips.get(agent).map(|t| t.as_str().to_string()),
                "status": reduced.map(|s| &s.status),
                "next_seq": reduced.map(|s| s.next_seq),
            })
        })
        .collect();

    print_json(&serde_json::json!({
        "roster_epoch": snapshot.roster_epoch.id.as_str(),
        "freshness": match snapshot.freshness {
            crate::sync::Freshness::Cached => "cached",
            crate::sync::Freshness::CurrentAsOfRemoteProbe => "current-as-of-remote-probe",
        },
        "agents": agents,
    }));
    Ok(())
}

fn succeed(args: SucceedArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let proposer = parse_agent(&args.proposer)?;
    let target = parse_agent(&args.target)?;
    let new_host = parse_short(&args.host)?;

    let registry_tip = crate::registry::read_registry_tip(&paths.repo)?
        .ok_or_else(|| invalid("no registry root exists yet -- run `genesis` first"))?;
    let epoch = crate::registry::read_epoch(
        &paths.repo,
        &registry_tip,
        &paths.worktrees.join("_succeed_epoch"),
    )?;

    let new_epoch = crate::registry::propose_custody_succession(
        &paths.repo,
        &epoch,
        &proposer,
        &target,
        new_host.clone(),
        &paths.worktrees.join("_succeed_transition"),
    )?;
    let new_custody_epoch = new_epoch.active_members[&target].coordinator_custody_epoch;

    let registry_receipt = crate::publish::publish(
        &paths.repo,
        &args.remote,
        &[RefUpdate::new(
            crate::registry::REGISTRY_REF,
            new_epoch.id.clone(),
        )],
    )?;

    // Resume whatever was left in `target`'s preserved outbox, now under
    // the new custody -- demonstrating gate 19's "resumes preserved
    // outboxes exactly once" rather than merely asserting it structurally.
    let (resumed, stream_receipt) = crate::coordinator::drain_and_publish(
        &paths.repo,
        &paths.common_dir,
        &target,
        &new_host,
        new_custody_epoch,
        &paths.worktrees,
        &args.remote,
    )?;

    print_json(&serde_json::json!({
        "registry_epoch": new_epoch.id.as_str(),
        "new_custody_epoch": new_custody_epoch,
        "registry_published": registry_receipt.published,
        "resumed_events": resumed.published.iter().map(|e| e.as_str().to_string()).collect::<Vec<_>>(),
        "stream_published": stream_receipt.published,
    }));
    Ok(())
}

fn outbox(args: OutboxArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let agent = parse_agent(&args.agent)?;

    let pending = crate::outbox::list_pending(&paths.common_dir, &agent)?;
    let pending_json: Vec<serde_json::Value> = pending
        .into_iter()
        .map(|(path, candidate)| {
            serde_json::json!({
                "kind": candidate.kind,
                "urgent": candidate.urgent,
                "outbox_path": path.display().to_string(),
            })
        })
        .collect();

    let rejected_dir = crate::outbox::outbox_dir(&paths.common_dir, &agent).join("rejected");
    let mut rejected_json = Vec::new();
    if rejected_dir.is_dir() {
        let mut entries: Vec<_> = std::fs::read_dir(&rejected_dir)
            .map_err(|e| AbError::Io {
                path: rejected_dir.display().to_string(),
                source: e,
            })?
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().and_then(|x| x.to_str()) == Some("json"))
            .collect();
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let bytes = std::fs::read(entry.path()).map_err(|e| AbError::Io {
                path: entry.path().display().to_string(),
                source: e,
            })?;
            let receipt: serde_json::Value = serde_json::from_slice(&bytes)?;
            rejected_json.push(receipt);
        }
    }

    print_json(&serde_json::json!({
        "agent": agent.as_str(),
        "pending": pending_json,
        "rejected": rejected_json,
    }));
    Ok(())
}
