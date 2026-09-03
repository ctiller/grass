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
use std::collections::{BTreeMap, BTreeSet};
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
    /// round trip -- so whether an urgent candidate is still waiting is
    /// always answerable here even when no coordinator has run at all
    /// (gate 18). This is the "last local receipt" half of section 2.3's
    /// "surface the last local receipt and coordinator health locally";
    /// it does not surface coordinator liveness/heartbeat data, which
    /// nothing in this crate tracks yet.
    Outbox(OutboxArgs),
    /// AGENT_REVIEW.md section 7 step 4: the accepting reviewer constructs
    /// the no-conflict merge candidate for `--nomination`/`--reviewed-
    /// commit`, tags it `agent-candidate/<agent>/<candidate>`, and pushes
    /// that tag to `--remote` (failing hard if the push fails -- a
    /// candidate tag only the reviewer's own clone can see is useless to
    /// every other agent and to `coordinator::drain_outbox`'s own gate for
    /// the eventual `review.merge_authorized` submission). A read-only
    /// reviewer-side helper, not itself a publication, so it reads whatever
    /// is already local rather than requiring a fresh remote probe.
    PrepareMerge(PrepareMergeArgs),
    /// AGENT_REVIEW.md section 8, the pre-merge gate: run immediately after
    /// publishing `review.merge_authorized` and immediately before pushing
    /// the candidate to `main`. Confirms the authorization is genuinely
    /// usable *right now* -- the reviewer is still eligible and accepted, no
    /// finding or blocking issue remains open, `reviewed_scope` still equals
    /// the nomination's `review_scope` -- and, crucially, re-checks live Git
    /// state that could only have changed *after* `review.merge_authorized`
    /// was published: `refs/heads/main` still equals exactly the authorized
    /// `previous_main` (a fast-forward past it, not just a divergence, still
    /// requires a fresh authorization), the candidate's actual parents are
    /// exactly `[previous_main, reviewed_commit]`, it carries exactly one
    /// matching `Agent-Bus-Reviewer` trailer, every path it changes falls
    /// within `reviewed_scope`, and every recorded check passed. This is a
    /// distinct, later check from `coordinator::verify_review_merge_
    /// authorized` (which gates the event at publication time, against
    /// whatever the payload itself claims) and from `apply::apply_review_
    /// merge_authorized` (the event's own internal bus-state consistency):
    /// neither can catch `main` having moved, or the candidate having been
    /// hand-tampered with, in the real time that elapses between publishing
    /// the authorization and actually pushing it. Reads local Git/bus state
    /// as-is rather than fetching first -- like `prepare-merge`, the
    /// reviewer is expected to have already fetched `main` themselves (per
    /// AGENT_REVIEW.md section 7 step 1); prints the exact candidate object
    /// id to push on success.
    MergeReady(MergeReadyArgs),
    /// AGENT_REVIEW.md sections 9/11/12 (fixture 10): a read-only
    /// correlation-and-report audit over post-bootstrap first-parent `main`
    /// history, from the bus's own `product_review_from` through `--to`
    /// (default `refs/heads/main`). For each merge commit it confirms: the
    /// commit is a genuine two-parent merge whose first parent is the prior
    /// audited commit; it carries exactly one `Agent-Bus-Reviewer` trailer
    /// naming a real, currently-a-reviewer identity who authored none of the
    /// commits actually introduced; a `review.merge_authorized` event exists
    /// whose recorded `candidate`/`previous_main`/`reviewed_commit` exactly
    /// match this real commit; and a `review.merged` or `review.merge_
    /// reconciled` receipt exists naming this exact commit. This is the
    /// mechanism section 1 refers to ("a missing or mismatched receipt is
    /// detected by `audit-main`") and the only way to catch a hand-pushed or
    /// otherwise out-of-protocol commit *after* it has already landed --
    /// nothing can refuse such a push server-side without a receive hook
    /// (section 9). A commit that landed on `main` before this repository
    /// ever adopted the protocol (i.e. before `product_review_from`'s first
    /// real reviewed merge) will also be flagged; that is the known,
    /// accepted one-time bootstrap-adoption gap documented in `audit_main`'s
    /// own module doc, not a live regression.
    AuditMain(AuditMainArgs),
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
    /// Probe the remote before reading, rather than reading whatever is
    /// already local. Fetches the same complete roster cut `status --sync`
    /// does (registry plus every active member's stream, not just `--agent`'s
    /// own), since that is what backs this command's `roster_epoch`/
    /// `freshness` fields honestly reporting a genuine
    /// `current-as-of-remote-probe` receipt rather than mixing a
    /// freshly-fetched stream with a possibly-stale local registry read.
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

#[derive(clap::Args)]
pub struct PrepareMergeArgs {
    /// The accepting reviewer.
    #[arg(long)]
    agent: String,
    /// The `review.nominated` (or a later `review.reassigned` link) this
    /// candidate is prepared for.
    #[arg(long)]
    nomination: String,
    /// The exact product-branch commit being reviewed.
    #[arg(long)]
    reviewed_commit: String,
    #[arg(long, default_value = "origin")]
    remote: String,
}

#[derive(clap::Args)]
pub struct MergeReadyArgs {
    /// The authorizing reviewer.
    #[arg(long)]
    agent: String,
    /// The `review.merge_authorized` event id to check.
    #[arg(long)]
    authorization: String,
}

#[derive(clap::Args)]
pub struct AuditMainArgs {
    /// End of the audited range (exclusive of nothing -- the commit itself
    /// is included). Defaults to `refs/heads/main`.
    #[arg(long)]
    to: Option<String>,
    /// Print the full findings array as JSON instead of one line per
    /// finding (or `audit-main: clean`).
    #[arg(long)]
    json: bool,
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

/// Writes `value` to stdout as pretty JSON. A broken pipe (the common,
/// entirely expected case of piping output into `head`, `grep -q`, or
/// anything else that can close its stdin early) exits quietly rather than
/// panicking with a backtrace -- there is no result left to report to
/// either the user or a downstream tool once the reader is gone.
fn print_json(value: &serde_json::Value) {
    use std::io::Write;
    let text = serde_json::to_string_pretty(value).expect("value always serializable");
    if let Err(e) = writeln!(std::io::stdout(), "{text}") {
        if e.kind() == std::io::ErrorKind::BrokenPipe {
            std::process::exit(0);
        }
        panic!("failed writing to stdout: {e}");
    }
}

/// The freshness envelope every command result whose output depends on a
/// [`crate::sync::Snapshot`] states (docs/AGENT_COORDINATION_EVOLUTION.md
/// section 2.4: "Every human and machine-readable result states its
/// snapshot receipt, roster epoch, causal frontier, last successful
/// synchronization time, and freshness class"; section 5 gate 8: "every
/// result labels its stale cut"). `submit` (no snapshot read at all -- a
/// pure local outbox write) and `genesis` (bootstrap; no prior snapshot
/// exists to report on) are deliberately not wired to this -- see their own
/// functions below.
///
/// `snapshot_receipt` and `causal_frontier` are two names for the same
/// underlying value here, `stream_tips`: it is simultaneously "what a later
/// validation re-checks a snapshot against" (its own receipt -- see
/// `sync::Snapshot`'s doc comment) and exactly the per-agent frontier a
/// causally-dependent event would be built against at this cut (see
/// `coordinator::build_frontier`/`build_complete_frontier`, which both
/// source their entries from the same per-agent stream tips). Nothing in
/// this crate has yet needed those two concepts to diverge, so rather than
/// invent a second, currently-identical representation, both field names
/// are kept (matching the design doc's own vocabulary) and populated from
/// the one value that is genuinely both.
///
/// `last_synced` is `null` if this local checkout has never yet completed a
/// synchronization (`sync::synced_snapshot`'s own fetch step succeeding),
/// never a fabricated or `now()`-derived value. Per section 2.4, "time
/// since sync is diagnostic; it never confers authority" -- nothing here,
/// or anywhere else in this crate, uses `last_synced`'s value to authorize
/// anything; `freshness` alone (not how recent `last_synced` looks) is what
/// a currency-sensitive caller must check.
fn freshness_fields(
    stream_tips: &BTreeMap<Agent, ObjectId>,
    roster_epoch: Option<&ObjectId>,
    last_synced: Option<&crate::scalars::Timestamp>,
    freshness: crate::sync::Freshness,
) -> serde_json::Value {
    let tips_json = serde_json::Value::Object(
        stream_tips
            .iter()
            .map(|(agent, tip)| (agent.as_str().to_string(), tip.as_str().into()))
            .collect(),
    );
    serde_json::json!({
        "snapshot_receipt": tips_json.clone(),
        "roster_epoch": roster_epoch.map(|e| e.as_str()),
        "causal_frontier": tips_json,
        "last_synced": last_synced.map(|t| t.as_str()),
        "freshness": match freshness {
            crate::sync::Freshness::Cached => "cached",
            crate::sync::Freshness::CurrentAsOfRemoteProbe => "current-as-of-remote-probe",
        },
    })
}

/// [`freshness_fields`] scoped to the whole roster a [`crate::sync::
/// Snapshot`] already knows -- the natural default for a command whose
/// result concerns the roster as a whole (`status`, `coordinate`,
/// `register`, `succeed`). `tail` builds its own narrower, single-agent
/// version directly instead (see `tail` below), since reporting every
/// other agent's tip for a single-stream read would overstate what that
/// command actually looked at.
fn freshness_envelope(snapshot: &crate::sync::Snapshot) -> serde_json::Value {
    freshness_fields(
        &snapshot.stream_tips,
        Some(&snapshot.roster_epoch.id),
        snapshot.last_synced.as_ref(),
        snapshot.freshness,
    )
}

/// Merges `extra`'s top-level fields into `value` (both expected to be JSON
/// objects), so every command below can build its own distinctive fields
/// first and then layer the shared freshness envelope on top in one place,
/// rather than six independent ad-hoc `json!{}` blocks whose field names
/// could silently drift apart from each other.
fn with_freshness(mut value: serde_json::Value, envelope: serde_json::Value) -> serde_json::Value {
    if let (Some(obj), serde_json::Value::Object(extra)) = (value.as_object_mut(), envelope) {
        obj.extend(extra);
    }
    value
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
        Command::PrepareMerge(args) => prepare_merge(args),
        Command::MergeReady(args) => merge_ready(args),
        Command::AuditMain(args) => audit_main(args),
    }
}

/// Deliberately does not report a freshness envelope (see
/// [`freshness_fields`]'s doc comment): this is the bus's bootstrap event --
/// there is no prior snapshot for a "snapshot receipt" or "roster epoch" to
/// have been read *from*, only the one this call itself is about to create.
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
        &args.remote,
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

    // A fresh local reduction of the just-published result -- not an
    // additional remote probe (the publish above already landed everything
    // this command changed), so this is honestly reported as `cached`, per
    // [`freshness_envelope`]'s doc comment: it reflects what is now known
    // locally, exactly like any other cached read taken immediately after
    // a local write.
    let snapshot = crate::sync::cached_snapshot(&paths.repo, &paths.common_dir, &paths.worktrees)?;

    print_json(&with_freshness(
        serde_json::json!({
            "registry_epoch": new_epoch.id.as_str(),
            "published_events": drained.published.iter().map(|e| e.as_str().to_string()).collect::<Vec<_>>(),
            "outbox_rejected": drained.rejected.iter().map(|r| serde_json::json!({"kind": r.kind, "reason": r.reason})).collect::<Vec<_>>(),
            "published": receipt.published,
            "rejected": receipt.rejected,
        }),
        freshness_envelope(&snapshot),
    ));
    Ok(())
}

/// Deliberately does not report a freshness envelope (see
/// [`freshness_fields`]'s doc comment): a pure local outbox write with no
/// snapshot read at all -- there is nothing here to have a receipt/epoch/
/// frontier/freshness *of*.
fn submit(args: SubmitArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let agent = parse_agent(&args.agent)?;
    let data_value: serde_json::Value = serde_json::from_str(&args.data)
        .map_err(|e| invalid(format!("--data is not valid JSON: {e}")))?;
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

    // See `register`'s identical comment: a local-only reduction of what
    // was just published, honestly reported as `cached`.
    let snapshot = crate::sync::cached_snapshot(&paths.repo, &paths.common_dir, &paths.worktrees)?;

    print_json(&with_freshness(
        serde_json::json!({
            "published_events": drained.published.iter().map(|e| e.as_str().to_string()).collect::<Vec<_>>(),
            "outbox_rejected": drained.rejected.iter().map(|r| serde_json::json!({"kind": r.kind, "reason": r.reason})).collect::<Vec<_>>(),
            "published": receipt.published,
            "rejected": receipt.rejected,
            "not_attempted": receipt.not_attempted,
        }),
        freshness_envelope(&snapshot),
    ));
    Ok(())
}

/// `--sync` fetches the same complete roster cut `status --sync` does (see
/// `TailArgs::sync`'s doc comment) rather than only `--agent`'s own stream:
/// `roster_epoch` and `freshness` are reported honestly only if the
/// registry itself was actually just probed too, not merely whichever
/// single stream `--agent` names.
fn tail(args: TailArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let agent = parse_agent(&args.agent)?;
    let snapshot = if args.sync {
        crate::sync::synced_snapshot(
            &paths.repo,
            &paths.common_dir,
            &args.remote,
            &paths.worktrees,
        )?
    } else {
        crate::sync::cached_snapshot(&paths.repo, &paths.common_dir, &paths.worktrees)?
    };
    let (header, log) = crate::stream::read_stream(
        &paths.repo,
        &agent,
        &paths.worktrees.join(format!("_tail_{agent}")),
    )?;

    // Scoped to just `--agent`'s own tip (see `freshness_envelope`'s doc
    // comment on `tail`): reporting every other agent's tip here would
    // overstate what a single-stream read actually looked at.
    let mut scoped_tips = BTreeMap::new();
    if let Some(tip) = snapshot.stream_tips.get(&agent) {
        scoped_tips.insert(agent.clone(), tip.clone());
    }
    let envelope = freshness_fields(
        &scoped_tips,
        Some(&snapshot.roster_epoch.id),
        snapshot.last_synced.as_ref(),
        snapshot.freshness,
    );

    print_json(&with_freshness(
        serde_json::json!({
            "agent": agent.as_str(),
            "activation_event": header.activation_event.map(|e| e.as_str().to_string()),
            "events": log,
        }),
        envelope,
    ));
    Ok(())
}

fn status(args: StatusArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let snapshot = if args.sync {
        crate::sync::synced_snapshot(
            &paths.repo,
            &paths.common_dir,
            &args.remote,
            &paths.worktrees,
        )?
    } else {
        crate::sync::cached_snapshot(&paths.repo, &paths.common_dir, &paths.worktrees)?
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

    print_json(&with_freshness(
        serde_json::json!({ "agents": agents }),
        freshness_envelope(&snapshot),
    ));
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

    // See `register`'s identical comment: a local-only reduction of what
    // was just published, honestly reported as `cached`.
    let snapshot = crate::sync::cached_snapshot(&paths.repo, &paths.common_dir, &paths.worktrees)?;

    print_json(&with_freshness(
        serde_json::json!({
            "registry_epoch": new_epoch.id.as_str(),
            "new_custody_epoch": new_custody_epoch,
            "registry_published": registry_receipt.published,
            "registry_rejected": registry_receipt.rejected,
            "registry_not_attempted": registry_receipt.not_attempted,
            "resumed_events": resumed.published.iter().map(|e| e.as_str().to_string()).collect::<Vec<_>>(),
            "resumed_rejected": resumed.rejected.iter().map(|r| serde_json::json!({"kind": r.kind, "reason": r.reason})).collect::<Vec<_>>(),
            "stream_published": stream_receipt.published,
            "stream_rejected": stream_receipt.rejected,
            "stream_not_attempted": stream_receipt.not_attempted,
        }),
        freshness_envelope(&snapshot),
    ));
    Ok(())
}

/// Reports a freshness envelope like every other snapshot-touching command
/// (gate 8: "cached reads and local candidate submission complete while the
/// host coordinator is stalled on the network indefinitely, and every
/// result labels its stale cut" -- this command is exactly that "cached
/// read... while stalled" scenario, so it must label its cut too), but with
/// one deliberate difference: `freshness` is unconditionally `"cached"` and
/// nothing here ever performs a network round trip to build it, preserving
/// this command's own documented "no network round trip at all" property
/// (see `Command::Outbox`'s doc comment). The roster-wide fields
/// (`snapshot_receipt`/`roster_epoch`/`causal_frontier`) come from a local
/// [`crate::sync::cached_snapshot`] read on a best-effort basis: `outbox`
/// itself has never required a registry to exist locally (`submit` writes
/// directly with no registry check at all), so a `cached_snapshot` failure
/// here (most commonly "no registry root exists locally" before the first
/// `genesis`) is not treated as an error -- those fields are simply `null`/
/// empty rather than this command now refusing to show local outbox state
/// it could always show before.
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

    let empty_tips = BTreeMap::new();
    let (tips, roster_epoch) =
        match crate::sync::cached_snapshot(&paths.repo, &paths.common_dir, &paths.worktrees) {
            Ok(snapshot) => (snapshot.stream_tips, Some(snapshot.roster_epoch.id)),
            Err(_) => (empty_tips, None),
        };
    let last_synced = crate::sync::read_last_synced(&paths.common_dir)?;
    let envelope = freshness_fields(
        &tips,
        roster_epoch.as_ref(),
        last_synced.as_ref(),
        crate::sync::Freshness::Cached,
    );

    print_json(&with_freshness(
        serde_json::json!({
            "agent": agent.as_str(),
            "pending": pending_json,
            "rejected": rejected_json,
        }),
        envelope,
    ));
    Ok(())
}

/// AGENT_REVIEW.md section 7 step 4 (see `Command::PrepareMerge`'s own doc
/// for why this matters): mirrors the shipped version-one helper's
/// `review_cmds::prepare_merge` closely, ported onto v2's `sync`/`state`
/// primitives instead of a v1 `BusCtx`/`load_state`. This is a convenience,
/// not an authority: nothing here is itself checked by `apply.rs` (which
/// deliberately never touches git -- see its module doc), so
/// `coordinator::drain_outbox` independently re-runs the same
/// `merge_candidate` checks against whatever `review.merge_authorized`
/// payload is actually submitted, rather than trusting that this command
/// was ever run, let alone run honestly.
fn prepare_merge(args: PrepareMergeArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let reviewer = parse_agent(&args.agent)?;
    let nomination = EventId::parse(args.nomination)?;
    let reviewed_commit = ObjectId::parse(args.reviewed_commit)?;

    let snapshot = crate::sync::cached_snapshot(&paths.repo, &paths.common_dir, &paths.worktrees)?;
    let envelope = freshness_envelope(&snapshot);
    let state = snapshot.state;
    let chain = state
        .review_chain(&nomination)
        .ok_or_else(|| invalid(format!("unknown nomination {nomination}")))?;
    if chain.current_nomination != nomination {
        return Err(invalid("nomination is no longer current"));
    }
    if chain.current_request.reviewer != reviewer {
        return Err(invalid(
            "only the nomination's reviewer may prepare a merge",
        ));
    }
    if !chain.accepted() {
        return Err(invalid(
            "the reviewer must accept the nomination before preparing a merge",
        ));
    }

    let previous_main = crate::gitrepo::rev_parse(&paths.repo, "refs/heads/main")?;
    let expected_authors: BTreeSet<Agent> = chain.current_request.authors.iter().cloned().collect();
    crate::merge_candidate::verify_authorship(
        &paths.repo,
        &reviewer,
        &expected_authors,
        &previous_main,
        reviewed_commit.as_str(),
    )?;

    let candidate = crate::merge_candidate::reconstruct_candidate(
        &paths.repo,
        &previous_main,
        reviewed_commit.as_str(),
        &reviewer,
    )?;
    let tag = crate::merge_candidate::candidate_tag_name(&reviewer, &candidate);
    crate::gitrepo::tag_lightweight(&paths.repo, &tag, &candidate)?;
    // A candidate tag that never reaches the remote cannot be fetched or
    // verified by any other agent, nor by `coordinator::drain_outbox`'s own
    // gate on a different host -- that must fail `prepare-merge` outright,
    // not silently proceed to print a `candidate` line the reviewer might
    // go on to submit an authorization for anyway (mirrors v1's identical
    // fix, see `merge_candidate.rs`'s module doc).
    let push = crate::gitrepo::run(
        &paths.repo,
        &["push", &args.remote, &format!("refs/tags/{tag}")],
    )?;
    if !push.success {
        return Err(invalid(format!(
            "failed to publish candidate tag refs/tags/{tag} to {}: {}",
            args.remote, push.stderr
        )));
    }

    print_json(&with_freshness(
        serde_json::json!({
            "candidate": candidate,
            "previous_main": previous_main,
            "merge_engine_epoch": state.current_merge_engine_epoch.as_ref().map(|e| e.as_str().to_string()),
        }),
        envelope,
    ));
    Ok(())
}

/// AGENT_REVIEW.md section 8, the pre-merge gate (see `Command::MergeReady`'s
/// own doc for the full rationale). A thin CLI wrapper -- arg parsing,
/// snapshot load, JSON output -- around `merge_ready::check_merge_ready`,
/// which holds the actual gate logic (and its own extensive test suite,
/// including the git-linked checks that need a real repo) so it stays
/// testable without going through `resolve_paths`/process cwd. Reads local
/// bus/git state as-is (like `prepare_merge`, this is a convenience read,
/// not a publication) -- re-verifies everything the authorization claims
/// against what is actually true *right now*, rather than trusting that it
/// was true when `review.merge_authorized` was published moments (or
/// longer) earlier.
fn merge_ready(args: MergeReadyArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let reviewer = parse_agent(&args.agent)?;
    let authorization = EventId::parse(args.authorization)?;

    let snapshot = crate::sync::cached_snapshot(&paths.repo, &paths.common_dir, &paths.worktrees)?;
    let candidate = crate::merge_ready::check_merge_ready(
        &paths.repo,
        &snapshot.state,
        &reviewer,
        &authorization,
    )?;

    print_json(&serde_json::json!({
        "ready": true,
        "candidate": candidate.as_str(),
    }));
    Ok(())
}

/// AGENT_REVIEW.md sections 9/11/12 (see `Command::AuditMain`'s own doc for
/// the full rationale). A thin CLI wrapper -- arg parsing, snapshot load,
/// plain-or-JSON output -- around `audit_main::audit_main_findings`, which
/// holds the actual correlation walk (and its own extensive test suite)
/// mirroring `cli::merge_ready`'s identical relationship to `merge_ready::
/// check_merge_ready`. Reads local bus/git state as-is: like `merge_ready`,
/// this is a read-only diagnostic, not a publication, and the caller is
/// expected to have already fetched both the bus and `refs/heads/main`
/// themselves if a current-as-of-remote-probe answer matters -- nothing here
/// performs a network round trip on its own.
fn audit_main(args: AuditMainArgs) -> AbResult<()> {
    let paths = resolve_paths()?;
    let snapshot = crate::sync::cached_snapshot(&paths.repo, &paths.common_dir, &paths.worktrees)?;
    let findings =
        crate::audit_main::audit_main_findings(&paths.repo, &snapshot.state, args.to.as_deref())?;

    if args.json {
        print_json(&serde_json::json!(findings));
    } else if findings.is_empty() {
        println!("audit-main: clean");
    } else {
        for f in &findings {
            println!("{f}");
        }
    }
    Ok(())
}
