//! One-time v1 -> v2 bus history converter (AGENT_COORDINATION_EVOLUTION.md
//! section 2.5's migration, simplified for a currently-quiesced fleet per the
//! maintainer's direction: full event-by-event replay of every v1 identity's
//! history into v2's registry+per-agent-stream format, each identity's v2
//! stream starting fresh at seq 0 since v2's `agent.registered` is hard-coded
//! to sequence zero (round 5/6/7/8 review never needed to relax that
//! invariant, and this tool doesn't ask it to) -- v1's own `refs/heads/
//! agent-bus` is left completely untouched as the permanent historical
//! record; nothing here reads its content directly. Instead every v1 event is
//! read back through v1's *own* compiled binary (`tail --agent <a> --json`),
//! since v1 and v2 share the exact same ~34 core event `data` schemas
//! (`docs/AGENT_BUS_SCHEMA.md` is unmodified by this branch) -- no field
//! -level translation is needed, only re-deriving each event's `observed`
//! frontier (v1: a single whole-bus-tip id; v2: a per-agent sparse/complete
//! map) and re-deriving registry epoch transitions (v1 has no registry
//! concept at all; `register`/`retire` are ungated, self-authored events on
//! the linear branch).
//!
//! This binary is deliberately built as a second `[[bin]]` target (Cargo
//! auto-discovers `src/bin/*.rs`) rather than a `cli.rs` subcommand, so it
//! never touches the branch currently under review at all -- it lives on its
//! own branch, `#[path]`-including the same module files as `main.rs` so it
//! gets its own self-contained copy of every internal (`pub(crate)`-visible
//! from within this copy) primitive it needs: `bootstrap::genesis`,
//! `registry::propose_transition`, `stream::create_root_commit`/
//! `append_to_stream`, `Envelope::new`, `EventData::from_kind_and_value` --
//! the exact same, already-reviewed construction logic every other command
//! uses, not a hand-rolled reimplementation of any of it.

#[path = "../apply.rs"]
mod apply;
#[path = "../bootstrap.rs"]
mod bootstrap;
#[path = "../canon.rs"]
mod canon;
#[path = "../common.rs"]
mod common;
#[path = "../envelope.rs"]
mod envelope;
#[path = "../error.rs"]
mod error;
#[path = "../events.rs"]
mod events;
#[path = "../exclusive.rs"]
mod exclusive;
#[path = "../frontier.rs"]
mod frontier;
#[path = "../gitrepo.rs"]
mod gitrepo;
#[path = "../registry.rs"]
mod registry;
#[path = "../scalars.rs"]
mod scalars;
#[path = "../state.rs"]
mod state;
#[path = "../storage.rs"]
mod storage;
#[path = "../stream.rs"]
mod stream;

use envelope::Envelope;
use error::{invalid, AbResult};
use events::EventData;
use frontier::{FrontierEntry, ObservedFrontier};
use scalars::{Agent, EventId, ObjectId, Short};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// One event as read back from v1's own `tail --json`, before any v2
/// construction happens -- `data`/`refs`/`kind` are taken as-is (v1 and v2
/// share the same schema for every kind this tool encounters; an unknown
/// kind is a hard error, not silently dropped, see `main`'s own check).
#[derive(Debug, Clone, serde::Deserialize)]
struct V1Event {
    id: String,
    agent: String,
    #[allow(dead_code)]
    seq: u64,
    kind: String,
    refs: Vec<String>,
    data: serde_json::Value,
}

/// Enumerates every identity that has ever published to v1 by listing the
/// top-level directories of `refs/heads/agent-bus`'s tree directly (v1's own
/// `storage::list_agents` does the identical thing, just against a checked
/// -out worktree rather than the ref's tree object) -- deliberately NOT
/// derived from `status --json`, which only reflects each identity's
/// *current* lifecycle/scope/plan state and would silently omit an identity
/// whose events exist but who currently has nothing to report there (a real
/// gap an adversarial haiku review caught: status-derived discovery both can
/// under-count a quiet-but-registered identity and can over-count any
/// unrelated JSON structure that happens to carry an `"agent"` key). A
/// directory listing of the bus tree itself cannot have either failure mode:
/// every identity that ever published at least one event has a directory
/// there (that's how v1 stores its own segments -- see `storage::agent_dir`),
/// and nothing else does.
fn v1_agents(v1_repo: &Path) -> AbResult<Vec<Agent>> {
    let listing = gitrepo::run_ok(
        v1_repo,
        &["ls-tree", "--name-only", "-d", "refs/heads/agent-bus"],
    )?;
    listing
        .lines()
        .map(str::trim)
        .filter(|name| !name.is_empty() && *name != "_bus")
        .map(|name| Agent::parse(name.to_string()).map_err(|e| invalid(format!("bad v1 agent name: {e}"))))
        .collect()
}

fn v1_tail(v1_bin: &Path, v1_repo: &Path, agent: &Agent) -> AbResult<Vec<V1Event>> {
    let out = std::process::Command::new(v1_bin)
        .args(["--repo"])
        .arg(v1_repo)
        // v1's `tail` defaults to the most recent 20 events only; this tool
        // needs the caller's entire history, so pass an effectively
        // unbounded count rather than relying on the default.
        .args(["tail", "--agent", agent.as_str(), "--count", "1000000", "--json"])
        .output()
        .map_err(|e| invalid(format!("failed to run v1 tail for {agent}: {e}")))?;
    if !out.status.success() {
        return Err(invalid(format!(
            "v1 tail --agent {agent} --json failed: {}",
            String::from_utf8_lossy(&out.stderr)
        )));
    }
    serde_json::from_slice(&out.stdout)
        .map_err(|e| invalid(format!("v1 tail --agent {agent} --json did not parse: {e}")))
}

/// Finds v1's bootstrap coordinator by decoding every seq-0
/// `agent.registered` event and looking for the sole one claiming
/// `Role::Coordinator` -- v1's own rule (`register`'s CLI help: coordinators
/// register only via bootstrap-init) guarantees there's exactly one. Errors
/// rather than guessing if that invariant doesn't hold in the real data.
fn find_coordinator(events: &BTreeMap<EventId, V1Event>) -> AbResult<EventId> {
    let mut found: Option<EventId> = None;
    for (id, e) in events {
        if id.seq() != 0 || e.kind != "agent.registered" {
            continue;
        }
        let data = EventData::from_kind_and_value(&e.kind, e.data.clone())
            .map_err(|err| invalid(format!("{id}: agent.registered did not convert: {err}")))?;
        let EventData::AgentRegistered(d) = &data else {
            unreachable!()
        };
        if d.primary_role == events::Role::Coordinator {
            if let Some(prior) = &found {
                return Err(invalid(format!(
                    "v1 has two coordinators: {prior} and {id} -- cannot determine a single \
                     bootstrap coordinator to migrate first"
                )));
            }
            found = Some(id.clone());
        }
    }
    found.ok_or_else(|| invalid("no agent.registered event in v1 history claims Role::Coordinator"))
}

fn parse_event_id(s: &str) -> AbResult<EventId> {
    let (agent, seq) = s
        .split_once(':')
        .ok_or_else(|| invalid(format!("malformed v1 event id: {s}")))?;
    let seq: u64 = seq
        .parse()
        .map_err(|_| invalid(format!("malformed v1 event id: {s}")))?;
    Ok(EventId::new(&Agent::parse(agent.to_string())?, seq))
}

/// The coordinator's real v1 events (seq >= 1) are shifted up by exactly one
/// v2 seq to make room for the synthesized merge-engine-genesis event
/// inserted right after their registration (see `run`'s module doc on why:
/// appending it at the *end* of the coordinator's stream instead would avoid
/// this shift, but real v1 data has the coordinator's own issue-tracking
/// events referencing review events, which the genesis event must precede --
/// the two constraints can't both hold without moving the coordinator's real
/// events out of the way). Every other agent, and the coordinator's own
/// registration (seq 0), is unaffected.
fn remap_event_id(id: &EventId, coordinator_agent: &Agent) -> EventId {
    if id.agent() == *coordinator_agent && id.seq() >= 1 {
        EventId::new(coordinator_agent, id.seq() + 1)
    } else {
        id.clone()
    }
}

/// Applies `remap_event_id` inside a raw v1 JSON payload, in place, without
/// needing per-`EventData`-variant field enumeration: walks every string
/// leaf and rewrites it only if the *entire* string value parses as a
/// `coordinator_agent:N` (N >= 1) event id -- not a substring match, so free
/// -text fields (rationale, summary, file:line locations like
/// `commands.rs:670`) can't collide, since `Agent::parse` rejects anything
/// that isn't a bare short identifier and a whole-value match against prose
/// is astronomically unlikely to begin with. Must run BEFORE typed decode
/// (`EventData::from_kind_and_value`) so every embedded reference --
/// `nomination`, `evidence`, `merge_engine_epoch`, whatever the kind has --
/// is already correct by the time `referenced_ids()`/gate-4 sees it.
fn remap_json_ids(v: &mut serde_json::Value, coordinator_agent: &Agent) {
    match v {
        serde_json::Value::String(s) => {
            if let Ok(id) = parse_event_id(s) {
                let remapped = remap_event_id(&id, coordinator_agent);
                if remapped != id {
                    *s = remapped.to_string();
                }
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                remap_json_ids(item, coordinator_agent);
            }
        }
        serde_json::Value::Object(map) => {
            for val in map.values_mut() {
                remap_json_ids(val, coordinator_agent);
            }
        }
        _ => {}
    }
}

/// Kahn's algorithm over the raw v1 id/refs graph: same-agent events in
/// increasing seq order, a cross-agent reference resolved before whatever
/// names it -- any valid topological order gives an identical v2 reduction
/// (gate 16), so this doesn't need to reconstruct v1's true wall-clock
/// publish interleaving, only a causally valid one -- EXCEPT for one thing
/// the raw v1 graph never encodes at all: v1 has no registry, so no other
/// identity's registration event ever actually `refs` the bootstrap
/// coordinator's. Left alone, a tie-breaking topo sort (this one breaks ties
/// by lowest `EventId`, i.e. alphabetically by agent name) can and did pick
/// some other identity's zero-dependency registration first ("c-agent" sorts
/// before "coord1"), which `register_identity`'s own coordinator-first
/// precondition then correctly rejected rather than silently mis-bootstrap.
/// So `coordinator`'s registration is threaded in here as an explicit
/// synthetic dependency of every *other* identity's own registration event,
/// making the real v1 invariant (the bootstrap coordinator's identity is
/// fixed and known, even though v1 never wrote that fact down as a
/// reference) an actual graph edge instead of hoping tie-breaking gets it
/// right.
fn build_deps(
    events: &BTreeMap<EventId, V1Event>,
    coordinator: &EventId,
) -> AbResult<BTreeMap<EventId, Vec<EventId>>> {
    let mut by_agent: BTreeMap<String, Vec<EventId>> = BTreeMap::new();
    for (id, e) in events {
        by_agent.entry(e.agent.clone()).or_default().push(id.clone());
    }
    for ids in by_agent.values_mut() {
        ids.sort_by_key(|i| i.seq());
    }
    let mut deps: BTreeMap<EventId, Vec<EventId>> = BTreeMap::new();
    for ids in by_agent.values() {
        for (i, id) in ids.iter().enumerate() {
            let mut d = Vec::new();
            if i > 0 {
                d.push(ids[i - 1].clone());
            } else if id != coordinator {
                d.push(coordinator.clone());
            }
            for r in &events[id].refs {
                let rid = parse_event_id(r)?;
                if rid.agent() != id.agent() {
                    d.push(rid);
                }
            }
            deps.insert(id.clone(), d);
        }
    }
    Ok(deps)
}

/// Kahn's algorithm over an arbitrary dependency graph (real v1 events plus,
/// where `build_deps`'s caller has added them, synthetic nodes with no
/// `V1Event` backing of their own -- see `run`'s merge-engine-genesis
/// handling). Any valid topological order gives an identical v2 reduction
/// (gate 16), so this doesn't need to reconstruct v1's true wall-clock
/// publish interleaving, only a causally valid one.
fn kahn_sort(deps: BTreeMap<EventId, Vec<EventId>>) -> AbResult<Vec<EventId>> {
    let total = deps.len();
    let mut remaining = deps.clone();
    let mut ready: BTreeSet<EventId> = remaining
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
        remaining.remove(&id);
        order.push(id.clone());
        if let Some(children) = dependents.get(&id) {
            for child in children {
                if let Some(d) = remaining.get_mut(child) {
                    d.retain(|x| x != &id);
                    if d.is_empty() {
                        ready.insert(child.clone());
                    }
                }
            }
        }
    }
    if order.len() != total {
        return Err(invalid(
            "v1 event graph has a cycle or an unresolvable reference -- cannot convert",
        ));
    }
    Ok(order)
}

/// Mirrors `coordinator::requires_complete_frontier` (private to that module,
/// not reachable from here without modifying the branch under review). Of
/// the kinds it lists, `review.merge_authorized`, `schema.activated`, and
/// `merge_engine.activated` all genuinely appear in v1 history -- v1's own
/// CLI has `schema-activate`/`merge-engine-activate` subcommands (confirmed
/// via `agent-bus.exe --help` against the live v1 binary; an earlier version
/// of this doc comment wrongly assumed both were v2-only additions, caught
/// by adversarial review). Only `broadcast.published` is actually v2-only --
/// v1's CLI has no broadcast-publishing command at all -- so it's excluded
/// here even though `coordinator::requires_complete_frontier` conditionally
/// requires a complete frontier for it too.
fn requires_complete_frontier_v1(data: &EventData) -> bool {
    matches!(
        data,
        EventData::ReviewMergeAuthorized(_)
            | EventData::SchemaActivated(_)
            | EventData::MergeEngineActivated(_)
    )
}

struct Converted {
    /// Each identity's current v2 stream tip and next seq, once its stream
    /// root exists.
    tips: BTreeMap<Agent, (ObjectId, u64)>,
    registry_epoch: registry::RosterEpoch,
    active_members: BTreeMap<Agent, registry::MemberBinding>,
}

/// Every active member's current stream position, exactly -- mirrors
/// `coordinator::build_complete_frontier` (private, not reachable from here).
/// Shared by the main replay loop and the synthetic merge-engine-genesis
/// event (see `run`), both of which construct a `MergeEngineActivated`/
/// `ReviewMergeAuthorized`-class event needing the same kind of frontier.
fn build_complete_frontier_v1(st: &Converted, id_for_errors: &EventId) -> AbResult<ObservedFrontier> {
    let mut entries = Vec::new();
    for member in st.active_members.keys() {
        let (tip, next_seq) = st
            .tips
            .get(member)
            .ok_or_else(|| invalid(format!("{id_for_errors}: {member} has no stream yet")))?;
        entries.push(FrontierEntry {
            agent: member.clone(),
            stream_tip: tip.clone(),
            through: EventId::new(member, next_seq.saturating_sub(1)),
        });
    }
    ObservedFrontier::complete(&st.registry_epoch, entries)
}

#[allow(clippy::too_many_arguments)]
fn main() {
    if let Err(e) = run() {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}

fn run() -> AbResult<()> {
    let mut args = std::env::args().skip(1);
    let mut v1_bin: Option<PathBuf> = None;
    let mut v1_repo: Option<PathBuf> = None;
    let mut out_repo: Option<PathBuf> = None;
    let mut host = Short::parse("migration".to_string())?;
    while let Some(a) = args.next() {
        match a.as_str() {
            "--v1-bin" => v1_bin = Some(PathBuf::from(args.next().expect("--v1-bin needs a value"))),
            "--v1-repo" => {
                v1_repo = Some(PathBuf::from(args.next().expect("--v1-repo needs a value")))
            }
            "--out-repo" => {
                out_repo = Some(PathBuf::from(args.next().expect("--out-repo needs a value")))
            }
            "--host" => host = Short::parse(args.next().expect("--host needs a value"))?,
            other => return Err(invalid(format!("unknown argument: {other}"))),
        }
    }
    let v1_bin = v1_bin.ok_or_else(|| invalid("--v1-bin is required"))?;
    let v1_repo = v1_repo.ok_or_else(|| invalid("--v1-repo is required"))?;
    let out_repo = out_repo.ok_or_else(|| invalid("--out-repo is required"))?;

    // Fresh, empty git repo -- this tool only ever writes here, never to
    // `v1_repo`, and the caller decides separately whether/when `out_repo`'s
    // refs are ever pushed anywhere real.
    std::fs::create_dir_all(&out_repo).ok();
    gitrepo::run_ok(&out_repo, &["init", "--quiet", "-b", "main"])?;
    gitrepo::run_ok(&out_repo, &["config", "user.email", "migrate-v1@localhost"])?;
    gitrepo::run_ok(&out_repo, &["config", "user.name", "migrate-v1"])?;
    std::fs::write(out_repo.join("README.md"), "migrated v2 bus\n")
        .map_err(|e| invalid(format!("{e}")))?;
    gitrepo::run_ok(&out_repo, &["add", "README.md"])?;
    gitrepo::run_ok(&out_repo, &["commit", "-q", "-m", "root"])?;
    let product_review_from =
        ObjectId::parse(gitrepo::rev_parse(&out_repo, "HEAD")?).map_err(|e| invalid(format!("{e}")))?;

    let agents = v1_agents(&v1_repo)?;
    eprintln!("v1 identities found: {}", agents.len());

    let mut all_events: BTreeMap<EventId, V1Event> = BTreeMap::new();
    for a in &agents {
        let events = v1_tail(&v1_bin, &v1_repo, a)?;
        eprintln!("  {a}: {} events", events.len());
        for e in events {
            let id = parse_event_id(&e.id)?;
            // `id.agent()` (parsed from the `id` string) and `e.agent` (v1's
            // own separate field) must agree -- `topo_order`'s same-agent
            // grouping trusts `e.agent` while its cross-agent-ref filtering
            // trusts `id.agent()` (an adversarial review flagged the
            // resulting graph as silently wrong if the two ever diverge on
            // malformed input); reject up front instead.
            if id.agent().as_str() != e.agent {
                return Err(invalid(format!(
                    "v1 event {} has id agent {} but agent field {} -- inconsistent v1 data, \
                     refusing to guess which is correct",
                    e.id,
                    id.agent(),
                    e.agent
                )));
            }
            if let Some(prior) = all_events.insert(id.clone(), e.clone()) {
                return Err(invalid(format!(
                    "duplicate v1 event id {id}: v1 tail returned two distinct events \
                     claiming this id (agent={}/seq={} vs agent={}/seq={}) -- refusing to \
                     silently drop one",
                    prior.agent, prior.seq, e.agent, e.seq
                )));
            }
        }
    }
    eprintln!("total events: {}", all_events.len());

    let mut max_v1_seq: BTreeMap<Agent, u64> = BTreeMap::new();
    for id in all_events.keys() {
        let entry = max_v1_seq.entry(id.agent()).or_insert(0);
        if id.seq() > *entry {
            *entry = id.seq();
        }
    }

    let coordinator = find_coordinator(&all_events)?;
    eprintln!("bootstrap coordinator: {coordinator}");
    let mut deps = build_deps(&all_events, &coordinator)?;

    // v1 bakes its initial merge-engine epoch directly into the immutable
    // bootstrap file (`merge_engine_epoch: "<coordinator>:0"`, confirmed
    // against the live v1 repo's `_bus/BUS.json`) -- no event ever
    // establishes it, since none is needed. v2 deliberately has no such
    // implicit bootstrap epoch: `coordinator::apply_merge_engine_activated`
    // requires an explicit `merge_engine.activated` event before
    // `current_merge_engine_epoch` is ever `Some`, with one documented
    // "genesis activation" exception for exactly this migration case
    // (previous_epoch names the coordinator's own registration event,
    // `EventId::new(&env.agent, 0)`) -- see that function's own doc comment,
    // which explicitly says this was "found by adversarial review while
    // porting v1's merge engine epoch convention". So this tool publishes
    // that genesis activation itself, using the real pinned engine/version
    // values from v1's own bootstrap file.
    //
    // It's inserted right after the coordinator's registration (it will
    // actually be appended as their v2 seq 1, established purely by
    // processing order below -- not by this id's numeric value), not
    // appended after their real history: appending at the end was tried
    // first and hit a real cycle -- the coordinator's own real issue
    // -tracking events (round 1 of this tool, against real v1 data) do
    // reference review events as evidence, so "the genesis event must follow
    // every real coordinator event" and "the genesis event must precede
    // every review.merge_authorized event" can't both hold when a
    // coordinator event references a review that must itself wait for the
    // genesis event. Inserting right after seq 0 avoids the cycle (the
    // genesis event then depends on nothing but the registration), at the
    // cost of shifting the coordinator's real v1 seq >= 1 events up by one
    // v2 seq -- `remap_event_id`/`remap_json_ids` (below, applied per event)
    // keep every reference to those ids correct after the shift.
    //
    // `genesis_graph_key` is only ever used as an opaque graph node label
    // for `deps`/`kahn_sort` and as a marker to recognize in the processing
    // loop below -- it is NOT the event's real eventual v2 id. Its numeric
    // seq is deliberately one past the coordinator's real v1 max
    // specifically so it CANNOT collide with a real event's id (round 2 of
    // this tool hit exactly that: using seq 1, the coordinator's real first
    // non-registration event's own id, as BOTH the map key AND the "coord's
    // real seq-1 depends on X" edge silently clobbered that event's own
    // entry in the `deps` map and made it depend on itself). The event's
    // REAL v2 id (`genesis_v2_id`, set below once its actual `next_seq` is
    // known) is what other events' payloads reference; the dependency edges
    // here guarantee that real id ends up being v2 seq 1.
    let coordinator_agent = coordinator.agent();
    let coordinator_last_real_seq = max_v1_seq.get(&coordinator_agent).copied().unwrap_or(0);
    let genesis_graph_key = EventId::new(&coordinator_agent, coordinator_last_real_seq + 1);
    deps.insert(genesis_graph_key.clone(), vec![coordinator.clone()]);
    if coordinator_last_real_seq >= 1 {
        let coordinator_first_real_id = EventId::new(&coordinator_agent, 1);
        deps.get_mut(&coordinator_first_real_id)
            .expect("build_deps covers every real event")
            .push(genesis_graph_key.clone());
    }
    for (id, e) in &all_events {
        if e.kind == "review.merge_authorized" {
            deps.get_mut(id)
                .expect("build_deps covers every real event")
                .push(genesis_graph_key.clone());
        }
    }

    let order = kahn_sort(deps)?;
    eprintln!("topological order computed: {} events", order.len());

    let worktrees = out_repo.join("_wt");
    let mut converted: Option<Converted> = None;
    let mut genesis_v2_id: Option<EventId> = None;

    for id in &order {
        if *id == genesis_graph_key {
            let st = converted.as_mut().ok_or_else(|| {
                invalid("synthetic merge-engine genesis event before any registration exists")
            })?;
            let (tip, next_seq) = st
                .tips
                .get(&coordinator_agent)
                .cloned()
                .ok_or_else(|| invalid(format!("{coordinator_agent} has no stream yet")))?;
            let this_id = EventId::new(&coordinator_agent, next_seq);
            let data = EventData::MergeEngineActivated(events::MergeEngineActivated {
                previous_epoch: coordinator.clone(),
                merge_engine: Short::parse("git-ort".to_string())?,
                merge_engine_version: Short::parse("2.53.0".to_string())?,
                // v1's bootstrap file has no design/helper-commit equivalent
                // at all (its engine is pinned by the helper binary, not by
                // a tracked product commit) -- `product_review_from` is the
                // one real, already-resolvable commit v1 did record, reused
                // here rather than inventing a value with no historical
                // basis. This event is a migration-only bootstrap synthesis,
                // not a claim that a genuine engine activation happened at
                // this commit.
                design_commit: product_review_from.clone(),
                helper_commit: product_review_from.clone(),
            });
            let observed = build_complete_frontier_v1(st, &this_id)?;
            let env = Envelope::new(&coordinator_agent, next_seq, observed, &data, []);
            let new_tip = stream::append_to_stream(
                &out_repo,
                &coordinator_agent,
                &tip,
                std::slice::from_ref(&env),
                &worktrees.join(format!("_append_{}_{}", coordinator_agent, next_seq)),
            )?;
            st.tips.insert(coordinator_agent.clone(), (new_tip, next_seq + 1));
            eprintln!("synthesized merge-engine genesis activation: {this_id}");
            genesis_v2_id = Some(this_id);
            continue;
        }

        let e = &all_events[id];
        let agent = Agent::parse(e.agent.clone())?;
        let mut raw_data = e.data.clone();
        remap_json_ids(&mut raw_data, &coordinator_agent);
        let mut data = EventData::from_kind_and_value(&e.kind, raw_data)
            .map_err(|err| invalid(format!("{id}: {} did not convert: {err}", e.kind)))?;
        if let EventData::ReviewMergeAuthorized(d) = &mut data {
            if d.merge_engine_epoch == coordinator {
                // Guaranteed `Some` by the dependency edge added above: every
                // `review.merge_authorized` event is ordered after the
                // synthetic genesis event.
                d.merge_engine_epoch = genesis_v2_id
                    .clone()
                    .expect("genesis activation processed before any review.merge_authorized event");
            }
        }

        if e.kind == "agent.registered" {
            let EventData::AgentRegistered(d) = &data else {
                unreachable!()
            };
            converted = Some(register_identity(
                &out_repo,
                &worktrees,
                converted,
                &agent,
                d,
                &host,
                &product_review_from,
                &max_v1_seq,
            )?);
            continue;
        }

        let st = converted
            .as_mut()
            .ok_or_else(|| invalid(format!("{id}: event before any registration exists")))?;

        let mut refs: Vec<EventId> = Vec::new();
        for r in &e.refs {
            refs.push(remap_event_id(&parse_event_id(r)?, &coordinator_agent));
        }
        let observed = if requires_complete_frontier_v1(&data) {
            build_complete_frontier_v1(st, id)?
        } else {
            let mut through: BTreeMap<Agent, EventId> = BTreeMap::new();
            // Mirrors `coordinator::build_frontier`: union the payload's own
            // `referenced_ids()` with the event's explicit `refs`, not just
            // `refs` alone -- v1's stored `refs` field may not have captured
            // every payload-embedded reference (the exact gap round-5
            // adversarial review found and fixed in `build_frontier` itself;
            // an earlier version of this loop reintroduced the identical gap
            // by iterating `refs` only, caught by adversarial review of this
            // tool).
            for r in data.referenced_ids().iter().chain(refs.iter()) {
                let ref_agent = r.agent();
                if ref_agent == agent {
                    continue;
                }
                through
                    .entry(ref_agent)
                    .and_modify(|existing| {
                        if r.seq() > existing.seq() {
                            *existing = r.clone();
                        }
                    })
                    .or_insert_with(|| r.clone());
            }
            let mut entries = Vec::new();
            for (ref_agent, r) in through {
                let (tip, _) = st.tips.get(&ref_agent).ok_or_else(|| {
                    invalid(format!("{id}: referenced agent {ref_agent} has no stream yet"))
                })?;
                entries.push(FrontierEntry {
                    agent: ref_agent,
                    stream_tip: tip.clone(),
                    through: r,
                });
            }
            ObservedFrontier::sparse(st.registry_epoch.id.clone(), entries)
        };

        let (tip, next_seq) = st
            .tips
            .get(&agent)
            .cloned()
            .ok_or_else(|| invalid(format!("{id}: {agent} has no stream yet")))?;
        // Deliberately `[]`, not `refs`: `Envelope::new` unions its last
        // argument with `data.referenced_ids()`, and gate 4 requires the
        // envelope's final `refs` to equal `data.referenced_ids()` exactly
        // (round-6 adversarial review of the reviewed branch itself). v1's
        // raw stored `refs` should already equal that set for any
        // unmodified event, so this is a no-op there -- but for the one kind
        // this tool rewrites in place (`review.merge_authorized`'s
        // `merge_engine_epoch`, above), v1's stored `refs` still names the
        // old `coordinator:0` sentinel, which is no longer present in the
        // rewritten payload's `referenced_ids()`; passing it here would
        // leave a stale extra ref and fail gate 4. `data.referenced_ids()`
        // alone is authoritative and correct in both cases.
        let env = Envelope::new(&agent, next_seq, observed, &data, []);
        let new_tip = stream::append_to_stream(
            &out_repo,
            &agent,
            &tip,
            std::slice::from_ref(&env),
            &worktrees.join(format!("_append_{}_{}", agent, next_seq)),
        )?;
        st.tips.insert(agent, (new_tip, next_seq + 1));
    }

    eprintln!("conversion complete. out repo: {}", out_repo.display());
    if let Some(st) = &converted {
        eprintln!("final registry epoch: {}", st.registry_epoch.id);
        for (a, (tip, next_seq)) in &st.tips {
            eprintln!("  {a}: {next_seq} events, tip {tip}");
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn register_identity(
    repo: &Path,
    worktrees: &Path,
    converted: Option<Converted>,
    agent: &Agent,
    d: &events::AgentRegistered,
    host: &Short,
    product_review_from: &ObjectId,
    max_v1_seq: &BTreeMap<Agent, u64>,
) -> AbResult<Converted> {
    // Every registered identity has at least its own `agent.registered`
    // event in `all_events`, so this is always populated for a real
    // registration; `unwrap_or(0)` only guards a value that can't actually
    // be absent.
    let final_v1_seq = Some(max_v1_seq.get(agent).copied().unwrap_or(0));
    match converted {
        None => {
            // First-ever registration: must be a coordinator, matching v1's
            // own "coordinators register only via bootstrap-init" rule and
            // v2's genesis precondition.
            if d.primary_role != events::Role::Coordinator {
                return Err(invalid(format!(
                    "{agent}: first identity converted must be a coordinator (v1's own first \
                     registration is expected to be its bootstrap coordinator)"
                )));
            }
            // Deliberately NOT `bootstrap::genesis`: that function is
            // documented as "the v2-native path only" and hardcodes
            // `final_v1_seq: None` with no way to override it -- a real v1
            // migration (this tool) needs the coordinator's own stream
            // header to correctly record the v1 sequence it replayed, so
            // this hand-constructs the identical root-epoch-plus-stream-root
            // sequence `genesis` performs internally (`registry::
            // create_root` then `stream::create_root_commit`), just with the
            // correct `final_v1_seq` (round-registry-review finding).
            let config = bootstrap::BusConfig::new("sha1".to_string(), product_review_from.clone())?;
            let mut members = BTreeMap::new();
            members.insert(
                agent.clone(),
                registry::MemberBinding {
                    role: d.primary_role,
                    host: host.clone(),
                    coordinator_custody_epoch: 0,
                    standby: None,
                },
            );
            let epoch = registry::create_root(
                repo,
                &config,
                members.clone(),
                &worktrees.join("_registry_root"),
            )?;
            let header = stream::StreamHeader {
                agent: agent.clone(),
                activation_event: None,
                registration_authority: EventId::new(agent, 0),
                final_v1_seq,
                object_format: config.object_format.clone(),
                schema_fingerprint: bootstrap::SCHEMA_FINGERPRINT.to_string(),
            };
            let observed = ObservedFrontier::sparse(epoch.id.clone(), []);
            let env = Envelope::new(agent, 0, observed, &EventData::AgentRegistered(d.clone()), []);
            let root_commit = stream::create_root_commit(
                repo,
                &header,
                &env,
                &worktrees.join(format!("_stream_root_{agent}")),
            )?;
            let mut tips = BTreeMap::new();
            tips.insert(agent.clone(), (root_commit, 1));
            Ok(Converted {
                tips,
                registry_epoch: epoch,
                active_members: members,
            })
        }
        Some(mut st) => {
            if st.active_members.contains_key(agent) {
                return Err(invalid(format!(
                    "{agent}: already registered earlier in this replay -- v1 history has two \
                     agent.registered events for the same identity, which this tool refuses to \
                     silently collapse into one"
                )));
            }
            let mut members = st.active_members.clone();
            members.insert(
                agent.clone(),
                registry::MemberBinding {
                    role: d.primary_role,
                    host: host.clone(),
                    coordinator_custody_epoch: 0,
                    standby: None,
                },
            );
            let new_epoch = registry::propose_transition(
                repo,
                &st.registry_epoch,
                members.clone(),
                &worktrees.join(format!("_transition_{agent}")),
            )?;
            let header = stream::StreamHeader {
                agent: agent.clone(),
                activation_event: None,
                registration_authority: EventId::new(agent, 0),
                final_v1_seq,
                object_format: "sha1".to_string(),
                schema_fingerprint: bootstrap::SCHEMA_FINGERPRINT.to_string(),
            };
            let env = Envelope::new(
                agent,
                0,
                ObservedFrontier::sparse(new_epoch.id.clone(), []),
                &EventData::AgentRegistered(d.clone()),
                [],
            );
            let root_commit = stream::create_root_commit(
                repo,
                &header,
                &env,
                &worktrees.join(format!("_stream_root_{agent}")),
            )?;
            st.tips.insert(agent.clone(), (root_commit, 1));
            st.registry_epoch = new_epoch;
            st.active_members = members;
            Ok(st)
        }
    }
}
