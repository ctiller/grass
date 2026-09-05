//! Property-based invariant tests across *several independently fetching
//! checkouts of one shared origin* -- the real deployment shape AGENT_BUS.md
//! section 2 describes, and the one every other test in this crate silently
//! collapses away.
//!
//! # Why this module exists
//!
//! Three severe bugs found late in this rewrite shared one root cause of
//! *invisibility*, not one root cause of failure: every existing test here
//! drives a single local repository, so a purely local write-then-read round
//! trip is all that ever gets exercised.
//!
//!  1. `gitrepo::ensure_bus_worktree` served permanently stale cached content
//!     once a second process invocation reused the same deterministic cache
//!     path.
//!  2. `git branch -f <fully-qualified-ref>` silently created a
//!     double-prefixed `refs/heads/refs/heads/...` ref that `rev-parse`'s own
//!     disambiguation fallback resolved *around* -- until a real `git fetch`
//!     from a second checkout created the correctly-named ref and permanently
//!     shadowed every further local write.
//!  3. `apply::topological_order`'s tie-break could place an event merely
//!     *naming* another agent before that agent's own registration, purely by
//!     name ordering.
//!
//! None of the three is exotic. All three needed a second checkout, fetching
//! for itself, to become visible at all. Rather than keep guessing which
//! hand-written scenario exposes the next one, this module explores the space:
//! `proptest` generates a [`World`], a plain in-memory value with no git or
//! filesystem involvement, which is then *planned* into a causally-valid
//! schedule, *materialized* into real temporary repositories, and *checked*
//! against a pure-Rust oracle.
//!
//! # Generate / materialize / check
//!
//! The three stages are deliberately separate, and only one of them touches
//! git:
//!
//!  - [`World`] and [`Step`] are what `proptest` generates and, crucially,
//!    *shrinks*. Every reference is a [`Sel`], which is total: it selects into
//!    whatever collection exists at that point, so no shrink can ever produce
//!    a structurally invalid `World`. Shrinking a live trace of git-mutating
//!    operations would be awkward and lossy; shrinking a plain `Vec` of plain
//!    enums is exactly what proptest is good at.
//!  - [`plan`] resolves that `World` into `Vec<Op>` -- fully concrete host
//!    indices, agent identities, and event references -- by running the pure
//!    [`Model`] forward as it goes, dropping any step whose preconditions the
//!    model says cannot hold and inserting the synchronization a real operator
//!    would have performed. The result is a schedule that the crate's own
//!    ordinary validation should accept in full, so a failure means a real
//!    defect rather than an uninteresting rejection.
//!  - [`materialize_op`] is the only code here that runs git. It performs the
//!    same library calls `cli.rs` performs, in the same order, against one
//!    bare origin and one working checkout per host.
//!  - [`check_hosts`] runs the invariants, comparing real reads against
//!    [`Model::expected`] -- the oracle computed purely from the `World`, with
//!    no git involved. The ref-name half runs after every single operation;
//!    the full reduction runs once the schedule is complete, on every checkout
//!    at whatever stale or current view the schedule left it at, and once more
//!    after the final fleet-wide synchronization. See [`Depth`] for why the
//!    expensive half is spent there rather than everywhere.
//!
//! # Evidence that it looks where it claims to
//!
//! A property test that has never failed is indistinguishable from one that
//! cannot fail, so this harness was validated by reintroducing two of the
//! three motivating bugs, one at a time, and confirming it catches each:
//!
//!  - Bug 2, with `stream::create_root_commit`'s `update-ref` reverted to `git
//!    branch -f`: caught on the *first* generated schedule, at the genesis
//!    operation -- "malformed, double-prefixed ref
//!    `refs/heads/refs/heads/agent-events/carol`". The rest of that schedule
//!    then went on working, which is precisely why the bug survived a whole
//!    crate's worth of single-repository tests.
//!  - Bug 1, with `gitrepo::ensure_bus_worktree`'s "verify before trusting"
//!    staleness check removed: caught as a *duplicated stream sequence
//!    number*. The second `agent.status` for an agent came back as `carol:1`
//!    where the oracle predicted `carol:2`, because the reused cache path
//!    still held the stream as it stood before the first append. That is a
//!    considerably louder symptom than the one this bug was originally found
//!    by.
//!
//! Both are pinned as a deterministic regression by
//! [`the_smallest_schedule_that_a_stale_cache_or_a_double_prefixed_ref_falls_to`],
//! so the class stays guarded regardless of what any given generated run draws.
//!
//! Bug 3 is not reproducible by simple reversion in the same way: the fix
//! changed a tie-break, and whether the old tie-break misorders anything
//! depends on agent-name ordering. The identity pool is arranged for that
//! reason -- it is deliberately not in lexicographic order, and which name
//! each agent takes is generated, so registration order and name order are
//! uncorrelated across runs.
//!
//! # What is deliberately not modelled
//!
//! Custody succession, retirement, and the currency-sensitive event kinds
//! (merge authorization, schema activation, broadcasts) are out of scope here:
//! each needs materially more oracle machinery, and this harness is aimed at
//! *scheduling*, *ordering*, and *staleness* defects rather than at fuzzing
//! every one of `events.rs`'s ~34 kinds. Registry transitions are always
//! performed from a checkout that has just synchronized, so the registry chain
//! stays linear -- a genuinely forked registry is a different (and separately
//! interesting) failure class whose expected behaviour is not modelled here.

use crate::common::Priority;
use crate::events::{
    AgentRegistered, AgentStatusEvent, EventData, IssueKind, IssueOpened, IssueResolved,
    LifecycleStatus, Role,
};
use crate::outbox::Candidate;
use crate::publish::RefUpdate;
use crate::registry::MemberBinding;
use crate::scalars::{Agent, EventId, ObjectId, Short, StringSet, Text};
use crate::state::ItemStatus;
use proptest::prelude::*;
use proptest::test_runner::TestCaseError;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use tempfile::TempDir;

/// Identities are drawn from a fixed pool rather than generated as `a0`,
/// `a1`, ... on purpose: `apply::topological_order` breaks ties by *agent
/// name*, so a pool whose lexicographic order is uncorrelated with
/// registration order is what actually exercises bug 3's class. Picking from
/// the pool by [`Sel`] means a run can register `dave` before `bob`.
const AGENT_NAMES: [&str; 4] = ["carol", "alice", "dave", "bob"];

/// Every additional checkout costs a real `git fetch` and a full re-reduction
/// on the convergence sweep, and every additional agent costs another worktree
/// checkout inside *every* reduction anywhere in the fleet -- so both the fleet
/// and the identity pool are capped rather than left to the generator. Three
/// checkouts is already enough for the shape that matters: one that authored
/// history, one that is behind it, and one that joined cold.
const MAX_HOSTS: usize = 3;

// ---------------------------------------------------------------- the World

/// A total selector into whatever collection exists at the point a step is
/// reached: `Sel(n).pick(len)` is always a valid index, whatever `len` turns
/// out to be, so shrinking can delete or reorder steps without ever producing
/// a `World` that references something absent.
///
/// Deliberately a small integer rather than `proptest::sample::Index`. It
/// shrinks toward zero just as well, it has a public constructor so the
/// planner can be unit-tested directly, and a minimal counterexample reads as
/// `Sel(2)` rather than as an opaque 64-bit fixed-point fraction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Sel(u8);

impl Sel {
    fn pick(self, len: usize) -> usize {
        assert!(len > 0, "Sel::pick against an empty collection");
        self.0 as usize % len
    }
}

fn sel() -> impl Strategy<Value = Sel> {
    any::<u8>().prop_map(Sel)
}

/// One generated scenario: a pure, `Debug`/`Clone` value describing a fleet's
/// whole life. Contains no paths, no repositories, and no git state -- see the
/// module doc for why that separation matters to shrinking.
#[derive(Debug, Clone)]
pub struct World {
    /// Which pool name the genesis coordinator takes. Generated rather than
    /// fixed so the coordinator is not always lexicographically first.
    genesis_name: Sel,
    /// The checkouts that join *after* the one that activates the bus, and how
    /// far into the schedule each of them joins: entry `k` selects a position
    /// in `steps`, and that checkout is created cold just before that step
    /// runs. A checkout selecting a position past the last step joins at the
    /// very end and only ever meets the bus through the final synchronization
    /// -- the coldest possible read, and the shape bug 1 and bug 2 needed.
    ///
    /// This is a field rather than a `Step` variant on purpose. Left to a
    /// weighted step generator, most short schedules came out with a single
    /// checkout, quietly collapsing the harness back into the single-repository
    /// round trip it exists to escape.
    joins: Vec<Sel>,
    steps: Vec<Step>,
}

/// One requested step. Every reference is a [`Sel`], which is total against
/// whatever collection exists when the step is reached, so shrinking can
/// delete or reorder steps freely without producing a malformed `World`.
#[derive(Debug, Clone)]
enum Step {
    /// One checkout catches up with whatever is on origin right now.
    Sync { host: Sel },
    /// A new agent joins, custodied by `host`.
    Register {
        host: Sel,
        name: Sel,
        coordinator: bool,
    },
    /// An `agent.status` event from its custodian checkout.
    Status { agent: Sel, blocked: bool },
    /// An `issue.opened` naming another agent -- the cross-agent reference
    /// whose ordering against the target's own registration is bug 3's class.
    OpenIssue { opener: Sel, target: Sel },
    /// The issue's target publishes `issue.resolved` from *its* checkout,
    /// which requires that checkout to have synchronized past the opening.
    ResolveIssue { issue: Sel },
}

fn step_strategy() -> impl Strategy<Value = Step> {
    // Weighted toward *publishing* rather than toward synchronizing. The
    // planner already inserts a synchronization wherever one is genuinely
    // needed, so an explicit `Sync` step only ever buys an *extra* catch-up
    // that no causality demanded -- worth generating, but not worth spending
    // most of a short schedule on. Two publications by the same agent from the
    // same checkout, by contrast, is the cheapest shape that exercises a
    // reused worktree cache whose target has moved (bug 1), so the three
    // publishing steps carry most of the weight between them.
    prop_oneof![
        2 => sel().prop_map(|host| Step::Sync { host }),
        3 => (sel(), sel(), any::<bool>())
            .prop_map(|(host, name, coordinator)| Step::Register { host, name, coordinator }),
        4 => (sel(), any::<bool>())
            .prop_map(|(agent, blocked)| Step::Status { agent, blocked }),
        4 => (sel(), sel())
            .prop_map(|(opener, target)| Step::OpenIssue { opener, target }),
        3 => sel().prop_map(|issue| Step::ResolveIssue { issue }),
    ]
}

fn world_strategy(max_steps: usize) -> impl Strategy<Value = World> {
    (
        sel(),
        // At least one further checkout, always: a fleet of one is exactly the
        // configuration in which all three motivating bugs stayed invisible.
        prop::collection::vec(sel(), 1..MAX_HOSTS),
        prop::collection::vec(step_strategy(), 2..=max_steps),
    )
        .prop_map(|(genesis_name, joins, steps)| World {
            genesis_name,
            joins,
            steps,
        })
}

// -------------------------------------------------------- the resolved plan

/// A fully concrete operation: no [`Sel`] left, every host and agent resolved
/// to a real position, every referenced event resolved to a real `EventId`.
/// [`materialize_op`] executes exactly this, and [`Model::apply`] predicts
/// exactly this.
#[derive(Debug, Clone)]
enum Op {
    AddHost,
    Sync {
        host: usize,
    },
    /// Always the very first op of any plan: the bus has to exist.
    Genesis {
        host: usize,
        name: Agent,
    },
    Register {
        host: usize,
        name: Agent,
        role: Role,
    },
    Status {
        agent: usize,
        status: LifecycleStatus,
    },
    OpenIssue {
        opener: usize,
        target: usize,
    },
    ResolveIssue {
        issue: usize,
    },
}

// ------------------------------------------------------------- the oracle

/// An event's identity inside the model: which agent's stream, and where.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct EventKey {
    agent: usize,
    seq: u64,
}

#[derive(Debug, Clone)]
struct AgentModel {
    name: Agent,
    role: Role,
    /// The one checkout holding this agent's stream custody. Custody is bound
    /// to a host by the registry, so no other checkout ever writes this
    /// stream -- which is exactly why stream pushes always fast-forward.
    host: usize,
    next_seq: u64,
}

#[derive(Debug, Clone)]
struct IssueModel {
    id: EventId,
    opened: EventKey,
    opener: usize,
    target: usize,
    resolved: Option<EventKey>,
}

#[derive(Debug, Clone, Default)]
struct HostModel {
    /// Index into [`Model::epochs`] of this checkout's local registry tip.
    /// `None` until this checkout has a registry at all.
    epoch: Option<usize>,
    /// Every event this checkout can read locally: whatever it authored
    /// itself, plus everything origin held at its last synchronization.
    known: BTreeSet<EventKey>,
    /// Whether a remote probe has ever succeeded here. Section 2.4 requires
    /// every result to state a last successful synchronization time, and
    /// requires it never to be fabricated -- so a checkout that has only ever
    /// written locally must report `None`, however much it has published.
    ever_synced: bool,
}

/// The pure replay of a [`World`] -- the ground truth every real read is
/// compared against. Never touches git.
#[derive(Debug, Clone, Default)]
struct Model {
    hosts: Vec<HostModel>,
    agents: Vec<AgentModel>,
    /// The registry epoch chain: `epochs[i]` is that epoch's active member
    /// set, as agent indices. Linear by construction (see the module doc).
    epochs: Vec<BTreeSet<usize>>,
    issues: Vec<IssueModel>,
    /// Every `agent.status` event ever published, in order. A checkout's
    /// reduced lifecycle status is the last of these it actually knows about,
    /// which is how a stale checkout is distinguished from a current one by
    /// *content* rather than merely by event count.
    statuses: Vec<(EventKey, LifecycleStatus)>,
    /// Everything that has reached the shared origin.
    origin: BTreeSet<EventKey>,
}

impl Model {
    fn latest_epoch(&self) -> Option<usize> {
        self.epochs.len().checked_sub(1)
    }

    /// The stream sequence number the *next* event for `agent` will carry --
    /// asserted against what `drain_outbox` actually published.
    fn next_seq(&self, agent: usize) -> u64 {
        self.agents[agent].next_seq
    }

    /// Does `host` have everything it needs locally to author an event that
    /// names `agent`: the registry epoch listing it, and its registration?
    fn host_sees_agent(&self, host: usize, agent: usize) -> bool {
        let Some(epoch) = self.hosts[host].epoch else {
            return false;
        };
        self.epochs[epoch].contains(&agent)
            && self.hosts[host].known.contains(&EventKey { agent, seq: 0 })
    }

    fn publish(&mut self, host: usize, key: EventKey) {
        self.hosts[host].known.insert(key);
        self.origin.insert(key);
    }

    fn apply(&mut self, op: &Op) {
        match op {
            Op::AddHost => self.hosts.push(HostModel::default()),
            Op::Sync { host } => {
                self.hosts[*host].epoch = self.latest_epoch();
                self.hosts[*host].known = self.origin.clone();
                self.hosts[*host].ever_synced = true;
            }
            Op::Genesis { host, name } => {
                let idx = self.agents.len();
                self.agents.push(AgentModel {
                    name: name.clone(),
                    role: Role::Coordinator,
                    host: *host,
                    next_seq: 1,
                });
                self.epochs.push(BTreeSet::from([idx]));
                self.hosts[*host].epoch = self.latest_epoch();
                self.publish(*host, EventKey { agent: idx, seq: 0 });
            }
            Op::Register { host, name, role } => {
                let idx = self.agents.len();
                self.agents.push(AgentModel {
                    name: name.clone(),
                    role: *role,
                    host: *host,
                    next_seq: 1,
                });
                let mut members = self.epochs.last().cloned().unwrap_or_default();
                members.insert(idx);
                self.epochs.push(members);
                self.hosts[*host].epoch = self.latest_epoch();
                self.publish(*host, EventKey { agent: idx, seq: 0 });
            }
            Op::Status { agent, status } => {
                let key = self.take_seq(*agent);
                self.publish(self.agents[*agent].host, key);
                self.statuses.push((key, *status));
            }
            Op::OpenIssue { opener, target } => {
                let key = self.take_seq(*opener);
                self.publish(self.agents[*opener].host, key);
                self.issues.push(IssueModel {
                    id: EventId::new(&self.agents[*opener].name, key.seq),
                    opened: key,
                    opener: *opener,
                    target: *target,
                    resolved: None,
                });
            }
            Op::ResolveIssue { issue } => {
                let target = self.issues[*issue].target;
                let key = self.take_seq(target);
                self.publish(self.agents[target].host, key);
                self.issues[*issue].resolved = Some(key);
            }
        }
    }

    fn take_seq(&mut self, agent: usize) -> EventKey {
        let seq = self.agents[agent].next_seq;
        self.agents[agent].next_seq += 1;
        EventKey { agent, seq }
    }

    /// What a `sync::cached_snapshot` on `host` must report right now.
    /// `None` means "this checkout has no registry at all yet", for which a
    /// cached read is *expected* to fail.
    fn expected(&self, host: usize) -> Option<Expected> {
        let epoch = self.hosts[host].epoch?;
        let known = &self.hosts[host].known;
        let members: BTreeSet<String> = self.epochs[epoch]
            .iter()
            .map(|&i| self.agents[i].name.as_str().to_string())
            .collect();
        let mut agents = BTreeMap::new();
        for &i in &self.epochs[epoch] {
            if known.contains(&EventKey { agent: i, seq: 0 }) {
                // Contiguous by construction: a checkout learns an agent's
                // stream either by authoring all of it (custody) or by
                // fetching a whole prefix of it, never a hole in the middle.
                let seen = known.iter().filter(|k| k.agent == i).count() as u64;
                let status = self
                    .statuses
                    .iter()
                    .rev()
                    .find(|(k, _)| k.agent == i && known.contains(k))
                    .map(|(_, s)| *s)
                    // `apply_registered` seeds every agent as `Active`.
                    .unwrap_or(LifecycleStatus::Active);
                agents.insert(
                    self.agents[i].name.as_str().to_string(),
                    ExpectedAgent {
                        next_seq: seen,
                        role: self.agents[i].role,
                        status,
                    },
                );
            }
        }
        let mut issues = BTreeMap::new();
        for issue in &self.issues {
            if !known.contains(&issue.opened) {
                continue;
            }
            let resolved = issue.resolved.is_some_and(|k| known.contains(&k));
            issues.insert(
                issue.id.as_str().to_string(),
                ExpectedIssue {
                    opener: self.agents[issue.opener].name.as_str().to_string(),
                    target: self.agents[issue.target].name.as_str().to_string(),
                    status: if resolved { "resolved" } else { "open" },
                },
            );
        }
        Some(Expected {
            members,
            agents,
            issues,
        })
    }

    /// The stream refs `host` must have locally, by name -- the direct
    /// bug-2 check: a double-prefixed ref would leave the correctly-named one
    /// missing from this set.
    fn expected_stream_refs(&self, host: usize) -> BTreeSet<String> {
        self.hosts[host]
            .known
            .iter()
            .filter(|k| k.seq == 0)
            .map(|k| {
                crate::stream::stream_ref(&self.agents[k.agent].name)
                    .as_str()
                    .to_string()
            })
            .collect()
    }
}

/// The oracle's prediction for one checkout at one moment.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Expected {
    /// Agent names in the checkout's *local* registry epoch.
    members: BTreeSet<String>,
    /// Reduced agents, by name.
    agents: BTreeMap<String, ExpectedAgent>,
    /// Reduced issues, by event id.
    issues: BTreeMap<String, ExpectedIssue>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedAgent {
    next_seq: u64,
    role: Role,
    /// The lifecycle status this checkout should have reduced to -- older than
    /// the fleet-wide latest whenever this checkout is behind.
    status: LifecycleStatus,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedIssue {
    opener: String,
    target: String,
    status: &'static str,
}

// ------------------------------------------------------------------ planning

/// Resolves a generated [`World`] into a concrete, causally-valid schedule.
///
/// Runs the [`Model`] forward as it goes so each step's [`Sel`] references
/// select from what actually exists at that point, and so a step whose
/// preconditions the crate's own validation would refuse is dropped rather
/// than executed -- a sequence rejected by correct validation tells us nothing
/// about scheduling. The one thing it *adds* is a synchronization before a
/// registry transition, which is what a real operator does and what keeps the
/// registry chain linear.
fn plan(world: &World) -> Vec<Op> {
    let mut model = Model::default();
    let mut ops = Vec::new();
    let mut used_names: BTreeSet<usize> = BTreeSet::new();

    fn emit(ops: &mut Vec<Op>, model: &mut Model, op: Op) {
        model.apply(&op);
        ops.push(op);
    }

    // The bus has to exist before anything else can be asked of it, so
    // genesis is implicit rather than generated: a `World` without it would
    // describe nothing at all.
    emit(&mut ops, &mut model, Op::AddHost);
    let gi = world.genesis_name.pick(AGENT_NAMES.len());
    used_names.insert(gi);
    emit(
        &mut ops,
        &mut model,
        Op::Genesis {
            host: 0,
            name: agent(AGENT_NAMES[gi]),
        },
    );

    // Each further checkout joins cold at its generated position, including
    // positions past the end of the schedule -- a checkout that never acts,
    // and first meets the bus at the final fleet-wide synchronization.
    let mut joins: Vec<usize> = world
        .joins
        .iter()
        .map(|s| s.pick(world.steps.len() + 1))
        .collect();
    joins.sort_unstable();
    let mut joined = 0;

    for (i, step) in world.steps.iter().enumerate() {
        while joined < joins.len() && joins[joined] <= i {
            emit(&mut ops, &mut model, Op::AddHost);
            joined += 1;
        }
        match step {
            Step::Sync { host } => {
                let h = host.pick(model.hosts.len());
                emit(&mut ops, &mut model, Op::Sync { host: h });
            }
            Step::Register {
                host,
                name,
                coordinator,
            } => {
                let free: Vec<usize> = (0..AGENT_NAMES.len())
                    .filter(|i| !used_names.contains(i))
                    .collect();
                if free.is_empty() {
                    continue;
                }
                let ni = free[name.pick(free.len())];
                let h = host.pick(model.hosts.len());
                // A registry transition is a compare-and-swap against origin's
                // current tip; performing one from a stale checkout would push
                // a sibling epoch and fork the chain. Real callers synchronize
                // first, so the plan does too.
                if model.hosts[h].epoch != model.latest_epoch() {
                    emit(&mut ops, &mut model, Op::Sync { host: h });
                }
                used_names.insert(ni);
                emit(
                    &mut ops,
                    &mut model,
                    Op::Register {
                        host: h,
                        name: agent(AGENT_NAMES[ni]),
                        role: if *coordinator {
                            Role::Coordinator
                        } else {
                            Role::Implementor
                        },
                    },
                );
            }
            Step::Status { agent, blocked } => {
                let a = agent.pick(model.agents.len());
                emit(
                    &mut ops,
                    &mut model,
                    Op::Status {
                        agent: a,
                        status: if *blocked {
                            LifecycleStatus::Blocked
                        } else {
                            LifecycleStatus::Active
                        },
                    },
                );
            }
            Step::OpenIssue { opener, target } => {
                if model.agents.len() < 2 {
                    continue;
                }
                let o = opener.pick(model.agents.len());
                // An issue against oneself would make every reference
                // same-agent, which is the causality this step exists to
                // avoid; nudge rather than discard the step.
                let t = match target.pick(model.agents.len()) {
                    t if t != o => t,
                    t => (t + 1) % model.agents.len(),
                };
                // The opener's own checkout has to already know the target
                // exists -- `coordinator::drain_outbox` validates against what
                // is *locally* reduced, and `build_frontier` needs the
                // target's stream ref to be present. A checkout that has not
                // caught up would be rightly refused, which is not what this
                // harness probes, so catch it up first: that is what a real
                // agent does, and it leaves every *other* checkout exactly as
                // stale as it was.
                let opener_host = model.agents[o].host;
                if !model.host_sees_agent(opener_host, t) {
                    emit(&mut ops, &mut model, Op::Sync { host: opener_host });
                }
                emit(
                    &mut ops,
                    &mut model,
                    Op::OpenIssue {
                        opener: o,
                        target: t,
                    },
                );
            }
            Step::ResolveIssue { issue } => {
                let open: Vec<usize> = (0..model.issues.len())
                    .filter(|&i| model.issues[i].resolved.is_none())
                    .collect();
                if open.is_empty() {
                    continue;
                }
                let i = open[issue.pick(open.len())];
                let target = model.issues[i].target;
                let opened = model.issues[i].opened;
                // Only the assignment's target may dispose of the issue, so it
                // is the target's own checkout that has to have caught up with
                // the opening -- which is exactly why a real agent syncs
                // before answering work addressed to it.
                let target_host = model.agents[target].host;
                if !model.hosts[target_host].known.contains(&opened) {
                    emit(&mut ops, &mut model, Op::Sync { host: target_host });
                }
                emit(&mut ops, &mut model, Op::ResolveIssue { issue: i });
            }
        }
    }
    // Whatever is left joins at the very end: a checkout that never acts and
    // meets the bus for the first time at the final synchronization.
    while joined < joins.len() {
        emit(&mut ops, &mut model, Op::AddHost);
        joined += 1;
    }
    ops
}

// ------------------------------------------------------------- materializing

struct HostRepo {
    dir: TempDir,
    name: Short,
}

impl HostRepo {
    fn repo(&self) -> &Path {
        self.dir.path()
    }

    /// Exactly what `cli::resolve_paths` computes for a real invocation --
    /// deterministic, and shared by every call in this checkout. Using a fresh
    /// scratch directory per operation instead would quietly step around the
    /// worktree-cache staleness bug this harness exists to catch.
    fn common_dir(&self) -> PathBuf {
        self.dir.path().join(".git")
    }

    fn worktrees(&self) -> PathBuf {
        self.common_dir().join("agent-bus").join("wt-v2")
    }
}

/// One bare origin plus every checkout pointed at it.
struct Fleet {
    hosts: Vec<HostRepo>,
    origin: TempDir,
}

fn git(dir: &Path, args: &[&str]) {
    let status = std::process::Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .status()
        .expect("git must be on PATH");
    assert!(status.success(), "git {args:?} failed in {}", dir.display());
}

/// A `/`-separated path string: a `\`-separated Windows path is not what we
/// want embedded as a git remote.
fn path_str(p: &Path) -> String {
    p.to_string_lossy().replace('\\', "/")
}

/// The same bare-origin setup `sync.rs` and `tests/cli_flow.rs` already use.
fn init_bare_origin() -> TempDir {
    let dir = tempfile::tempdir().unwrap();
    git(dir.path(), &["init", "--quiet", "--bare", "-b", "main"]);
    dir
}

/// The same working-checkout setup `tests/cli_flow.rs` already uses: one
/// ordinary commit (so genesis's `product_review_from` resolves) and `origin`
/// pointed at the shared bare repository.
fn init_repo(origin: &Path) -> TempDir {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path();
    git(path, &["init", "--quiet", "-b", "main"]);
    git(path, &["config", "user.email", "test@example.com"]);
    git(path, &["config", "user.name", "Test"]);
    std::fs::write(path.join("README.md"), "hello\n").unwrap();
    git(path, &["add", "README.md"]);
    git(path, &["commit", "-q", "-m", "initial"]);
    git(path, &["remote", "add", "origin", &path_str(origin)]);
    dir
}

fn agent(name: &str) -> Agent {
    Agent::parse(name.to_string()).expect("pool names are valid agent names")
}

fn short(s: &str) -> Short {
    Short::parse(s.to_string()).expect("test short is in bounds")
}

fn text(s: &str) -> Text {
    Text::parse(s.to_string()).expect("test text is in bounds")
}

fn fail(context: &str, e: impl std::fmt::Display) -> TestCaseError {
    TestCaseError::fail(format!("{context}: {e}"))
}

/// Runs one operation against the real repositories, using the same library
/// calls `cli.rs` uses, in the same order. `model` is the state *before* the
/// operation, so expected sequence numbers can be asserted against what the
/// coordinator actually published.
fn materialize_op(
    fleet: &mut Fleet,
    model: &Model,
    op: &Op,
    step: usize,
) -> Result<(), TestCaseError> {
    match op {
        Op::AddHost => {
            let idx = fleet.hosts.len();
            fleet.hosts.push(HostRepo {
                dir: init_repo(fleet.origin.path()),
                name: short(&format!("host{idx}")),
            });
        }
        Op::Sync { host } => {
            let h = &fleet.hosts[*host];
            let snap =
                crate::sync::synced_snapshot(h.repo(), &h.common_dir(), "origin", &h.worktrees())
                    .map_err(|e| fail(&format!("sync on host{host}"), e))?;
            prop_assert_eq!(
                snap.freshness,
                crate::sync::Freshness::CurrentAsOfRemoteProbe
            );
            prop_assert!(
                snap.last_synced.is_some(),
                "a successful synchronization must record its own time"
            );
        }
        Op::Genesis { host, name } => {
            let h = &fleet.hosts[*host];
            let review_from = crate::gitrepo::rev_parse(h.repo(), "HEAD")
                .map_err(|e| fail("rev-parse HEAD for genesis", e))?;
            let (_config, epoch, stream_commit) = crate::bootstrap::genesis(
                h.repo(),
                name,
                short(&format!("{name} display")),
                text("proptest genesis coordinator"),
                "sha1".to_string(),
                ObjectId::parse(review_from).map_err(|e| fail("parse HEAD object id", e))?,
                h.name.clone(),
                &h.worktrees(),
            )
            .map_err(|e| fail("genesis", e))?;
            let updates = vec![
                RefUpdate::new(crate::registry::REGISTRY_REF, epoch.id.clone()),
                RefUpdate::new(crate::stream::stream_ref(name).into_string(), stream_commit),
            ];
            let receipt = crate::publish::publish(h.repo(), "origin", &updates)
                .map_err(|e| fail("publish genesis", e))?;
            prop_assert!(
                updates
                    .iter()
                    .all(|u| receipt.published.get(&u.refname) == Some(&u.new)),
                "genesis publication must land in full, got {:?}",
                receipt
            );
        }
        Op::Register { host, name, role } => {
            let h = &fleet.hosts[*host];
            let tip = crate::registry::read_registry_tip(h.repo())
                .map_err(|e| fail("read registry tip before register", e))?
                .ok_or_else(|| TestCaseError::fail("register needs a registry root"))?;
            let epoch =
                crate::registry::read_epoch(h.repo(), &tip, &h.worktrees().join("_register_epoch"))
                    .map_err(|e| fail("read epoch before register", e))?;
            let mut members = epoch.active_members.clone();
            members.insert(
                name.clone(),
                MemberBinding {
                    role: *role,
                    host: h.name.clone(),
                    coordinator_custody_epoch: 0,
                    standby: None,
                },
            );
            let new_epoch = crate::registry::propose_transition(
                h.repo(),
                &epoch,
                members,
                &h.worktrees().join("_register_transition"),
            )
            .map_err(|e| fail("propose registration transition", e))?;

            let candidate = Candidate::new(
                name,
                &EventData::AgentRegistered(AgentRegistered {
                    display_name: short(&format!("{name} display")),
                    primary_role: *role,
                    purpose: text("proptest agent"),
                    product_base: None,
                    product_branch: None,
                    provider: None,
                    model: None,
                }),
                vec![],
            );
            drain_one(fleet, *host, name, &candidate, 0, step, "register")?;

            let h = &fleet.hosts[*host];
            let new_tip = crate::stream::read_stream_tip(h.repo(), name)
                .map_err(|e| fail("read new stream tip", e))?
                .ok_or_else(|| TestCaseError::fail("a just-drained agent must have a stream"))?;
            let updates = vec![
                RefUpdate::new(crate::registry::REGISTRY_REF, new_epoch.id.clone()),
                RefUpdate::new(crate::stream::stream_ref(name).into_string(), new_tip),
            ];
            let receipt = crate::publish::publish(h.repo(), "origin", &updates)
                .map_err(|e| fail("publish registration", e))?;
            prop_assert!(
                updates
                    .iter()
                    .all(|u| receipt.published.get(&u.refname) == Some(&u.new)),
                "registration publication must land in full, got {:?}",
                receipt
            );
        }
        Op::Status { agent: a, status } => {
            let name = model.agents[*a].name.clone();
            let host = model.agents[*a].host;
            let candidate = Candidate::new(
                &name,
                &EventData::AgentStatus(AgentStatusEvent {
                    status: *status,
                    note: text("proptest status"),
                    product_branch: None,
                    product_commit: None,
                }),
                vec![],
            );
            drain_one(
                fleet,
                host,
                &name,
                &candidate,
                model.next_seq(*a),
                step,
                "status",
            )?;
        }
        Op::OpenIssue { opener, target } => {
            let name = model.agents[*opener].name.clone();
            let host = model.agents[*opener].host;
            let target_name = model.agents[*target].name.clone();
            // The target's own registration, cited as evidence: `IssueOpened::
            // referenced_ids()` covers `blocks`/`evidence` but not `target`,
            // and `Envelope::parse_line` insists `refs` equal exactly what the
            // data references -- so this is the only way to carry a real
            // cross-agent causal edge to the target here.
            let target_reg = EventId::new(&target_name, 0);
            let candidate = Candidate::new(
                &name,
                &EventData::IssueOpened(IssueOpened {
                    target: target_name,
                    issue_kind: IssueKind::Bug,
                    severity: Priority::Normal,
                    summary: text("proptest issue"),
                    code_commit: None,
                    locations: vec![],
                    expected: None,
                    observed_behavior: None,
                    reproduction: vec![],
                    blocks: StringSet::default(),
                    evidence: StringSet::from_iter([target_reg.clone()]),
                }),
                vec![target_reg],
            );
            drain_one(
                fleet,
                host,
                &name,
                &candidate,
                model.next_seq(*opener),
                step,
                "issue.opened",
            )?;
        }
        Op::ResolveIssue { issue } => {
            let issue = &model.issues[*issue];
            let name = model.agents[issue.target].name.clone();
            let host = model.agents[issue.target].host;
            let candidate = Candidate::new(
                &name,
                &EventData::IssueResolved(IssueResolved {
                    issue: issue.id.clone(),
                    assignment: issue.id.clone(),
                    summary: text("proptest resolution"),
                    fix_commit: None,
                    verification: vec![],
                }),
                vec![issue.id.clone()],
            );
            drain_one(
                fleet,
                host,
                &name,
                &candidate,
                model.next_seq(issue.target),
                step,
                "issue.resolved",
            )?;
        }
    }
    Ok(())
}

/// Submits exactly one candidate and drains it, asserting the coordinator
/// accepted it at the sequence the oracle predicted.
///
/// One candidate per drain on purpose: `outbox::list_pending` breaks ties by
/// filesystem modified time, whose resolution is coarse enough that two
/// candidates submitted in the same instant would have an unspecified relative
/// order -- nondeterminism this harness would rather not import.
///
/// A rejection here is itself an invariant violation: the plan only ever emits
/// operations whose preconditions the model says hold on this very checkout,
/// so `drain_outbox` refusing one means either a real defect or a divergence
/// between the model and the implementation. Both deserve a failure.
fn drain_one(
    fleet: &Fleet,
    host: usize,
    name: &Agent,
    candidate: &Candidate,
    expected_seq: u64,
    step: usize,
    what: &str,
) -> Result<(), TestCaseError> {
    let h = &fleet.hosts[host];
    let client_id = format!("proptest-{step}");
    crate::outbox::submit(&h.common_dir(), &client_id, candidate)
        .map_err(|e| fail(&format!("submit {what}"), e))?;
    let (drained, receipt) = crate::coordinator::drain_and_publish(
        h.repo(),
        &h.common_dir(),
        name,
        &h.name,
        0,
        &h.worktrees(),
        "origin",
    )
    .map_err(|e| fail(&format!("drain_and_publish {what}"), e))?;
    prop_assert!(
        drained.rejected.is_empty(),
        "step {step}: {what} for {name} on host{host} was rejected, but the plan only emits \
         candidates whose preconditions hold on this very checkout: {:?}",
        drained.rejected
    );
    prop_assert_eq!(
        drained.published,
        vec![EventId::new(name, expected_seq)],
        "step {}: {} for {} must publish exactly the sequence the oracle predicted",
        step,
        what,
        name
    );
    prop_assert!(
        receipt
            .published
            .contains_key(crate::stream::stream_ref(name).as_str()),
        "step {step}: {what} for {name} did not reach origin: {:?}",
        receipt
    );
    Ok(())
}

// -------------------------------------------------------------- the checking

/// Every ref in `dir`, by name.
fn refs_of(dir: &Path) -> Result<Vec<String>, TestCaseError> {
    let out = crate::gitrepo::run_ok(dir, &["for-each-ref", "--format=%(refname)"])
        .map_err(|e| fail("for-each-ref", e))?;
    Ok(out.lines().map(|l| l.trim().to_string()).collect())
}

/// Bug 2's direct, cheap check, run against every repository after every
/// operation: a ref written by handing a fully-qualified name to a command
/// that wanted a short one lands as `refs/heads/refs/heads/...`, and
/// `rev-parse`'s disambiguation fallback hides that in a purely local round
/// trip. Nothing hides it from `for-each-ref`.
fn check_no_malformed_refs(label: &str, dir: &Path) -> Result<(), TestCaseError> {
    for name in refs_of(dir)? {
        prop_assert!(
            name.starts_with("refs/"),
            "{label}: ref {name:?} is not under refs/"
        );
        let rest = name
            .strip_prefix("refs/heads/")
            .or_else(|| name.strip_prefix("refs/tags/"))
            .or_else(|| name.strip_prefix("refs/remotes/"))
            .unwrap_or_else(|| name.strip_prefix("refs/").expect("checked above"));
        prop_assert!(
            !rest.contains("refs/"),
            "{label}: malformed, double-prefixed ref {name:?} -- a fully-qualified name was \
             handed to something that wanted a short one"
        );
    }
    Ok(())
}

/// The invariant sweep. `hosts` names which checkouts to examine.
///
/// Every checkout lives in its own repository and only ever mutates its own,
/// so a checkout that did not act cannot have changed since it was last
/// examined -- sweeping only the acting checkout after each operation costs a
/// fraction of a full sweep and misses nothing. [`run_world`] still sweeps
/// everything once the schedule is complete, and again after the final
/// fleet-wide synchronization.
fn check_hosts(
    fleet: &Fleet,
    model: &Model,
    at: &str,
    hosts: &[usize],
    depth: Depth,
) -> Result<(), TestCaseError> {
    check_no_malformed_refs("origin", fleet.origin.path())?;
    for &i in hosts {
        let h = &fleet.hosts[i];
        let label = format!("{at}, host{i}");
        check_no_malformed_refs(&label, h.repo())?;

        let expected = model.expected(i);
        // The ref-name half of the sweep, which is where bug 2 shows: cheap
        // enough to run after literally every operation.
        let actual_refs: BTreeSet<String> = refs_of(h.repo())?
            .into_iter()
            .filter(|r| r.starts_with(crate::stream::STREAM_REF_PREFIX))
            .collect();
        prop_assert_eq!(
            &actual_refs,
            &model.expected_stream_refs(i),
            "{}: stream refs present locally, by exact name",
            label
        );
        if depth == Depth::RefsOnly {
            continue;
        }

        let tip = crate::registry::read_registry_tip(h.repo())
            .map_err(|e| fail(&format!("{label}: read_registry_tip"), e))?;
        prop_assert_eq!(
            tip.is_some(),
            expected.is_some(),
            "{}: local registry presence disagrees with the model",
            label
        );

        let snapshot = crate::sync::cached_snapshot(h.repo(), &h.common_dir(), &h.worktrees());
        let Some(expected) = expected else {
            // A checkout that has never synchronized and never hosted a
            // registry transition genuinely has nothing to reduce; that, and
            // only that, may fail.
            prop_assert!(
                snapshot.is_err(),
                "{}: a checkout with no registry must not produce a snapshot",
                label
            );
            continue;
        };
        // Anything this checkout *can* read, it must read without error --
        // a spurious failure here is exactly bug 1's and bug 2's signature.
        let snapshot = snapshot.map_err(|e| fail(&format!("{label}: cached_snapshot"), e))?;
        prop_assert_eq!(snapshot.freshness, crate::sync::Freshness::Cached);
        prop_assert_eq!(
            snapshot.last_synced.is_some(),
            model.hosts[i].ever_synced,
            "{}: a last successful synchronization time must be reported exactly when one \
             has actually happened here, and never fabricated",
            label
        );

        let actual_members: BTreeSet<String> = snapshot
            .roster_epoch
            .active_members
            .keys()
            .map(|a| a.as_str().to_string())
            .collect();
        prop_assert_eq!(
            &actual_members,
            &expected.members,
            "{}: local roster epoch membership",
            label
        );

        let actual_agents: BTreeMap<String, ExpectedAgent> = snapshot
            .state
            .agents
            .iter()
            .map(|(a, s)| {
                (
                    a.as_str().to_string(),
                    ExpectedAgent {
                        next_seq: s.next_seq,
                        role: s.primary_role,
                        status: s.status,
                    },
                )
            })
            .collect();
        prop_assert_eq!(
            &actual_agents,
            &expected.agents,
            "{}: reduced agents and their stream positions",
            label
        );

        let actual_issues: BTreeMap<String, ExpectedIssue> = snapshot
            .state
            .issues
            .iter()
            .map(|(id, s)| {
                (
                    id.as_str().to_string(),
                    ExpectedIssue {
                        opener: s.opener.as_str().to_string(),
                        target: s.current_target.as_str().to_string(),
                        status: match s.status {
                            ItemStatus::Terminal(l) => l,
                            ItemStatus::Open => "open",
                            ItemStatus::LifecycleConflict => "conflict",
                        },
                    },
                )
            })
            .collect();
        prop_assert_eq!(
            &actual_issues,
            &expected.issues,
            "{}: reduced issues and their dispositions",
            label
        );

        for name in expected.agents.keys() {
            let a = agent(name);
            prop_assert!(
                crate::stream::read_stream_tip(h.repo(), &a)
                    .map_err(|e| fail(&format!("{label}: read_stream_tip {a}"), e))?
                    .is_some(),
                "{label}: {a} reduced but has no readable stream tip"
            );
            prop_assert!(
                snapshot.stream_tips.contains_key(&a),
                "{label}: {a} reduced but absent from the snapshot receipt"
            );
        }
    }
    Ok(())
}

/// How much of the sweep to run. A full reduction is by far the most expensive
/// thing this harness does -- it is what `coordinator::drain_outbox` itself
/// pays on every publication -- so it is spent where it buys something: at the
/// end of the schedule, when each checkout is sitting at whatever stale or
/// current view the schedule actually left it at.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Depth {
    /// Ref names and their exact spelling only.
    RefsOnly,
    /// Ref names, plus a full reduction compared against the oracle.
    Full,
}

fn check_all(fleet: &Fleet, model: &Model, at: &str) -> Result<(), TestCaseError> {
    let all: Vec<usize> = (0..fleet.hosts.len()).collect();
    check_hosts(fleet, model, at, &all, Depth::Full)
}

/// Which checkout's repository an operation actually writes to -- the only one
/// whose invariants can have changed as a result. `model` is the state
/// *before* the operation.
fn touched_host(model: &Model, op: &Op) -> usize {
    match op {
        Op::AddHost => model.hosts.len(),
        Op::Sync { host } | Op::Genesis { host, .. } | Op::Register { host, .. } => *host,
        Op::Status { agent, .. } => model.agents[*agent].host,
        Op::OpenIssue { opener, .. } => model.agents[*opener].host,
        Op::ResolveIssue { issue } => model.agents[model.issues[*issue].target].host,
    }
}

/// The convergence invariant (gate 16), checked once the whole schedule has
/// run: bring every checkout to the same point and assert they agree
/// *exactly*, using the same `Debug`-equality convention `apply.rs`'s
/// `cold_replay_and_incremental_replay_produce_identical_state` established.
///
/// Every checkout reaches this point differently -- one authored much of the
/// history locally and never fetched it back, one has been fetching all along,
/// one may have been created cold moments ago and has replayed everything from
/// scratch in a single pass. Byte-identical reduced state across all of them is
/// the property that makes the bus's "reduce anywhere" claim mean anything.
fn check_convergence(fleet: &Fleet, model: &mut Model) -> Result<(), TestCaseError> {
    let mut reference: Option<(usize, String)> = None;
    for i in 0..fleet.hosts.len() {
        let h = &fleet.hosts[i];
        let snap =
            crate::sync::synced_snapshot(h.repo(), &h.common_dir(), "origin", &h.worktrees())
                .map_err(|e| fail(&format!("final sync on host{i}"), e))?;
        model.apply(&Op::Sync { host: i });
        let rendered = format!("{:?}", snap.state);
        match &reference {
            None => reference = Some((i, rendered)),
            Some((j, expected)) => prop_assert_eq!(
                &rendered,
                expected,
                "host{} and host{} both synchronized to the same point but reduced to different \
                 state",
                i,
                j
            ),
        }
    }
    // ...and that common state is the one the oracle predicts, so "they all
    // agree" cannot be satisfied by all of them being wrong together. One full
    // reduction is enough to pin it: the pairwise equality above already
    // proves every other checkout reduced to exactly the same thing.
    check_hosts(
        fleet,
        model,
        "after the final fleet-wide synchronization",
        &[0],
        Depth::Full,
    )
}

/// One generated scenario, end to end: plan it, lay it down, and check it.
///
/// Setting `AGENT_BUS_PROPTEST_TRACE` prints each operation with how long its
/// materialization and its check took. That is a tuning aid rather than a
/// debugging one -- the cost here is dominated by real `git` process spawning,
/// and the trace is what showed which operations are worth their place in a
/// schedule short enough to run routinely.
fn run_world(world: &World) -> Result<(), TestCaseError> {
    let ops = plan(world);
    let origin = init_bare_origin();
    let mut fleet = Fleet {
        hosts: Vec::new(),
        origin,
    };
    let mut model = Model::default();
    let trace = std::env::var_os("AGENT_BUS_PROPTEST_TRACE").is_some();
    for (step, op) in ops.iter().enumerate() {
        let touched = touched_host(&model, op);
        let t0 = std::time::Instant::now();
        materialize_op(&mut fleet, &model, op, step)?;
        let t1 = std::time::Instant::now();
        model.apply(op);
        check_hosts(
            &fleet,
            &model,
            &format!("step {step} ({op:?})"),
            &[touched],
            Depth::RefsOnly,
        )?;
        if trace {
            eprintln!(
                "  step {step}: {:?} run={:?} check={:?}",
                op,
                t1 - t0,
                t1.elapsed()
            );
        }
    }
    let t = std::time::Instant::now();
    check_all(&fleet, &model, "after the whole schedule")?;
    let t2 = std::time::Instant::now();
    check_convergence(&fleet, &mut model)?;
    if trace {
        eprintln!(
            "  final sweep={:?} convergence={:?} ({} ops, {} hosts)",
            t2 - t,
            t2.elapsed(),
            ops.len(),
            fleet.hosts.len()
        );
    }
    Ok(())
}

// ------------------------------------------------------------------- the test

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

/// Far more modest than a property test would ordinarily want, and honestly so.
///
/// A single operation here is on the order of a hundred `git` subprocesses --
/// `coordinator::drain_outbox` alone reduces the whole bus before it will
/// publish anything, and each stream in that reduction is a real worktree
/// checkout. Measured on the machine this was written on, a generated schedule
/// costs on the order of fifteen seconds, so the conventional "a few hundred
/// cases" would be a run of hours rather than a test. The defaults below cost
/// about a minute in total, which is what an ordinary `cargo test` can absorb
/// without anyone starting to avoid running it.
///
/// The consequence is worth stating plainly: at four cases this explores far
/// less per run than a property test normally would, and leans on being run
/// repeatedly -- each run draws a fresh seed -- rather than on breadth within
/// any one run. `AGENT_BUS_PROPTEST_CASES` and `AGENT_BUS_PROPTEST_STEPS` raise
/// both for a deliberate longer hunt, which is where real breadth comes from.
fn config() -> ProptestConfig {
    ProptestConfig {
        cases: env_usize("AGENT_BUS_PROPTEST_CASES", 4) as u32,
        // Every shrink iteration re-runs a whole schedule against fresh
        // repositories -- tens of seconds each, not microseconds -- so an
        // unbounded shrink on a real failure would run far longer than the
        // search that found it. A `World` this small has a correspondingly
        // small shrink space (drop a step, halve a `Sel`), so this cap is
        // generous for it while still bounding the worst case.
        max_shrink_iters: 32,
        ..ProptestConfig::default()
    }
}

proptest! {
    #![proptest_config(config())]

    /// Generate a fleet's whole life, lay it down across real checkouts of one
    /// shared origin, and check every read against a pure-Rust oracle after
    /// every single operation.
    #[test]
    fn a_multi_checkout_fleet_upholds_its_invariants_under_any_schedule(
        world in world_strategy(env_usize("AGENT_BUS_PROPTEST_STEPS", 4))
    ) {
        run_world(&world)?;
    }
}

mod planning_tests {
    use super::*;

    /// A `World` with no extra checkouts, for tests that only care about the
    /// step handling.
    fn solo(steps: Vec<Step>) -> World {
        World {
            genesis_name: Sel(0),
            joins: vec![],
            steps,
        }
    }

    /// A `World` whose second checkout exists from the very start.
    fn pair(steps: Vec<Step>) -> World {
        World {
            genesis_name: Sel(0),
            joins: vec![Sel(0)],
            steps,
        }
    }

    fn register_on(host: u8) -> Step {
        Step::Register {
            host: Sel(host),
            name: Sel(0),
            coordinator: false,
        }
    }

    /// The planner is what decides what the implementation is even asked to
    /// do, so it gets direct tests of its own: a defect here would silently
    /// narrow the explored space rather than fail anything.
    #[test]
    fn every_plan_starts_by_creating_a_checkout_and_activating_the_bus() {
        let ops = plan(&solo(vec![]));
        assert!(matches!(ops[0], Op::AddHost), "{ops:?}");
        assert!(matches!(ops[1], Op::Genesis { host: 0, .. }), "{ops:?}");
    }

    /// A join position past the last step still produces a checkout -- the
    /// cold one that only ever reads, which is the configuration all three
    /// motivating bugs hid in.
    #[test]
    fn a_checkout_joining_past_the_end_of_the_schedule_is_still_created() {
        let world = World {
            genesis_name: Sel(0),
            joins: vec![Sel(255)],
            steps: vec![Step::Status {
                agent: Sel(0),
                blocked: false,
            }],
        };
        let ops = plan(&world);
        assert_eq!(
            ops.iter().filter(|o| matches!(o, Op::AddHost)).count(),
            2,
            "{ops:?}"
        );
        assert!(matches!(ops.last(), Some(Op::AddHost)), "{ops:?}");
    }

    /// A registration is never planned from a checkout whose registry is
    /// behind origin -- the property that keeps the registry chain linear.
    #[test]
    fn a_registration_is_always_preceded_by_synchronization_when_the_host_is_behind() {
        let ops = plan(&pair(vec![register_on(1)]));
        let at = ops
            .iter()
            .position(|o| matches!(o, Op::Register { .. }))
            .expect("the registration must survive planning");
        assert!(
            matches!(ops[at - 1], Op::Sync { host: 1 }),
            "a behind checkout must be synchronized first: {ops:?}"
        );
    }

    /// ...and is *not* preceded by one when that checkout is already current,
    /// so the harness does not quietly synchronize everything all the time.
    #[test]
    fn a_registration_from_an_already_current_checkout_needs_no_synchronization() {
        let ops = plan(&solo(vec![register_on(0)]));
        assert!(!ops.iter().any(|o| matches!(o, Op::Sync { .. })), "{ops:?}");
    }

    /// An issue can only be opened against an agent the opener's own checkout
    /// has already seen, so the planner catches that one checkout up first --
    /// and leaves every other checkout exactly as stale as it was.
    #[test]
    fn an_issue_against_an_unseen_agent_synchronizes_only_the_openers_checkout() {
        let world = World {
            genesis_name: Sel(0),
            // Three checkouts: 0 activates the bus, 1 registers an agent, 2
            // never acts at all.
            joins: vec![Sel(0), Sel(0)],
            steps: vec![
                register_on(1),
                // host0's coordinator has not synchronized since, so it cannot
                // yet see the agent host1 just registered.
                Step::OpenIssue {
                    opener: Sel(0),
                    target: Sel(1),
                },
            ],
        };
        let ops = plan(&world);
        let at = ops
            .iter()
            .position(|o| matches!(o, Op::OpenIssue { .. }))
            .expect("the issue must survive planning");
        assert!(
            matches!(ops[at - 1], Op::Sync { host: 0 }),
            "the opener's checkout must be caught up first: {ops:?}"
        );
        assert!(
            !ops.iter().any(|o| matches!(o, Op::Sync { host: 2 })),
            "the uninvolved checkout must be left stale: {ops:?}"
        );
    }

    /// An issue whose target is its own opener would make every reference
    /// same-agent, which is exactly the causality this step exists to
    /// exercise; the planner nudges the target rather than discarding it.
    #[test]
    fn an_issue_never_targets_its_own_opener() {
        let world = solo(vec![
            register_on(0),
            Step::OpenIssue {
                opener: Sel(0),
                target: Sel(0),
            },
        ]);
        let ops = plan(&world);
        let Some(Op::OpenIssue { opener, target }) = ops
            .iter()
            .find(|o| matches!(o, Op::OpenIssue { .. }))
            .cloned()
        else {
            panic!("the issue must survive planning: {ops:?}");
        };
        assert_ne!(opener, target, "{ops:?}");
    }

    /// The oracle's per-checkout view must actually differ between a stale and
    /// a current checkout -- if it did not, the harness would be checking a
    /// property that cannot tell staleness from correctness.
    #[test]
    fn the_oracle_distinguishes_a_stale_checkout_from_a_current_one() {
        let ops = plan(&pair(vec![register_on(1)]));
        let mut model = Model::default();
        for op in &ops {
            model.apply(op);
        }
        let stale = model.expected(0).expect("host0 activated the bus");
        let fresh = model.expected(1).expect("host1 registered an agent");
        assert_eq!(stale.agents.len(), 1, "{stale:?}");
        assert_eq!(fresh.agents.len(), 2, "{fresh:?}");
        assert_ne!(stale, fresh);
    }

    /// A checkout that has never synchronized has no local registry at all,
    /// which the oracle reports as "nothing to reduce" rather than as an empty
    /// reduction -- the one case in which a failing read is the right answer.
    #[test]
    fn the_oracle_expects_no_snapshot_at_all_from_a_checkout_that_never_synchronized() {
        let ops = plan(&pair(vec![]));
        let mut model = Model::default();
        for op in &ops {
            model.apply(op);
        }
        assert!(model.expected(0).is_some());
        assert!(model.expected(1).is_none());
    }
}

/// One fixed schedule, run deterministically: activate the bus, publish twice
/// from the same checkout for the same agent, and let a second checkout join
/// cold and read the result.
///
/// This is the smallest world that both bug 1 and bug 2 fall to, and it is
/// pinned here rather than left to the generator so this class stays guarded
/// no matter what a given run happens to draw -- a property test's coverage of
/// any *particular* shape is a matter of chance, and this shape is too
/// load-bearing to leave to chance.
///
/// It is also what validated the harness. Against `ensure_bus_worktree` with
/// its staleness check removed, this fails with `left: [EventId("carol:1")],
/// right: [EventId("carol:2")]` -- the second publication silently reusing the
/// first one's sequence number, because the reused worktree cache still held
/// the stream as it was before the first append. Against `create_root_commit`
/// reverted to `git branch -f`, it fails at the genesis operation on the
/// double-prefixed ref. Against the code as it stands, it passes.
#[test]
fn the_smallest_schedule_that_a_stale_cache_or_a_double_prefixed_ref_falls_to() {
    let world = World {
        genesis_name: Sel(0),
        joins: vec![Sel(255)],
        steps: vec![
            Step::Status {
                agent: Sel(0),
                blocked: false,
            },
            Step::Status {
                agent: Sel(0),
                blocked: true,
            },
        ],
    };
    run_world(&world).expect("the fixed schedule must hold");
}
