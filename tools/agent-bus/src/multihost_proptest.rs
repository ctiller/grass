//! Property-based invariant tests across *several independently fetching
//! checkouts of one shared origin* -- the real deployment shape AGENT_BUS.md
//! section 2 describes, and the one every other test in this crate silently
//! collapses away.
//!
//! # The property
//!
//! **No action an agent can invoke, in any combination or order, can wedge
//! the bus.** That is one sentence with two independent halves, and an
//! oracle that checks only the first will bless a fix that breaks the
//! second:
//!
//!  1. **Totality.** `apply::reduce` must never answer `Err` for an event
//!     that was legitimately published. It has no per-event isolation
//!     (`reduce`'s bare `?`), the log is append-only, and force-push is
//!     prohibited -- so one such `Err` is `status`, `tail` and `coordinate`
//!     down for every host, permanently, with no way back.
//!  2. **Confluence.** Hosts that received the same event set in different
//!     orders must reduce to the *same* state (gates 15/16). A handler that
//!     stops erroring but still depends on arrival order has traded a wedged
//!     bus for silent permanent divergence, which is worse, because nothing
//!     surfaces it.
//!
//! # Which layer is allowed to say no
//!
//! The boundary is the whole design of this crate, and the harness is built
//! around it:
//!
//!  - `coordinator::drain_outbox` and its `verify_*` gates MAY refuse a
//!    candidate. That is correct and expected: a rejection is per-candidate,
//!    writes a durable receipt, and costs one author a retry. So this
//!    harness *submits* freely and treats a rejection as an ordinary
//!    outcome, never as a counterexample. An event the coordinator refused
//!    is simply not in the log.
//!  - `apply::reduce` MUST NOT. Anything that actually landed in a stream is
//!    held to both properties above, on every checkout, in every valid
//!    order.
//!
//! Every generated action therefore goes through the real publication path
//! -- `outbox::submit` then `coordinator::drain_outbox` -- rather than being
//! written into a stream directly. The oracle only ever asserts about what
//! that path accepted.
//!
//! # Why the alphabet aims at completeness
//!
//! This module's generator used to construct six of the schema's event
//! kinds, and the reason was always the same one: the author's guess about
//! where bugs live. The alphabet was last extended to cover *issues*, after
//! two fleet-wide reduction outages landed in exactly the shape it could not
//! express. Reviews, agent lifecycle, schema and engine activation were left
//! out because nobody suspected them -- and a later cold audit of every
//! error site in `apply.rs` found *nine* distinct totality/confluence
//! defects, every one of them in that blind spot, each capable of making the
//! bus permanently unreadable. No amount of proptest budget would have found
//! any of them.
//!
//! So the target is not a curated list of interesting operations. `cli.rs`
//! exposes `submit --kind <k> --data <json>`, which builds a candidate for
//! *any* kind, so the agent-invocable surface is effectively the whole
//! schema. [`GENERATED_KINDS`] is what this generator builds payloads for,
//! [`UNGENERATED_KINDS`] names what it cannot yet reach *and why*, and
//! [`every_event_kind_is_either_generated_or_explicitly_excused`] fails the
//! build if those two do not together account for every variant of
//! `EventData`. When kind 43 is added next month, this test fails until
//! someone decides which list it belongs in. That guard is the part that
//! stops the blind spot from silently reopening.
//!
//! # Generate / materialize / check
//!
//! Three stages, and only one of them touches git:
//!
//!  - [`World`] and [`Step`] are what `proptest` generates and, crucially,
//!    *shrinks*. Every reference is a [`Sel`], which is total: it selects
//!    into whatever collection exists at that point, so no shrink can ever
//!    produce a structurally invalid `World`.
//!  - [`drive`] resolves that `World` step by step against the pure
//!    [`Model`], building a fully concrete [`Op`], handing it to an
//!    [`Exec`], and folding the *observed* outcome back into the model.
//!    Resolution is interleaved with execution rather than planned up front
//!    precisely because a candidate may be rejected: the model must learn
//!    what actually landed before it resolves the next step, or every later
//!    sequence-number prediction is wrong.
//!  - [`GitExec`] is the only code here that runs git. It performs the same
//!    library calls `cli.rs` performs, in the same order, against one bare
//!    origin and one working checkout per host. [`DryExec`] is the same loop
//!    with the executor stubbed out, which is what [`plan`] uses so the
//!    planner can be unit-tested without repositories.
//!
//! # How races are actually reached
//!
//! Every one of the nine defects needed *two agents acting on one subject
//! without having observed each other*. Two mechanisms produce that here,
//! and both are ordinary fleet behaviour rather than contrivance:
//!
//!  - **A stale checkout.** Most kinds are validated against
//!    `sync::cached_snapshot`, so a checkout that has not fetched genuinely
//!    does not see what another host just published.
//!  - **A deferred publication.** [`Op::Act`]'s `defer` drains a candidate
//!    into the local stream without pushing it to origin yet, which is the
//!    real window between a coordinator committing and the push landing. It
//!    is the only way to race the *currency-sensitive* kinds (gate 17:
//!    reassignment, schema/engine activation, audit), whose own drain
//!    fetches first and would otherwise always observe the other side. A
//!    checkout holding unpushed commits cannot fetch its own stream ref back
//!    without a non-fast-forward rejection, so [`Model`] tracks that and the
//!    driver flushes before anything that must synchronize.
//!
//! A third, cheaper mechanism covers order-independence directly:
//! [`check_reduction_is_total_and_confluent`] reads the whole published log
//! back and re-reduces it under several *randomly chosen linear extensions
//! of the causal partial order* -- the orders different hosts genuinely
//! reach after fetching in different sequences -- and requires every one of
//! them to succeed and to agree byte for byte. That check needs no git at
//! all, so it is cheap enough to run on every case, and it is what makes the
//! confluence half of the property real rather than aspirational.
//!
//! # Evidence that it looks where it claims to
//!
//! A property test that has never failed is indistinguishable from one that
//! cannot fail, so this harness is validated by reintroducing real defects
//! and confirming it catches each:
//!
//!  - Bug 2, with `stream::create_root_commit`'s `update-ref` reverted to
//!    `git branch -f`: caught on the *first* generated schedule, at the
//!    genesis operation -- "malformed, double-prefixed ref
//!    `refs/heads/refs/heads/agent-events/carol`".
//!  - Bug 1, with `gitrepo::ensure_bus_worktree`'s "verify before trusting"
//!    staleness check removed: caught as a *duplicated stream sequence
//!    number*.
//!  - The seven reduction-totality defects fixed in "seven more ways
//!    reduction could wedge the bus permanently": run against that commit's
//!    parent, this harness fails. See
//!    [`the_smallest_schedule_that_reaches_the_review_reassignment_race`],
//!    which pins the smallest such schedule deterministically.
//!
//! Bugs 1 and 2 are pinned by
//! [`the_smallest_schedule_that_a_stale_cache_or_a_double_prefixed_ref_falls_to`],
//! so those classes stay guarded regardless of what any given run draws.
//!
//! Bug 3 (`apply::topological_order`'s tie-break placing an event merely
//! *naming* another agent before that agent's own registration) is not
//! reproducible by simple reversion: the fix changed a tie-break, and
//! whether the old one misorders anything depends on agent-name ordering.
//! [`AGENT_NAMES`] is arranged for that reason -- deliberately not in
//! lexicographic order, and which name each agent takes is generated, so
//! registration order and name order are uncorrelated across runs.
//!
//! # What is deliberately not modelled
//!
//! The *oracle* predicts reduced content only for the state it can model
//! exactly: roster membership, every agent's stream position and role, and
//! issues opened through the modelled operations. An event kind that can
//! move an agent's lifecycle status or an issue's disposition in a way the
//! model does not replicate marks that particular agent or issue
//! *unpredicted* rather than being excluded from the alphabet -- see
//! [`ExpectedAgent::status`]. Totality and confluence are checked
//! kind-agnostically and so cover everything.
//!
//! Registry transitions are always performed from a checkout that has just
//! synchronized, so the registry chain stays linear -- a genuinely forked
//! registry is a different (and separately interesting) failure class whose
//! expected behaviour is not modelled here.

use crate::common::{
    AckRequirement, AudienceSelector, Finding, FindingRef, FrictionDispositionKind, Impact,
    Importance, Measurement, PlanStep, PlanStepState, Priority,
};
use crate::events::{
    AgentRegistered, AgentResumed, AgentRetired, AgentStatusEvent, AuditReported,
    BroadcastAcknowledged, BroadcastPublished, BroadcastSeen, DependencyAcknowledged,
    DependencyReassigned, DependencyRejected, DependencyRequested, DependencyResolved, EventData,
    FrictionReported, FrictionSynthesized, HandoffAccepted, HandoffDeclined, HandoffOffered,
    HandoffWithdrawn, IssueAcknowledged, IssueKind, IssueOpened, IssueReassigned, IssueRejected,
    IssueResolved, LifecycleConflictResolved, LifecycleStatus, MergeEngineActivated, PlanSet,
    ProgressReported, ReviewChangesRequested, ReviewFindingsCleared, ReviewFindingsSuperseded,
    ReviewNominationAccepted, ReviewNominationDeclined, ReviewReassigned, ReviewRequest,
    ReviewWithdrawn, Role, SchemaActivated, ScopeSet, SubscriptionSet,
};
use crate::outbox::Candidate;
use crate::publish::RefUpdate;
use crate::registry::MemberBinding;
use crate::scalars::{
    Agent, Branch, CoordinationTopic, EventId, ObjectId, PathClaim, Short, StringSet, Text,
};
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
///
/// Seven rather than four because the review protocol needs two authors, two
/// reviewers to reassign between, and a coordinator, all distinct, before the
/// reassignment race is expressible at all -- plus an auditor, and one more
/// identity that can be retired without taking any of those out of play.
const AGENT_NAMES: [&str; 7] = ["carol", "alice", "dave", "bob", "frank", "erin", "grace"];

/// Every additional checkout costs a real `git fetch` and a full
/// re-reduction on the convergence sweep, so the fleet is capped rather than
/// left to the generator. Three checkouts is already enough for the shape
/// that matters: one that authored history, one that is behind it, and one
/// that joined cold.
const MAX_HOSTS: usize = 3;

// -------------------------------------------------------- the kind coverage

/// Every event kind this module's generator builds a payload for.
///
/// Six of them are reached through the dedicated, precisely-modelled
/// operations ([`Step::Register`] and friends) whose outcomes the content
/// oracle predicts exactly; the rest are reached through the generic
/// [`Step::Act`], which submits a generated payload and lets the
/// coordinator's own gates decide whether it publishes.
///
/// This list is the generator's own dispatch table -- [`build_act`] matches
/// on exactly these strings -- so it cannot drift from what is really
/// produced without failing to compile or failing
/// [`every_generated_kind_is_constructible`].
const GENERATED_KINDS: &[&str] = &[
    // reached through the precisely-modelled operations
    "agent.registered",
    "agent.status",
    "issue.opened",
    "issue.acknowledged",
    "issue.resolved",
    "issue.reassigned",
    // reached through the generic submit path
    "agent.resumed",
    "agent.retired",
    "schema.activated",
    "merge_engine.activated",
    "scope.set",
    "plan.set",
    "progress.reported",
    "issue.rejected",
    "dependency.requested",
    "dependency.acknowledged",
    "dependency.resolved",
    "dependency.rejected",
    "dependency.reassigned",
    "handoff.offered",
    "handoff.accepted",
    "handoff.declined",
    "handoff.withdrawn",
    "review.nominated",
    "review.nomination_accepted",
    "review.nomination_declined",
    "review.changes_requested",
    "review.findings_cleared",
    "review.findings_superseded",
    "review.reassigned",
    "review.withdrawn",
    "lifecycle.conflict_resolved",
    "friction.reported",
    "friction.synthesized",
    "subscription.set",
    "broadcast.published",
    "broadcast.acknowledged",
    "broadcast.seen",
    "audit.reported",
];

/// The kinds this generator cannot yet produce, each with the reason.
///
/// Listed out loud rather than silently skipped, because a named gap is
/// something the next person can close one at a time, while silent coverage
/// of a subset is exactly how the previous blind spot lasted months. Adding
/// an entry here is a deliberate act with a reason attached; forgetting to
/// add one fails
/// [`every_event_kind_is_either_generated_or_explicitly_excused`].
const UNGENERATED_KINDS: &[(&str, &str)] = &[
    (
        "review.merge_authorized",
        "coordinator::verify_review_merge_authorized re-derives the candidate from real product \
         history: it needs commits carrying Agent-Bus-Agent trailers, a deterministic merge \
         reconstruction performed by the *pinned* git/ORT version, and a candidate tag already \
         fetchable from the remote. The crate's own CLI tests skip themselves when the pinned \
         engine is absent (tests/cli_flow.rs `requires_the_pinned_engine`), so generating this \
         kind would make the property test's own coverage depend on the host's git build. \
         Reaching it needs a product-repository generator this harness does not have.",
    ),
    (
        "review.merged",
        "A receipt is only publishable against an accepted review.merge_authorized, so it is \
         unreachable for exactly the reason above. This is a real gap with a known cost: the \
         'reassignment concurrent with a merge receipt' race -- one of the seven fixed \
         reduction-totality defects -- is not reachable here, and stays covered only by the \
         hand-written regression test in apply.rs.",
    ),
    (
        "review.merge_reconciled",
        "Same precondition as review.merged, plus coordinator::verify_review_merge_reconciled \
         fetches refs/heads/main from the remote and requires the authorized candidate to \
         already be a first-parent commit of it -- a real product merge this harness never \
         performs.",
    ),
];

// ---------------------------------------------------------------- the World

/// A total selector into whatever collection exists at the point a step is
/// reached: `Sel(n).pick(len)` is always a valid index, whatever `len` turns
/// out to be, so shrinking can delete or reorder steps without ever
/// producing a `World` that references something absent.
///
/// Deliberately a small integer rather than `proptest::sample::Index`. It
/// shrinks toward zero just as well, it has a public constructor so the
/// planner can be unit-tested directly, and a minimal counterexample reads
/// as `Sel(2)` rather than as an opaque 64-bit fixed-point fraction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Sel(u8);

impl Sel {
    fn pick(self, len: usize) -> usize {
        assert!(len > 0, "Sel::pick against an empty collection");
        self.0 as usize % len
    }

    /// The same selection against a possibly-empty collection.
    fn try_pick(self, len: usize) -> Option<usize> {
        (len > 0).then(|| self.0 as usize % len)
    }
}

fn sel() -> impl Strategy<Value = Sel> {
    any::<u8>().prop_map(Sel)
}

/// One generated scenario: a pure, `Debug`/`Clone` value describing a
/// fleet's whole life. Contains no paths, no repositories, and no git state.
#[derive(Debug, Clone)]
pub struct World {
    /// Which pool name the genesis coordinator takes. Generated rather than
    /// fixed so the coordinator is not always lexicographically first.
    genesis_name: Sel,
    /// The checkouts that join *after* the one that activates the bus, and
    /// how far into the schedule each of them joins: entry `k` selects a
    /// position in `steps`, and that checkout is created cold just before
    /// that step runs. A checkout selecting a position past the last step
    /// joins at the very end and only ever meets the bus through the final
    /// synchronization -- the coldest possible read.
    ///
    /// This is a field rather than a `Step` variant on purpose. Left to a
    /// weighted step generator, most short schedules came out with a single
    /// checkout, quietly collapsing the harness back into the
    /// single-repository round trip it exists to escape.
    joins: Vec<Sel>,
    steps: Vec<Step>,
    /// Seeds for the randomized linear extensions
    /// [`check_reduction_is_total_and_confluent`] re-reduces the published
    /// log under. Generated (rather than fixed or drawn from the clock) so a
    /// failing order is reproducible from the counterexample and shrinks
    /// with it.
    orders: Vec<u64>,
}

/// One requested step. Every reference is a [`Sel`], which is total against
/// whatever collection exists when the step is reached, so shrinking can
/// delete or reorder steps freely without producing a malformed `World`.
#[derive(Debug, Clone)]
enum Step {
    /// One checkout catches up with whatever is on origin right now.
    Sync { host: Sel },
    /// A new agent joins, custodied by `host`.
    Register { host: Sel, name: Sel, role: Sel },
    /// An `agent.status` event from its custodian checkout.
    Status { agent: Sel, blocked: bool },
    /// An `issue.opened` naming another agent -- the cross-agent reference
    /// whose ordering against the target's own registration is bug 3's
    /// class.
    OpenIssue { opener: Sel, target: Sel },
    /// The issue's target publishes `issue.resolved` from *its* checkout,
    /// which requires that checkout to have synchronized past the opening.
    ResolveIssue { issue: Sel },
    /// The opener reassigns the issue to someone else. Deliberately does not
    /// force anyone else to synchronize first: a target that has not
    /// observed the reassignment is the whole point.
    ReassignIssue { issue: Sel, new_target: Sel },
    /// The issue's target acknowledges *the assignment its own checkout
    /// knows about*, which is not necessarily the one that is current
    /// globally.
    ///
    /// An acknowledgement racing a reassignment is an ordinary, blameless
    /// schedule -- the target answers the work it was given while the opener
    /// concurrently moves it -- and two fleet-wide reduction outages were
    /// exactly that shape.
    AckIssue { issue: Sel },
    /// The generic door: build a payload of one generated kind and submit it
    /// through the ordinary publication path. The coordinator's gates decide
    /// whether it lands; either answer is a valid outcome.
    ///
    /// `defer` holds the resulting stream commit back from origin, which is
    /// the publication window a real fleet has between a coordinator's local
    /// commit and its push -- and the only way to race a kind whose own
    /// drain fetches first (gate 17).
    Act {
        kind: Sel,
        a: Sel,
        b: Sel,
        c: Sel,
        flag: bool,
        defer: bool,
    },
    /// Push whatever one checkout is holding back.
    Flush { host: Sel },
}

fn step_strategy() -> impl Strategy<Value = Step> {
    // Weighted toward *publishing* rather than toward synchronizing. The
    // driver already inserts a synchronization wherever one is genuinely
    // needed, so an explicit `Sync` step only ever buys an *extra* catch-up
    // that no causality demanded -- worth generating, but not worth spending
    // most of a short schedule on.
    //
    // `Act` carries most of the weight between it and `Register`: an agent
    // pool is what everything else needs, and `Act` is where thirty-three of
    // the thirty-nine covered kinds live.
    prop_oneof![
        1 => sel().prop_map(|host| Step::Sync { host }),
        1 => sel().prop_map(|host| Step::Flush { host }),
        4 => (sel(), sel(), sel())
            .prop_map(|(host, name, role)| Step::Register { host, name, role }),
        2 => (sel(), any::<bool>())
            .prop_map(|(agent, blocked)| Step::Status { agent, blocked }),
        2 => (sel(), sel())
            .prop_map(|(opener, target)| Step::OpenIssue { opener, target }),
        1 => sel().prop_map(|issue| Step::ResolveIssue { issue }),
        2 => (sel(), sel())
            .prop_map(|(issue, new_target)| Step::ReassignIssue { issue, new_target }),
        2 => sel().prop_map(|issue| Step::AckIssue { issue }),
        10 => (sel(), sel(), sel(), sel(), any::<bool>(), any::<bool>())
            .prop_map(|(kind, a, b, c, flag, defer)| Step::Act { kind, a, b, c, flag, defer }),
    ]
}

fn world_strategy(max_steps: usize) -> impl Strategy<Value = World> {
    (
        sel(),
        // At least one further checkout, always: a fleet of one is exactly
        // the configuration in which all three motivating bugs stayed
        // invisible.
        prop::collection::vec(sel(), 1..MAX_HOSTS),
        prop::collection::vec(step_strategy(), 2..=max_steps),
        prop::collection::vec(any::<u64>(), 2..=4),
    )
        .prop_map(|(genesis_name, joins, steps, orders)| World {
            genesis_name,
            joins,
            steps,
            orders,
        })
}

// -------------------------------------------------------- the resolved plan

/// What the model should record about an [`Op::Act`] *if and only if* the
/// coordinator actually published it.
///
/// Deliberately a bag of optional facts rather than an enum per kind: the
/// model's job here is to keep enough bookkeeping to build the *next*
/// plausible payload, not to re-implement `apply.rs`. A wrong guess costs a
/// rejection, which is a legitimate outcome, so approximate is fine and
/// exhaustive would be waste.
#[derive(Debug, Clone, Default)]
struct Record {
    /// This event becomes that agent's newest lifecycle event.
    lifecycle_tip_of: Option<usize>,
    /// That agent has been retired, so `coordinator::verify_author_active`
    /// will refuse anything further from it -- generating for it is waste.
    retire: Option<usize>,
    /// Open a review chain: (authors, reviewer, product branch suffix).
    new_review: Option<ReviewSeed>,
    /// Append a nomination link to review `.0`, naming reviewer `.1`.
    review_link: Option<(usize, usize)>,
    /// The named reviewer accepted link `.1` of review `.0`.
    review_accept: Option<(usize, EventId)>,
    /// File a finding on review `.0` under short id `.1`.
    review_finding: Option<(usize, Short)>,
    /// Dispose of finding `(changes event, finding id)` on review `.0`.
    review_dispose: Option<(usize, EventId, String)>,
    /// This review chain is closed to further work.
    review_close: Option<usize>,
    /// Open a dependency assigned to that agent.
    new_dependency: Option<usize>,
    /// Reassign dependency `.0` to agent `.1`.
    dep_reassign: Option<(usize, usize)>,
    /// Dependency `.0` reached a terminal disposition.
    dep_terminal: Option<usize>,
    /// Open a handoff offered to that agent.
    new_handoff: Option<usize>,
    /// Handoff `.0` reached a terminal disposition.
    handoff_terminal: Option<usize>,
    /// Publish a broadcast: (acknowledgement required, audience).
    broadcast: Option<(bool, Vec<usize>)>,
    /// This event becomes one more known merge engine activation.
    engine_epoch: bool,
    friction_report: bool,
    friction_synthesis: bool,
    /// One more claim on an exclusive-transition predecessor: the key the
    /// implementation would group it under, plus the predecessor's own id.
    claim: Option<(String, EventId, EventKey)>,
    /// A coordinator resolved that key.
    resolve_claim: Option<String>,
    /// Agents whose reduced lifecycle status the content oracle can no
    /// longer predict once this lands.
    blur_agents: Vec<usize>,
    /// Issues whose reduced disposition the content oracle can no longer
    /// predict once this lands.
    blur_issues: Vec<usize>,
}

/// The immutable half of a review chain, shared by every link.
#[derive(Debug, Clone)]
struct ReviewSeed {
    authors: Vec<usize>,
    reviewer: usize,
    request: ReviewRequest,
}

/// A fully concrete operation: no [`Sel`] left, every host and agent
/// resolved to a real position, every referenced event resolved to a real
/// `EventId`. [`GitExec`] executes exactly this, and [`Model::apply`]
/// predicts exactly this.
#[derive(Debug, Clone)]
enum Op {
    AddHost,
    Sync {
        host: usize,
    },
    /// Push whatever `host` has drained locally but not yet published.
    Flush {
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
    ReassignIssue {
        issue: usize,
        new_target: usize,
    },
    /// `assignment` is an index into the issue's `assignments` chain --
    /// which entry the acknowledging checkout actually knows about.
    AckIssue {
        issue: usize,
        assignment: usize,
    },
    /// The generic submit-and-drain. May be rejected; see [`Step::Act`].
    Act {
        agent: usize,
        kind: &'static str,
        data: Box<EventData>,
        record: Box<Record>,
        /// Mirrors `coordinator::requires_synced_snapshot`: this drain will
        /// fetch before it validates, so the model must record the
        /// synchronization or it reports a fabricated `last_synced`.
        syncs: bool,
        defer: bool,
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
    /// The one checkout holding this agent's stream custody. Custody is
    /// bound to a host by the registry, so no other checkout ever writes
    /// this stream -- which is exactly why stream pushes always
    /// fast-forward.
    host: usize,
    next_seq: u64,
    /// Drained into this agent's local stream but not yet pushed to origin.
    /// A checkout holding any of these cannot fetch (its own ref is ahead of
    /// the remote's, which a non-force fetch rejects outright), so the
    /// driver flushes before anything that must synchronize.
    unpushed: Vec<EventKey>,
    /// This agent's newest lifecycle event, as the model believes it: the
    /// registration, then each `agent.status`/`agent.resumed`, and an
    /// `agent.retired` a coordinator published against it.
    lifecycle_tip: EventId,
    /// The model's belief about the reduced lifecycle status, and whether it
    /// is still worth asserting. An `agent.resumed`/`agent.retired` whose
    /// effect depends on a race the model does not replicate clears this,
    /// which is honest rather than lossy: totality and confluence are
    /// checked kind-agnostically and still cover the event.
    status: LifecycleStatus,
    status_predictable: bool,
    /// Model-side belief about whether this agent may still publish. A
    /// retired author is refused by `coordinator::verify_author_active`, so
    /// generating for it is pure waste.
    retired: bool,
}

#[derive(Debug, Clone)]
struct IssueModel {
    id: EventId,
    opened: EventKey,
    opener: usize,
    target: usize,
    resolved: Option<EventKey>,
    /// Every assignment this issue has had, oldest first: the opening event,
    /// then one entry per reassignment. `(assignment id, event key, target)`.
    ///
    /// The whole chain is kept, not just the current entry, because a
    /// checkout that has not synchronized still legitimately holds an older
    /// one and will acknowledge *that*.
    assignments: Vec<(EventId, EventKey, usize)>,
    /// Cleared once an event kind the oracle does not model may have moved
    /// this issue's disposition.
    predictable: bool,
}

/// The model's shadow of a review chain: enough to build the next plausible
/// payload, not a re-implementation of `state::ReviewChain`.
#[derive(Debug, Clone)]
struct ReviewModel {
    root: EventId,
    root_key: EventKey,
    seed: ReviewSeed,
    /// Every nomination link ever published on this chain, oldest first:
    /// `(id, key, reviewer)`. Kept whole, because a reassignment naming an
    /// *older* link is exactly the event a stale author would have written,
    /// and is what makes two reassignments compete.
    links: Vec<(EventId, EventKey, usize)>,
    /// Links whose named reviewer has accepted them.
    accepted: BTreeSet<EventId>,
    /// `(changes event id, key, finding id)` for every finding filed.
    findings: Vec<(EventId, EventKey, Short)>,
    /// `(changes event id, finding id)` for every finding already disposed.
    disposed: BTreeSet<(EventId, String)>,
    closed: bool,
}

/// The model's shadow of a dependency or handoff: the two subject kinds
/// whose payloads need an id, a target, and a disposition.
#[derive(Debug, Clone)]
struct SubjectModel {
    id: EventId,
    key: EventKey,
    author: usize,
    /// Every assignment, oldest first, exactly as [`IssueModel`].
    assignments: Vec<(EventId, EventKey, usize)>,
    terminal: bool,
}

/// One exclusive-transition predecessor and every candidate claiming it --
/// the model's shadow of an `ExclusiveTracker` group, kept only so a
/// coordinator's `lifecycle.conflict_resolved` has a real contested group to
/// aim at rather than a fabricated one.
#[derive(Debug, Clone)]
struct ClaimGroup {
    /// The predecessor itself, which a resolution names as its `root`.
    root: EventId,
    root_key: EventKey,
    /// Every candidate recorded against it, oldest first.
    members: Vec<(EventId, EventKey)>,
}

#[derive(Debug, Clone)]
struct BroadcastModel {
    id: EventId,
    key: EventKey,
    ack_required: bool,
    audience: Vec<usize>,
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
    /// requires it never to be fabricated -- so a checkout that has only
    /// ever written locally must report `None`, however much it has
    /// published.
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
    reviews: Vec<ReviewModel>,
    dependencies: Vec<SubjectModel>,
    handoffs: Vec<SubjectModel>,
    broadcasts: Vec<BroadcastModel>,
    friction_reports: Vec<(EventId, EventKey)>,
    friction_syntheses: Vec<(EventId, EventKey)>,
    /// Every `agent.status` event ever published, in order. A checkout's
    /// reduced lifecycle status is the last of these it actually knows
    /// about, which is how a stale checkout is distinguished from a current
    /// one by *content* rather than merely by event count.
    statuses: Vec<(EventKey, LifecycleStatus)>,
    /// Claims on an exclusive-transition predecessor, grouped exactly the
    /// way `apply.rs` groups them: key -> the competing candidates, plus the
    /// predecessor's own id so a resolution can reference it. Two or more
    /// members is a contested group a coordinator may resolve.
    claims: BTreeMap<String, ClaimGroup>,
    /// Keys some coordinator has already resolved.
    resolved_claims: BTreeSet<String>,
    /// The highest schema version the model believes is activated. Used only
    /// to bias generation toward an advancing version (which publishes) and
    /// a repeated one (which does not, and used to wedge reduction).
    schema_version: u32,
    /// Every `merge_engine.activated` the model believes landed.
    engine_epochs: Vec<(EventId, EventKey)>,
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

    /// Can `host` build a frontier entry covering `key`? `build_frontier`
    /// reads the referenced agent's stream and refuses an id past its tip,
    /// so an event may only reference what its own checkout already holds.
    fn host_knows(&self, host: usize, key: &EventKey) -> bool {
        self.hosts[host].known.contains(key)
    }

    /// Is `host` holding drained-but-unpushed commits? Such a checkout
    /// cannot fetch: its own stream ref is ahead of the remote's, and
    /// `sync::synced_snapshot`'s non-force fetch rejects that outright.
    fn host_is_dirty(&self, host: usize) -> bool {
        self.agents
            .iter()
            .any(|a| a.host == host && !a.unpushed.is_empty())
    }

    fn agent_by_name(&self, name: &Agent) -> Option<usize> {
        self.agents.iter().position(|a| &a.name == name)
    }

    /// Every agent the current epoch lists that the model believes may still
    /// publish, filtered by role.
    fn live_agents_with_role(&self, role: Role) -> Vec<usize> {
        let Some(epoch) = self.latest_epoch() else {
            return vec![];
        };
        self.epochs[epoch]
            .iter()
            .copied()
            .filter(|&i| {
                self.agents[i].role == role
                    && !self.agents[i].retired
                    && !self.agents[i].status.deactivates()
            })
            .collect()
    }

    fn live_agents(&self) -> Vec<usize> {
        let Some(epoch) = self.latest_epoch() else {
            return vec![];
        };
        self.epochs[epoch]
            .iter()
            .copied()
            .filter(|&i| !self.agents[i].retired && !self.agents[i].status.deactivates())
            .collect()
    }

    fn publish(&mut self, host: usize, key: EventKey, defer: bool) {
        self.hosts[host].known.insert(key);
        if defer {
            self.agents[key.agent].unpushed.push(key);
        } else {
            self.origin.insert(key);
        }
    }

    fn sync(&mut self, host: usize) {
        self.hosts[host].epoch = self.latest_epoch();
        let mut known = self.origin.clone();
        // A checkout never loses what it authored itself; the driver
        // guarantees a dirty checkout is flushed before it synchronizes, so
        // this union only ever restates what origin already holds.
        for a in &self.agents {
            if a.host == host {
                known.extend(a.unpushed.iter().copied());
            }
        }
        self.hosts[host].known = known;
        self.hosts[host].ever_synced = true;
    }

    fn flush(&mut self, host: usize) {
        let mut pushed = Vec::new();
        for a in &mut self.agents {
            if a.host == host {
                pushed.append(&mut a.unpushed);
            }
        }
        self.origin.extend(pushed);
    }

    fn apply(&mut self, op: &Op, landed: bool) {
        match op {
            Op::AddHost => self.hosts.push(HostModel::default()),
            Op::Sync { host } => self.sync(*host),
            Op::Flush { host } => self.flush(*host),
            Op::Genesis { host, name } => {
                let idx = self.agents.len();
                self.agents.push(AgentModel {
                    name: name.clone(),
                    role: Role::Coordinator,
                    host: *host,
                    next_seq: 1,
                    unpushed: vec![],
                    lifecycle_tip: EventId::new(name, 0),
                    status: LifecycleStatus::Active,
                    status_predictable: true,
                    retired: false,
                });
                self.epochs.push(BTreeSet::from([idx]));
                self.hosts[*host].epoch = self.latest_epoch();
                self.publish(*host, EventKey { agent: idx, seq: 0 }, false);
            }
            Op::Register { host, name, role } => {
                let idx = self.agents.len();
                self.agents.push(AgentModel {
                    name: name.clone(),
                    role: *role,
                    host: *host,
                    next_seq: 1,
                    unpushed: vec![],
                    lifecycle_tip: EventId::new(name, 0),
                    status: LifecycleStatus::Active,
                    status_predictable: true,
                    retired: false,
                });
                let mut members = self.epochs.last().cloned().unwrap_or_default();
                members.insert(idx);
                self.epochs.push(members);
                self.hosts[*host].epoch = self.latest_epoch();
                self.publish(*host, EventKey { agent: idx, seq: 0 }, false);
            }
            Op::Status { agent, status } => {
                let key = self.take_seq(*agent);
                self.publish(self.agents[*agent].host, key, false);
                self.statuses.push((key, *status));
                let name = self.agents[*agent].name.clone();
                let a = &mut self.agents[*agent];
                a.lifecycle_tip = EventId::new(&name, key.seq);
                a.status = *status;
            }
            Op::OpenIssue { opener, target } => {
                let key = self.take_seq(*opener);
                self.publish(self.agents[*opener].host, key, false);
                let id = EventId::new(&self.agents[*opener].name, key.seq);
                self.issues.push(IssueModel {
                    id: id.clone(),
                    opened: key,
                    opener: *opener,
                    target: *target,
                    resolved: None,
                    assignments: vec![(id, key, *target)],
                    predictable: true,
                });
            }
            Op::ResolveIssue { issue } => {
                let target = self.issues[*issue].target;
                let key = self.take_seq(target);
                self.publish(self.agents[target].host, key, false);
                self.issues[*issue].resolved = Some(key);
            }
            Op::ReassignIssue { issue, new_target } => {
                let opener = self.issues[*issue].opener;
                // `issue.reassigned` is currency-sensitive (gate 17), so
                // `drain_outbox` probes the remote before publishing it and
                // this checkout genuinely synchronizes as a side effect. The
                // oracle has to model it or it reports a fabricated
                // `last_synced`.
                let host = self.agents[opener].host;
                self.sync(host);
                let key = self.take_seq(opener);
                self.publish(self.agents[opener].host, key, false);
                let id = EventId::new(&self.agents[opener].name, key.seq);
                self.issues[*issue].target = *new_target;
                self.issues[*issue].assignments.push((id, key, *new_target));
            }
            Op::AckIssue { issue, assignment } => {
                let acker = self.issues[*issue].assignments[*assignment].2;
                let key = self.take_seq(acker);
                self.publish(self.agents[acker].host, key, false);
            }
            Op::Act {
                agent,
                record,
                syncs,
                defer,
                ..
            } => {
                let host = self.agents[*agent].host;
                if *syncs {
                    self.sync(host);
                }
                if !landed {
                    return;
                }
                let key = self.take_seq(*agent);
                self.publish(host, key, *defer);
                let id = EventId::new(&self.agents[*agent].name, key.seq);
                self.record_act(record, &id, key);
            }
        }
    }

    /// Files the bookkeeping an [`Op::Act`] earns once it has actually
    /// published.
    fn record_act(&mut self, record: &Record, id: &EventId, key: EventKey) {
        if let Some(a) = record.lifecycle_tip_of {
            self.agents[a].lifecycle_tip = id.clone();
        }
        if let Some(a) = record.retire {
            self.agents[a].retired = true;
        }
        for &a in &record.blur_agents {
            self.agents[a].status_predictable = false;
        }
        for &i in &record.blur_issues {
            self.issues[i].predictable = false;
        }
        if let Some(seed) = &record.new_review {
            self.reviews.push(ReviewModel {
                root: id.clone(),
                root_key: key,
                seed: seed.clone(),
                links: vec![(id.clone(), key, seed.reviewer)],
                accepted: BTreeSet::new(),
                findings: vec![],
                disposed: BTreeSet::new(),
                closed: false,
            });
        }
        if let Some((r, reviewer)) = record.review_link {
            self.reviews[r].links.push((id.clone(), key, reviewer));
        }
        if let Some((r, link)) = &record.review_accept {
            self.reviews[*r].accepted.insert(link.clone());
        }
        if let Some((r, finding)) = &record.review_finding {
            self.reviews[*r]
                .findings
                .push((id.clone(), key, finding.clone()));
        }
        if let Some((r, changes, finding)) = &record.review_dispose {
            self.reviews[*r]
                .disposed
                .insert((changes.clone(), finding.clone()));
        }
        if let Some(r) = record.review_close {
            self.reviews[r].closed = true;
        }
        if let Some(t) = record.new_dependency {
            self.dependencies.push(SubjectModel {
                id: id.clone(),
                key,
                author: key.agent,
                assignments: vec![(id.clone(), key, t)],
                terminal: false,
            });
        }
        if let Some((d, t)) = record.dep_reassign {
            self.dependencies[d].assignments.push((id.clone(), key, t));
        }
        if let Some(d) = record.dep_terminal {
            self.dependencies[d].terminal = true;
        }
        if let Some(r) = record.new_handoff {
            self.handoffs.push(SubjectModel {
                id: id.clone(),
                key,
                author: key.agent,
                assignments: vec![(id.clone(), key, r)],
                terminal: false,
            });
        }
        if let Some(h) = record.handoff_terminal {
            self.handoffs[h].terminal = true;
        }
        if let Some((ack, audience)) = &record.broadcast {
            self.broadcasts.push(BroadcastModel {
                id: id.clone(),
                key,
                ack_required: *ack,
                audience: audience.clone(),
            });
        }
        if record.engine_epoch {
            self.engine_epochs.push((id.clone(), key));
        }
        if record.friction_report {
            self.friction_reports.push((id.clone(), key));
        }
        if record.friction_synthesis {
            self.friction_syntheses.push((id.clone(), key));
        }
        if let Some((k, root, root_key)) = &record.claim {
            let entry = self.claims.entry(k.clone()).or_insert_with(|| ClaimGroup {
                root: root.clone(),
                root_key: *root_key,
                members: vec![],
            });
            entry.members.push((id.clone(), key));
        }
        if let Some(k) = &record.resolve_claim {
            self.resolved_claims.insert(k.clone());
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
                let status = self.agents[i].status_predictable.then(|| {
                    self.statuses
                        .iter()
                        .rev()
                        .find(|(k, _)| k.agent == i && known.contains(k))
                        .map(|(_, s)| *s)
                        // `apply_registered` seeds every agent as `Active`.
                        .unwrap_or(LifecycleStatus::Active)
                });
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
                    target: issue
                        .predictable
                        .then(|| self.agents[issue.target].name.as_str().to_string()),
                    status: issue
                        .predictable
                        .then_some(if resolved { "resolved" } else { "open" }),
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
    /// bug-2 check: a double-prefixed ref would leave the correctly-named
    /// one missing from this set.
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
    /// The lifecycle status this checkout should have reduced to -- older
    /// than the fleet-wide latest whenever this checkout is behind.
    ///
    /// `None` once an `agent.resumed`/`agent.retired` whose effect the model
    /// does not replicate has landed for this agent: the content oracle
    /// stops asserting rather than asserting something it has guessed. That
    /// costs nothing for the property this module exists for -- totality and
    /// confluence are checked kind-agnostically, over every event -- and it
    /// is what lets the alphabet grow past what the oracle can predict
    /// exactly.
    status: Option<LifecycleStatus>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedIssue {
    opener: String,
    /// `None` once an unmodelled kind may have moved this issue; see
    /// [`ExpectedAgent::status`].
    target: Option<String>,
    status: Option<&'static str>,
}

// ------------------------------------------------------------------ driving

/// What actually happened when an [`Op`] was executed.
///
/// `Published(false)` is an ordinary outcome, not a failure: the
/// coordinator's gates are *entitled* to refuse a candidate, and this
/// harness's whole point is that a refusal costs one author a retry while an
/// accepted-then-unreducible event costs the fleet.
type Landed = bool;

/// The side of the harness that owns real repositories, so [`drive`] can be
/// unit-tested with them stubbed out.
trait Exec {
    /// A real object id resolvable in `host`'s repository, for the payload
    /// fields `coordinator::verify_object_ids_resolve` checks.
    fn head_commit(&self, host: usize) -> ObjectId;
    /// `host`'s current local registry epoch id, for a broadcast's
    /// `audience_epoch`.
    fn epoch_id(&self, host: usize) -> Option<ObjectId>;
    /// Runs the operation. Returns whether it published.
    fn run(&mut self, model: &Model, op: &Op, step: usize) -> Result<Landed, TestCaseError>;
    /// Runs whatever invariant sweep this executor performs after each op.
    fn check(&mut self, model: &Model, op: &Op, step: usize) -> Result<(), TestCaseError>;
}

/// The stub executor: every operation is reported as having published, and
/// nothing is checked. What [`plan`] runs, so the planner's own tests need
/// no repositories.
#[derive(Default)]
struct DryExec {
    hosts: usize,
}

/// A fixed, well-formed object id for the stub executor. Never resolved
/// against anything, since [`DryExec`] runs no git.
fn dummy_object_id() -> ObjectId {
    ObjectId::parse("0".repeat(40)).expect("forty zeroes is a valid sha1 object id")
}

impl Exec for DryExec {
    fn head_commit(&self, _host: usize) -> ObjectId {
        dummy_object_id()
    }
    fn epoch_id(&self, host: usize) -> Option<ObjectId> {
        (host < self.hosts).then(dummy_object_id)
    }
    fn run(&mut self, _model: &Model, op: &Op, _step: usize) -> Result<Landed, TestCaseError> {
        if matches!(op, Op::AddHost) {
            self.hosts += 1;
        }
        Ok(true)
    }
    fn check(&mut self, _model: &Model, _op: &Op, _step: usize) -> Result<(), TestCaseError> {
        Ok(())
    }
}

/// Resolves a generated [`World`] into a concrete, causally-valid schedule
/// and runs it.
///
/// Runs the [`Model`] forward as it goes so each step's [`Sel`] references
/// select from what actually exists at that point, and so a step whose
/// preconditions cannot hold is dropped rather than executed. Resolution and
/// execution are interleaved rather than separated because an [`Op::Act`]
/// may be rejected: the model has to learn what actually landed before it
/// resolves the next step, or every later sequence-number prediction is
/// wrong.
///
/// The one thing it *adds* is synchronization and flushing where a real
/// operator would have performed them: before a registry transition (which
/// is what keeps the registry chain linear), and before anything that
/// fetches from a checkout still holding unpushed commits.
fn drive(world: &World, exec: &mut dyn Exec) -> Result<(Model, Vec<Op>), TestCaseError> {
    let mut model = Model::default();
    let mut ops = Vec::new();
    let mut used_names: BTreeSet<usize> = BTreeSet::new();
    let mut step_no = 0usize;

    macro_rules! emit {
        ($op:expr) => {{
            let op = $op;
            let landed = exec.run(&model, &op, step_no)?;
            model.apply(&op, landed);
            exec.check(&model, &op, step_no)?;
            ops.push(op);
            step_no += 1;
        }};
    }

    // The bus has to exist before anything else can be asked of it, so
    // genesis is implicit rather than generated: a `World` without it would
    // describe nothing at all.
    emit!(Op::AddHost);
    let gi = world.genesis_name.pick(AGENT_NAMES.len());
    used_names.insert(gi);
    emit!(Op::Genesis {
        host: 0,
        name: agent(AGENT_NAMES[gi]),
    });

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
            emit!(Op::AddHost);
            joined += 1;
        }
        match step {
            Step::Sync { host } => {
                let h = host.pick(model.hosts.len());
                if model.host_is_dirty(h) {
                    emit!(Op::Flush { host: h });
                }
                emit!(Op::Sync { host: h });
            }
            Step::Flush { host } => {
                let h = host.pick(model.hosts.len());
                if model.host_is_dirty(h) {
                    emit!(Op::Flush { host: h });
                }
            }
            Step::Register { host, name, role } => {
                let free: Vec<usize> = (0..AGENT_NAMES.len())
                    .filter(|i| !used_names.contains(i))
                    .collect();
                if free.is_empty() {
                    continue;
                }
                let ni = free[name.pick(free.len())];
                let h = host.pick(model.hosts.len());
                // A registry transition is a compare-and-swap against
                // origin's current tip; performing one from a stale checkout
                // would push a sibling epoch and fork the chain. Real
                // callers synchronize first, so the driver does too.
                if model.hosts[h].epoch != model.latest_epoch() {
                    if model.host_is_dirty(h) {
                        emit!(Op::Flush { host: h });
                    }
                    emit!(Op::Sync { host: h });
                }
                used_names.insert(ni);
                emit!(Op::Register {
                    host: h,
                    name: agent(AGENT_NAMES[ni]),
                    role: ROLE_POOL[role.pick(ROLE_POOL.len())],
                });
            }
            Step::Status { agent, blocked } => {
                let a = agent.pick(model.agents.len());
                if model.agents[a].retired {
                    continue;
                }
                emit!(Op::Status {
                    agent: a,
                    status: if *blocked {
                        LifecycleStatus::Blocked
                    } else {
                        LifecycleStatus::Active
                    },
                });
            }
            Step::OpenIssue { opener, target } => {
                if model.agents.len() < 2 {
                    continue;
                }
                let live = model.live_agents();
                if live.len() < 2 {
                    continue;
                }
                let o = live[opener.pick(live.len())];
                // An issue against oneself would make every reference
                // same-agent, which is the causality this step exists to
                // avoid; nudge rather than discard the step.
                let t = match target.pick(model.agents.len()) {
                    t if t != o => t,
                    t => (t + 1) % model.agents.len(),
                };
                // The opener's own checkout has to already know the target
                // exists -- `coordinator::drain_outbox` validates against
                // what is *locally* reduced, and `build_frontier` needs the
                // target's stream ref to be present. A checkout that has not
                // caught up would be rightly refused, which is not what this
                // step probes, so catch it up first: that is what a real
                // agent does, and it leaves every *other* checkout exactly
                // as stale as it was.
                let opener_host = model.agents[o].host;
                if !model.host_sees_agent(opener_host, t) {
                    if model.host_is_dirty(opener_host) {
                        emit!(Op::Flush { host: opener_host });
                    }
                    emit!(Op::Sync { host: opener_host });
                }
                emit!(Op::OpenIssue {
                    opener: o,
                    target: t,
                });
            }
            Step::ResolveIssue { issue } => {
                let open: Vec<usize> = (0..model.issues.len())
                    .filter(|&i| model.issues[i].resolved.is_none() && model.issues[i].predictable)
                    .collect();
                if open.is_empty() {
                    continue;
                }
                let i = open[issue.pick(open.len())];
                let target = model.issues[i].target;
                if model.agents[target].retired {
                    continue;
                }
                let opened = model.issues[i].opened;
                // Only the assignment's target may dispose of the issue, so
                // it is the target's own checkout that has to have caught up
                // with the opening -- which is exactly why a real agent
                // syncs before answering work addressed to it.
                let target_host = model.agents[target].host;
                if !model.hosts[target_host].known.contains(&opened) {
                    if model.host_is_dirty(target_host) {
                        emit!(Op::Flush { host: target_host });
                    }
                    emit!(Op::Sync { host: target_host });
                }
                emit!(Op::ResolveIssue { issue: i });
            }
            Step::ReassignIssue { issue, new_target } => {
                let open: Vec<usize> = (0..model.issues.len())
                    .filter(|&i| model.issues[i].resolved.is_none() && model.issues[i].predictable)
                    .collect();
                if open.is_empty() {
                    continue;
                }
                let i = open[issue.pick(open.len())];
                let current = model.issues[i].target;
                let opener = model.issues[i].opener;
                if model.agents[opener].retired {
                    continue;
                }
                let candidates: Vec<usize> =
                    (0..model.agents.len()).filter(|&t| t != current).collect();
                if candidates.is_empty() {
                    continue;
                }
                let t = candidates[new_target.pick(candidates.len())];
                // Gate 17: this drain fetches, so the checkout must not be
                // holding unpushed commits of its own.
                let host = model.agents[opener].host;
                if model.host_is_dirty(host) {
                    emit!(Op::Flush { host });
                }
                // Deliberately no synchronization for anyone else. The
                // opener authored the issue so its own checkout already
                // knows it, and leaving every other checkout behind is
                // precisely the state that makes the next acknowledgement
                // race.
                emit!(Op::ReassignIssue {
                    issue: i,
                    new_target: t,
                });
            }
            Step::AckIssue { issue } => {
                let open: Vec<usize> = (0..model.issues.len())
                    .filter(|&i| model.issues[i].resolved.is_none() && model.issues[i].predictable)
                    .collect();
                if open.is_empty() {
                    continue;
                }
                let i = open[issue.pick(open.len())];
                // Whichever assignment this issue's assignee actually knows
                // about from its own checkout -- the newest such, since that
                // is what a real agent would answer. When a reassignment has
                // happened elsewhere and has not reached that checkout, this
                // is an older entry than the current one, and the resulting
                // acknowledgement is superseded by the time it is reduced.
                let chosen = model.issues[i]
                    .assignments
                    .iter()
                    .enumerate()
                    .rev()
                    .find(|(_, (_, key, target))| {
                        !model.agents[*target].retired
                            && model.hosts[model.agents[*target].host].known.contains(key)
                    })
                    .map(|(idx, _)| idx);
                let Some(idx) = chosen else {
                    continue;
                };
                emit!(Op::AckIssue {
                    issue: i,
                    assignment: idx,
                });
            }
            Step::Act {
                kind,
                a,
                b,
                c,
                flag,
                defer,
            } => {
                let k = ACT_KINDS[kind.pick(ACT_KINDS.len())];
                let Some(act) = build_act(&model, exec, k, [*a, *b, *c], *flag) else {
                    continue;
                };
                let syncs = crate::coordinator::requires_synced_snapshot(&act.data);
                let host = model.agents[act.agent].host;
                if syncs && model.host_is_dirty(host) {
                    emit!(Op::Flush { host });
                }
                emit!(Op::Act {
                    agent: act.agent,
                    kind: k,
                    data: Box::new(act.data),
                    record: Box::new(act.record),
                    syncs,
                    // Deferring a currency-sensitive kind's *own* push is
                    // what opens the window another host publishes into;
                    // deferring is harmless for the rest.
                    defer: *defer,
                });
            }
        }
    }
    // Whatever is left joins at the very end: a checkout that never acts and
    // meets the bus for the first time at the final synchronization.
    while joined < joins.len() {
        emit!(Op::AddHost);
        joined += 1;
    }
    // Nothing may stay unpushed past the end of the schedule: the
    // convergence sweep asks every checkout to reduce the *same* set, which
    // is only meaningful once every checkout can fetch it.
    for h in 0..model.hosts.len() {
        if model.host_is_dirty(h) {
            emit!(Op::Flush { host: h });
        }
    }
    Ok((model, ops))
}

/// The shape [`drive`] uses for the planner's own unit tests: run the whole
/// resolution loop with the executor stubbed out.
fn plan(world: &World) -> Vec<Op> {
    let mut exec = DryExec::default();
    drive(world, &mut exec)
        .expect("the stub executor never fails")
        .1
}

/// Registration draws from this rather than a boolean, because the review
/// protocol needs reviewers and `audit.reported` needs an auditor -- and a
/// pool that could only produce implementors and coordinators is exactly the
/// silent narrowing this module exists to stop. Weighted toward the two
/// roles most events need.
const ROLE_POOL: [Role; 6] = [
    Role::Implementor,
    Role::Implementor,
    Role::Reviewer,
    Role::Reviewer,
    Role::Coordinator,
    Role::Auditor,
];

// ------------------------------------------------------------ payload building

/// The kinds [`Step::Act`] draws from: every [`GENERATED_KINDS`] entry that
/// is not already reached through a dedicated, precisely-modelled operation.
const ACT_KINDS: &[&str] = &[
    "agent.resumed",
    "agent.retired",
    "schema.activated",
    "merge_engine.activated",
    "scope.set",
    "plan.set",
    "progress.reported",
    "issue.rejected",
    "dependency.requested",
    "dependency.acknowledged",
    "dependency.resolved",
    "dependency.rejected",
    "dependency.reassigned",
    "handoff.offered",
    "handoff.accepted",
    "handoff.declined",
    "handoff.withdrawn",
    "review.nominated",
    "review.nomination_accepted",
    "review.nomination_declined",
    "review.changes_requested",
    "review.findings_cleared",
    "review.findings_superseded",
    "review.reassigned",
    "review.withdrawn",
    "lifecycle.conflict_resolved",
    "friction.reported",
    "friction.synthesized",
    "subscription.set",
    "broadcast.published",
    "broadcast.acknowledged",
    "broadcast.seen",
    "audit.reported",
];

/// One resolved generic action.
struct Act {
    agent: usize,
    data: EventData,
    record: Record,
}

/// The exclusive-transition key `apply.rs` would group a claim under.
/// Mirrors its grouping (one group per predecessor id per class), which is
/// all the model needs in order to know when a contested group exists and a
/// coordinator's `lifecycle.conflict_resolved` has something to resolve.
fn claim_key(class: &str, predecessor: &EventId) -> String {
    format!("{class}:{predecessor}")
}

fn text_of(s: &str) -> Text {
    text(s)
}

fn branch_for(name: &Agent) -> Branch {
    Branch::parse(format!("refs/heads/agent/{name}/work")).expect("a valid product branch")
}

fn path_claim(s: &str) -> PathClaim {
    PathClaim::parse(s.to_string()).expect("a valid path claim")
}

fn topic(s: &str) -> CoordinationTopic {
    CoordinationTopic::parse(s.to_string()).expect("a valid coordination topic")
}

/// Builds one generic action, or `None` when the model says nothing of this
/// kind is currently expressible.
///
/// Deliberately biased rather than random: a payload naming ids that do not
/// exist would be refused at publication and prove nothing, so every
/// reference is drawn from history the acting checkout can actually see, and
/// every *subject* selection prefers a subject someone else has already
/// acted on. Getting a wide-but-shallow generator that never produces a
/// collision would satisfy the coverage guard while testing nothing.
fn build_act(
    model: &Model,
    exec: &dyn Exec,
    kind: &'static str,
    sels: [Sel; 3],
    flag: bool,
) -> Option<Act> {
    let [s0, s1, s2] = sels;
    let pick = |v: &[usize], s: Sel| -> Option<usize> { v.get(s.try_pick(v.len())?).copied() };

    match kind {
        // ------------------------------------------------- agent lifecycle
        "agent.resumed" => {
            // An agent resuming from whatever it believes its own newest
            // lifecycle event to be. Racing a coordinator's `agent.retired`
            // citing the same predecessor is the shape that matters.
            let live = model.live_agents();
            let a = pick(&live, s0)?;
            let prev = model.agents[a].lifecycle_tip.clone();
            Some(Act {
                agent: a,
                data: EventData::AgentResumed(AgentResumed {
                    previous_lifecycle: prev,
                    reason: text_of("proptest resume"),
                    user_authority: text_of("proptest operator"),
                }),
                record: Record {
                    lifecycle_tip_of: Some(a),
                    blur_agents: vec![a],
                    ..Default::default()
                },
            })
        }
        "agent.retired" => {
            let coords = model.live_agents_with_role(Role::Coordinator);
            let c = pick(&coords, s0)?;
            let targets: Vec<usize> = model
                .live_agents()
                .into_iter()
                .filter(|&t| t != c)
                .collect();
            let t = pick(&targets, s1)?;
            let host = model.agents[c].host;
            // The coordinator must be able to build a frontier entry for the
            // predecessor it names, so it may only cite one it can see.
            let prev = model.agents[t].lifecycle_tip.clone();
            let prev_key = event_key_of(model, &prev)?;
            if !model.host_knows(host, &prev_key) {
                return None;
            }
            Some(Act {
                agent: c,
                data: EventData::AgentRetired(AgentRetired {
                    target: model.agents[t].name.clone(),
                    previous_lifecycle: prev,
                    reason: text_of("proptest retirement"),
                    user_authority: text_of("proptest operator"),
                }),
                record: Record {
                    retire: Some(t),
                    blur_agents: vec![t],
                    ..Default::default()
                },
            })
        }
        // ------------------------------------------------ fleet-wide authority
        "schema.activated" => {
            let coords = model.live_agents_with_role(Role::Coordinator);
            let c = pick(&coords, s0)?;
            // Half the draws repeat the currently activated version, which
            // is exactly the pair two coordinators produce when neither has
            // observed the other -- and which used to make the whole bus
            // unreducible in *both* orders.
            let version = if flag {
                model.schema_version.max(1)
            } else {
                model.schema_version + 1
            };
            let commit = exec.head_commit(model.agents[c].host);
            Some(Act {
                agent: c,
                data: EventData::SchemaActivated(SchemaActivated {
                    version,
                    design_commit: commit.clone(),
                    helper_commit: commit,
                }),
                record: Record::default(),
            })
        }
        "merge_engine.activated" => {
            let coords = model.live_agents_with_role(Role::Coordinator);
            let c = pick(&coords, s0)?;
            let host = model.agents[c].host;
            // The genesis activation names the coordinator's own
            // registration as the synthetic anchor (see
            // `apply_merge_engine_activated`'s bootstrap exception);
            // afterwards it must name a real prior activation this checkout
            // can see.
            let previous = if model.engine_epochs.is_empty() {
                EventId::new(&model.agents[c].name, 0)
            } else {
                let visible: Vec<usize> = (0..model.engine_epochs.len())
                    .filter(|&i| model.host_knows(host, &model.engine_epochs[i].1))
                    .collect();
                let i = pick(&visible, s1)?;
                model.engine_epochs[i].0.clone()
            };
            let commit = exec.head_commit(host);
            Some(Act {
                agent: c,
                data: EventData::MergeEngineActivated(MergeEngineActivated {
                    previous_epoch: previous.clone(),
                    merge_engine: short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
                    merge_engine_version: short(crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION),
                    design_commit: commit.clone(),
                    helper_commit: commit,
                }),
                record: Record {
                    engine_epoch: true,
                    claim: Some((
                        claim_key("engine_epoch", &previous),
                        previous.clone(),
                        event_key_of(model, &previous).unwrap_or(EventKey { agent: 0, seq: 0 }),
                    )),
                    ..Default::default()
                },
            })
        }
        // ------------------------------------------------ ordinary self-reports
        "scope.set" => {
            let impls = model.live_agents_with_role(Role::Implementor);
            let a = pick(&impls, s0)?;
            Some(Act {
                agent: a,
                data: EventData::ScopeSet(ScopeSet {
                    base_code_commit: exec.head_commit(model.agents[a].host),
                    exclusive: StringSet::from_iter([path_claim(if flag {
                        "src/one/**"
                    } else {
                        "src/two/**"
                    })]),
                    shared: StringSet::default(),
                    exports: StringSet::from_iter([short("iface")]),
                    // Deliberately empty: a cross-agent import is not
                    // reachable from `ScopeSet::referenced_ids` (which is
                    // empty), so a generated one would be an implicit
                    // dependency no valid replay order is obliged to honour.
                    depends_on: vec![],
                    note: text_of("proptest scope"),
                }),
                record: Record::default(),
            })
        }
        "plan.set" => {
            let live = model.live_agents();
            let a = pick(&live, s0)?;
            Some(Act {
                agent: a,
                data: EventData::PlanSet(PlanSet {
                    summary: text_of("proptest plan"),
                    steps: vec![PlanStep {
                        id: short("s1"),
                        state: if flag {
                            PlanStepState::Active
                        } else {
                            PlanStepState::Pending
                        },
                        text: text_of("do the thing"),
                    }],
                    risks: vec![],
                }),
                record: Record::default(),
            })
        }
        "progress.reported" => {
            let live = model.live_agents();
            let a = pick(&live, s0)?;
            let implementor = model.agents[a].role == Role::Implementor;
            Some(Act {
                agent: a,
                data: EventData::ProgressReported(ProgressReported {
                    product_commit: implementor.then(|| exec.head_commit(model.agents[a].host)),
                    completed: vec![text_of("one")],
                    current: vec![],
                    next: vec![],
                    blockers: vec![],
                    verification: vec![],
                }),
                record: Record::default(),
            })
        }
        "subscription.set" => {
            let live = model.live_agents();
            let a = pick(&live, s0)?;
            Some(Act {
                agent: a,
                data: EventData::SubscriptionSet(SubscriptionSet {
                    topics: StringSet::from_iter([topic(if flag {
                        "bus.contention"
                    } else {
                        "proof.rebuild"
                    })]),
                }),
                record: Record::default(),
            })
        }
        // ------------------------------------------------------------ issues
        "issue.rejected" => {
            let open: Vec<usize> = (0..model.issues.len())
                .filter(|&i| model.issues[i].resolved.is_none())
                .collect();
            let i = pick(&open, s0)?;
            let issue = &model.issues[i];
            // Whichever assignment the disposing agent's own checkout knows
            // about, exactly as `Step::AckIssue`: a stale target rejecting
            // work that has since been moved is the ordinary race.
            let (aid, akey, target) = issue
                .assignments
                .iter()
                .rev()
                .find(|(_, key, t)| {
                    !model.agents[*t].retired && model.host_knows(model.agents[*t].host, key)
                })?
                .clone();
            let _ = akey;
            Some(Act {
                agent: target,
                data: EventData::IssueRejected(IssueRejected {
                    issue: issue.id.clone(),
                    assignment: aid.clone(),
                    reason: text_of("proptest rejection"),
                    normative_refs: vec![],
                }),
                record: Record {
                    blur_issues: vec![i],
                    claim: Some((claim_key("issue", &aid), aid.clone(), issue.opened)),
                    ..Default::default()
                },
            })
        }
        // -------------------------------------------------------- dependencies
        "dependency.requested" => {
            let live = model.live_agents();
            let a = pick(&live, s0)?;
            let targets: Vec<usize> = live
                .iter()
                .copied()
                .filter(|&t| t != a && model.host_sees_agent(model.agents[a].host, t))
                .collect();
            let t = pick(&targets, s1)?;
            Some(Act {
                agent: a,
                data: EventData::DependencyRequested(DependencyRequested {
                    target: model.agents[t].name.clone(),
                    interface: short("iface"),
                    needed_by: text_of("soon"),
                    blocking: flag,
                    summary: text_of("proptest dependency"),
                    evidence: StringSet::default(),
                }),
                record: Record {
                    new_dependency: Some(t),
                    ..Default::default()
                },
            })
        }
        "dependency.acknowledged" | "dependency.resolved" | "dependency.rejected" => {
            let open: Vec<usize> = (0..model.dependencies.len())
                .filter(|&i| !model.dependencies[i].terminal)
                .collect();
            let i = pick(&open, s0)?;
            let dep = &model.dependencies[i];
            let (aid, _, target) = dep
                .assignments
                .iter()
                .rev()
                .find(|(_, key, t)| {
                    !model.agents[*t].retired && model.host_knows(model.agents[*t].host, key)
                })?
                .clone();
            if !model.host_knows(model.agents[target].host, &dep.key) {
                return None;
            }
            let (data, terminal) = match kind {
                "dependency.acknowledged" => (
                    EventData::DependencyAcknowledged(DependencyAcknowledged {
                        dependency: dep.id.clone(),
                        assignment: aid.clone(),
                        note: text_of("proptest ack"),
                    }),
                    false,
                ),
                "dependency.resolved" => (
                    EventData::DependencyResolved(DependencyResolved {
                        dependency: dep.id.clone(),
                        assignment: aid.clone(),
                        summary: text_of("proptest resolution"),
                        product_commit: None,
                        verification: vec![],
                    }),
                    true,
                ),
                _ => (
                    EventData::DependencyRejected(DependencyRejected {
                        dependency: dep.id.clone(),
                        assignment: aid.clone(),
                        reason: text_of("proptest rejection"),
                    }),
                    true,
                ),
            };
            Some(Act {
                agent: target,
                data,
                record: Record {
                    dep_terminal: terminal.then_some(i),
                    claim: terminal.then(|| (claim_key("dependency", &aid), aid.clone(), dep.key)),
                    ..Default::default()
                },
            })
        }
        "dependency.reassigned" => {
            let open: Vec<usize> = (0..model.dependencies.len())
                .filter(|&i| !model.dependencies[i].terminal)
                .collect();
            let i = pick(&open, s0)?;
            let dep = &model.dependencies[i];
            let requester = dep.author;
            if model.agents[requester].retired {
                return None;
            }
            let host = model.agents[requester].host;
            // Deliberately the assignment the requester *knew about*, which
            // when two requesters act concurrently is the same one -- that
            // is what makes them compete rather than chain.
            let (aid, akey, prev_target) = dep
                .assignments
                .iter()
                .find(|(_, key, _)| model.host_knows(host, key))?
                .clone();
            let _ = akey;
            let live = model.live_agents();
            let candidates: Vec<usize> = live
                .into_iter()
                .filter(|&t| t != prev_target && model.host_sees_agent(host, t))
                .collect();
            let t = pick(&candidates, s1)?;
            Some(Act {
                agent: requester,
                data: EventData::DependencyReassigned(DependencyReassigned {
                    dependency: dep.id.clone(),
                    previous_assignment: aid.clone(),
                    previous_target: model.agents[prev_target].name.clone(),
                    new_target: model.agents[t].name.clone(),
                    reason: text_of("proptest reassignment"),
                }),
                record: Record {
                    dep_reassign: Some((i, t)),
                    claim: Some((claim_key("dependency", &aid), aid.clone(), dep.key)),
                    ..Default::default()
                },
            })
        }
        // ------------------------------------------------------------ handoffs
        "handoff.offered" => {
            let impls = model.live_agents_with_role(Role::Implementor);
            let a = pick(&impls, s0)?;
            let live = model.live_agents();
            let receivers: Vec<usize> = live
                .into_iter()
                .filter(|&r| r != a && model.host_sees_agent(model.agents[a].host, r))
                .collect();
            let r = pick(&receivers, s1)?;
            Some(Act {
                agent: a,
                data: EventData::HandoffOffered(HandoffOffered {
                    receiver: model.agents[r].name.clone(),
                    scope: StringSet::from_iter([path_claim("src/one/**")]),
                    product_branch: branch_for(&model.agents[a].name),
                    product_commit: exec.head_commit(model.agents[a].host),
                    verification: vec![],
                    known_issues: StringSet::default(),
                    evidence: StringSet::default(),
                    summary: text_of("proptest handoff"),
                }),
                record: Record {
                    new_handoff: Some(r),
                    ..Default::default()
                },
            })
        }
        "handoff.accepted" | "handoff.declined" | "handoff.withdrawn" => {
            let open: Vec<usize> = (0..model.handoffs.len())
                .filter(|&i| !model.handoffs[i].terminal)
                .collect();
            let i = pick(&open, s0)?;
            let h = &model.handoffs[i];
            let receiver = h.assignments[0].2;
            // A withdrawal comes from the offerer; the other two from the
            // receiver. Both may be concurrent with each other, which is the
            // handoff race.
            let actor = if kind == "handoff.withdrawn" {
                h.author
            } else {
                receiver
            };
            if model.agents[actor].retired || !model.host_knows(model.agents[actor].host, &h.key) {
                return None;
            }
            let data = match kind {
                "handoff.accepted" => EventData::HandoffAccepted(HandoffAccepted {
                    handoff: h.id.clone(),
                    note: text_of("proptest accept"),
                }),
                "handoff.declined" => EventData::HandoffDeclined(HandoffDeclined {
                    handoff: h.id.clone(),
                    reason: text_of("proptest decline"),
                }),
                _ => EventData::HandoffWithdrawn(HandoffWithdrawn {
                    handoff: h.id.clone(),
                    reason: text_of("proptest withdrawal"),
                }),
            };
            Some(Act {
                agent: actor,
                data,
                record: Record {
                    handoff_terminal: Some(i),
                    claim: Some((claim_key("handoff", &h.id), h.id.clone(), h.key)),
                    ..Default::default()
                },
            })
        }
        // ------------------------------------------------------------- reviews
        "review.nominated" => {
            let impls = model.live_agents_with_role(Role::Implementor);
            let reviewers = model.live_agents_with_role(Role::Reviewer);
            let a = pick(&impls, s0)?;
            let host = model.agents[a].host;
            let rv = pick(
                &reviewers
                    .iter()
                    .copied()
                    .filter(|&r| model.host_sees_agent(host, r))
                    .collect::<Vec<_>>(),
                s1,
            )?;
            // A second author, when one is visible: two authors is what makes
            // two concurrent reassignments of one nomination possible at all.
            let mut authors = vec![a];
            if let Some(&other) = impls
                .iter()
                .find(|&&o| o != a && o != rv && model.host_sees_agent(host, o))
            {
                if flag {
                    authors.push(other);
                }
            }
            let request = ReviewRequest {
                authors: StringSet::from_iter(
                    authors.iter().map(|&i| model.agents[i].name.clone()),
                ),
                product_branch: branch_for(&model.agents[a].name),
                reviewer: model.agents[rv].name.clone(),
                required_checks: vec![],
                review_scope: StringSet::from_iter([path_claim("src/one/**")]),
                summary: text_of("proptest nomination"),
                target_branch: Branch::parse("refs/heads/main".to_string())
                    .expect("refs/heads/main is a valid branch"),
                evidence: StringSet::default(),
            };
            Some(Act {
                agent: a,
                data: EventData::ReviewNominated(request.clone()),
                record: Record {
                    new_review: Some(ReviewSeed {
                        authors,
                        reviewer: rv,
                        request,
                    }),
                    ..Default::default()
                },
            })
        }
        "review.nomination_accepted" | "review.nomination_declined" => {
            let r = pick(&open_reviews(model), s0)?;
            let review = &model.reviews[r];
            // Any link, not merely the newest: a reviewer accepting a link a
            // concurrent reassignment has already superseded is the exact
            // shape that used to be answered with a fleet-wide `Err`.
            let links: Vec<usize> = (0..review.links.len())
                .filter(|&i| {
                    let (id, key, rv) = &review.links[i];
                    !model.agents[*rv].retired
                        && model.host_knows(model.agents[*rv].host, key)
                        && (kind != "review.nomination_accepted" || !review.accepted.contains(id))
                })
                .collect();
            let li = pick(&links, s1)?;
            let (id, key, rv) = review.links[li].clone();
            let data = if kind == "review.nomination_accepted" {
                EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                    nomination: id.clone(),
                    note: text_of("proptest acceptance"),
                })
            } else {
                EventData::ReviewNominationDeclined(ReviewNominationDeclined {
                    nomination: id.clone(),
                    reason: text_of("proptest decline"),
                })
            };
            let declining = kind == "review.nomination_declined";
            Some(Act {
                agent: rv,
                data,
                record: Record {
                    review_accept: (!declining).then(|| (r, id.clone())),
                    review_close: declining.then_some(r),
                    claim: declining.then(|| (claim_key("review", &id), id.clone(), key)),
                    ..Default::default()
                },
            })
        }
        "review.withdrawn" => {
            let r = pick(&open_reviews(model), s0)?;
            let review = &model.reviews[r];
            let authors = review.seed.authors.clone();
            let a = pick(&authors, s1)?;
            if model.agents[a].retired {
                return None;
            }
            let host = model.agents[a].host;
            let links: Vec<usize> = (0..review.links.len())
                .filter(|&i| model.host_knows(host, &review.links[i].1))
                .collect();
            let li = pick(&links, s2)?;
            let (id, key, _) = review.links[li].clone();
            Some(Act {
                agent: a,
                data: EventData::ReviewWithdrawn(ReviewWithdrawn {
                    nomination: id.clone(),
                    reason: text_of("proptest withdrawal"),
                }),
                record: Record {
                    review_close: Some(r),
                    claim: Some((claim_key("review", &id), id.clone(), key)),
                    ..Default::default()
                },
            })
        }
        "review.changes_requested" => {
            let r = pick(&open_reviews(model), s0)?;
            let review = &model.reviews[r];
            // Filed against a link this reviewer accepted -- including one a
            // concurrent reassignment may already have superseded, which is
            // precisely the pairing that made a *different* reviewer's
            // honest authorization fatal.
            let links: Vec<usize> = (0..review.links.len())
                .filter(|&i| {
                    let (id, key, rv) = &review.links[i];
                    review.accepted.contains(id)
                        && !model.agents[*rv].retired
                        && model.host_knows(model.agents[*rv].host, key)
                })
                .collect();
            let li = pick(&links, s1)?;
            let (id, _, rv) = review.links[li].clone();
            let finding_id = short(if flag { "f1" } else { "f2" });
            Some(Act {
                agent: rv,
                data: EventData::ReviewChangesRequested(ReviewChangesRequested {
                    nomination: id,
                    reviewed_commit: exec.head_commit(model.agents[rv].host),
                    findings: vec![Finding {
                        id: finding_id.clone(),
                        priority: Priority::Normal,
                        locations: vec![],
                        rationale: text_of("proptest finding"),
                        closure_conditions: text_of("fix it"),
                    }],
                    evidence: StringSet::default(),
                }),
                record: Record {
                    review_finding: Some((r, finding_id)),
                    ..Default::default()
                },
            })
        }
        "review.findings_cleared" | "review.findings_superseded" => {
            let r = pick(&open_reviews(model), s0)?;
            let review = &model.reviews[r];
            let open: Vec<usize> = (0..review.findings.len())
                .filter(|&i| {
                    let (ce, _, fid) = &review.findings[i];
                    !review
                        .disposed
                        .contains(&(ce.clone(), fid.as_str().to_string()))
                })
                .collect();
            let fi = pick(&open, s1)?;
            let (changes, changes_key, finding_id) = review.findings[fi].clone();
            // Only the reviewer of the link the finding was filed against
            // may dispose of it.
            let (nom_id, _, rv) = review
                .links
                .iter()
                .find(|(id, _, _)| *id == nomination_of(model, r, &changes))
                .cloned()
                .or_else(|| review.links.last().cloned())?;
            if model.agents[rv].retired || !model.host_knows(model.agents[rv].host, &changes_key) {
                return None;
            }
            let data = if kind == "review.findings_cleared" {
                EventData::ReviewFindingsCleared(ReviewFindingsCleared {
                    nomination: nom_id,
                    changes_event: changes.clone(),
                    finding_id: finding_id.clone(),
                    resolved_commit: exec.head_commit(model.agents[rv].host),
                    summary: text_of("proptest clearance"),
                })
            } else {
                EventData::ReviewFindingsSuperseded(ReviewFindingsSuperseded {
                    nomination: nom_id,
                    changes_event: changes.clone(),
                    finding_id: finding_id.clone(),
                    rationale: text_of("proptest supersession"),
                })
            };
            Some(Act {
                agent: rv,
                data,
                record: Record {
                    review_dispose: Some((r, changes, finding_id.as_str().to_string())),
                    ..Default::default()
                },
            })
        }
        "review.reassigned" => {
            let r = pick(&open_reviews(model), s0)?;
            let review = &model.reviews[r];
            let a = pick(&review.seed.authors.clone(), s1)?;
            if model.agents[a].retired {
                return None;
            }
            let host = model.agents[a].host;
            // The *oldest* link this author can see, not the newest. Two
            // authors each replacing the same link, each honestly naming the
            // link they knew, is what forms the contested group -- and when
            // they independently reach for the same replacement reviewer
            // (which round-robin nomination makes the expected outcome, not
            // a coincidence) it used to be refused in both orders.
            let (replaces, replaces_key, replaced_reviewer) = review
                .links
                .iter()
                .find(|(_, key, _)| model.host_knows(host, key))?
                .clone();
            let reviewers: Vec<usize> = model
                .live_agents_with_role(Role::Reviewer)
                .into_iter()
                .filter(|&rv| {
                    rv != replaced_reviewer
                        && !review.seed.authors.contains(&rv)
                        && model.host_sees_agent(host, rv)
                })
                .collect();
            // Deliberately the *first* such reviewer half the time: two
            // authors picking deterministically is how they collide.
            let rv = if flag {
                reviewers.first().copied()?
            } else {
                pick(&reviewers, s2)?
            };
            let mut request = review.seed.request.clone();
            request.reviewer = model.agents[rv].name.clone();
            let inherited: Vec<FindingRef> = review
                .findings
                .iter()
                .filter(|(ce, _, fid)| {
                    !review
                        .disposed
                        .contains(&(ce.clone(), fid.as_str().to_string()))
                        && model.host_knows(host, &find_key(review, ce))
                })
                .map(|(ce, _, fid)| FindingRef {
                    changes_event: ce.clone(),
                    finding_id: fid.clone(),
                })
                .collect();
            Some(Act {
                agent: a,
                data: EventData::ReviewReassigned(ReviewReassigned {
                    authors: request.authors.clone(),
                    product_branch: request.product_branch.clone(),
                    reviewer: request.reviewer.clone(),
                    required_checks: request.required_checks.clone(),
                    review_scope: request.review_scope.clone(),
                    summary: request.summary.clone(),
                    target_branch: request.target_branch.clone(),
                    evidence: request.evidence.clone(),
                    replaces: replaces.clone(),
                    reason: text_of("proptest reassignment"),
                    inherited_findings: inherited,
                }),
                record: Record {
                    review_link: Some((r, rv)),
                    claim: Some((claim_key("review", &replaces), replaces, replaces_key)),
                    ..Default::default()
                },
            })
        }
        // ------------------------------------------------ conflict resolution
        "lifecycle.conflict_resolved" => {
            let coords = model.live_agents_with_role(Role::Coordinator);
            let c = pick(&coords, s0)?;
            let host = model.agents[c].host;
            // Only a genuinely contested group is worth resolving, and a
            // group that another coordinator has *already* resolved is worth
            // resolving again: two coordinators settling one visible race is
            // routine under succession, and used to wedge the bus in both
            // orders.
            let keys: Vec<String> = model
                .claims
                .iter()
                .filter(|(_, group)| {
                    group.members.len() >= 2
                        && model.host_knows(host, &group.root_key)
                        && group.members.iter().all(|(_, k)| model.host_knows(host, k))
                })
                .map(|(k, _)| k.clone())
                .collect();
            let ki = s1.try_pick(keys.len())?;
            let key = keys[ki].clone();
            let group = model.claims.get(&key)?.clone();
            let (root, members) = (group.root, group.members);
            let selected = members[s2.pick(members.len())].0.clone();
            Some(Act {
                agent: c,
                data: EventData::LifecycleConflictResolved(LifecycleConflictResolved {
                    root,
                    competing: StringSet::from_iter(members.iter().map(|(id, _)| id.clone())),
                    selected,
                    reason: text_of("proptest resolution"),
                    user_authority: text_of("proptest operator"),
                }),
                record: Record {
                    resolve_claim: Some(key),
                    blur_issues: (0..model.issues.len()).collect(),
                    blur_agents: vec![],
                    ..Default::default()
                },
            })
        }
        // ------------------------------------------------------------ friction
        "friction.reported" => {
            let live = model.live_agents();
            let a = pick(&live, s0)?;
            Some(Act {
                agent: a,
                data: EventData::FrictionReported(FrictionReported {
                    area: topic("bus.contention"),
                    summary: short("proptest friction"),
                    impact: Impact::Coordination,
                    evidence: StringSet::default(),
                    product_locations: vec![],
                    // Empty: a report carrying measurements must cite
                    // evidence, and the evidence would have to be an id this
                    // checkout can see, which is a different property.
                    measurements: Vec::<Measurement>::new(),
                    frequency: None,
                    workaround: None,
                    suggestion: None,
                    likely_owner: None,
                }),
                record: Record {
                    friction_report: true,
                    ..Default::default()
                },
            })
        }
        "friction.synthesized" => {
            let live = model.live_agents();
            let a = pick(&live, s0)?;
            let host = model.agents[a].host;
            let visible: Vec<usize> = (0..model.friction_reports.len())
                .filter(|&i| model.host_knows(host, &model.friction_reports[i].1))
                .collect();
            if visible.is_empty() {
                return None;
            }
            let ri = s1.pick(visible.len());
            let report = model.friction_reports[visible[ri]].0.clone();
            Some(Act {
                agent: a,
                data: EventData::FrictionSynthesized(FrictionSynthesized {
                    theme: topic("bus.contention"),
                    reports: StringSet::from_iter([report]),
                    disposition: if flag {
                        FrictionDispositionKind::AcceptedCost
                    } else {
                        FrictionDispositionKind::NeedsEvidence
                    },
                    rationale: text_of("proptest synthesis"),
                    promoted_to: None,
                    duplicate_of: None,
                    revisit_trigger: None,
                }),
                record: Record {
                    friction_synthesis: true,
                    ..Default::default()
                },
            })
        }
        // ---------------------------------------------------------- broadcasts
        "broadcast.published" => {
            let live = model.live_agents();
            let a = pick(&live, s0)?;
            let host = model.agents[a].host;
            let epoch_id = exec.epoch_id(host)?;
            // An explicit list resolves against the pinned epoch alone, so
            // the claimed snapshot is exactly the members of that list this
            // host's epoch still lists -- computable here without racing
            // anybody's `subscription.set`.
            let epoch = model.hosts[host].epoch?;
            let audience: Vec<usize> = model.epochs[epoch].iter().copied().collect();
            if audience.is_empty() {
                return None;
            }
            Some(Act {
                agent: a,
                data: EventData::BroadcastPublished(BroadcastPublished {
                    topics: StringSet::from_iter([topic("bus.contention")]),
                    importance: Importance::Informational,
                    summary: short("proptest broadcast"),
                    detail: text_of("proptest detail"),
                    affected_paths: StringSet::default(),
                    affected_interfaces: StringSet::default(),
                    product_commits: StringSet::default(),
                    audience_selector: AudienceSelector::Agents(StringSet::from_iter(
                        audience.iter().map(|&i| model.agents[i].name.clone()),
                    )),
                    audience_epoch: epoch_id,
                    audience_snapshot: StringSet::from_iter(
                        audience.iter().map(|&i| model.agents[i].name.clone()),
                    ),
                    acknowledgement: if flag {
                        AckRequirement::Required
                    } else {
                        AckRequirement::None
                    },
                    deadline: None,
                    supersedes: StringSet::default(),
                    workaround: None,
                    expiry_condition: None,
                }),
                record: Record {
                    broadcast: Some((flag, audience)),
                    ..Default::default()
                },
            })
        }
        "broadcast.acknowledged" | "broadcast.seen" => {
            let want_ack = kind == "broadcast.acknowledged";
            let candidates: Vec<usize> = (0..model.broadcasts.len())
                .filter(|&i| !want_ack || model.broadcasts[i].ack_required)
                .collect();
            let bi = pick(&candidates, s0)?;
            let b = &model.broadcasts[bi];
            let addressees: Vec<usize> = b
                .audience
                .iter()
                .copied()
                .filter(|&a| {
                    !model.agents[a].retired
                        && !model.agents[a].status.deactivates()
                        && model.host_knows(model.agents[a].host, &b.key)
                })
                .collect();
            let a = pick(&addressees, s1)?;
            let data = if want_ack {
                EventData::BroadcastAcknowledged(BroadcastAcknowledged {
                    broadcasts: StringSet::from_iter([b.id.clone()]),
                })
            } else {
                EventData::BroadcastSeen(BroadcastSeen {
                    broadcasts: StringSet::from_iter([b.id.clone()]),
                })
            };
            Some(Act {
                agent: a,
                data,
                record: Record::default(),
            })
        }
        // --------------------------------------------------------------- audit
        "audit.reported" => {
            let auditors = model.live_agents_with_role(Role::Auditor);
            let a = pick(&auditors, s0)?;
            let host = model.agents[a].host;
            // A complete frontier names *every* active member, so it can
            // only be built where every one of them has published a stream
            // this checkout can see.
            let epoch = model.hosts[host].epoch?;
            if !model.epochs[epoch]
                .iter()
                .all(|&m| model.host_knows(host, &EventKey { agent: m, seq: 0 }))
            {
                return None;
            }
            let issues: Vec<EventId> = model
                .issues
                .iter()
                .filter(|i| model.host_knows(host, &i.opened))
                .map(|i| i.id.clone())
                .take(if flag { 1 } else { 0 })
                .collect();
            Some(Act {
                agent: a,
                data: EventData::AuditReported(AuditReported {
                    inspected_commits: StringSet::default(),
                    areas: vec![text_of("coordination history")],
                    methods: vec![text_of("read the streams")],
                    limitations: vec![],
                    issues: StringSet::from_iter(issues),
                    summary: text_of("proptest audit"),
                }),
                record: Record::default(),
            })
        }
        other => unreachable!("ACT_KINDS contains an unhandled kind: {other}"),
    }
}

/// Review chains the model believes are still open to further events.
fn open_reviews(model: &Model) -> Vec<usize> {
    (0..model.reviews.len())
        .filter(|&i| !model.reviews[i].closed)
        .collect()
}

/// Which nomination link a `review.changes_requested` was filed against, as
/// far as the model recorded it. Falls back to the chain's newest link,
/// which is what a real reviewer would name.
fn nomination_of(model: &Model, review: usize, changes: &EventId) -> EventId {
    let r = &model.reviews[review];
    let _ = changes;
    r.links
        .last()
        .map(|(id, _, _)| id.clone())
        .unwrap_or_else(|| r.root.clone())
}

/// The [`EventKey`] of a `review.changes_requested` the model recorded.
fn find_key(review: &ReviewModel, changes: &EventId) -> EventKey {
    review
        .findings
        .iter()
        .find(|(ce, _, _)| ce == changes)
        .map(|(_, k, _)| *k)
        .unwrap_or(review.root_key)
}

/// Resolves an `EventId` the model produced back to its [`EventKey`], so a
/// payload can be checked against what the acting checkout actually holds.
fn event_key_of(model: &Model, id: &EventId) -> Option<EventKey> {
    let agent = model.agent_by_name(&id.agent())?;
    Some(EventKey {
        agent,
        seq: id.seq(),
    })
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
    /// deterministic, and shared by every call in this checkout. Using a
    /// fresh scratch directory per operation instead would quietly step
    /// around the worktree-cache staleness bug this harness exists to catch.
    fn common_dir(&self) -> PathBuf {
        self.dir.path().join(".git")
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
/// ordinary commit (so genesis's `product_review_from` resolves) and
/// `origin` pointed at the shared bare repository.
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

/// The executor that owns real repositories: performs each operation with
/// the same library calls `cli.rs` uses, in the same order, and runs the
/// per-operation half of the invariant sweep afterwards.
struct GitExec {
    fleet: Fleet,
    trace: bool,
    /// Every kind that actually *published* during this run.
    ///
    /// Constructibility is not coverage: a payload builder that always
    /// produces something the coordinator then refuses would satisfy
    /// [`every_generated_kind_is_constructible`] while landing nothing in
    /// any stream. This is what
    /// [`a_hand_written_schedule_really_publishes_the_alphabet`] holds to
    /// account.
    census: BTreeSet<&'static str>,
}

impl Exec for GitExec {
    fn head_commit(&self, host: usize) -> ObjectId {
        let h = &self.fleet.hosts[host];
        let raw = crate::gitrepo::rev_parse(h.repo(), "HEAD").expect("every checkout has a HEAD");
        ObjectId::parse(raw).expect("rev-parse HEAD is a full object id")
    }

    fn epoch_id(&self, host: usize) -> Option<ObjectId> {
        let h = self.fleet.hosts.get(host)?;
        crate::registry::read_registry_tip(h.repo()).ok().flatten()
    }

    fn run(&mut self, model: &Model, op: &Op, step: usize) -> Result<Landed, TestCaseError> {
        let t0 = std::time::Instant::now();
        let landed = materialize_op(&mut self.fleet, model, op, step)?;
        if landed {
            if let Some(kind) = published_kind(op) {
                self.census.insert(kind);
            }
        }
        if self.trace {
            eprintln!(
                "  step {step}: {} landed={landed} run={:?}",
                op_label(op),
                t0.elapsed()
            );
        }
        Ok(landed)
    }

    fn check(&mut self, model: &Model, op: &Op, step: usize) -> Result<(), TestCaseError> {
        let touched = touched_host(model, op);
        check_hosts(
            &self.fleet,
            model,
            &format!("step {step} ({})", op_label(op)),
            &[touched],
            Depth::RefsOnly,
        )
    }
}

/// The event kind an operation publishes, if it publishes one at all.
fn published_kind(op: &Op) -> Option<&'static str> {
    Some(match op {
        Op::Genesis { .. } | Op::Register { .. } => "agent.registered",
        Op::Status { .. } => "agent.status",
        Op::OpenIssue { .. } => "issue.opened",
        Op::ResolveIssue { .. } => "issue.resolved",
        Op::ReassignIssue { .. } => "issue.reassigned",
        Op::AckIssue { .. } => "issue.acknowledged",
        Op::Act { kind, .. } => kind,
        Op::AddHost | Op::Sync { .. } | Op::Flush { .. } => return None,
    })
}

/// A one-line name for an operation. `Op::Act` carries a whole `EventData`,
/// whose `Debug` runs to hundreds of characters and would otherwise be
/// formatted into the label of every single invariant assertion.
fn op_label(op: &Op) -> String {
    match op {
        Op::Act {
            agent, kind, defer, ..
        } => {
            format!("Act {{ agent: {agent}, kind: {kind}, defer: {defer} }}")
        }
        other => format!("{other:?}"),
    }
}

/// Runs one operation against the real repositories. `model` is the state
/// *before* the operation, so expected sequence numbers can be asserted
/// against what the coordinator actually published. Returns whether the
/// operation published anything.
fn materialize_op(
    fleet: &mut Fleet,
    model: &Model,
    op: &Op,
    step: usize,
) -> Result<Landed, TestCaseError> {
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
            let snap = crate::sync::synced_snapshot(h.repo(), &h.common_dir(), "origin")
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
        Op::Flush { host } => {
            for a in &model.agents {
                if a.host == *host && !a.unpushed.is_empty() {
                    let h = &fleet.hosts[*host];
                    let receipt =
                        crate::coordinator::publish_stream(h.repo(), "origin", &a.name)
                            .map_err(|e| fail(&format!("flush {} on host{host}", a.name), e))?;
                    prop_assert!(
                        receipt
                            .published
                            .contains_key(crate::stream::stream_ref(&a.name).as_str()),
                        "step {}: a deferred publication for {} did not reach origin: {:?}",
                        step,
                        a.name,
                        receipt
                    );
                }
            }
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
            let epoch = crate::registry::read_epoch(h.repo(), &tip)
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
            let new_epoch = crate::registry::propose_transition(h.repo(), &epoch, members)
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
            drain_strict(fleet, *host, name, &candidate, 0, step, "register")?;

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
            drain_strict(
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
            // and `Envelope::parse_line` insists `refs` equal exactly what
            // the data references -- so this is the only way to carry a real
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
            drain_strict(
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
            drain_strict(
                fleet,
                host,
                &name,
                &candidate,
                model.next_seq(issue.target),
                step,
                "issue.resolved",
            )?;
        }
        Op::ReassignIssue { issue, new_target } => {
            let issue = &model.issues[*issue];
            let (prev_id, _, prev_target) = issue
                .assignments
                .last()
                .expect("an issue always has at least its opening assignment")
                .clone();
            let name = model.agents[issue.opener].name.clone();
            let host = model.agents[issue.opener].host;
            let candidate = Candidate::new(
                &name,
                &EventData::IssueReassigned(IssueReassigned {
                    issue: issue.id.clone(),
                    previous_assignment: prev_id.clone(),
                    previous_target: model.agents[prev_target].name.clone(),
                    new_target: model.agents[*new_target].name.clone(),
                    reason: text("proptest reassignment"),
                }),
                vec![issue.id.clone(), prev_id],
            );
            drain_strict(
                fleet,
                host,
                &name,
                &candidate,
                model.next_seq(issue.opener),
                step,
                "issue.reassigned",
            )?;
        }
        Op::AckIssue { issue, assignment } => {
            let issue = &model.issues[*issue];
            let (assignment_id, _, acker) = issue.assignments[*assignment].clone();
            let name = model.agents[acker].name.clone();
            let host = model.agents[acker].host;
            let candidate = Candidate::new(
                &name,
                &EventData::IssueAcknowledged(IssueAcknowledged {
                    issue: issue.id.clone(),
                    assignment: assignment_id.clone(),
                    note: text("proptest acknowledgement"),
                }),
                vec![issue.id.clone(), assignment_id],
            );
            drain_strict(
                fleet,
                host,
                &name,
                &candidate,
                model.next_seq(acker),
                step,
                "issue.acknowledged",
            )?;
        }
        Op::Act {
            agent,
            kind,
            data,
            defer,
            ..
        } => {
            let name = model.agents[*agent].name.clone();
            let host = model.agents[*agent].host;
            let candidate = Candidate::new(&name, data, vec![]);
            return drain_tolerant(
                fleet,
                host,
                &name,
                &candidate,
                model.next_seq(*agent),
                step,
                kind,
                *defer,
            );
        }
    }
    Ok(true)
}

/// Submits exactly one candidate and drains it, asserting the coordinator
/// accepted it at the sequence the oracle predicted.
///
/// One candidate per drain on purpose: `outbox::list_pending` breaks ties by
/// filesystem modified time, whose resolution is coarse enough that two
/// candidates submitted in the same instant would have an unspecified
/// relative order -- nondeterminism this harness would rather not import.
///
/// A rejection here is itself an invariant violation, and that is what makes
/// this the *strict* path: these operations are the precisely-modelled ones,
/// emitted only when the model says their preconditions hold on this very
/// checkout, so `drain_outbox` refusing one means either a real defect or a
/// divergence between the model and the implementation. The generic
/// [`drain_tolerant`] path is the one that treats a rejection as ordinary.
fn drain_strict(
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
        "origin",
    )
    .map_err(|e| fail(&format!("drain_and_publish {what}"), e))?;
    prop_assert!(
        drained.rejected.is_empty(),
        "step {step}: {what} for {name} on host{host} was rejected, but the driver only emits \
         these candidates when their preconditions hold on this very checkout: {:?}",
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

/// Submits one generated candidate and drains it, accepting either outcome.
///
/// This is the layering the whole module is built around. `drain_outbox` and
/// its `verify_*` gates are *entitled* to refuse a candidate: a rejection is
/// per-candidate, writes a durable receipt, and costs one author a retry. So
/// a refusal here is recorded and the model simply does not advance that
/// agent's sequence. What is not tolerated is the other side of the
/// boundary -- an event that was accepted and published, and that reduction
/// then cannot replay -- and that is checked everywhere else.
///
/// `defer` holds the resulting stream commit back from origin instead of
/// pushing it, which is the real window a fleet has between a coordinator
/// committing locally and its push landing, and the only way to race a kind
/// whose own drain fetches first.
#[allow(clippy::too_many_arguments)]
fn drain_tolerant(
    fleet: &Fleet,
    host: usize,
    name: &Agent,
    candidate: &Candidate,
    expected_seq: u64,
    step: usize,
    what: &str,
    defer: bool,
) -> Result<Landed, TestCaseError> {
    let h = &fleet.hosts[host];
    let client_id = format!("proptest-{step}");
    crate::outbox::submit(&h.common_dir(), &client_id, candidate)
        .map_err(|e| fail(&format!("submit {what}"), e))?;
    let drained =
        crate::coordinator::drain_outbox(h.repo(), &h.common_dir(), name, &h.name, 0, "origin")
            .map_err(|e| fail(&format!("drain_outbox {what}"), e))?;
    prop_assert!(
        drained.published.len() + drained.rejected.len() == 1,
        "step {step}: exactly one candidate was submitted, so exactly one verdict is expected, \
         got {drained:?}"
    );
    if drained.published.is_empty() {
        return Ok(false);
    }
    prop_assert_eq!(
        &drained.published,
        &vec![EventId::new(name, expected_seq)],
        "step {}: {} for {} published at an unexpected sequence",
        step,
        what,
        name
    );
    if !defer {
        let receipt = crate::coordinator::publish_stream(h.repo(), "origin", name)
            .map_err(|e| fail(&format!("publish_stream {what}"), e))?;
        prop_assert!(
            receipt
                .published
                .contains_key(crate::stream::stream_ref(name).as_str()),
            "step {step}: {what} for {name} did not reach origin: {:?}",
            receipt
        );
    }
    Ok(true)
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
/// examined -- sweeping only the acting checkout after each operation costs
/// a fraction of a full sweep and misses nothing. [`run_world`] still sweeps
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

        let snapshot = crate::sync::cached_snapshot(h.repo(), &h.common_dir());
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
        // this is the totality half of the property, asked of every host at
        // whatever stale or current view the schedule left it at.
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
                let name = a.as_str().to_string();
                let predicted = expected.agents.get(&name);
                (
                    name,
                    ExpectedAgent {
                        next_seq: s.next_seq,
                        role: s.primary_role,
                        // Compared only where the model still predicts it;
                        // see `ExpectedAgent::status`.
                        status: predicted.and_then(|p| p.status.is_some().then_some(s.status)),
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
                let key = id.as_str().to_string();
                let predicted = expected.issues.get(&key);
                (
                    key,
                    ExpectedIssue {
                        opener: s.opener.as_str().to_string(),
                        target: predicted
                            .is_some_and(|p| p.target.is_some())
                            .then(|| s.current_target.as_str().to_string()),
                        status: predicted.and_then(|p| {
                            p.status.is_some().then_some(match s.status {
                                ItemStatus::Terminal(l) => l,
                                ItemStatus::Open => "open",
                                ItemStatus::LifecycleConflict => "conflict",
                            })
                        }),
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

/// How much of the sweep to run. A full reduction is by far the most
/// expensive thing this harness does -- it is what `coordinator::
/// drain_outbox` itself pays on every publication -- so it is spent where it
/// buys something: at the end of the schedule, when each checkout is sitting
/// at whatever stale or current view the schedule actually left it at.
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

/// Which checkout's repository an operation actually writes to -- the only
/// one whose invariants can have changed as a result. `model` is the state
/// *after* the operation, so an `AddHost` names the checkout it just made.
fn touched_host(model: &Model, op: &Op) -> usize {
    match op {
        Op::AddHost => model.hosts.len() - 1,
        Op::Sync { host } | Op::Flush { host } | Op::Genesis { host, .. } => *host,
        Op::Register { host, .. } => *host,
        Op::Status { agent, .. } => model.agents[*agent].host,
        Op::Act { agent, .. } => model.agents[*agent].host,
        Op::OpenIssue { opener, .. } => model.agents[*opener].host,
        Op::ResolveIssue { issue } => model.agents[model.issues[*issue].target].host,
        Op::ReassignIssue { issue, .. } => model.agents[model.issues[*issue].opener].host,
        Op::AckIssue { issue, assignment } => {
            model.agents[model.issues[*issue].assignments[*assignment].2].host
        }
    }
}

/// The convergence invariant (gate 16), checked once the whole schedule has
/// run: bring every checkout to the same point and assert they agree
/// *exactly*, using the same `Debug`-equality convention `apply.rs`'s
/// `cold_replay_and_incremental_replay_produce_identical_state` established.
///
/// Every checkout reaches this point differently -- one authored much of the
/// history locally and never fetched it back, one has been fetching all
/// along, one may have been created cold moments ago and has replayed
/// everything from scratch in a single pass. Byte-identical reduced state
/// across all of them is the property that makes the bus's "reduce anywhere"
/// claim mean anything.
fn check_convergence(fleet: &Fleet, model: &mut Model) -> Result<(), TestCaseError> {
    let mut reference: Option<(usize, String)> = None;
    for i in 0..fleet.hosts.len() {
        let h = &fleet.hosts[i];
        let snap = crate::sync::synced_snapshot(h.repo(), &h.common_dir(), "origin")
            .map_err(|e| fail(&format!("final sync on host{i}"), e))?;
        model.apply(&Op::Sync { host: i }, true);
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
    // agree" cannot be satisfied by all of them being wrong together. One
    // full reduction is enough to pin it: the pairwise equality above
    // already proves every other checkout reduced to exactly the same thing.
    check_hosts(
        fleet,
        model,
        "after the final fleet-wide synchronization",
        &[0],
        Depth::Full,
    )
}

// ------------------------------------------------- totality and confluence

/// A tiny deterministic generator, so a shuffled order is reproducible from
/// the seed the counterexample prints. Not cryptographic and not meant to
/// be: it only has to be different from run to run and identical given the
/// same seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// One randomly chosen linear extension of the causal partial order over
/// `streams` -- i.e. one of the orders a real host genuinely reaches after
/// fetching in some particular sequence.
///
/// The edges are exactly the ones `apply::topological_order` builds, and
/// they are worth naming because the module's own doc used to get this
/// wrong: an edge comes from each stream's own predecessor and from
/// `e.refs`, **never** from `env.observed`. An event is therefore routinely
/// replayed *before* the very event its frontier says it saw, which is why
/// no reduction rule may ask a causal question of `observed` -- and why this
/// function is a faithful model of what hosts really do rather than an
/// artificial stress.
///
/// The one non-`refs` rule reproduced here is the seq-0 tier: every agent's
/// own `agent.registered` is preferred over every later event, because most
/// kinds name another agent by identity without that agent's registration
/// appearing in `referenced_ids()`. `topological_order` has the same
/// exception for the same reason.
fn random_linear_extension<'a>(
    streams: &'a BTreeMap<Agent, Vec<crate::envelope::Envelope>>,
    rng: &mut Rng,
) -> Vec<&'a crate::envelope::Envelope> {
    let mut by_id: BTreeMap<EventId, &crate::envelope::Envelope> = BTreeMap::new();
    for events in streams.values() {
        for e in events {
            by_id.insert(e.id.clone(), e);
        }
    }
    let mut indegree: BTreeMap<EventId, usize> = by_id.keys().map(|k| (k.clone(), 0)).collect();
    let mut dependents: BTreeMap<EventId, Vec<EventId>> = BTreeMap::new();
    let mut edge = |from: EventId, to: EventId, indegree: &mut BTreeMap<EventId, usize>| {
        dependents.entry(from).or_default().push(to.clone());
        *indegree.get_mut(&to).expect("every node is present") += 1;
    };
    for (agent, events) in streams {
        for e in events {
            if e.seq > 0 {
                let prev = EventId::new(agent, e.seq - 1);
                if by_id.contains_key(&prev) {
                    edge(prev, e.id.clone(), &mut indegree);
                }
            }
            for r in e.refs.iter() {
                // A dangling reference is not an edge: an event may name an
                // id that does not exist yet, and reduction tolerates it.
                if r != &e.id && by_id.contains_key(r) {
                    edge(r.clone(), e.id.clone(), &mut indegree);
                }
            }
        }
    }

    let mut ready: Vec<EventId> = indegree
        .iter()
        .filter(|(_, &d)| d == 0)
        .map(|(k, _)| k.clone())
        .collect();
    let mut order = Vec::with_capacity(by_id.len());
    let mut done: BTreeSet<EventId> = BTreeSet::new();
    while order.len() < by_id.len() {
        if ready.is_empty() {
            // A cycle. `topological_order` breaks it by the smallest
            // remaining `EventId`, which is a pure function of the remaining
            // set, so this does the same rather than inventing a second
            // answer.
            let Some(next) = indegree.keys().find(|k| !done.contains(*k)).cloned() else {
                break;
            };
            ready.push(next);
        }
        // Every agent's own registration first, exactly as
        // `topological_order` does.
        let pos = ready
            .iter()
            .position(|id| id.seq() == 0)
            .unwrap_or_else(|| rng.below(ready.len()));
        let id = ready.swap_remove(pos);
        if !done.insert(id.clone()) {
            continue;
        }
        order.push(by_id[&id]);
        if let Some(next) = dependents.get(&id) {
            for n in next.clone() {
                let d = indegree.get_mut(&n).expect("every node is present");
                *d -= 1;
                if *d == 0 && !done.contains(&n) {
                    ready.push(n);
                }
            }
        }
    }
    order
}

/// Where two renderings of a `BusState` first disagree, with enough context
/// on either side to name the field.
///
/// A whole reduced `BusState` is tens of kilobytes, and printing two of them
/// side by side answers "they differ" without ever answering "where" -- so a
/// confluence failure would arrive as a wall of text nobody can act on. This
/// finds the divergence point and shows only its neighbourhood, which is the
/// difference between a report and a diagnosis.
fn first_difference(a: &str, b: &str) -> String {
    let at = a
        .bytes()
        .zip(b.bytes())
        .position(|(x, y)| x != y)
        .unwrap_or_else(|| a.len().min(b.len()));
    // Back up to a character boundary, then to something that reads as the
    // start of a field rather than the middle of an identifier.
    let mut start = at.saturating_sub(220);
    while start > 0 && !a.is_char_boundary(start) {
        start -= 1;
    }
    let window = |s: &str| -> String {
        let mut end = (at + 220).min(s.len());
        while end < s.len() && !s.is_char_boundary(end) {
            end += 1;
        }
        let from = start.min(s.len());
        s[from..end].to_string()
    };
    format!(
        "first difference at byte {at}:\n  cold reduce: ...{}...\n  this order:  ...{}...",
        window(a),
        window(b)
    )
}

/// The two halves of the property, asked directly of the published log.
///
/// Reads every stream back off `host`, then:
///
///  1. **Totality.** A cold `apply::reduce` of the whole set must succeed,
///     and so must a fresh `reduce_onto` under each of several randomly
///     chosen valid orders. Anything that got published must reduce, full
///     stop -- an event the coordinator refused is not here to begin with.
///  2. **Confluence.** Every one of those reductions must produce
///     byte-identical state. This is the half a "never errors" oracle would
///     bless a broken fix on: a handler that stops returning `Err` while
///     still depending on which of two unordered events arrived first has
///     traded a loud outage for silent, permanent divergence, and only a
///     comparison across orders can tell the difference.
///
/// Costs no git beyond reading the streams once, which is why it runs on
/// every case rather than being reserved for a deep run.
fn check_reduction_is_total_and_confluent(
    fleet: &Fleet,
    world: &World,
    host: usize,
    at: &str,
) -> Result<(), TestCaseError> {
    let h = &fleet.hosts[host];
    let Some(registry_tip) = crate::registry::read_registry_tip(h.repo())
        .map_err(|e| fail(&format!("{at}: read_registry_tip"), e))?
    else {
        return Ok(());
    };
    let reader = crate::gitobjects::Libgit2Reader::open(h.repo())
        .map_err(|e| fail(&format!("{at}: open object database"), e))?;
    let epoch = crate::registry::read_epoch_at(&reader, &registry_tip)
        .map_err(|e| fail(&format!("{at}: read_epoch_at"), e))?;
    let known_epochs = crate::registry::read_epoch_chain(h.repo(), &registry_tip)
        .map_err(|e| fail(&format!("{at}: read_epoch_chain"), e))?;
    let config = crate::registry::read_bus_config_at(&reader, &registry_tip)
        .map_err(|e| fail(&format!("{at}: read_bus_config_at"), e))?;

    let mut streams = BTreeMap::new();
    for a in epoch.active_members.keys() {
        let Some(tip) = crate::stream::read_stream_tip(h.repo(), a)
            .map_err(|e| fail(&format!("{at}: read_stream_tip {a}"), e))?
        else {
            continue;
        };
        let (_header, log) = crate::stream::read_stream_at(&reader, &tip, a)
            .map_err(|e| fail(&format!("{at}: read_stream_at {a}"), e))?;
        streams.insert(a.clone(), log);
    }

    let cold = crate::apply::reduce(
        config.clone(),
        Some(epoch.clone()),
        known_epochs.clone(),
        &streams,
    )
    .map_err(|e| {
        fail(
            &format!(
                "{at}: reduction of the published log failed, which is every host unable to read \
                 the bus, permanently -- the log is append-only and force-push is prohibited"
            ),
            e,
        )
    })?;
    let cold_rendered = format!("{cold:?}");

    for (n, seed) in world.orders.iter().enumerate() {
        let mut rng = Rng(seed | 1);
        let order = random_linear_extension(&streams, &mut rng);
        let owned: Vec<crate::envelope::Envelope> = order.into_iter().cloned().collect();
        let mut base = crate::state::BusState::new(config.clone());
        base.roster_epoch = Some(epoch.clone());
        base.known_epochs = known_epochs.clone();
        let shuffled = crate::apply::reduce_onto(base, &owned).map_err(|e| {
            fail(
                &format!(
                    "{at}: valid replay order #{n} (seed {seed}) failed to reduce, though the \
                     same events reduce fine in the order this host happened to walk them -- a \
                     host that fetched in that order could never read the bus again"
                ),
                e,
            )
        })?;
        let shuffled_rendered = format!("{shuffled:?}");
        prop_assert!(
            shuffled_rendered == cold_rendered,
            "{at}: valid replay order #{n} (seed {seed}) reduced the same events to different \
             state -- hosts that fetched in different orders have silently and permanently \
             diverged, which no error message will ever surface.\n{}",
            first_difference(&cold_rendered, &shuffled_rendered)
        );
    }
    Ok(())
}

/// One generated scenario, end to end: drive it, lay it down, and check it.
///
/// Setting `AGENT_BUS_PROPTEST_TRACE` prints each operation with how long
/// its materialization took. That is a tuning aid rather than a debugging
/// one -- the cost here is dominated by real `git` process spawning.
fn run_world(world: &World) -> Result<(), TestCaseError> {
    run_world_censused(world).map(|_| ())
}

/// [`run_world`], additionally reporting which event kinds actually
/// published.
fn run_world_censused(world: &World) -> Result<BTreeSet<&'static str>, TestCaseError> {
    let trace = std::env::var_os("AGENT_BUS_PROPTEST_TRACE").is_some();
    let mut exec = GitExec {
        fleet: Fleet {
            hosts: Vec::new(),
            origin: init_bare_origin(),
        },
        trace,
        census: BTreeSet::new(),
    };
    let (mut model, ops) = drive(world, &mut exec)?;
    let GitExec { fleet, census, .. } = exec;
    check_all(&fleet, &model, "after the whole schedule")?;
    check_convergence(&fleet, &mut model)?;
    check_reduction_is_total_and_confluent(
        &fleet,
        world,
        0,
        "after the final fleet-wide synchronization",
    )?;
    if trace {
        eprintln!(
            "  {} ops, {} hosts, published kinds: {:?}",
            ops.len(),
            fleet.hosts.len(),
            census
        );
    }
    Ok(census)
}

// ------------------------------------------------------------------- the test

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

/// Far more modest than a property test would ordinarily want, and honestly
/// so.
///
/// A single operation here is on the order of a hundred `git` subprocesses --
/// `coordinator::drain_outbox` alone reduces the whole bus before it will
/// publish anything. Cost scales as roughly cases times steps; measured on
/// the machine this was written on, 120 cases at eight steps is about nine
/// minutes, so the conventional "a few hundred cases" would be a run of
/// hours rather than a test. The defaults below cost about a minute in
/// total, which is what an ordinary `cargo test` can absorb without anyone
/// starting to avoid running it.
///
/// The consequence is worth stating plainly: at these defaults this explores
/// far less per run than a property test normally would, and leans on being
/// run repeatedly -- each run draws a fresh seed -- rather than on breadth
/// within any one run. `AGENT_BUS_PROPTEST_CASES` and
/// `AGENT_BUS_PROPTEST_STEPS` raise both for a deliberate longer hunt, which
/// is where real breadth comes from; `CASES=120 STEPS=12` is about fifteen
/// minutes and is the budget worth spending when touching `apply.rs`.
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

    /// Generate a fleet's whole life, lay it down across real checkouts of
    /// one shared origin, and check every read against a pure-Rust oracle
    /// after every single operation -- then check the two halves of the
    /// property directly against the published log.
    ///
    /// The default step budget is deliberately small, and that is a real
    /// limitation worth knowing rather than a tuning detail. A race between
    /// two authors reassigning one nomination needs a nomination, two
    /// reassignments, and enough registrations to have two authors and two
    /// reviewers, so at four steps this harness *cannot express it at all*.
    /// Nine reduction-totality defects lived in exactly that blind spot.
    /// Running with `AGENT_BUS_PROPTEST_STEPS=12` reaches it; at the default
    /// the deterministic regression tests below carry that shape instead,
    /// which is why they are pinned rather than left to the generator.
    #[test]
    fn a_multi_checkout_fleet_upholds_its_invariants_under_any_schedule(
        world in world_strategy(env_usize("AGENT_BUS_PROPTEST_STEPS", 4))
    ) {
        run_world(&world)?;
    }
}

// ------------------------------------------------------- the coverage guard

/// The single most load-bearing test in this module, and the reason the
/// blind spot cannot silently reopen.
///
/// `cli.rs` exposes `submit --kind <k> --data <json>`, which builds a
/// candidate for *any* kind, so the surface an agent can invoke is the whole
/// schema rather than a curated subset. This module's generator used to
/// construct six of them, and nine reduction-totality defects lived for
/// months in the rest. Nothing announced that gap: the tests were green, and
/// green meant "the six kinds we thought to generate are fine".
///
/// So the alphabet is held to `EventData`'s own variant list. When kind 43
/// is added, this fails until someone decides -- explicitly, with a written
/// reason -- whether it is generated or excused. A guard that names its gaps
/// out loud is worth far more than silent coverage of a subset, because the
/// next person can close them one at a time and cannot forget they exist.
#[test]
fn every_event_kind_is_either_generated_or_explicitly_excused() {
    let all: BTreeSet<&str> = EventData::all_kinds().into_iter().collect();
    let generated: BTreeSet<&str> = GENERATED_KINDS.iter().copied().collect();
    let excused: BTreeSet<&str> = UNGENERATED_KINDS.iter().map(|(k, _)| *k).collect();

    assert_eq!(
        generated.len(),
        GENERATED_KINDS.len(),
        "GENERATED_KINDS contains a duplicate"
    );
    assert_eq!(
        excused.len(),
        UNGENERATED_KINDS.len(),
        "UNGENERATED_KINDS contains a duplicate"
    );
    let both: Vec<&&str> = generated.intersection(&excused).collect();
    assert!(
        both.is_empty(),
        "a kind cannot be both generated and excused: {both:?}"
    );

    let covered: BTreeSet<&str> = generated.union(&excused).copied().collect();
    let missing: Vec<&&str> = all.difference(&covered).collect();
    assert!(
        missing.is_empty(),
        "these event kinds are neither generated by this harness nor listed in \
         UNGENERATED_KINDS with a reason: {missing:?}. An agent can submit any kind \
         (`submit --kind`), so an ungenerated one is an untested way to wedge the bus. Add a \
         payload builder to `build_act` and list it in GENERATED_KINDS, or add it to \
         UNGENERATED_KINDS saying why it cannot be reached."
    );
    let unknown: Vec<&&str> = covered.difference(&all).collect();
    assert!(
        unknown.is_empty(),
        "these kinds are listed here but are not variants of EventData any more: {unknown:?}"
    );

    for (kind, reason) in UNGENERATED_KINDS {
        assert!(
            reason.len() > 60,
            "the excuse for {kind} is too short to be a reason: {reason:?}"
        );
    }
}

/// Every kind [`Step::Act`] can draw is one [`build_act`] really builds.
///
/// The coverage guard above compares two lists of strings, which would still
/// pass if `build_act` returned `None` for a kind on every input it could
/// ever receive -- coverage on paper, nothing generated in practice. This
/// runs the builder against a model rich enough for every precondition and
/// requires a payload of the right kind back.
#[test]
fn every_generated_kind_is_constructible() {
    let model = rich_model();
    let exec = DryExec { hosts: 2 };
    for kind in ACT_KINDS {
        let mut built = None;
        // The selectors decide which subject and which participant, so a
        // single draw proves nothing; sweep a small grid instead.
        'outer: for a in 0..6u8 {
            for b in 0..6u8 {
                for c in 0..6u8 {
                    for flag in [false, true] {
                        if let Some(act) =
                            build_act(&model, &exec, kind, [Sel(a), Sel(b), Sel(c)], flag)
                        {
                            built = Some(act);
                            break 'outer;
                        }
                    }
                }
            }
        }
        let act = built.unwrap_or_else(|| {
            panic!(
                "build_act never produced a {kind} payload against a model that has every \
                 precondition for it -- the kind is listed as generated but is not really \
                 reachable"
            )
        });
        assert_eq!(
            act.data.kind(),
            *kind,
            "build_act returned the wrong kind for {kind}"
        );
    }
}

/// One `Step::Act` for a named kind, so a hand-written schedule reads as the
/// list of actions it is rather than as a column of `Sel` literals.
fn act(kind: &str, a: u8, b: u8, c: u8, flag: bool) -> Step {
    act_with(kind, a, b, c, flag, false)
}

/// [`act`], with the resulting stream commit held back from origin -- the
/// publication window another checkout then acts inside without having
/// observed it.
fn act_deferred(kind: &str, a: u8, b: u8, c: u8, flag: bool) -> Step {
    act_with(kind, a, b, c, flag, true)
}

fn act_with(kind: &str, a: u8, b: u8, c: u8, flag: bool, defer: bool) -> Step {
    let i = ACT_KINDS
        .iter()
        .position(|k| *k == kind)
        .unwrap_or_else(|| panic!("{kind} is not in ACT_KINDS"));
    Step::Act {
        kind: Sel(i as u8),
        a: Sel(a),
        b: Sel(b),
        c: Sel(c),
        flag,
        defer,
    }
}

/// A model with one of everything the payload builders need: two checkouts,
/// two implementors, two reviewers, a coordinator, an auditor, and one open
/// subject of every kind, with a contested group already formed.
///
/// Built by driving [`broad_world`] rather than by hand-assembling the
/// struct, so the fixture the constructibility guard checks against cannot
/// drift away from what a real schedule actually produces.
fn rich_model() -> Model {
    let mut exec = DryExec::default();
    drive(&broad_world(), &mut exec)
        .expect("the stub executor never fails")
        .0
}

// ---------------------------------------------------------- planner unit tests

mod planning_tests {
    use super::*;

    /// A `World` with no extra checkouts, for tests that only care about the
    /// step handling.
    fn solo(steps: Vec<Step>) -> World {
        World {
            genesis_name: Sel(0),
            joins: vec![],
            steps,
            orders: vec![1],
        }
    }

    /// A `World` whose second checkout exists from the very start.
    fn pair(steps: Vec<Step>) -> World {
        World {
            genesis_name: Sel(0),
            joins: vec![Sel(0)],
            steps,
            orders: vec![1],
        }
    }

    fn register_on(host: u8) -> Step {
        Step::Register {
            host: Sel(host),
            name: Sel(0),
            role: Sel(0),
        }
    }

    /// The driver is what decides what the implementation is even asked to
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
            orders: vec![1],
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

    /// ...and is *not* preceded by one when that checkout is already
    /// current, so the harness does not quietly synchronize everything all
    /// the time.
    #[test]
    fn a_registration_from_an_already_current_checkout_needs_no_synchronization() {
        let ops = plan(&solo(vec![register_on(0)]));
        assert!(!ops.iter().any(|o| matches!(o, Op::Sync { .. })), "{ops:?}");
    }

    /// An issue can only be opened against an agent the opener's own
    /// checkout has already seen, so the driver catches that one checkout up
    /// first -- and leaves every other checkout exactly as stale as it was.
    #[test]
    fn an_issue_against_an_unseen_agent_synchronizes_only_the_openers_checkout() {
        let world = World {
            genesis_name: Sel(0),
            // Three checkouts: 0 activates the bus, 1 registers an agent, 2
            // never acts at all.
            joins: vec![Sel(0), Sel(0)],
            steps: vec![
                register_on(1),
                // host0's coordinator has not synchronized since, so it
                // cannot yet see the agent host1 just registered.
                Step::OpenIssue {
                    opener: Sel(0),
                    target: Sel(1),
                },
            ],
            orders: vec![1],
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
    /// exercise; the driver nudges the target rather than discarding it.
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

    /// The oracle's per-checkout view must actually differ between a stale
    /// and a current checkout -- if it did not, the harness would be
    /// checking a property that cannot tell staleness from correctness.
    #[test]
    fn the_oracle_distinguishes_a_stale_checkout_from_a_current_one() {
        let world = pair(vec![register_on(1)]);
        let mut exec = DryExec::default();
        let (model, _) = drive(&world, &mut exec).expect("the stub executor never fails");
        let stale = model.expected(0).expect("host0 activated the bus");
        let fresh = model.expected(1).expect("host1 registered an agent");
        assert_eq!(stale.agents.len(), 1, "{stale:?}");
        assert_eq!(fresh.agents.len(), 2, "{fresh:?}");
        assert_ne!(stale, fresh);
    }

    /// A checkout that has never synchronized has no local registry at all,
    /// which the oracle reports as "nothing to reduce" rather than as an
    /// empty reduction -- the one case in which a failing read is the right
    /// answer.
    #[test]
    fn the_oracle_expects_no_snapshot_at_all_from_a_checkout_that_never_synchronized() {
        let world = pair(vec![]);
        let mut exec = DryExec::default();
        let (model, _) = drive(&world, &mut exec).expect("the stub executor never fails");
        assert!(model.expected(0).is_some());
        assert!(model.expected(1).is_none());
    }

    /// A checkout holding unpushed commits cannot fetch -- its own stream
    /// ref is ahead of the remote's, which a non-force fetch rejects
    /// outright -- so the driver must flush before it synchronizes. Without
    /// this the deferred-publication window would break every later `Sync`
    /// rather than opening a race.
    #[test]
    fn a_checkout_holding_a_deferred_publication_is_flushed_before_it_synchronizes() {
        let status_kind = ACT_KINDS
            .iter()
            .position(|k| *k == "plan.set")
            .expect("plan.set is generated");
        let world = solo(vec![
            Step::Act {
                kind: Sel(status_kind as u8),
                a: Sel(0),
                b: Sel(0),
                c: Sel(0),
                flag: false,
                defer: true,
            },
            Step::Sync { host: Sel(0) },
        ]);
        let ops = plan(&world);
        let at = ops
            .iter()
            .position(|o| matches!(o, Op::Sync { .. }))
            .expect("the synchronization must survive planning");
        assert!(
            matches!(ops[at - 1], Op::Flush { host: 0 }),
            "a dirty checkout must be flushed before it fetches: {ops:?}"
        );
    }

    /// ...and nothing may stay unpushed once the schedule ends, or the
    /// convergence sweep would be comparing checkouts that cannot see the
    /// same set.
    #[test]
    fn the_schedule_always_ends_with_every_deferred_publication_flushed() {
        let kind = ACT_KINDS
            .iter()
            .position(|k| *k == "plan.set")
            .expect("plan.set is generated");
        let world = solo(vec![Step::Act {
            kind: Sel(kind as u8),
            a: Sel(0),
            b: Sel(0),
            c: Sel(0),
            flag: false,
            defer: true,
        }]);
        let ops = plan(&world);
        assert!(matches!(ops.last(), Some(Op::Flush { host: 0 })), "{ops:?}");
    }
}

/// The schedule [`a_hand_written_schedule_really_publishes_the_alphabet`]
/// drives: one deliberate action of nearly every generated kind, in an order
/// where each one's subject already exists.
///
/// Hand-written rather than generated because it is a *coverage* fixture,
/// not a search: a generated schedule reaches these kinds only by luck, and
/// the point here is to prove each one survives the real publication path
/// every single run.
fn broad_world() -> World {
    let mut steps: Vec<Step> = Vec::new();
    // Genesis supplies the coordinator; the six remaining pool names become
    // two implementors, two reviewers, an auditor and a spare implementor
    // (retired at the very end, so retirement never takes a participant some
    // other kind still needs), spread across both checkouts so cross-host
    // visibility is real rather than incidental.
    for (i, role) in [0u8, 1, 2, 3, 5, 0].into_iter().enumerate() {
        steps.push(Step::Register {
            host: Sel(i as u8 % 2),
            name: Sel(0),
            role: Sel(role),
        });
    }
    steps.push(Step::Sync { host: Sel(0) });
    steps.push(Step::Sync { host: Sel(1) });

    // Self-reports and fleet-wide authority.
    steps.push(Step::Status {
        agent: Sel(1),
        blocked: true,
    });
    steps.push(Step::Status {
        agent: Sel(1),
        blocked: false,
    });
    steps.push(act("subscription.set", 0, 0, 0, true));
    steps.push(act("scope.set", 0, 0, 0, true));
    steps.push(act("plan.set", 0, 0, 0, true));
    steps.push(act("progress.reported", 0, 0, 0, true));
    steps.push(act("schema.activated", 0, 0, 0, false));
    steps.push(act("merge_engine.activated", 0, 0, 0, false));

    // Issues: two, so a terminal rejection and a terminal resolution can
    // both be reached, plus an acknowledgement and a reassignment.
    steps.push(Step::OpenIssue {
        opener: Sel(0),
        target: Sel(1),
    });
    steps.push(Step::OpenIssue {
        opener: Sel(0),
        target: Sel(2),
    });
    steps.push(Step::AckIssue { issue: Sel(0) });
    steps.push(Step::ReassignIssue {
        issue: Sel(0),
        new_target: Sel(0),
    });
    steps.push(act("issue.rejected", 0, 0, 0, false));
    steps.push(Step::ResolveIssue { issue: Sel(0) });

    // Dependencies: three -- one per terminal disposition, plus one left
    // open, so `rich_model` (which is this schedule's *final* state) still
    // has an open subject for the constructibility guard to aim at.
    steps.push(act("dependency.requested", 0, 0, 0, true));
    steps.push(act("dependency.requested", 0, 1, 0, true));
    steps.push(act("dependency.requested", 0, 2, 0, true));
    steps.push(Step::Sync { host: Sel(0) });
    steps.push(Step::Sync { host: Sel(1) });
    steps.push(act("dependency.acknowledged", 0, 0, 0, true));
    steps.push(act("dependency.reassigned", 0, 0, 0, true));
    steps.push(Step::Sync { host: Sel(0) });
    steps.push(Step::Sync { host: Sel(1) });
    steps.push(act("dependency.resolved", 0, 0, 0, true));
    steps.push(act("dependency.rejected", 0, 0, 0, true));

    // Handoffs: four, one per terminal disposition plus one left open.
    for _ in 0..4 {
        steps.push(act("handoff.offered", 0, 0, 0, true));
    }
    steps.push(Step::Sync { host: Sel(1) });
    steps.push(act("handoff.accepted", 0, 0, 0, true));
    steps.push(act("handoff.declined", 0, 0, 0, true));
    steps.push(act("handoff.withdrawn", 0, 0, 0, true));

    // The whole review lifecycle, on two chains: one that runs through
    // acceptance, findings, dispositions and a reassignment, and two more
    // that exist only to be declined and withdrawn (both of which close a
    // chain, so neither can share one).
    // `flag` gives each nomination a second author, which is what makes two
    // concurrent reassignments of one nomination expressible at all.
    steps.push(act("review.nominated", 0, 0, 0, true));
    steps.push(act("review.nominated", 0, 0, 0, true));
    steps.push(act("review.nominated", 0, 0, 0, true));
    steps.push(Step::Sync { host: Sel(1) });
    steps.push(act("review.nomination_accepted", 0, 0, 0, false));
    // Three findings: one cleared, one superseded, one left open so the
    // final state still has something either disposition could aim at.
    steps.push(act("review.changes_requested", 0, 0, 0, true));
    steps.push(act("review.changes_requested", 0, 0, 0, false));
    steps.push(act("review.changes_requested", 0, 0, 0, true));
    steps.push(act("review.findings_cleared", 0, 0, 0, false));
    steps.push(act("review.findings_superseded", 0, 0, 0, false));
    steps.push(Step::Sync { host: Sel(1) });
    // The race the whole module was extended for: both authors replace the
    // *same* nomination link, and `flag` makes each of them reach for the
    // same replacement reviewer -- which round-robin nomination makes the
    // expected outcome rather than a coincidence. The first is deferred, so
    // the second author's own gate-17 fetch genuinely does not see it and
    // both are published in good faith.
    steps.push(act_deferred("review.reassigned", 0, 0, 0, true));
    steps.push(act("review.reassigned", 0, 1, 0, true));
    steps.push(Step::Flush { host: Sel(0) });
    steps.push(Step::Flush { host: Sel(1) });
    steps.push(Step::Sync { host: Sel(0) });
    steps.push(Step::Sync { host: Sel(1) });
    // The second and third chains exist only to be closed: a decline and a
    // withdrawal each close one, so neither can share the chain the
    // acceptance/findings/reassignment sequence above needs left open.
    steps.push(act("review.nomination_declined", 1, 0, 0, false));
    steps.push(act("review.withdrawn", 1, 0, 0, false));

    // Friction and broadcasts. No synchronization between these: each one's
    // author already holds what the next one names, and a `Sync` late in
    // this schedule is a full re-reduction of a bus with sixty events in it
    // -- by far the most expensive step here, and worth spending only where
    // a checkout genuinely needs to see another's work.
    steps.push(act("friction.reported", 0, 0, 0, true));
    steps.push(act("friction.synthesized", 0, 0, 0, true));
    steps.push(act("broadcast.published", 0, 0, 0, true));
    steps.push(act("broadcast.acknowledged", 0, 0, 0, true));
    steps.push(act("broadcast.seen", 0, 0, 0, true));
    steps.push(act("audit.reported", 0, 0, 0, false));

    // A contested group and its resolution: two reassignments of one issue,
    // published from checkouts that have not observed one another.
    steps.push(Step::OpenIssue {
        opener: Sel(0),
        target: Sel(1),
    });
    steps.push(Step::ReassignIssue {
        issue: Sel(0),
        new_target: Sel(0),
    });
    steps.push(Step::ReassignIssue {
        issue: Sel(0),
        new_target: Sel(1),
    });
    // The coordinator resolving the review race above is on host0, which
    // already fetched both candidates when they were flushed, so no further
    // synchronization is needed here.
    steps.push(act("lifecycle.conflict_resolved", 0, 0, 0, false));

    // Lifecycle last, because retirement takes an identity out of play.
    steps.push(act("agent.resumed", 0, 0, 0, false));
    // ...and the one it retires is the spare, chosen by selector so no other
    // kind loses a participant it needs.
    steps.push(act("agent.retired", 0, 5, 0, false));

    World {
        genesis_name: Sel(0),
        joins: vec![Sel(0)],
        steps,
        orders: vec![1, 2, 3],
    }
}

/// Constructibility is not coverage.
///
/// [`every_generated_kind_is_constructible`] proves `build_act` can *build*
/// a payload of every kind it claims. It says nothing about whether the
/// coordinator would accept one, and a builder whose payloads are always
/// refused would leave the whole alphabet untested while both the coverage
/// guard and the property test stayed green -- coverage on paper, six kinds
/// in practice, which is precisely the failure this module is being repaired
/// from.
///
/// So this drives a hand-written schedule through the *real* publication
/// path -- `outbox::submit` then `coordinator::drain_outbox`, against real
/// repositories -- and requires every generated kind to have actually landed
/// in a stream. It also runs the full invariant sweep on the way, so the
/// schedule doubles as a deterministic regression over a bus that has one of
/// nearly everything in it.
#[test]
fn a_hand_written_schedule_really_publishes_the_alphabet() {
    let census = run_world_censused(&broad_world()).expect("the broad schedule must hold");
    let expected: BTreeSet<&str> = GENERATED_KINDS.iter().copied().collect();
    let missing: Vec<&&str> = expected.difference(&census).collect();
    assert!(
        missing.is_empty(),
        "these kinds are listed as generated but never actually published through the real \
         submit/drain path in the broad schedule: {missing:?}. Either the payload builder \
         produces something the coordinator refuses, or the schedule does not set up the \
         precondition. Published: {census:?}"
    );
}

/// The smallest schedule that reaches the review-reassignment race, pinned
/// deterministically because it is the shape the whole alphabet extension
/// was built to reach and far too load-bearing to leave to a generator's
/// luck at four steps.
///
/// Two authors of one nomination each replace it, and each independently
/// names the same replacement reviewer -- which round-robin nomination makes
/// the *expected* outcome rather than a coincidence. Neither has observed
/// the other: the first reassignment is drained into its own checkout's
/// stream and held back from origin, so the second author's own gate-17
/// fetch genuinely cannot see it. Both are therefore published in good
/// faith, and both are correct at the moment they publish.
///
/// This is the before/after evidence that the harness looks where it claims
/// to. Against `origin/agent/c-agent/reduction-totality-sweep~1` -- the
/// commit before "seven more ways reduction could wedge the bus
/// permanently" -- it fails, and it fails in the loudest possible way:
///
/// ```text
/// sync on host0: dave:3: replacement reviewer must differ from the current reviewer
/// ```
///
/// That is `sync::synced_snapshot` returning `Err`, which is a checkout that
/// cannot read the bus at all -- not one rejected event. `apply_review_
/// reassigned` judged the replacement against `chain.current_request.
/// reviewer`, a derived view the *other* reassignment had already moved, so
/// the second to reduce was refused; and since the log is append-only and
/// force-push is prohibited, there is no way back. Against the fix -- which
/// judges against `nomination_reviewer[&d.replaces]`, append-only and
/// reachable through this event's own `refs` -- it passes.
#[test]
fn the_smallest_schedule_that_reaches_the_review_reassignment_race() {
    let world = World {
        genesis_name: Sel(0),
        // The second checkout exists from the start: the two authors have to
        // be custodied separately or there is no race to have.
        joins: vec![Sel(0)],
        steps: vec![
            // Two implementors (the authors), split across the checkouts,
            // and two reviewers to round-robin between.
            Step::Register {
                host: Sel(0),
                name: Sel(0),
                role: Sel(0),
            },
            Step::Register {
                host: Sel(1),
                name: Sel(0),
                role: Sel(1),
            },
            Step::Register {
                host: Sel(0),
                name: Sel(0),
                role: Sel(2),
            },
            Step::Register {
                host: Sel(0),
                name: Sel(0),
                role: Sel(3),
            },
            Step::Sync { host: Sel(0) },
            Step::Sync { host: Sel(1) },
            // `flag` gives the nomination its second author.
            act("review.nominated", 0, 0, 0, true),
            // ...which that author's own checkout then has to be able to see.
            Step::Sync { host: Sel(1) },
            // The race. `flag` makes each author reach for the same
            // replacement reviewer; `defer` is what stops the second author
            // from observing the first.
            act_deferred("review.reassigned", 0, 0, 0, true),
            act("review.reassigned", 0, 1, 0, true),
        ],
        orders: vec![1, 2, 3],
    };
    run_world(&world).expect("the reassignment race must reduce, in every valid order");
}

/// One fixed schedule, run deterministically: activate the bus, publish
/// twice from the same checkout for the same agent, and let a second
/// checkout join cold and read the result.
///
/// This is the smallest world that both bug 1 and bug 2 fall to, and it is
/// pinned here rather than left to the generator so this class stays guarded
/// no matter what a given run happens to draw -- a property test's coverage
/// of any *particular* shape is a matter of chance, and this shape is too
/// load-bearing to leave to chance.
///
/// It is also what validated the harness. Against `ensure_bus_worktree` with
/// its staleness check removed, this fails with `left: [EventId("carol:1")],
/// right: [EventId("carol:2")]` -- the second publication silently reusing
/// the first one's sequence number, because the reused worktree cache still
/// held the stream as it was before the first append. Against
/// `create_root_commit` reverted to `git branch -f`, it fails at the genesis
/// operation on the double-prefixed ref. Against the code as it stands, it
/// passes.
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
        orders: vec![1, 2],
    };
    run_world(&world).expect("the fixed schedule must hold");
}
