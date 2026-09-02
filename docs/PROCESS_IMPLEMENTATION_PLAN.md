# Process implementation plan

Status: implementation plan owned by the `c-process` implementation agent. This
is a tier-four document under [README.md](README.md) authority ordering: it
schedules work against the normative demands of [PROCESS.md](PROCESS.md) and
[PROCESS_SHARDING.md](PROCESS_SHARDING.md). It may not weaken either. Where it
proposes a structural change outside its ownership, or takes temporary custody
of a layer another agent owns, it says so explicitly and names the handover.

Section 10 is a ledger of defects this plan found in the normative corpus. Those
are not this plan's to ratify; they are raised, with a proposed resolution, so
that the milestone which depends on each one is not scheduled against an
ambiguity.

## 0. Ownership boundary

Owned by this plan:

| Area | Normative owner |
|---|---|
| process vocabulary, events, specs, runs, correctness | [PROCESS.md](PROCESS.md) §2, §4 |
| protocol registries and their open merge | §3, [PROCESS_SHARDING.md](PROCESS_SHARDING.md) §2 |
| the driver boundary type and root projection | §2, §5 |
| topology, population, spawn and supervision law shapes | §3 |
| typed channels, escrow, session and capacity laws | §3, FOUNDATION law 16 |
| the exhaustive `NetworkTransition` family and nominal freshness | §3, FOUNDATION law 22 |
| child and API-call protocols and their lifecycle | §3 |
| byte-flow ingress/egress and partial I/O | §3, FOUNDATION law 19 |
| cancellation masks, summaries, termination contracts, facets | §3, §5 |
| the application proof package and the driver contract | §4, §5 |
| flattening, serialization, the serial-callable bridge | §4 |
| process independence, diamonds, syscall linearization | §4 |
| the commit transition and the desired-view reconciliation law | §6 |
| per-process progress and the network progress theorem | §7 |
| weaving, invariant mixins, refinement lenses | §8 |
| process resource metrics, capacity credit, scope flux | §5, FOUNDATION law 20 |
| process signatures, shard and facet certificates, SCC summaries | [PROCESS_SHARDING.md](PROCESS_SHARDING.md) |
| the sequential authoring mode and its adapter | §4 |

Not owned, and this plan must consume rather than restate:

- `SpecProcess`, `BehaviorContract`, `SpecificationSuite`, execution traces, the
  observation oracle, and the abstract progress/liveness contract belong to
  [SEMANTICS.md](SEMANTICS.md).
- the resource algebra classes (`ResourceModel`, ordered partial commutative
  monoid laws, axis names and limits) belong to [RESOURCES.md](RESOURCES.md) and
  are being implemented by `c-mem` as `Grass.Resource.*`.
  `Grass.Process.Resource` *instantiates* them; it must not declare a second
  algebra.
- obligation identity, ledger law, and terminal dispositions belong to
  [OBLIGATIONS.md](OBLIGATIONS.md) (`Grass.Obligation.*`, `c-mem`).
- loans, provenance, initialization, and race freedom belong to
  [MEMORY_MODEL.md](MEMORY_MODEL.md) (`c-mem`). Byte-flow read and write *loans*
  are consumed from there, not redefined here.
- providers, platform plans, and commits belong to
  [PLATFORM_ABI.md](PLATFORM_ABI.md); the `ProcessDriver` record is stated here
  but every provider-side field is that document's.
- application process graphs (HTTP/2 roles, Vulkan roles, the spike plans) are
  explicitly **not** owned by this plan. This plan supplies the algebra they
  instantiate.

Blocked on this plan:

- `Grass.Semantics` itself, for two declarations: `SpecProcess.driverBoundary`
  needs `DriverBoundary` ([PROCESS.md](PROCESS.md) §2) and `ProcessPresentation`
  needs the abstract specification process network. See §10.2 — this is a cycle
  in [MODULES.md](MODULES.md)'s stated chain, and this plan proposes the cut.
- `Grass.Refinement`, which quantifies over the same abstract network.
- `Grass.Std.Process.*` (network, supervision, clock, graphics protocols) cannot
  declare a protocol before `ProcessSpec` and `ChannelContract` are frozen.
- `Grass.Std.Protocol.Http2` needs the channel, capacity-credit, and child
  lifecycle vocabulary.
- `Grass.Verify` cannot state the process leg of `VerifiedProgram` without
  `RootProcessCertificate`.
- every spike from 1 upward: even Hello World is a sequential process elaborated
  by `SequentialAdapter`.

## 1. Sequencing principle

The expensive mistake in this layer is not a missing proof; it is a *vocabulary*
that forces an application author to write down a realization fact. Three
foundation laws are specifically about what must **not** appear in a type:

- law 15 (no weave leakage) — no selected topology in the precious root;
- law 18 (no schedule leakage) — no occurrence identity, batching, or routing in
  `ProcessSpec.Step`;
- law 17 (one scalable algebra) — a serial author may not get a second
  semantics.

So work is ordered:

1. **Author vocabulary.** What a protocol author, a standard-library protocol,
   a *serial* author, and a spike actually write. Changing this rewrites source
   everywhere.
2. **Network semantics.** The exhaustive transition family and the laws that
   make it exact. Changing this rebuilds proofs, not source.
3. **Composition and lowering.** Flattening, serialization, weaving, resources.
4. **Certificates and sharding.** The boundary that keeps 2 and 3 local.

Law 17 puts the serial authoring surface in step 1, not step 3: `SequentialMachine`
is what a Hello World author writes, so it is author vocabulary by this plan's
own test, even though the adapter that elaborates it is composition work.

Milestones are ordered, not dated. Each names its exit criterion and who it
unblocks. A milestone exits on *expressiveness plus what its own fixtures need*,
not on completing every theorem the normative document eventually demands.

## 2. M0 — Ground

### 2.1 What this plan needs from lower layers

| Need | Owner | Status |
|---|---|---|
| a monotone fresh-identity supply (law 22) | `Grass.Core` (`c-mem` custody) | committed on `c-mem`'s branch, unmerged |
| finite maps with framing lemmas | `Grass.Std.Logical` | committed on `c-mem`'s branch, unmerged |
| a bag/multiset with a permutation quotient | `Grass.Std.Logical` | **absent**; see §2.2 |
| `ReadBufferLoan` / `WriteBufferLoan` | `Grass.Memory` (`c-mem`) | **absent**; hard block on M3 byte flow |
| the resource algebra classes | `Grass.Resource` (`c-mem`) | planned, not landed |
| obligation ledger and dispositions | `Grass.Obligation` (`c-mem`) | partly committed on `c-mem`'s branch, unmerged |
| `SpecProcess`, `BehaviorContract`, execution traces | `Grass.Semantics` | **unclaimed**; see §10.2 |
| `lakefile.toml` glob and `warningAsError` | build | on this branch, textually identical to `c-mem`'s |

The byte-flow loan row matters more than its position suggests.
[PROCESS.md](PROCESS.md) §3 makes `ReadBufferLoan` and `WriteBufferLoan`
constructor arguments of `ByteIngressPhase` and `ByteEgressPhase`, so M3's
byte-flow modules cannot be written against a placeholder without changing every
phase constructor later. If that deliverable has not landed when M3 starts, the
byte-flow modules are parameterized over an abstract loan type and the
instantiation is a named M3 exit item, not a silent substitution.

### 2.2 Decisions taken because the agent bus is not yet available

**Decided — parametricity instead of custody, wherever possible.** Rather than
squatting on `Grass.Semantics` to obtain `SpecProcess`, this plan keeps the
process layer parametric in exactly the way [PROCESS.md](PROCESS.md) already
writes it: `ProcessVocabulary` carries its own `Type` fields and `ProcessSpec` is
self-contained. The consequence is that `Grass.Process.Spec` and
`Grass.Process.Run` — the modules every other agent is waiting on — depend on
nothing outside `Grass.Process` and Lean core.

This does **not** dissolve the dependency cycle between this layer and
`Grass.Semantics`; §10.2 records that cycle and the proposed cut. Parametricity
buys the modules that genuinely have no semantic content; it does not buy
`DriverBoundary`, the abstract network, or `ProcessCorrect`.

**Decided — `ProcessCorrect` takes acceptance as an explicit parameter.**
[PROCESS.md](PROCESS.md) §4 gives `ProcessCorrect` the fields
`terminal : ... -> TerminalAccepts p result` and
`observationsAccept : ... -> TraceAccepts p run.observations`. A bare
`ProcessSpec` carries no acceptance data, so those relations are relative to a
contract this plan does not own. Inventing a local acceptance notion would
create the second oracle [FOUNDATION.md](FOUNDATION.md) law 11 forbids.
`ProcessCorrect` therefore takes an explicit `ProcessAcceptance p` record —
terminal acceptance, trace acceptance, view acceptance, demand well-formedness —
which `Grass.Semantics` supplies from a `BehaviorContract` when it lands, and
which a standalone protocol supplies directly. The same applies to the third
disjunct of §7 progress ("produce an *independently specified* observation"),
which is specification-relative and is a field of that record.

**Decided — temporary custody of one bag type, handed to `c-mem`.**
`AbstractDemandBag` is used by `ProcessSpec.Step` itself, so it cannot be
deferred, and no multiset exists in Lean core or on any branch.
`Grass/Process/Bag.lean` defines `Bag α := Quotient (List.isSetoid α)`
(`List.isSetoid` and `List.Perm` are Lean 4.33.1 core; verified, no dependency
added) under explicit custody. The handover addressee is `c-mem`, who already
ships `Grass.Std.Logical.FiniteMap`; the handover milestone is whichever of M2
or `c-mem`'s next milestone comes first, and the handover is a rename plus a
re-export because this module carries no process vocabulary. The
process-specific *laws* over it (consume exactly one, no fabrication, no joint
consumption) stay here.

That definition is also mathlib's `Multiset`. [MODULES.md](MODULES.md) permits
mathlib, so hand-rolling is a choice, and it needs its own record rather than a
parenthetical: `lakefile.toml` deliberately carries no dependencies,
[FOUNDATION.md](FOUNDATION.md) §3 puts every selected dependency in the TCB and
build ledgers, and `c-mem` has already taken the no-dependency route for finite
maps. Adding mathlib for one quotient would be a repository-wide TCB decision
taken by the wrong agent. This plan therefore hand-rolls and files the
alternative in §10.6 for a [DECISIONS.md](DECISIONS.md) entry.

**Decided — the nominal history is finite, not a predicate.** An earlier draft
of this plan made `usedNominals` a `LogicalNominal -> Prop`. That is wrong.
[PROCESS.md](PROCESS.md) §3 writes `allocatedNominals : ... -> Finset
LogicalNominal`, `fresh : Disjoint ...`, and
`historyExact : after.usedNominals = before.usedNominals ∪ transition.allocatedNominals`.
An execution *prefix* is finite by construction — the history starts empty and
each step adds finitely many — so unboundedness is a property of the limit and
not of any value the union equation ranges over. A `Prop`-valued history would
make `historyExact` an equality of predicates provable only through `funext`
and `propext`, lose decidability, and leave the occurrence-count axes of
[PROCESS.md](PROCESS.md) §5 with nothing to count. The history is therefore a
finite collection with `∉` freshness and a union equation, matching the
normative declaration. No `Finset` exists in Lean core, so the representation is
a list under the same custody note as the bag; the *interface* is the normative
one.

**Decided — a run state carries the flat trace, not its segmentation.** An
earlier draft put a `Segmented` history inside `ProcessRunState`. That was a law
18 violation: `segments.length` is the number of transitions taken, so an
acceptance relation handed a segmented history could distinguish one transition
emitting two observations from two transitions emitting one each, which is
provider batching and a replaceable realization fact. The segmentation and its
origin theorems stay in `Grass/Process/Observation.lean` for the run-level
causality bookkeeping that [PROCESS.md](PROCESS.md) §4 keeps out of the
application proof, and the origin theorem is stated over an occurrence's
*position* with a uniqueness half, because a statement about observation values
would not identify a single emission.

**Decided — `List` for step segments and for prefix histories; not for maximal
runs.** [PROCESS.md](PROCESS.md) §2 writes `List Observation` for a step's
segment, and that is genuinely finite. A `ProcessRunState` carries the history
of a finite prefix, which is also genuinely finite. A *maximal* run need not be
finite — [PROCESS.md](PROCESS.md) §7: "Long-lived processes need not terminate"
— so the trace of a maximal run is not a `List` and this plan does not assume it
is. Concretely: `Grass.Process` defines segments and prefix histories as `List`,
proves no lemma by `List` induction over a maximal run, and leaves the maximal
execution and its limit trace to `Grass.Semantics`. `ProcessAcceptance`'s trace
field is stated over prefixes so it survives that arrival.

**Decided — `ProcessSpec` has two universes and `ProtocolRegistry` three.**
The interface types — external events, demands, results, observations, fault
classes — live in one universe; the private types — request, state, terminal
result, view — live in another; a registry's keys live in a third.

**Decided — the terminal-remainder law lives in `ProcessAcceptance`, and is
indexed by the partition.** See §10.5, which withdraws the earlier claim that it
had to be a `ProcessSpec` field. A law indexed by a demand value cannot express a
bound, and a bound is what law 7 and law 20 require; a law that is a mandatory
spec field is the author obligation [PROCESS.md](PROCESS.md) §3 explicitly
refuses to impose on a leaf.

**Decided — progress distinguishes entropy from the program's own activity, not
settling from non-settling.** An earlier draft made a transition progressing
whenever its event settled no outstanding demand, which gave `.fault` and
`.environmentViolation` a free pass: a process that faults in a loop, emits
nothing, and decreases no measure satisfied the condition. The disjunct is now
`ProcessEvent.externalEntropy`, so only a genuine external event counts as
waiting. `MeetsProcessProgress.silent_fault_decreases` is the corollary that
records it.

Two limits of this layer are recorded in the module rather than hidden. There is
no *declaration* of which frontiers are law-bearing — `ProcessAcceptance` carries
none — so waiting forever for entropy that never arrives passes here and must be
excluded by the network adequacy theorem. And `StepProgresses` reads a
transition's own emitted segment, which makes progress a per-specification
property to be re-proved after a refinement rather than transported.

**Decided — the segmentation is an index of `Reachable`, not a field of the run
state and not absent.** Two failed drafts bracket this. Putting `Segmented`
inside `ProcessRunState` let an acceptance relation branch on the transition
count, which breaks under a refinement that produces the same observations in a
different number of steps. Deleting it left `docs/PROCESS.md` §4's observation
causality with nothing to be stated over — the module was 186 lines with no
consumer. Carrying it as an index gives `Reachable.observationCausality` while
keeping it out of reach of `TraceAccepts`, which sees only the flat history.

**Decided — `ProcessCorrect.progress` is indexed by request.**
[PROCESS.md](PROCESS.md) §4 writes `progress : MeetsProcessProgress p`. The
implementation writes `∀ request, MeetsProcessProgress p accept Invariant request`,
because the responsiveness fields quantify over states reachable *for a request*
and the terminal disjunct mentions `p.Terminal request`. A single un-indexed
record would have to quantify internally over requests, which is the same
obligation with a worse shape.

**Decided — law 5 applies where the process is still working.**
`MeetsProcessProgress.handlesEveryEvent` demands a `Step` for every deliverable
event only at reachable states the specification does not call terminal. The
guard is not a weakening: without it the field contradicts
`ProcessCorrect.terminalNoStep`, because the running state a terminating run
fires `terminate` from is reachable *and* terminal, so no terminating process
had a `ProcessCorrect` at all. At a terminal state the obligation is to
terminate, which is `notStuck`'s left disjunct.

**Recorded — this layer cannot exclude a self-delivered livelock.**
`StepProgresses`'s entropy disjunct asks whether the arriving event was
`.external`, and `ExternalEvent` is chosen by the specification author. A
process can therefore route its own internal work through a self-delivered tick,
satisfy the disjunct forever, never terminate, never emit, and never decrease
its measure — and it has a complete `ProcessCorrect`.

Excluding it needs a declaration that a given external event is genuinely
produced by the environment, which `ProcessAcceptance` does not carry and this
layer cannot check. [PROCESS.md](PROCESS.md) §7 puts the burden on the network,
and §6 below carries it as an M4 exit obligation rather than leaving it implied.

**Decided — `ProtocolRegistry` is universe-polymorphic from M1.**
[PROCESS.md](PROCESS.md) §4 makes a flattened realization's private state
`LogicalProcessNetwork r.plan`, which ranges over every registered protocol's
`State`, so `r.flatten` lives strictly above the registry that produced it, and
`RegisteredProcess` demands an embedding of the old registry into the extended
one across that shift. Freezing `protocol : Key -> ProcessSpec` at one universe
in M1 would guarantee a rewrite of every registry value in M4.

The split has to reach inside `ProcessSpec` and not only the registry. With one
universe parameter for all of a spec's types, moving a flattened process's
private state up would drag its `Demand` and `Observation` up with it, and every
demand-multiplicity and observation-projection theorem would then need
transporting through a lift. With the split, flattening moves the private
universe and leaves the interface universe alone, so those theorems transport by
identity. M1 carries the fixture: two protocols sharing one interface universe,
one of whose private state is built from the other's run states, registered
together. This is risk 3 of the earlier draft, resolved rather than deferred.

**Decided — a `PEmpty` fault or violation class is an assumption until M2
discharges it.** Carrying `InterruptReason`, `LogicalFault`, and
`EnvironmentViolation` per vocabulary (§10.6) moves an obligation rather than
removing one. With a single global classification, "the network may deliver an
environment violation to this process" is handled by every process by
construction. With per-vocabulary classes, a process whose class is `PEmpty` has
made the corresponding `NetworkTransition.environmentViolation` unconstructible
rather than handled. That is sound only once the transition carries a total
classification from the delivering side's classes into the receiving
vocabulary's, exactly as `ChildDemandBinding.classify` does at a child boundary.
That classification is an M2 exit item for `Network/Transition.lean`; until it
exists, an empty class is an explicit assumption about the environment, and the
source says so rather than implying the obligation is gone.

## 3. M1 — Author vocabulary freeze

**Status: written, unmerged, unratified.** The modules and fixtures below are
committed on the `c-process` product branch and `lake build` is green with
`warningAsError`. They are not merged: [AGENT_REVIEW.md](AGENT_REVIEW.md) makes
merge reviewer-owned, and no nomination has run. Several of the shapes below
also depend on §10 entries that are proposals, not decisions. A transitive axiom audit over the
new declarations reports only `propext`, `Quot.sound`, and `Classical.choice`,
which is the [FOUNDATION.md](FOUNDATION.md) §3 allowlist.

Four adversarial review rounds have been absorbed. Two of them found defects
worth recording, because both are the kind an M1 freeze exists to catch:

- the terminal disposition was multiplicity-blind, so one claim about a demand
  *value* discharged any number of outstanding occurrences of it;
- `MeetsProcessProgress.handlesEveryEvent` and `ProcessCorrect.terminalNoStep`
  contradicted each other for every process that terminates other than
  immediately, so `ProcessCorrect` was *uninhabited* and nothing noticed,
  because no fixture built one.

The second is why §3.3 now requires a positive correctness fixture and not only
run-relation fixtures.

Goal: a protocol author, a standard-library protocol, a serial author, and the
sequential adapter can write final source. Exit criterion is expressiveness plus
a fixture corpus, not depth of proof.

### 3.1 Modules

```text
Grass/Process/Scope.lean        nominal scope identities and containment
Grass/Process/Bag.lean          demand multiset, custody, consume-exactly-one
Grass/Process/Observation.lean  observation segments, prefix histories, origin
Grass/Process/Vocabulary.lean   ProcessVocabulary, ProcessEvent, fault classes
Grass/Process/Spec.lean         ProcessSpec, ViewFacet, DeterministicProcess
Grass/Process/Run.lean          run states, initial forms, transitions, runs
Grass/Process/Acceptance.lean   the acceptance record ProcessCorrect consumes
Grass/Process/Progress.lean     the §7 per-process progress condition
Grass/Process/Correct.lean      ProcessCorrect and its derived facts
Grass/Process/Nominal.lean      LogicalNominal, finite monotone history
Grass/Process/Protocol/Registry.lean  ProtocolRegistry, open fragments, merge
Grass/Process/Network/Boundary.lean   DriverBoundary, requirement sets
Grass/Process/Sequential/Machine.lean SequentialMachine, SequentialDecision
```

`Sequential/Machine.lean` is in M1 by §1's test: it is what a serial author
writes, and its one theorem — that finitely many internal decisions reach a
frontier — is provable from the author's own rank with nothing else in scope.

`DirectRelationalProgram` is *not* in M1, despite an earlier draft placing it
here. [PROCESS.md](PROCESS.md) §4 calls it the low-level escape hatch for
genuinely relational sequential machines and says ordinary serial programs use
`SequentialMachine`; its dependent effect-site inventory and child bindings need
the occurrence machinery, so it moves to M4 with the adapter.

### 3.2 Why these and not more

`ProcessSpec` and `ProcessCorrect` are what every other agent's source mentions.
`ProcessRunTransition` is in M1 rather than M2 because the demand-bag equations
in it are what make `Step`'s signature *mean* anything; freezing the signature
without them would freeze a shape whose linearity is unchecked.

`Progress` is in M1 because [PROCESS.md](PROCESS.md) §7 states the per-process
condition concretely: decrease a well-founded internal measure, reach a
law-bearing external or demand-result frontier in finite internal work, or
produce an independently specified observation. Only the third disjunct is
specification-relative, and it reaches the condition through
`ProcessAcceptance`. The *network* progress theorem of the same section is
explicitly not here; see §6.

The view facet, the deterministic constructor, and the `.external`/`.result`/
`.interrupted`/`.fault`/`.environmentViolation` event split are all M1 because
they appear in authored `ProcessSpec` values in Spikes 4 and 5.

### 3.3 Fixtures

M1 is not exited on a type-checking file. It is exited on a fixture corpus under
`Tests/Process/` that an adversarial reviewer can read:

- a zero-demand silent step;
- two equal-valued demands with distinct multiplicity, one resolved;
- a result that consumes exactly one item and issues a new one;
- an interruption consuming an item without a result;
- a terminal state that classifies a nonempty remainder;
- a terminal state that provably *cannot* be reached, because the specification
  permits no disposition for a demand still outstanding — stated as the
  non-existence of a classification, so the obstruction is unconstructibility
  and not a missing proof;
- a classification of a two-occurrence bag whose parts still count two, which is
  what a value-indexed disposition function would have lost;
- a zero-transition terminal run (the `ProcessRunInitial.terminal` case);
- a deterministic `update` process and its relational image, with the theorem
  that the image's runs are exactly the function's;
- two protocols sharing one interface universe, one of whose private state is
  built from the other's run states, registered together with the embedding of
  every prior key (the §2.2 stratification fixture);
- a terminating process with a complete `ProcessCorrect` and
  `MeetsProcessProgress`, including the derived "no reachable state is stuck"
  theorem. This one is not optional: the two records had contradictory fields
  through three review rounds precisely because nothing inhabited them;
- a terminal-remainder law that constrains only `pending`, with the proof that
  it bounds nothing — the same occurrences can be relabelled `resolved`. The
  trap is a theorem rather than a warning in a docstring.

These are `Tests/Process/M1Fixtures.lean` and
`Tests/Process/M1CorrectFixtures.lean`, built by a `Tests` Lake library that is
a default target, so a green build means they still hold.

Each fixture states a theorem, not an `#eval`. [FOUNDATION.md](FOUNDATION.md)
law 3 forbids an executed example standing in for a proof.

## 4. M2 — Network semantics

**Status: five of ten modules, unmerged.** Committed with fixtures:
`Network/Exposure.lean`, `Network/Graph.lean`, `Network/Topology.lean`,
`Network/Structural.lean` (the canonical network, `coord1:4`), and
`Network/Delivery.lean` (the total cross-vocabulary classifier that `g-design:4`
made a condition of per-vocabulary fault classes). Not started: assertions,
channels, the plan, the transition family, child bindings, mailbox profiles, and
the commit law. **None of the exit criteria below is discharged.**

Two structures here are named for what they are rather than for what a reader
might assume. `ProcessTopologyCore` carries graph, channels and spawn authority
only, with `ProcessTopology requirements` reserved for the aggregate carrying
the demanded facets (§10.8, `g-design:5`). An earlier draft also gave the core a
channel well-formedness field requiring an edge's endpoints to be spawn-adjacent,
which [PROCESS.md](PROCESS.md) §3 does not declare and which wrongly rejected
every edge between the root and a role that is not its direct child; channel
connectivity is a plan-level obligation.

Goal: the exhaustive transition family, with each constructor's exactness
carried in its own index rather than in an ambient predicate.

```text
Grass/Process/Network/Exposure.lean    ProtocolExposesBoundary, observation projection
Grass/Process/Network/Graph.lean       ProcessGraph, population, logical access
Grass/Process/Network/Topology.lean    refs, generations, channel ids, epochs
Grass/Process/Network/Structural.lean  the one canonical structural network
Grass/Process/Network/Delivery.lean    total cross-vocabulary fault classification
Grass/Process/Network/Assertion.lean   network assertions, separating conjunction
Grass/Process/Network/Channel.lean     ChannelContract, escrow, session, resolution
Grass/Process/Network/Plan.lean        ProcessPlan, LogicalProcessNetwork
Grass/Process/Network/Transition.lean  NetworkTransition, NetworkStep, freshness
Grass/Process/Network/Child.lean       child requests, bindings, lifecycle events
Grass/Process/Network/Mailbox.lean     ordering profiles, selective receive
Grass/Process/Network/Commit.lean      the commit transition and view reconciliation
```

`NetworkTransition` has twenty-three constructors, four of which
(`requestCancel`, `acknowledgeCancel`, `timeout`, `interrupt`) an earlier draft
of this plan put in M3 and one of which (`commit`) it scheduled nowhere. That
was wrong: the transition *indices* are `NetworkTransition` content and belong
here, while the cancellation *policy* that decides where points may be placed is
M3. `Commit.lean` carries [PROCESS.md](PROCESS.md) §6, including the rule that
a reconciler may coalesce pending renders "only when no skipped render has a
demanded commit observation".

Exit criterion, in three parts, because the earlier single criterion was not
dischargeable in this milestone:

- routing coverage: every endpoint input and output enters through exactly one
  constructor, over all twenty-three;
- the escrow prefix laws — conservation, at-most-one resolution, and stability
  under unrelated steps — over that same full family;
- a total classification from the delivering side's interrupt, fault, and
  violation classes into each receiving vocabulary's, so that the `PEmpty` case
  of §2.2 is discharged rather than assumed;
- an explicit re-proof obligation, recorded rather than discharged, for the two
  facts that genuinely need later milestones: `insufficient_credit_disables_send`
  and `EveryNetworkStepHasExactCapacityTransitionLaw` need M5's credit ledger,
  so M2 states send-enabledness parametrically in a credit predicate and M5
  instantiates it.

The known hard part is `NetworkAssertion` and its separating conjunction. This
plan does **not** build a general separation logic: the assertion language is
over the logical process network only (instances, shared regions, escrow ledger,
sessions, obligations, observations), and `*` is disjointness of the named
fragments. Physical separation is `c-mem`'s and is reached only through the
representation relation.

## 5. M3 — Cancellation and lifecycle

**Status: one module landed early.** `coord1:6` ruled the canonical scoped
cancellation form while M2 was in progress, so `Cancellation/Policy.lean` and its
two invalidation fixtures were built out of order to discharge that disposition.
The rest of M3 — masks, the `|>` algebra, termination contracts, facets, and all
of byte flow — has not started, and the exit criterion below is undischarged.

```text
Grass/Process/Cancellation/Policy.lean scoped policy and certificate (landed early
                                       under coord1:6, ahead of the rest of M3)
Grass/Process/Cancellation.lean        masks, summaries, the |> algebra
Grass/Process/Termination.lean         modes, contracts, dispositions
Grass/Process/Facet.lean               TerminationFacet and its constructors
Grass/Process/Policy.lean              CancellationPolicy, scoped certificates
Grass/Process/ByteFlow/Ingress.lean    phases, resolutions, conservation
Grass/Process/ByteFlow/Egress.lean     offered/committed/queued, suffix retention
Grass/Process/ByteFlow/Rechunk.lean    functional and capacity-aware rechunking
```

Exit criterion: the `uncancellable |> cancelpoint |> uncancellable` worked
example from [PROCESS.md](PROCESS.md) §3 is a theorem, the sequential
composition of summaries is associative up to the stated transport, and both
byte-flow conservation theorems hold over their full transition families.

Byte flow is here rather than in M2 because its phases are a cancellation race
in disguise: `cancelling` is a phase, and the resolution tables are the
substance. Its hard block on `c-mem`'s buffer loans is recorded in §2.1.

`Policy.lean` is scheduled against an unresolved corpus ambiguity; see §10.3.
It is written last in this milestone, after that entry is ratified.

## 6. M4 — Composition, lowering, and the proof package

**Status: not started.**

```text
Grass/Process/Trace/Independence.lean   Independent, diamonds, swap congruence
Grass/Process/Trace/Linearization.lean  syscall partial orders
Grass/Process/Proof/Adequate.lean       ProcessNetworkAdequate, network progress
Grass/Process/Proof/Simulation.lean     ProcessNetworkSimulation
Grass/Process/Proof/Realizes.lean       ProcessPlanRealizes, ProcessRealization
Grass/Process/Proof/Driver.lean         ProcessDriver, ProcessLoopInvariant
Grass/Process/Proof/Scope.lean          ScopedProcessPlan, SubsystemRealization
Grass/Process/Blend.lean                ClosedBlendProvenance, ProcessPlanSource
Grass/Process/Flatten/Flatten.lean      ProcessRealization.flatten and its theorem
Grass/Process/Flatten/Serialize.lean    SerializablePlan, serialize, round trips
Grass/Process/Function/Serial.lean      SerialFunctionContract and the call rule
Grass/Process/Function/Export.lean      asSerialFunction, the fractal bridge
Grass/Process/Sequential/Adapter.lean   elaborateMachine and its transport
Grass/Process/Sequential/Standard.lean  the standard realizer registry and lookup
Grass/Process/Weave/Mixin.lean          WeaveInvariantMixin, families, aggregate
Grass/Process/Weave/Lens.lean           ProcessRefinementLens, contextual framing
```

The `Proof/` directory is [MODULES.md](MODULES.md)'s name for exactly this
content — "adequacy, simulation, global-loop lifting, physical templates" — and
`ProcessPlanRealizes` is the closing theorem of Spikes 4 and 5, so this
milestone is what makes any spike statable. `Blend.lean` is a spike import
(`Grass.Process.Blend`) and is here for the same reason.

This milestone needs `Grass.Semantics`. If that layer is still unclaimed when M3
exits, the `SpecProcess`-indexed statements are the only part that waits; the
adapter, flattening, and independence results are all statable over
`DriverBoundary` and `ProcessPlan` alone.

Exit criteria:

- `flatten_sequential_roundtrip` and `serialize_refines_flatten`, because those
  two are what make law 17 true rather than aspirational;
- the network progress theorem of [PROCESS.md](PROCESS.md) §7: every maximal
  network execution produces a demanded observation, remains at a declared
  frontier, or decreases a global well-founded rank across process steps, spawn,
  retry, cancellation, death, join, and restart, with supervision carrying a
  restart bound. This must in particular exclude the self-delivered livelock
  §2.2 records, which per-process progress admits: the "declared frontier" has
  to be a declaration about the environment, not about the event type;
- the five canonical adapter fixtures [PROCESS.md](PROCESS.md) §4 mandates by
  name — zero-effect transition, duplicate equal-valued effects with distinct
  occurrences, initially pending effects, issue-then-cancel, and
  result-plus-new-effect in one transition — each checked in both execution
  directions against the exact pending equation and child binding;
- the proof-economics acceptance rule of the same section: selecting a
  registered standard sequential specification is one expression at the
  application process boundary. This is checkable — it is a line count on a
  fixture, not a preference — and if it fails, the constructor is incomplete.

## 7. M5 — Certificates and sharding

**Status: not started.**

```text
Grass/Process/Shard/Signature.lean      ProcessSignature, RealizesProcessSignature
Grass/Process/Shard/Certificate.lean    opaque shard certificates
Grass/Process/Shard/Facet.lean          facet summaries and certificates
Grass/Process/Shard/Compose.lean        composition, SCC condensation, aggregates
Grass/Process/Shard/Root.lean           RootProcessCertificate
Grass/Process/Resource/Metric.lean      NetworkResourceState, ResourceMetric
Grass/Process/Resource/Credit.lean      capacity credit, ledgers, backpressure
Grass/Process/Resource/Scope.lean       scope partition, boundary flux, bounds
```

Exit criteria are theorems, plus a structural check, plus a measurement:

- `ScopedProcessPlan.projectionExact` and
  `SubsystemRealization.siblingInsensitive` as Lean theorems.
  [PROCESS.md](PROCESS.md) §5 states the second as "structural: an outside-scope
  edit leaves the induced nodes, edges, imported summaries, and demand keys
  definitionally equal", which is provable with no tooling at all;
- an import-graph check per [OLEAN_SHARDING.md](OLEAN_SHARDING.md) §2: no
  consumer imports a `ProcessImpl`, and aggregate modules import only child
  certificate modules;
- the [PROCESS_SHARDING.md](PROCESS_SHARDING.md) §9 locality scenarios as
  corroboration *once* the ratchet tooling exists. An earlier draft made this
  the only exit criterion, which would have discharged a stated theorem through
  a tool that [IMPLEMENTATION_RATCHET.md](IMPLEMENTATION_RATCHET.md) says does
  not exist.

## 8. Standing risks

1. **`NetworkAssertion` scope creep.** If the assertion language grows toward a
   general separation logic it will eat this plan. The mitigation is that it is
   defined only over the named network fragments and has no frame rule beyond
   the one `WeaveInvariantMixin` needs.
2. **The `ChannelContract` field count.** Fifteen fields is a signature an
   application author must never fill by hand. If the standard channel profiles
   (identity-correlated reply, ordered mailbox, bounded byte flow) do not cover
   the spikes, the contract is wrong, not the spikes.
3. **M4 is large.** It carries the proof package, the adapter, flattening,
   weaving, and the network progress theorem. It is the milestone most likely to
   need splitting; the split line, if needed, is between the `Proof/` package
   (which needs `Grass.Semantics`) and everything statable over `ProcessPlan`
   alone.
4. **`Grass/Process/Bag.lean` has no owner to hand back to.** Not merely an
   unassigned one: `g-foundation:6` declined `Grass/Std/Logical` as outside its
   mandate, so the layer `docs/MODULES.md` assigns the multiset to is
   unclaimed, and `coord1` is routing it. The custody note in that module names
   `c-mem` as its addressee, which is now stale. Until the routing lands, a
   process-layer module owns a general collection type, which
   `docs/FOUNDATION.md` law 11 tolerates only as the temporary arrangement it is
   declared to be.
5. **`import Grass.Process`.** Spikes 4 and 5 import a single module.
   [OLEAN_SHARDING.md](OLEAN_SHARDING.md) §2 forbids a *leaf* importing an
   umbrella. A spike is a client, not a leaf, so a curated author-surface facade
   is defensible — but it must re-export the author vocabulary only, never every
   certificate module, and no `Grass.Process.*` module may import it.

## 8a. Temporary custody: what is held, and on what gate

Three pieces on this branch were taken under explicitly temporary custody
because no owner existed. `agent-bus` issue `c-process:28` asked `coord1` for
sequencing now that `g-foundation` has registered; `coord1:19` answered **hold
all three and keep maintaining them**, and made a distinction worth recording:
registration is not a scope claim, and these are three items on three different
gates rather than one bucket.

| Item | Gate | Status |
|---|---|---|
| `Grass/Process/Bag.lean` | does `Grass/Std/Logical/**` have an owner at all? (`coord1:14`) | `g-foundation` claims neither `Std/Logical` nor `Specification`; if the answer is no, Bag has *no* owner rather than a new one |
| `Grass/Specification/Scope.lean` | owner only — the naming gate cleared | held |
| `Grass/Specification/Boundary.lean` | same | held |

`coord1:22` reports one gate moved and two did not. The **naming** gate is
cleared: `g-design:13` ruled on `coord1:16` and `g-foundation:7` agreed to
rename `Grass/Semantics/Specification.lean` to `Grass/Semantics/SpecProcess.lean`,
so `Grass.Specification` unambiguously names the neutral layer and no rename is
pending here. Both **ownership** gates remain closed, and `Bag.lean`'s position
got worse rather than better: `g-foundation:6` *declined* `Grass/Std/Logical`
as outside its mandate rather than deferring, so that path has no owner at all
and `coord1` is routing it.

Release order once the gates clear, per `coord1:19`: `c-mem`'s `Grass/Core`
offer first, then `Bag`, then the `Specification` pair last. No
`handoff.offered` before `coord1` says a gate has cleared.

**Prepared for the eventual offer**, so the receiving owner inherits them as
declared facts rather than discovering them: `Bag` is a hand-rolled
`Quotient (List.isSetoid _)` rather than mathlib's `Multiset` (§10.10), and the
finite sets in `Specification/Scope.lean` and `Process/Nominal.lean` are
duplicate-free `List`s rather than a `Finset`. Both are recorded in the module
docstrings and belong in the offer's `known_issues`. This plan takes no position
on whether they should change; that is for whoever accepts.

## 9. Review

**No work scheduled by this plan has been merged or reviewed in the sense
[AGENT_REVIEW.md](AGENT_REVIEW.md) means.** That protocol requires the author to
nominate a distinct reviewer on the agent bus, and that reviewer — not the
author — to select a snapshot, authorize, and merge. It has not run, and the bus
tool is not yet available.

What has happened is local iteration: adversarial review agents spawned by the
author, with fresh context each round, to find defects early. That found real
ones — a multiplicity-blind terminal disposition, an uninhabitable
`ProcessCorrect` — and it is not a substitute for the nomination. An author
reviewing their own work through an agent they instructed is still an author
reviewing their own work.

Each milestone is offered for that nomination after local iteration stops
finding defects, against [REVIEW.md](REVIEW.md) and the distinct-author rule.

The questions a reviewer of this layer should ask first:

- does any authored `ProcessSpec` field mention an occurrence identity, a
  worker, a queue, or a schedule? (law 18)
- can a demand bag element be fabricated, duplicated, jointly consumed, or lost
  by any transition in the family? (§2)
- is there a transition that resolves an occurrence without consuming its affine
  token? (law 16)
- does any freshness claim quantify over the live set rather than the monotone
  history? (law 22)
- does a serial author's source mention a channel, population, or escrow?
  (law 17)
- is any acceptance, progress, or observation-filter fact defined here rather
  than consumed from the specification? (law 11)

## 10. Corpus defects found while planning

These were raised for ratification, not resolved by this plan. **Every one has
now been ruled**, through the `agent-bus` protocol, and each entry below records
its disposition and what `c-process` did in response. The rulings are on the bus
as `coord1:4` through `coord1:8` and `g-design:4` through `g-design:6`;
`g-design` is transcribing them into [DECISIONS.md](DECISIONS.md), which is
their exclusive file.

Three entries are implemented and closed (`c-process:4`, `:5`, `:6`, `:7`); one
is implemented on the library side with its spike half delegated (`c-process:3`,
dependency `c-process:26`); and the three ratification questions are ruled with
their implementations landed.

| Entry | Bus issue | Ruling | State |
|---|---|---|---|
| §10.1 duplicate network | `c-process:3` | `coord1:4` | library + three docs done; spikes with `g-design` |
| §10.2 Process/Semantics cycle | `c-process:4` | `coord1:5` | closed; `MODULES.md` with `g-design` |
| §10.3 `CancellationPolicy` arities | `c-process:5` | `coord1:6` | closed |
| §10.4 `ProcessNetwork` arity | `c-process:6` | `coord1:7` | closed |
| §10.5 terminal disposition | — | withdrawn by author | closed |
| §10.6 per-vocabulary fault classes | `c-process:9` | `g-design:4` | ratified with a constraint; implemented |
| §10.7 spike resync | `c-process:26` | `g-design:9` | `g-design` owns the synchronized update |
| §10.8 topology facets | `c-process:10` | `g-design:5` | ratified; renamed `ProcessTopologyCore` |
| §10.9 `EffectDemand` undeclared | `c-process:7` | `coord1:8` | ratified as abbreviations; closed |
| §10.10 hand-rolled multiset | — | — | open, low; `g-foundation` now owns that layer |

What follows is each entry as originally raised, with its ruling appended, so
that the reasoning that produced the question survives alongside the answer.

### 10.1 `AbstractSpecificationProcessNetwork` is declared twice, incompatibly

**Ruled `coord1:4`.** One canonical structural abstraction, owned by Process,
carrying no `BehaviorContract`, `denotation`, `traceDenotation`, or exactness
field, generalized over its protocol family. Implemented as
`Grass/Process/Network/Structural.lean`, with `PROCESS.md`, `SEMANTICS.md` and
`REFINEMENT.md` corrected together and an elaborating fixture preventing either
historical field family from returning. The spike surfaces are delegated to
`g-design` as dependency `c-process:26`, accepted in `g-design:9`, because they
also need `g-design:4`'s vocabulary shape and the mirror check compares them
byte-for-byte.

[PROCESS.md](PROCESS.md) §2 declares it with fields `registry`, `root`,
`channels`, `linearState`, `sharedState`, `abstraction`, `denotation`,
`traceDenotation`, `exact`. [SEMANTICS.md](SEMANTICS.md) declares a different
structure of the same name with fields `RoleSchema`, `finiteSchemas`,
`Instance`, `protocol`, `instances`, `composition`. Every consumer uses the
second shape: `Spikes/4_Web_Server/Process.lean` passes `roleSchema` and
`instances`, `Spikes/5_Spinning_Cube/Process.lean` reads `.protocol schema`, and
[REFINEMENT.md](REFINEMENT.md) mixes both, reading `network.RoleSchema` *and*
`network.traceDenotation`.

[README.md](README.md) forbids a document restating a narrower owner's term
differently and requires that every term have one owner. Proposed resolution:
the [SEMANTICS.md](SEMANTICS.md) shape is normative, because it is the one the
spikes and [REFINEMENT.md](REFINEMENT.md) instantiate; the
[PROCESS.md](PROCESS.md) declaration becomes a reference, and the fields it
carries that the other lacks (`traceDenotation`, `exact`) are relocated to the
owner or dropped with a reason. Blocks: M4 `Proof/Realizes.lean`.

### 10.2 Process and Semantics are mutually dependent

**Ruled `coord1:5`.** An acyclic diamond: neutral vocabulary below both,
Semantics owning `SpecProcess` and `BehaviorContract`, Process owning
replaceable structural networks, Refinement owning `ProcessPresentation`.
Implemented as `Grass/Specification`, pinned by a fixture that elaborates the
neutral layer with no `Grass.Process` declaration in scope. `MODULES.md` is
`g-design`'s and was requested as `c-process:17`, accepted in `g-design:7`.

[SEMANTICS.md](SEMANTICS.md) defines `SpecProcess.driverBoundary` in terms of
`DriverBoundary` and `ProcessPresentation` in terms of the abstract network,
both of which [PROCESS.md](PROCESS.md) owns; while [PROCESS.md](PROCESS.md)'s
abstract network carries `denotation : BehaviorContract resources`, which
[SEMANTICS.md](SEMANTICS.md) owns. [MODULES.md](MODULES.md) declares the chain
strict, so this is a cycle rather than a missing edge.

Proposed cut: `DriverBoundary` is a pure interface record — external event,
demand, dependent result, observation, requirement set — with no semantic
content, so it belongs in a module strictly *below* `Grass.Semantics`, and
`Grass.Semantics` imports it. The abstract network's `denotation` field is the
only genuinely semantic one, so the network splits: the shape (roles,
instances, protocols) below, the denotation and its exactness above, meeting at
`ProcessPresentation`. Blocks: any `Grass.Semantics` work, and M4.

### 10.3 `CancellationPolicy` has four incompatible arities

**Ruled `coord1:6`.** The scope-indexed form is canonical, `blockingCalls` is
the field name, whole-plan cancellation is hierarchical composition of scoped
certificates, and spike syntax is elaborator sugar rather than a second arity.
Implemented as `Grass/Process/Cancellation/Policy.lean` with both documents
corrected and the two fixtures the ruling names.

- `Spikes/4_Web_Server/Cancellation.lean` writes `CancellationPolicy memoryServerProcess`
  — indexed by a `ProcessSpec`.
- [PROCESS.md](PROCESS.md) §5 writes `CancellationPolicy (network : ProcessNetwork root) (source : MachineSource plan)`.
- [PROCESS_SHARDING.md](PROCESS_SHARDING.md) §4 writes
  `CancellationPolicy scope.publicCancellationPoints` — indexed by a scope
  summary.
- The field is `policy.blockingCalls` in [PROCESS.md](PROCESS.md) §5 and
  `policy.calls` in [PROCESS_SHARDING.md](PROCESS_SHARDING.md) §4.

Proposed resolution: the scope-indexed form is normative, because it is the only
one whose `callsExact` is local; the §5 form is the whole-plan scope; the spike
form is shorthand for the scope induced by a root protocol; the field is
`blockingCalls`. Blocks: M3 `Policy.lean`.

### 10.4 `ProcessNetwork root` and `ProcessPlan root` are undeclared arities

**Ruled `coord1:7`.** The spelling is deleted; `ProcessPlan` is applied only
at its declared parameters. Done in `PROCESS.md`.

[PROCESS.md](PROCESS.md) §5 writes `ProcessNetwork root`, a type that appears
nowhere else in the corpus, and `ProcessPlan root`, while §3 declares
`ProcessPlan (registry : ProtocolRegistry) (boundary : DriverBoundary)`.
Proposed resolution: both are the §3 `ProcessPlan`, with `root` an abbreviation
for a plan whose root protocol is named; `ProcessNetwork` is deleted or defined.
Blocks: M3 `Policy.lean`, M4 `Proof/Driver.lean`.

### 10.5 Withdrawn: `ProcessSpec` does not need a terminal disposition field

**This entry previously claimed a corpus defect and was wrong.** It said that
[PROCESS.md](PROCESS.md) §2 requires a terminating run to dispose of every
outstanding demand "according to the specification's progress/lifecycle law",
that the declared `ProcessSpec` contains no field in which that law could live,
and that a field therefore had to be added.

§3 already owns that law. `ProcessTerminationContract.disposition` and
`TerminationFacet` are the lifecycle machinery, and the section is explicit that
they are a *facet* attached where a promise is exported:

> `ProcessCorrect` itself retains only ordinary invariant, terminal,
> observation, demand, and progress facts. A process plan attaches
> `TerminationFacet` only when the process exports a cancellation/restart/upgrade
> promise or another component relies on one. … Pure serial functions,
> straight-line helpers, and uncancellable leaf processes gain no new author
> obligation.

A mandatory field on every `ProcessSpec` is exactly the obligation that sentence
refuses. The name collides too, though an earlier draft of this entry described
the collision wrongly: §3 binds `TerminalDisposition p state` to the per-state
disposition a termination contract produces, carrying `exactTransfer` over
state, resources, loans, and obligations. That is a *related* concept, which is
what makes reusing the name for a second thing a [README.md](README.md)
one-owner violation rather than a coincidence.

**Resolution, implemented.** The law is `TerminalRemainderLaw` in
`Grass/Process/Spec.lean`, and it is supplied through `ProcessAcceptance`.

One caveat, because the relocation is weaker than it first looks. For an
acceptance that is *derived* — built from a `BehaviorContract`, or composed by a
weave — the obligation genuinely leaves the protocol author. For a standalone
protocol whose author writes both records, the field moved one record over; what
it buys there is that a reviewer can see a lifecycle claim being made, not that
nobody makes it. It is
indexed by the three sub-bags of the terminal partition rather than by a demand
value, because the obligation law 7 and law 20 need is a *bound*: a law indexed
by a value permits `tick` to be left pending and thereby permits any number of
outstanding ticks at once, which the count in `card_partition` makes visible but
does not prevent. `Tests/Process/M1Fixtures.lean` carries the negative fixture —
a run holding three ticks provably cannot terminate under a law that permits
two.

The three outcome names (`resolved`, `transferred`, `pending`) are
[PROCESS.md](PROCESS.md) §2's own words. Their relation to
[OBLIGATIONS.md](OBLIGATIONS.md) §3's five terminal dispositions is a mapping
this layer owes when obligations land; in particular `pending` has no evident
counterpart there and may turn out to require one.

Blocks: nothing. The withdrawal removes the spike churn §10.7 predicted for this
entry; §10.6's four-field addition is now three.

### 10.6 The fault, interruption, and violation classes are carried per vocabulary

**Ruled `g-design:4`.** Per-vocabulary classes are ratified, *with a
constraint*: selection belongs at a reusable protocol boundary rather than
adding bespoke fields to every ordinary author surface. `ProcessSpec` therefore
has a `vocabulary` field instead of extending `ProcessVocabulary`, so an author
writes one line and no interface fields. Cross-vocabulary delivery owes a total
classifier — an empty class must *prove* unreachability rather than bypass fault
handling — which is an M2 obligation on the transition family.

[PROCESS.md](PROCESS.md) §2 writes `InterruptReason`, `LogicalFault`, and
`EnvironmentViolation` unqualified in `ProcessEvent`, as one fixed global
classification. This plan carries them in `ProcessVocabulary`, because a global
`LogicalFault` is the closed whole-program sum
[PROCESS_SHARDING.md](PROCESS_SHARDING.md) §10 lists as a foundational failure —
HTTP/2 error codes, Vulkan device loss, and a Win32 handle violation are the
fault classes of unrelated subsystems — and [FOUNDATION.md](FOUNDATION.md) law 8
forbids the `| other (name : String)` escape. Blocks: nothing; it is
implemented, and needs ratification.

### 10.7 The spike sources must change with the deviations

`Spikes/4_Web_Server/Process.lean` and `Spikes/5_Spinning_Cube/Process.lean`
write `ProcessSpec` literals supplying eleven fields. The deviation in §10.6
adds three mandatory fields to every authored spec — `InterruptReason`,
`LogicalFault`, and `EnvironmentViolation` — so neither spike literal would
elaborate against the declaration as implemented.
[MODULES.md](MODULES.md) makes those files the golden author-surface test, and
`check-spike-sources.ps1` compares them against the fenced blocks in
[SPIKE_4.md](SPIKE_4.md) and [SPIKE_5.md](SPIKE_5.md) rather than against the
library, so the existing gate will not catch it.

The spike sources and their document blocks therefore move in lockstep with
§10.6 when it is ratified. This plan does not change them
unilaterally: they are shared review fixtures, and editing them before
ratification would encode an unratified decision in the golden surface.
Blocks: nothing yet; it is ratification's first consequence.

### 10.8 Cancellation and supervision are facets, not `ProcessTopology` fields

**Ruled `g-design:5`.** The facet split is ratified so simple processes pay no
ceremony, *and* the weaker exported structure is renamed `ProcessTopologyCore`,
with `ProcessTopology` reserved for the aggregate carrying every required facet.
That closes `g-reviewer`'s `topology-laws-omitted` finding, which was about the
name rather than the split.

[PROCESS.md](PROCESS.md) §3 declares `ProcessTopology` with three law fields:
`spawn`, `cancellation`, and `supervision`. The implementation carries only
`spawnAuthority`.

[PROCESS_SHARDING.md](PROCESS_SHARDING.md) §3 requires a composition invariant
to depend "on the smallest named facet that supplies its facts", and §10 lists
as a foundational failure "a composition witness indexed by the complete
realization plan when each field consumes only a facet". A `ChannelContract`
consumes the endpoints and the spawn authority; it does not consume a restart
intensity window. With all three in one record, every channel proof would depend
on the supervision policy, and adding a cancellation point would rebuild proofs
that cannot mention one — which is exactly the mutation
[PROCESS_SHARDING.md](PROCESS_SHARDING.md) §9 requires to stay local.

Proposed resolution: cancellation and supervision are certificates over a
topology rather than fields of it, landing with M3, and the §3 declaration is
amended. Blocks: nothing; the split is implemented and M3 depends on it.

### 10.9 `EffectDemand` and `EffectResult` are undeclared

**Ruled `coord1:8`.** Ratified as abbreviations of the boundary's demand and
dependent result — the identification that had been frozen. Declared in
`PROCESS.md` and in `Sequential/Machine.lean`, with the fixture the ruling names.

[PROCESS.md](PROCESS.md) §4 writes
`SequentialDecision.effect (demand : EffectDemand boundary) (resume : EffectResult demand -> State)`
and `DirectRelationalProgram` uses `AbstractDemandBag (EffectDemand boundary)`.
Neither `EffectDemand` nor `EffectResult` is declared anywhere in the corpus —
the same defect class as §10.4's `ProcessNetwork root`.

`Grass/Process/Sequential/Machine.lean` currently identifies them with
`boundary.Demand` and `boundary.Result`. The surrounding text does not obviously
support that: §4 speaks of "structured dynamic effects", "an inventory of
possible sites", and "one reusable dependent result/boundary constructor" per
new effect protocol, which suggests a layer between an authored effect and a
boundary demand.

Proposed resolution: either ratify `EffectDemand boundary := boundary.Demand`,
or declare the intended type. This matters before M4, because the adapter's
`Pending` equation is stated over it and the identification is already frozen in
the serial authoring surface. Blocks: M4 `Sequential/Adapter.lean`.

### 10.10 A multiset is hand-rolled rather than taken from mathlib

Recorded in §2.2. The decision is reversible and local: `Grass/Process/Bag.lean`
is one module with a documented custody note, and adopting mathlib later is a
deletion. Blocks: nothing.
