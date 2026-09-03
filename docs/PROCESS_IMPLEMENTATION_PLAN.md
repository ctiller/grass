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

**Status: fifteen of fifteen modules written; unmerged, unratified.** Written
with fixtures: `Network/Exposure.lean`, `Network/Graph.lean`,
`Network/Topology.lean`, `Network/Structural.lean` (the canonical network,
`coord1:4`), `Network/Delivery.lean` (the total cross-vocabulary classifier that
`g-design:4` made a condition of per-vocabulary fault classes),
`Network/Child.lean` (the binding that authorizes a spawn and routes every child
outcome), `Network/Mailbox.lean` (ordering profiles and selective receive),
`Network/Assertion.lean` (network assertions and separating conjunction),
`Network/Death.lean` and `Network/Instance.lean` (incarnations, parentage and the
lifecycle), `Network/Escrow.lean` (the escrow ledger and its prefix laws), and
`Network/World.lean` (`LogicalProcessNetworkCore` and the canonical agreement),
`Network/Channel.lean` (`ChannelContract`, its footprint discipline, and the
laws that discipline derives), and `Network/Plan.lean` (`ProcessPlan`,
`LogicalProcessNetwork`, and the boundary projection), and
`Network/Transition.lean` (`NetworkTransition`'s twenty-three constructors, the
scope discipline they respect, `allocatedNominals` and `NetworkStep`), and
`Network/Commit.lean` (§6's coalescing law). Every module in the table is
written.

`Commit.lean` is small because most of what [PROCESS.md](PROCESS.md) §6 indexes
a commit transition by belongs to layers this one cannot see — physical worlds
and affected resource identities are the memory owner's, obligations are too.
What is a *process* fact is the one sentence that carries the section: a
reconciler may replace several pending renders by the latest "only when no
skipped render has a demanded commit observation". `Coalescing` is that, with
the condition stated over the *skipped* list rather than the survivor, because
the claim is about what was dropped. `skipNothing` is the satisfiability half: a
side condition that could make every commit impossible would be a bug rather
than a law.

The observation filter is a parameter, for the same reason
`Network/World.lean` parameterizes the obligation ledger — it is
`Grass.Semantics`'s, and reaching into another layer to state a process fact is
the import edge `coord1:5`'s diamond exists to prevent.

`Transition.lean` carries the organising idea the corpus does not state and
which makes §3's declaration checkable: **every step carries the set of
fragments it may change, and a proof that it changed nothing else**.
`TouchesOnly` is that, over the same `Agrees` relation the assertion layer frames
with, so it *is* §8's `TransitionScope step` — and it turns
`Channel.lean`'s `escrow_survives_unrelated_steps` from a theorem with a
caller-supplied hypothesis into a theorem about steps.

Eight step shapes carry the constructors' payloads. `ResolvesEscrow` is what all
ten of §3's competing endings do to the world, shared rather than repeated; they
stay ten constructors because routing coverage is a claim *about constructors*,
and one `resolve` carrying a `ChannelResolution` would make it vacuous.
`SendsEscrow` is the only transition that adds to a ledger, tied to the plan by
requiring the edge's own `ChannelSteps.Send` to admit it. `EndsInstance` stores
decision 129's exact ending, `Spawns` carries decision 130's parent
authorization and the nominal allocation, `StepsLocally` is scoped to *two*
fragments because a process step may emit, `RequestsCancel` records the request
and states that the escrow is untouched, `Commits` appends to the trace, and
`Detaches` is decision 130's transition at the network.

`Tests/Process/TransitionFixtures.lean` builds the first `ProcessPlan` — nothing
until now had shown a topology, a message family, the step relations and a
contract per edge could be satisfied together — takes a receive step of it, and
reads its scope back out.

`Channel.lean` is where standing risk 2 got smaller rather than larger.
[PROCESS.md](PROCESS.md) §3 declares `ChannelContract` with seventeen fields,
seven of them opaque law names, and an opaque field of an undeclared type is a
promise nothing checks. The Lean structure has fourteen. **Three** of the seven
— `escrowStable`, `session` and `frame` — are replaced by a *footprint
discipline*: `escrowLocal`, `receiverPreLocal` and `sessionLocal` bound what the
author's own assertions may read, `sendOnOpenSession` makes the session law a
demand rather than a conditional, and from those `escrow_survives_unrelated_steps`,
`frame_unmentioned` and `receiverPre_separate_from_escrow` are theorems. The
third is the one that matters most, because §3 requires `ReceiverPre * Escrow`
to be *formable*, and it is formable only because `NetworkFragment` splits
`escrow` from `session`.

The other **four** are not fields at all, and are deferred to owners the module
names rather than dropped. `prefixConservation` and `atMostOneResolution` are
`Network/Escrow.lean`'s, proved there over the ledger, and a contract cannot
restate them because it cannot see a ledger through an abstract agreement.
`resolutions` and `transferExact` quantify over the transition family, so they
are `Transition.lean`'s. `ChannelSteps` is the seam that lets the contract be
written and checked first: the send and receive relations are parameters, and
the family instantiates them. That divergence from the declared field list is
§10.14.

An earlier revision of this paragraph said "fifteen fields, four replaced, three
stayed opaque", and every one of those numbers was wrong. `Channel.lean`
reproduced them from here. The counts above are from the declarations.

`Plan.lean` closes the loop decision 128 opened, and turned out to be the
smallest module in M2 rather than the largest, because every law it was supposed
to own was statable one layer down. Its `boundaryProjection` is derived from
`ProcessGraph.rootBoundary` rather than declared again (§10.15), and its `Sound`
is a wrapper around the world's `WellFormed` until the transition family gives
it something of its own — including the reroute-landing obligation
`Network/Escrow.lean` records as the plan's, which is the world's.

An earlier revision of this line said "five of ten" while listing seven modules
and a twelve-row module table. The count was stale in both directions and is
corrected here rather than quietly re-based.

`Child.lean` was taken before `Assertion.lean` deliberately. The assertion
language is standing risk 1 — the one most likely to eat this milestone if it
drifts toward a general separation logic — and it is the wrong thing to start
while the branch is in a holding pattern awaiting a merge. The child binding is
the natural complement to `Delivery.lean` instead: delivery handles the three
fault classes, which translate as free functions because they carry no dependent
result, and the binding handles the case that is not free, where a child's
success answers a specific parent demand whose answer type depends on which
demand it was. **None of the exit criteria below is discharged.**

`Assertion.lean` was then taken as soon as the branch was held with no imminent
candidate selection, which is the one window in which the risky module can be
written without a merge deadline pressing on it. It came in at the size the risk
note asks for: six declarations and eleven theorems, no points-to, no magic
wand, no heap, no entailment relation. What it does carry that the normative
declaration does not is a world parameter — see §10.11.

Its first draft was wrong in a way worth recording, because the mistake is the
one standing risk 1 is really about. It claimed that `framed` — an assertion's
proof that it reads nothing outside its footprint — was "the whole content" of
the type. It was not. `WorldAgreement` supplied only an equivalence relation per
fragment, so a caller could supply equality, discharge every `framed` by `subst`
at any footprint whatsoever, and reduce every framing obligation in the weave to
"the worlds are identical". Nothing was unsound; everything was useless, and no
theorem in the module noticed. The fix is `agreesGlue`: any two worlds can be
mixed along any set of fragments, which is the statement that the fragments are
a complete independent decomposition of the world, and which the equality
agreement fails. Two further defects came from the same review: the frame rule
was not stated in the shape `docs/PROCESS.md` §8 asks for (scope-disjointness
implies preservation, not agreement-implies-preservation), and `Separate` had no
consumer anywhere, so the separating conjunction's formation gate gated nothing.
`frame_of_disjoint_scope` and `sep_right_survives_left_step` are those.

`Instance.lean` followed because `ProcessLifecycle` is named in
[PROCESS.md](PROCESS.md) §3 and declared nowhere. Its first draft derived the
states from the `NetworkTransition` family and got it wrong four separate ways,
which is worth recording because the mistake has a shape. "Which transitions
enter this state" is the wrong question: `NetworkTransition` says how a network
moves, not how a process can have ended. §3's `ChildLifecycleEvent` does
enumerate the endings, and the states are now exactly its non-continuing cases.
The draft's table omitted `childLifecycle` — the transition that actually
terminates a *child*, which its own fixture's example was — attributed `died` to
"supervisor shutdown", which is not a constructor at all, claimed `restart`
reached no state when the restarted incarnation is plainly `running`, and gave
no state to an acknowledged cancellation, which §3 lists as a terminal
`ChildLifecycleEvent`. `cancelled` is now a state, and the claim it replaces is
sharper than the one it replaces: a process under an unacknowledged *request* is
running, and it is *acknowledgement* that ends it.

The rule the tags follow is that a tag carries a payload exactly when the
instance's other fields do not determine it. `died` carries its reason because
nothing else records it. `terminated` carries no result because `localState` and
`LifecycleWitnessed` recover one — with the caveat in §10.12, since
`ProcessSpec.Terminal` is a relation and recovers *a* result rather than *the*
result. `faulted`, `violated`, `interrupted` and `cancelled` carry nothing and
do not satisfy the rule; that is §10.12 too.

`IsRoot` is the kind facing the boundary *and* an absent parent, not the absent
parent alone, because a detached child also has none.

`ChildDeathReason` was renamed `ProcessDeathReason` in the same change — none of
its three reasons is about being a child, and §3 gives `senderDeath` and
`receiverDeath` to processes that may be roots — and lives in its own leaf
module, `Network/Death.lean`. Putting it in `Instance.lean` would have made
`Child.lean`, which mentions no topology at all, import the whole topology
stack for a three-constructor enum.

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
Grass/Process/Network/Death.lean       ProcessDeathReason, a shared leaf
Grass/Process/Cancellation/Identity.lean  masks, point/call/region ids, CancelReason
Grass/Process/Network/Instance.lean    incarnations, parentage, lifecycle, witnessing
Grass/Process/Network/Escrow.lean      the escrow ledger and its prefix laws
Grass/Process/Network/World.lean       LogicalProcessNetworkCore, the canonical agreement
Grass/Process/Network/Channel.lean     ChannelContract and its footprint discipline
Grass/Process/Network/Plan.lean        ProcessPlan, LogicalProcessNetwork, the projection
Grass/Process/Network/Transition.lean  NetworkTransition, scopes, NetworkStep
Grass/Process/Network/Commit.lean      coalescing and the demanded-observation law
Grass/Process.lean                     the authoring facade (decision 134)
Grass/Process/Cancellation.lean        the cancellation facet (decision 134)
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
  constructor, over all twenty-three. **Discharged, in the form this layer can
  state it.** `NetworkTransition` has the twenty-three constructors;
  `NetworkTransition.scope` is total over them, so there is no transition whose
  scope is undefined; and `NetworkTransition.touchesOnly` proves by cases over
  the whole family that each one changed nothing outside the scope it declares.
  What that gives is §3's "no bypass": a step cannot reach a fragment it did not
  name. What it does not yet give is the *injective* half — that a given endpoint
  input enters through exactly one constructor rather than at least one — which
  needs the endpoint vocabulary the driver contract supplies and is M4's;
- the escrow prefix laws — conservation, at-most-one resolution, and stability
  under unrelated steps — over that same full family;
- a total classification from the delivering side's interrupt, fault, and
  violation classes into each receiving vocabulary's, so that the `PEmpty` case
  of §2.2 is discharged rather than assumed;
- `LogicalProcessNetwork` requires `ProcessInstance.LifecycleWitnessed` of every
  instance it holds, so a network cannot tag a running process `terminated`.
  `Grass/Process/Network/Instance.lean` states the predicate and cannot enforce
  it — there is no network there to enforce it over — and a docstring in one
  module is not a place an obligation can safely live, so it is written here as
  well;
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

**Status: eight of eight modules written, unmerged, unratified.** `coord1:6` ruled the
canonical scoped cancellation form while M2 was in progress, so
`Cancellation/Identity.lean` and `Cancellation/Policy.lean` were built out of
order to discharge that disposition. `Cancellation/Compose.lean` follows, and it
discharges the first two thirds of the exit criterion below. `Termination.lean`
carries the safety half of the termination contract, `Facet.lean` the
termination facets, `ByteFlow/Ingress.lean` and `ByteFlow/Egress.lean` both
conservation theorems, and `ByteFlow/Rechunk.lean` the chunking laws. Every
module in the table is written and every part of the exit criterion below is
discharged.

`Rechunk.lean` is the one place §2.1's `List`-for-`Vec` substitution actually
bites, and the module says how: `Vec` carries its length in the type, so a
capacity bound could be a type-level fact rather than a proof obligation on
every chunk. With `List` it is `splitForCapacity_fits`, which constrains what
this splitter produces rather than what a chunk can be. That is the named exit
item, and it is narrower than it looked before the module was written.

The scoping is the substance of the chunking law, and it is a hypothesis rather
than a theorem: `ChunkExtensional` says a reader's result depends only on the
concatenation, and `counting_chunks_is_not_extensional` exhibits an ordinary
reader that fails it. A law that assumed every parser were chunk-blind would be
false of any parser that treats a chunk edge as a record separator, which is a
real thing to write.

```text
Grass/Process/Cancellation/Identity.lean masks, point/call/region ids, CancelReason
Grass/Process/Cancellation/Policy.lean   scoped policy and certificate (written
                                         early under coord1:6, ahead of M3)
Grass/Process/Cancellation/Compose.lean  the |> algebra and bounded cancellation
Grass/Process/Termination.lean           modes, contracts, dispositions (safety half)
Grass/Process/Facet.lean                 TerminationFacet, and the two §3 claims it keeps
Grass/Process/ByteFlow/Ingress.lean      phases, resolutions, conservation
Grass/Process/ByteFlow/Egress.lean       offered/committed/queued, suffix retention
                                         (both parameterized over the absent loan
                                          type, per §2.1; instantiation is an
                                          M3 exit item)
Grass/Process/ByteFlow/Rechunk.lean      functional and capacity-aware rechunking
```

Two rows an earlier revision of this table had are gone. `Grass/Process/Policy.lean`
duplicated `Cancellation/Policy.lean` and was left over from before the
directory split. `Grass/Process/Cancellation.lean` was listed as the masks and
`|>` module, and that path is now the cancellation *facade* under decision 134
(§11), so the algebra went to `Cancellation/Compose.lean` instead — a collision
this plan created for itself and is recording rather than quietly re-pointing.

Exit criterion, in three parts:

- **Discharged.** The `uncancellable |> cancelpoint |> uncancellable` worked
  example from [PROCESS.md](PROCESS.md) §3 is a theorem.
  `Tests/Process/ComposeFixtures.lean` states each of §3's four assertions about
  it separately, including the closing one that carries the weight: a
  forever-blocking uncancellable region cannot acquire eventual cancellation
  merely by being sequenced with a later point. `blockingExample` contains the
  very same cancellation point and is provably not eventually cancellable, which
  is the case an author gets by writing the shape and forgetting the bounds.
- **Discharged.** Sequential composition is associative — by `List.append_assoc`,
  because a composite is a list of regions rather than a tree, so the two
  bracketings are not merely equivalent but the same object. No transport is
  needed, which is why this reads more simply than the criterion anticipated.
- **Discharged.** Both byte-flow conservation theorems over their full
  transition families — `ByteIngressTransition.preserves_conservation` and
  `ByteEgressTransition.preserves_conservation`, each by cases over every
  constructor, with the invariant a *predicate* rather than a field. §10.19
  records why that distinction is the whole difference between a theorem and a
  projection.

`Termination.lean` carries `docs/PROCESS.md` §3's typed-termination principle
and the field that makes it one: `noArbitraryDeath`, which says a permitted stop
is either at a proved safe point or is a fault. The theorems that follow are the
ones a supervisor's author needs — a forced stop is safe, a cooperative stop is
safe, and off a safe point the only permitted mode is `faulted`, which is §3's
"a supervisor cannot manufacture a safe forced stop".

Its first draft was uninhabitable twice, in the same way and for the same reason
`ProcessCorrect` once was: a field quantified over more situations than can
arise. It demanded a `TerminalDisposition` for a *faulted* stop, which contains
`p.Terminal` and so is impossible for a process that faults away from a terminal
state; and it let `permitted` see the state but not the outstanding demands
while `disposition` ranged over every bag, which is impossible under the `strict`
remainder law the corpus supplies by name. Both were found by writing the
fixture, not by reading the module, and both are recorded in its note.

What is deferred and named rather than dropped: `reachesSafePoint`, §3's
cooperative-cancellation *liveness* theorem, which needs a fairness model and a
`TerminationPremiseFamily` this layer does not have — `ReachesSafePointObligation`
names it — and the fault path's custody of the demands a faulting process was
holding, which `FaultCustodyObligation` names. Writing either as a discharged
field would have been the liveness theorem in name only.

`Facet.lean` makes two of §3's sentences checkable rather than conventional.
"Pure serial functions, straight-line helpers, and uncancellable leaf processes
gain no new author obligation" is kept because `TerminationFacet.ordinary` takes
*no argument at all* — and that is possible because
`Grass/Process/Run.lean`'s `ProcessRunTransition.terminate` cannot be formed
without a `TerminalDemandClassification`, so every terminating transition
already carries the disposition an ordinary facet would otherwise have had to
supply. `terminal_transitions_have_exact_disposition` is that, proved by case
analysis over the run relation. If the run relation ever admitted a termination
without a classification, the proof would fail there rather than the facet
quietly weakening.

"The bridge cannot discard it after manufacturing a liveness contract" is kept
by `retainedContract`, and by `cancellable_facet_forbids_arbitrary_death`, which
derives §3's "a supervisor cannot manufacture a safe forced stop" *from the
facet*. An earlier revision of that theorem took the contract as a parameter and
mentioned the facet only in a hypothesis it never used, which made it a theorem
about contracts wearing a facet's name; the unused-variable linter is what
caught it.

One tightening over §3's declaration: the retained contract is against
`accept.terminalRemainder`, the specification's own law, rather than any law the
author names. §3 writes `ProcessTerminationContract p` with the law open, which
would let a facet promise cancellation whose dispositions the specification does
not accept. `SupervisorPolicy` and the version family stay parameters, since
supervision is a weave combinator rather than this layer's to invent.

What `Compose.lean` deliberately does *not* model is §3's `CancellationSummary`
itself, whose fields — `PendingCancellationCustody`,
`CancellationDelayBoundOrEnvironmentPending`, `CancellationDispositionAt`,
`ProcessTerminationContract` — are types the corpus names and does not declare.
They belong with the termination contract, and inventing them to make the
summary look complete would be worse than leaving the row unwritten. The algebra
is what this milestone's exit criterion actually asks for, and it is stated over
regions carrying a mask and a bound, which is enough for every claim §3 makes
about the example.

Byte flow is here rather than in M2 because its phases are a cancellation race
in disguise: `cancelling` is a phase, and the resolution tables are the
substance. Its hard block on `c-mem`'s buffer loans is recorded in §2.1.

`Policy.lean` is scheduled against an unresolved corpus ambiguity; see §10.3.
It is written last in this milestone, after that entry is ratified.

## 6. M4 — Composition, lowering, and the proof package

**Status: two modules written, unmerged, unratified.** `Weave/Mixin.lean` is
taken first, out of the table's order, because it is where M2's two scope
disciplines were supposed to pay off and the only way to find out was to try.

They did. [PROCESS.md](PROCESS.md) §8 declares `WeaveInvariantMixin` with a
`frame` field — an assertion survives a step whose scope is disjoint from its
own — and that field is not needed here. `Network/Assertion.lean` makes an
assertion carry a footprint it provably reads within; `Network/Transition.lean`
makes a transition carry a scope it provably changes within; so framing is a
theorem. The mixin keeps `withinScope`, a checkable claim that the footprint
lies inside the mixin's declared scope, and `affected`, which is the author's
real obligation and the one nothing structural can discharge.

Neither ingredient was built for this. The footprint discipline was forced by an
assertion language that would otherwise have bounded nothing (§10.11's
neighbourhood), and the transition scope by a routing-coverage claim. That they
compose into §8's framing rule is the strongest available argument that both
were the right shape.

Writing the module's fixture also found a defect in M2's transition family, and
it is the kind only a *consumer* finds: no constructor could touch a shared
region at all, because `processStep`'s scope named the instance slot and the
observation trace and stopped. A weave mixin about shared state would have
framed past every step in the program, vacuously and wrongly — and nothing in
`Transition.lean` or its own fixture would have complained, because a family
that touches *fewer* fragments satisfies its scope law more easily. `StepsLocally`
now carries the regions a step wrote and requires write access for each, so
`ProcessGraph.sharedAccess` decides who touches what.

`Trace/Independence.lean` follows, and it is short for a reason worth recording.
Independence is scope disjointness — available only because a transition carries
its scope — and the *usable* content of it turns out not to be the diamond at
all. What a weave argument consumes is
`unaffected_by_an_independent_step`: an invariant living inside one step's scope
is untouched by every step independent of it, whatever the schedule chose. That
is [FOUNDATION.md](FOUNDATION.md) law 18's requirement, and it needs no
reordering theorem.

The constructive diamond is named and not proved. Swapping means rebuilding each
transition at a state it was not built at, and every interesting constructor
carries a proof about its own before-state — `wasOutstanding`, `wasFresh`,
`wasLive` — so whether those survive is a lemma per constructor rather than a
definition. `SwapsWith` records it. A consumer reading only outside both scopes
never needs it, and one reading inside a scope was not schedule-independent to
begin with, so its absence costs nothing that this layer exports.

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
sequencing once `g-foundation` registered; `coord1:19` answered **hold all three
and keep maintaining them**, and made a distinction worth recording: regis-
tration is not a scope claim, and these were three items on three different
gates rather than one bucket. That turned out to matter, because the gates then
cleared separately and one of them cleared the other way.

**Both ownership gates are now answered, by the user.** `coord1:24` relays it:
`Grass/Specification/**` is assigned to `g-foundation`, and `Grass/Std/Logical`
is not being folded into an existing mandate — a dedicated standard-library
agent is being stood up for it. The naming gate had already cleared earlier
(`g-design:13` on `coord1:16`, with `g-foundation:7` agreeing to rename
`Grass/Semantics/Specification.lean` to `SpecProcess.lean`), so
`Grass.Specification` unambiguously names the neutral layer.

| Item | Gate | Status |
|---|---|---|
| `Grass/Specification/Scope.lean` | owner | **offered**, `c-process:49` to `g-foundation` |
| `Grass/Specification/Boundary.lean` | owner | **offered**, same |
| `Grass/Process/Bag.lean` | owner | parked, and directed: it goes to the stdlib agent when that identity registers. `coord1` will name the receiver; no offer before then |

`Bag`'s wait is now bounded rather than open. `g-foundation:6` *declined*
`Grass/Std/Logical` as outside its mandate, so it is not the receiver, and
`coord1:24` says plainly not to offer before the stdlib identity appears.

The representation choices went into the offer so the receiving owner inherits
them as stated facts rather than discovering them: `RequirementSet` is a
hand-rolled `List` with `Covers` as pointwise implication and no deduplication
law; `withRequirements` replaces rather than extends and deliberately proves no
coverage; `DriverBoundary.Result` is a dependent family that
`ProtocolExposesBoundary` consumes as one; and `ScopeId`'s own note says it may
belong in `Grass.Core` once that layer has a `Uid` discipline. They went in the
offer's `summary` rather than its `known_issues`, because that field takes event
ids and not prose — `c-process:49` says so where it says them.

`Bag`'s own note, for when its turn comes: it is a hand-rolled
`Quotient (List.isSetoid _)` rather than mathlib's `Multiset` (§10.10), and the
finite sets in `Process/Nominal.lean` are duplicate-free `List`s rather than a
`Finset`. This plan takes no position on whether either should change; that is
for whoever accepts.

## 9. Review

**No work scheduled by this plan has been merged.** The branch is nominated and
under independent review; nothing on it has been authorized or merged.

[AGENT_REVIEW.md](AGENT_REVIEW.md) requires the author to nominate a distinct
reviewer on the agent bus, and that reviewer — not the author — to select a
snapshot, authorize, and merge.

### 9.1 One branch per nomination

A nominated branch stops moving. New work goes on a new branch.

That is obvious in retrospect and this plan learned it the hard way: `c-process`
nominated `agent/c-process/process-layer` at `4c41042` and then pushed three
more commits to it while the review was open. The nomination named the exact
commit, and `AGENT_REVIEW.md` §1's no-force rule keeps every reviewed snapshot
reachable, so nothing was lost — but a reviewer fetching the ref got a tip three
commits past the thing they had accepted, and §2's "authors are responsible for
a focused branch" was not being honoured.

It could not be fixed by rewinding, for the same reason the trailer defect in
§9.2 could not: rewinding a published product branch is a force-push. So the
correction is forward, and it is a rule rather than a repair:

- `agent/c-process/process-layer` carries M1 and M2 and is nominated. It
  receives **only** commits a reviewer of that nomination asks for — mistakes
  corrected by new commits, which is exactly what §1 prescribes.
- `agent/c-process/m3-cancellation` branches from that branch's tip and carries
  everything after: the facades of §11, the cancellation algebra of §5, and the
  rest of M3. It is nominated separately when it has a coherent chunk.
- The next milestone gets its own branch when this one is nominated, and so on.

The three commits that landed late are on both branches, with the same object
ids, because a branch is a pointer and they were already published. They will be
reviewed as part of the M3 nomination, which is where they belong: a trailer
convention, two authoring facades, and a composition algebra are all post-M2
work that happened to be committed to the wrong ref.

Working on more than one branch also stops the reviewer being a bottleneck. A
nomination that is waiting is not a reason for the author to wait too, and the
protocol has never required it.

### 9.2 An open finding this plan cannot close by itself

Twelve of the forty commits on this branch carry a broken trailer block, and the
correction is not the author's to make.

`AGENT_REVIEW.md` §2 requires every introduced product commit to carry
`Agent-Bus-Agent: <name>`. Those twelve write it, but with a blank line between
it and the `Co-Authored-By:` line that follows, so it is not in the final
contiguous block and `git interpret-trailers --parse` reports only the
`Co-Authored-By:`. To a human reading `git log` the trailer is plainly there; to
any checker that parses rather than greps — and §5's "selected commit authors
match trailers" implies parsing — it is absent. The affected commits are
`d23eca2` through `4c41042`; the twenty-eight before them are contiguous and
parse correctly.

It cannot be fixed forward. A commit message is only changed by rewriting the
commit, and `AGENT_REVIEW.md` §1 is unconditional: "No participant force-pushes
any protocol branch: not `main`, a product branch, or `agent-bus`. Product
branches advance through ordinary commits and merges. Mistakes are corrected by
new commits." The stated reason is the one that applies here — rewriting would
make the snapshot a reviewer has already accepted unreachable mid-review.

So the options belong to the reviewer or the coordinator, not to this plan:

- rule that the requirement is satisfied, on the ground that the line is present
  and a checker should grep rather than parse — which is a decision about what
  the check *is*, and should be written down either way;
- authorize a single corrective rewrite as the explicit exception §1 contemplates
  for a revert or administrator exception, accepting that the accepted snapshot
  moves; or
- accept the branch with the defect recorded, and require the trailer check only
  of commits introduced after the ruling.

This plan takes no position. What it does record is the convention that stops it
recurring: **the trailer block is contiguous, with no blank line between
trailers.** Every commit after `4c41042` on this branch follows it.

### 9.3 What local iteration did and did not do

Adversarial review agents spawned by the author, with fresh context each round,
to find defects early. That found real ones and it is not a substitute for the
nomination: an author reviewing their own work through an agent they instructed
is still an author reviewing their own work.

The defects it caught are worth listing, because each is a case where the code
built, the fixtures passed, and the module's own docstring was wrong:

- a multiplicity-blind terminal disposition, where one claim about a demand
  *value* discharged any number of occurrences of it;
- an uninhabitable `ProcessCorrect`, whose `handlesEveryEvent` field demanded a
  step from a state `terminalNoStep` forbids one from;
- an assertion footprint that bounded nothing, because `WorldAgreement` admitted
  the equality relation (§10.11's neighbourhood, fixed by `agreesGlue`);
- a lifecycle enumeration derived from the transition family rather than from
  the endings, which gave no state to an acknowledged cancellation;
- an escrow law that forbade self-merging but admitted coalescing *cycles*, in
  which every payload was passed on and none landed;
- an escrow law that forbade any real reroute, by demanding the carrier be
  escrowed in the ledger the payload was leaving;
- a `SlotsAgree` that checked an instance's kind and not its slot, with its own
  docstring describing the defect the missing half left open; and
- a `RootUnique` implied by `SlotsAgree` and therefore empty, with a fixture
  whose hypotheses were jointly unsatisfiable.

Each fix carries a negative fixture that would have caught it.

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
their implementations written on this branch.

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

### 10.11 `NetworkAssertion topology` has no world to assert about

[PROCESS.md](PROCESS.md) §3 declares assertions as `NetworkAssertion topology`
and consumes them at that arity throughout `ChannelContract`. It never says
what an assertion is *about*. The obvious answer — `LogicalProcessNetwork plan`
— is not available at that arity, and cannot be made available, because
`ChannelContract` is a field of `ProcessPlan`. The document already knows this:
it says `ProcessGraph` exists separately "so topology and channel contracts can
quantify over ... process-network assertions without a self-referential
structure declaration."

So the world is genuinely below the plan, and most of it is: `instances` and
`shared` need only `ProcessKind`, `ProcessRef`, `SharedRegion` and
`SharedState`, all of which `ProcessTopologyCore` has. One field is not.
`inFlight : ChannelEscrowLedger plan` is indexed by the plan, because each
edge's `Message` type is a field of that edge's `ChannelContract`. A
topology-level world therefore does not exist unless the escrow ledger's
carrier is made opaque at topology level, which is a design choice nobody has
made.

`Grass/Process/Network/Assertion.lean` does not make it either. It takes a
`WorldAgreement topology World` — an abstract per-fragment agreement relation
over a supplied world — so `NetworkAssertion` is indexed by that agreement
rather than by the topology alone. This is strictly weaker than committing to a
world: it admits the intended instantiation, at `World := LogicalProcessNetwork
plan`, once `Plan.lean` supplies one, and it lets `Channel.lean` be written
against the framing laws without `Plan.lean` existing. It is not the declared
arity, and pretending otherwise would be the divergence, not the abstraction.

The reconciliation is a normative edit and belongs to whoever holds
[PROCESS.md](PROCESS.md) when the merge order settles: either the declaration
gains its world argument, or the corpus commits to an opaque topology-level
escrow carrier and the world becomes derivable. c-process has a preference — the
world argument, because the opaque carrier buys nothing that
`ChannelEscrowLedger plan` does not already provide at the arity where it is
used — but not the authority. Blocks: the normative surface of `Channel.lean`,
which cannot match a declaration that does not typecheck.

### 10.12 A terminal `ProcessLifecycle` tag does not determine what ended the process

**Ruled and closed.** `agent-bus` issue `c-process:46`, ruled by `g-design:37`
as [DECISIONS.md](DECISIONS.md) decision 129: `ProcessLifecycle` is indexed by
the instance's `ProcessSpec` and stores the exact terminal result, cancellation
reason, interruption reason, logical fault, environment violation, or death
reason. `Grass/Process/Network/Instance.lean` implements it, and
`Tests/Process/InstanceFixtures.lean` keeps the defect visible — the protocol
whose terminal states ignore the answer is still there, and the ending is now
exact anyway. §3 also states the cost the ruling accepts: the payload "does not
duplicate an independent fact", because the transition owns one value and
records it in the child event, the parent projection, and the instance through
equality proofs. The account below is what was filed.


[PROCESS.md](PROCESS.md) §3 declares `lifecycle : ProcessLifecycle` unindexed,
and [DECISIONS.md](DECISIONS.md) decision 128 re-ratified the `ProcessInstance`
record with that field unchanged. `Grass/Process/Network/Instance.lean` declares
the type accordingly. The rule it follows is that a tag carries a payload
exactly when the instance's other fields do not determine it, and by that rule
two of the tags are wrong.

`faulted` and `violated` do not determine their class. A faulted instance's
`localState` says nothing about which `LogicalFault` it raised; a violated one's
says nothing about which `EnvironmentViolation` its environment committed.
`cancelled` does not determine its `CancelReason`, and `interrupted` does not
determine its `InterruptReason`. §3's own `ChildLifecycleEvent` carries all four
— `faulted (fault : ChildFault)`, `environmentViolation (violation : ...)`,
`cancellationAcknowledged (reason : CancelReason)`, `interrupted (reason :
InterruptReason)` — so the corpus already treats the class as part of the
ending. The instance record does not, and there is nowhere else in network state
for it to go.

`terminated` is the same defect one step milder. `ProcessSpec.Terminal` is a
*relation*, so a state may be terminal with several results, and
`terminated_has_result` recovers *a* result rather than *the* result a parent's
`ChildDemandBinding` routed. `Tests/Process/InstanceFixtures.lean` exhibits a
protocol where both `true` and `false` are recovered from the same terminated
instance. Only for a protocol whose terminal relation is functional — which
`Grass/Process/Spec.lean`'s `DeterministicProcess.terminal_functional` supplies
— do the two coincide. `TerminatedWith` names a specific result so the
obligation is at least statable, and `terminated_result_unique` states when it
is discharged.

None of this is unsound, and none of it loses information *globally*: the class
was delivered as an event and the parent recorded it. What is lost is that the
network state alone cannot answer "what ended this process", so a join, a
supervisor's restart-intensity accounting, or a later audit reading the network
has to consult the parent's transition rather than the instance.

The fix is to index the type — `lifecycle : ProcessLifecycle (topology.protocol
kind)`, with `terminated` carrying its result and the three others carrying
their class. That is a normative change to a record decision 128 has just
re-ratified, so it is a ruling and not c-process's to make. Blocks: nothing
today; `Plan.lean` proceeds against the unindexed form, and `Transition.lean`
will inherit whichever shape is ruled.

### 10.13 `detach` erases the fact that a process ever had a parent

**Ruled and closed.** `agent-bus` issue `c-process:47`, ruled by `g-design:38`
as [DECISIONS.md](DECISIONS.md) decision 130: `ProcessInstance` carries a typed
`ProcessParentage` with `root`, `attached` and `detached` cases, where `root` is
indexed at exactly the topology's root kind and `detached` retains the exact
former parent incarnation without granting it authority. Root uniqueness and the
validity of attached relationships stay network well-formedness laws rather than
fields each instance author pays. `Grass/Process/Network/Instance.lean`
implements it, `detach` is the transition's parentage half, and
`detached_keeps_its_history` is the fixture. The account below is what was filed.


[PROCESS.md](PROCESS.md) §3 declares `parent : Option (Sigma fun parentKind =>
ProcessRef topology parentKind)` and separately provides a `detach` transition.
A detached child's parent therefore becomes `none`, which is exactly what a
root's is, and the two are indistinguishable by that field.

Two consequences. First, "the root is the instance with no parent" is false as a
network law; `Grass/Process/Network/Instance.lean` defines `IsRoot` as the kind
facing the boundary *and* an absent parent for this reason, and keeps
`HasNoParent` as the weaker, honest reading of the field. Second, and less
easily worked around, `Grass/Process/Network/Child.lean`'s
`NonReturningReason.detached` becomes unjustifiable from state: a binding may
say an outcome does not return because the child was detached, and nothing in
the network records that it ever was.

The fix is a three-way field — root, detached-from, child-of — rather than an
`Option`, which keeps the fact of former parenthood while making the absence of
a *current* parent equally explicit. Like §10.12 this changes a record decision
128 has just re-ratified. Blocks: nothing today. c-process has implemented the
weaker `IsRoot` and pinned the distinction in a fixture, so the erasure is
visible rather than assumed away.

### 10.14 `ChannelContract` has seven opaque law fields, four of which need not be

[PROCESS.md](PROCESS.md) §3 declares `ChannelContract` with `escrowStable`,
`prefixConservation`, `atMostOneResolution`, `resolutions`, `transferExact`,
`session` and `frame`, each typed by a name — `StableUnderUnrelatedProcessSteps
Escrow`, `NoFabricationDuplicationOrLoss Escrow`, and so on — that the corpus
declares nowhere. This plan's standing risk 2 is the field count; the sharper
problem is that an opaque field of an undeclared type is a promise no consumer
can check, and a contract author discharges it by writing anything at all.

Three of them do not need to be fields — `escrowStable`, `session` and `frame`.
`Grass/Process/Network/Channel.lean` carries a *footprint discipline* instead:
`escrowLocal` bounds what the escrow assertion may read to its own session's
escrow fragment or the nominal history, `receiverPreLocal` bounds the receiver's
precondition to that session's cursor or the receiving process's own slot, and
`sessionLocal` does the same for the session predicate. `sendOnOpenSession`
makes the session law a demand rather than a conditional on `send`, which is
what stops a contract discharging it with a never-satisfiable `SessionOpen`.
Those are checkable claims about values the author supplies, and they yield
`escrowStable` and `frame` as theorems (`escrow_survives_unrelated_steps`,
`frame_unmentioned`) plus the property §3 needs and never states — that
`ReceiverPre * Escrow` can be *formed* (`receiverPre_separate_from_escrow`).

Two of those bounds were too tight in a first attempt and are worth recording,
because both made a real contract unwritable. Bounding `Escrow` to the escrow
fragment alone forbade any dependency on `usedNominals`, which is exactly what
§3's "affine resolve token" needs and what `Network/Assertion.lean` gives the
`nominals` fragment *for*. Bounding `ReceiverPre` to the session fragment alone
read §3's "the receiver's independently evolving **local**/session cursor" as if
`local` were not there, so a contract whose receive depended on the receiving
process's own state could not exist. Both bounds are now disjunctions, and
`receiverPre_separate_from_escrow` still holds because no admitted fragment on
one side is admitted on the other.

The other four are not fields here at all, and the module says where they went.
`prefixConservation` and `atMostOneResolution` are already proved in
`Network/Escrow.lean` over the ledger, and a contract quantifying over an
abstract `WorldAgreement` cannot see a ledger to restate them. `resolutions` and
`transferExact` quantify over the transition family, which is
`Transition.lean`'s.

The remaining divergence is `ChannelSteps`. §3's `send` and `receive` are
`HoareTransition`s with no step relation named, because the transition family is
declared later in the same section. This module takes the two relations as a
parameter, which is the same seam decision 128 used for the world and lets the
contract be written and checked before the family exists.

Whether the normative declaration should shed the four fields is a ruling, not
c-process's call. Blocks: nothing — the Lean is stricter than the declaration in
the direction that matters, since every law the declaration names is either
proved or explicitly deferred with a named owner.

### 10.15 The boundary projection is declared twice, and at two different levels

[PROCESS.md](PROCESS.md) §3 declares `ProcessGraph.rootBoundary :
ProtocolExposesBoundary (registry.protocol (protocolKey root)) boundary` and,
about a hundred lines later, `ProcessPlan.boundaryProjection :
RootLocalDemandProjection toProcessTopologyCore boundary`. `RootLocalDemandProjection`
is declared nowhere. Both name the same job — selecting which of the root
protocol's demands the driver boundary sees, with the rest staying private — and
the first one already has a partial map (`exportDemand : Demand -> Option
boundary.Demand`) that does it.

`Grass/Process/Network/Plan.lean` therefore *derives*
`rootLocalDemandProjection` from `rootBoundary` rather than carrying a second
field. Two objects with one job is the defect class §10.1 already found once, in
`AbstractSpecificationProcessNetwork`.

There is a real difference between them that the derivation does not capture,
and it is a second gap rather than a reason to keep both fields. §3 describes the
plan-level projection as running "from selected root-local **occurrences** to
`DriverBoundary` occurrences", and the execution-complete simulation is supposed
to prove "the exported projection is exact". Occurrences, not demands. This
layer's outstanding demands are a `Grass/Process/Bag.lean` multiset: it has
multiplicities, so two outstanding `log` demands are two elements, but it has no
*identities*, so neither of them can be projected to a particular boundary
occurrence. An occurrence-level projection is not statable here at all.

The fix is to give outstanding demands nominal identities, which is
`Grass/Process/Nominal.lean` territory and touches `ProcessRunState`,
`TerminalDemandClassification` and the child binding. That is a substantial
change to M1's author surface and it needs a ruling, not a unilateral edit.
Blocks: the exactness half of the boundary projection, and any later theorem
that needs to say *which* outstanding demand a boundary result answered.

### 10.16 A network's live population is not related to its declared bound

`ProcessGraph.population` gives each kind a `PopulationBound` — `exactlyOne`,
`boundedByResourcePolicy`, and so on — and nothing in
`LogicalProcessNetworkCore.WellFormed` relates it to the instances a network
actually holds. A topology declaring `.exactlyOne` of its listener may hold
several, and every other well-formedness clause is satisfied.

The obstacle is counting. A network's instances are a function from
`InstanceId kind`, which is an arbitrary type with no finiteness or
enumerability, so "how many live instances of this kind are there" has no
statement. `.exactlyOne` could be stated without counting — at most one slot
holds an instance — but `boundedByResourcePolicy` cannot, and stating one and
not the other would leave the harder case looking discharged.

Recorded rather than half-implemented. It plausibly wants the same nominal
machinery as §10.15, since a live-instance census and a live-occurrence census
are the same shape of problem. Blocks: nothing today; `Transition.lean` will
need it, because a spawn transition has to be refused when the bound is reached.

### 10.17 Every §3 citation in the process layer is currently uncheckable in-tree

`docs/DECISIONS.md` on this branch ends at decision 115, and the §3 paragraphs
that decisions 128, 129 and 130 added — `LogicalProcessNetworkCore`,
`WorldAgreement`, `NetworkAssertion`, `logicalWorldAgreement`, the indexed
`ProcessLifecycle`, and `ProcessParentage` — exist only on
`agent/g-design/normative-design`. `Grass/Process/Network/{Assertion,World,
Instance,Channel,Plan}.lean` quote and cite all of them.

Nothing is wrong with the citations; they are accurate against the branch that
will merge first. But a link or quotation checker run against this branch alone
cannot verify any of them, and a reviewer reading this branch in isolation will
find the references dangling. This is the same forward-reference window
`c-reviewer:7` accepted for the spikes and `c-process:41` described, one merge
later and pointing the other way.

Recorded so it is expected rather than discovered at merge. It closes when
`g-design`'s branch lands, which the settled order puts first.

### 10.18 A transition's allocation is checked only where it is spawned

**Partly closed.** `Spawns.allocatesTheGeneration` now requires a spawn's
allocation to contain the generation the spawned incarnation carries, which is
the correspondence this entry was filed for, at the two constructors that
allocate. The general statement below still stands for the identities `spawn`
and `restart` do *not* introduce — channel epochs, message occurrences, child
demands — because the constructors that introduce those do not yet name them
either. The account below is what was filed.

### 10.18a A transition's allocation is not checked against what it allocates

`Grass/Process/Nominal.lean` already carries `Allocation`, `NominalHistory`,
`Fresh`, `Admissible` and `extend`, so `docs/PROCESS.md` §3's `NetworkStep` —
`fresh` and `historyExact` — is a thin wrapper and not the hard part.

The hard part is the correspondence §3 states informally: "`allocatedNominals`
… contains every new process generation, channel epoch, local/child/message
occurrence, restart identity, and coalesced replacement". A step supplies its own
allocation, and nothing relates that allocation to the identities the step
actually introduced. A spawn can allocate the empty set and still install an
incarnation with a fresh generation; the history then omits it, and
`LogicalProcessNetworkCore.NominalsAllocated` — which does check that live
generations are in the history — rejects the resulting network, but only after
the fact and without saying which step lied.

The fix is per-constructor: each one's exactness record has to name the
identities it introduces and require its allocation to be exactly those. That is
part of building the twenty-three constructors rather than a separate task, and
it is why `Transition.lean` does not yet declare `NetworkStep`: a step wrapper
whose freshness law ranges over an unconstrained allocation would look like the
law and not be it.

Blocks: M2's first exit criterion, which is routing coverage over the full
family.

## 11. The authoring facade

`docs/DECISIONS.md` decision 134, ruling `c-spike:4`'s third question and the
process-side facts `c-process` supplied for it: `Grass.Process` is a bounded
signature-only authoring facade, and `Grass.Process.Cancellation` a bounded
public facet. Neither is the Lake root and neither is an aggregate of
`Grass/Process/**`.

The spikes have written `import Grass.Process` since they were drafted, and
until decision 134 that line named nothing. The question was never whether to
add the module — an author surface that does not exist is not an author surface
— but what shape [OLEAN_SHARDING.md](OLEAN_SHARDING.md) §2 leaves available,
given that it forbids both a leaf importing a whole-program umbrella and an
aggregate importing every leaf.

### 11.1 What "bounded" can mean, and what it cannot

It cannot mean hiding. Importing a module in Lean makes its whole transitive
closure visible, and `export` adds names rather than removing them, so a facade
cannot show an author less than what it imports. A module note claiming
otherwise would be the overclaiming this plan's §9.3 lists as the defect class
local review keeps finding.

What it can mean is that the closure is small, declared, and *checked*.
`Grass/Process.lean` imports four modules; `Grass/Process/Cancellation.lean`
imports two. `Tests/Process/FacadeFixtures.lean` and
`Tests/Process/FacadeCancellationFixtures.lean` author against each import line
alone and then guard that the excluded vocabulary does not resolve, so widening
either list breaks a fixture rather than passing unnoticed.

That is `g-foundation:46`'s lesson applied before it could be taught twice: an
import list is only a check if something fails when it changes.

### 11.2 The two closures are not nested

`Grass.Process` excludes cancellation. `Grass.Process.Cancellation` excludes the
network — no plan, no channel contract, no assertion, no escrow ledger, no
topology. Neither is a subset of the other, which is why decision 134 makes them
two facets rather than one with a larger closure.

The second exclusion is [PROCESS_SHARDING.md](PROCESS_SHARDING.md) §4's argument
made visible in the import graph. A policy is exact against one scope's
discovered blocking calls; a policy indexed by a plan would make `callsExact` a
global equality, so adding one `Sleep` anywhere would invalidate every
cancellation proof in the program. A facet that cannot name a topology cannot
acquire one by accident.

### 11.3 What is out, and on what grounds

Mailboxes, the structural network, child bindings, cross-vocabulary delivery,
the transition family and the commit law are machinery a *realization* consumes,
not vocabulary an author writes. An author who needs one imports the module that
owns it, which is what §2's "consumers import the narrowest module that owns the
fact they need" already says.

`Grass.Specification.Boundary` arrives through `Sequential/Machine.lean` and is
deliberately not excluded. That is not leakage: `coord1:5` puts the neutral
vocabulary *below* both Semantics and Process, so a process author naming
`DriverBoundary` reaches down the diamond rather than across it.

`Grass.lean` remains the Lake root, still imports nothing, and is a different
object from the facade. If a definition ever appears in either facade module, it
has stopped being one.

### 10.19 Both byte-flow conservation theorems are projections of fields

[PROCESS.md](PROCESS.md) §3 makes `conservation` a *field* of
`ByteIngressState` and of `ByteEgressState`, and then states as theorems:

```text
theorem ingress_transition_preserves_conservation
    (step : ByteIngressTransition before after) : after.conservation

theorem egress_partial_conservation (s : ByteEgressState) :
  s.offered = s.committed ++ InFlightRequestedBytes s.phase ++ s.queued
```

Neither has content. `after.conservation` is the field of `after`, so the first
is discharged by projection and says nothing about `step`. The second restates
the field's own type at a state that carries it, so it is discharged by
projection too. Both sit where §5's exit criterion for this milestone points.

Carrying the invariant as a field is a legitimate design — it makes an
unconserved state unconstructible — but it moves the obligation onto whoever
builds a state and leaves the *transition family* unchecked, which is precisely
what the exit criterion asks about. The two readings are not equivalent: under
the field reading, a transition function that could not preserve conservation
would simply be unwritable, and nothing would say which constructor was at
fault.

`Grass/Process/ByteFlow/Ingress.lean` takes the other reading. `Conserves` is a
predicate, `ByteIngressState` carries no proof, and `preserves_conservation`
quantifies over every constructor. That turned out to matter twice over: writing
the *companion* theorem `no_step_after_terminal` against the same family showed
that an earlier draft's `enqueue`, `deliver`, `consume` and resolutions had no
phase precondition at all, so a terminal flow could still move bytes. A
buffer-moving step from a terminal state conserves perfectly well, so no
conservation theorem — field or predicate — would ever have caught it.

Which reading the corpus intends is a ruling. Blocks: nothing; the predicate
form is strictly stronger, so a later move to the field form loses nothing but
the theorem's name.

### 10.20 `DirectEvent` is undeclared, and cannot be indexed by demand

`docs/PROCESS.md` §4 gives `DirectRelationalProgram.Step` the type

```text
  Step : State -> DirectEvent boundary -> State ->
    AbstractDemandBag (EffectDemand boundary) -> List boundary.Observation -> Prop
```

and never declares `DirectEvent`. `Grass/Process/Sequential/Adapter.lean`
declares it, and does not give it the signature §4 writes: it takes the
occurrence type and its demand assignment as parameters, so a delivered result
names the occurrence it answers rather than the demand it answers.

The reason is the same clause §4 closes the passage with. Suppose a program
holds two outstanding occurrences of equal demand value — §4 explicitly requires
that to be possible, since "equal-valued demands retain multiplicity through
distinct occurrences". An event carrying only `EffectDemand boundary` then
cannot say which of the two was answered, so `Step` cannot say which one was
consumed, so the transition equation could only ever be stated up to demand
value. That is the "set membership" weakening, arrived at not by a lazy proof
but by the vocabulary the event was given.

`Tests/Process/AdapterFixtures.lean`'s fifth fixture is the concrete case:
answering one `log "hi"` occurrence and issuing another leaves the demand bag
literally unchanged, so the demand-level reading of that step is that nothing
happened.

Needs a ruling on the signature. Blocks: nothing in this layer; the adapter is
`DirectEvent`'s only producer and consumer today.

### 10.21 §4's `Pending` field permits exactly what §4's closing clause forbids

`DirectRelationalProgram` declares `Pending : State -> AbstractDemandBag
(EffectDemand boundary)` as a field, alongside a `transitionEquation` connecting
it to the step outputs. A field is a value the producer supplies, so a program
can present any demand bag it likes and satisfy the equation by construction —
including one blind to the multiplicity the `binding` field is separately
required to supply.

`Grass/Process/Sequential/Adapter.lean` makes `held : State → Bag Occurrence`
the field and derives `Pending` as `held` mapped through the occurrence's
demand. `Bag.card_map` then makes multiplicity preservation structural rather
than an obligation, and a program has no way to present a demand bag that
disagrees with its occurrences, because it never presents one.

This is the same trade decision 131 adopted for `ChannelContract` and
`Grass/Process/Weave/Mixin.lean` adopted for §8's `frame`: an opaque field is a
promise nothing checks; a derived value is a claim about something the author
supplied. Needs ratification as a deviation from the declared field list.

### 10.22 `sites : FiniteDependentEffectSiteInventory` is dropped, on §4's own grounds

§4 lists a `sites` field and, three paragraphs earlier, says what it must not be
used for: "an inventory of possible sites is not treated as the effects issued
by a particular execution". The adapter has no use for one — `held` reports what
an execution actually holds — and a field a producer asserts unchecked is
exactly the shape that would let an inventory be mistaken for an issuance.

Recorded rather than silently omitted (law 7). A later module that needs an
inventory, for code generation say, should add it as an independent claim with
its own soundness statement relating it to `Step`, not as a field of this
structure.

### 10.23 `DynamicOccurrences Initial Step` is not definable from `Initial` and `Step`

§4's `binding` field reads

```text
  binding : forall occurrence,
    occurrence 2208 DynamicOccurrences Initial Step ->
    ExactSiteProtocolAndChildBinding occurrence
```

`Initial` and `Step` are `Prop`-valued relations. A proof of `Step before event
after issued observations` carries no derivation to name an occurrence by, and
two different executions reaching the same state are the same proposition — so
there is no function from `Initial` and `Step` to a set of occurrence
identities. `DynamicOccurrences` cannot be what its arguments say it is.

The adapter resolves this by generating occurrence identity *before* the
relation rather than after it: an occurrence is an execution point (the state
and how many steps reached it), the occurrence type is a field of
`DirectRelationalProgram`, and `stepBinding` is stated as a law on steps —
which is where the binding can actually be violated, since a program could carry
a correct `resumeOf` and still step elsewhere.

Needs a ruling on whether `DynamicOccurrences` is intended as something else
this reading has missed. Blocks: nothing today.

### 10.24 The sequential route's terminal disposition is vacuous, and that is a limit

A `SequentialMachine` holds at most one outstanding occurrence, because the only
way to hold one is to be blocked on it (`held_card_le_one`). It follows that it
cannot reach a terminal state holding anything (`terminal_holds_nothing`), so
§4's `EveryTerminalStateClassifiesEveryPendingOccurrence` is discharged at this
route by the empty partition and §3's "resolve, transfer, or permit" has no work
to do.

Recorded because a reader could carry the conclusion across. It is true of this
authoring surface and false of the general network, where
`Grass/Process/Run.lean`'s `TerminalDemandClassification` is what discharges the
same requirement and has real content. `docs/FOUNDATION.md` law 17 permits the
degeneracy — "serial authoring may synthesize a degenerate process realization"
— on condition that it is not an alternate semantics, and the check on that
condition is that the *equations* here are the general ones and only the bags
are small.

No ruling needed; this is a note against a later reader concluding that
termination never has custody work to do.

### 10.25 What deriving `Pending` from occurrences does not close

`Grass/Process/Sequential/Adapter.lean` derives `Pending` from a bag of
occurrences rather than accepting a demand bag, and §10.21 records why. Local
adversarial review found the boundary of that move, and it is narrower than the
module's first draft claimed.

**A producer still chooses the occurrence type.** A `DirectRelationalProgram`
whose `Occurrence` is `Unit` holds a bag of indistinguishable elements;
`DirectEvent.result` then names "the exact occurrence" while there is still no
fact of the matter about which of several was answered. The structure has no way
to check this, so `OccurrencesAreDistinct` names it as an obligation and
`elaborate_occurrences_are_distinct` discharges it for the elaboration — where it
is trivial, because a sequential machine holds at most one thing.
`Tests/Process/AdapterFixtures.lean` discharges it by hand for the
explicitly-authored two-occurrence program, which is what an author of one owes.

**`transitionEquation` has a consumption side and no freshness side.** Nothing
in the structure stops a step re-issuing an occurrence already outstanding —
`Grass/Process/Bag.lean`'s "replayed" among the four failure modes.
`issued_occurrences_are_fresh` closes it for the elaboration and is the only
thing `Point.age` is for; an age-free elaboration discharges every field of
`DirectRelationalProgram` and loses exactly that.

**`DemandDisposition` is an accounting, not a discharge.**
`Grass/Process/Run.lean`'s `TerminalDemandClassification` carries a `permitted`
field and this one carries no analogue, so a program may declare its whole
outstanding bag `resolved` with nothing having resolved anything.
`DispositionIsEarned` names the missing law as an obligation on whoever composes
a program with a specification. It cannot be a field: acceptance is a
specification's word, and §4 routes explicitly authored programs through the
same type.

Needs a ruling on whether the corpus intends these three as program-level fields
or as composition obligations. Blocks: nothing today; the elaboration discharges
all three.

### 10.26 §4 names a canonical fixture the sequential route cannot exhibit

"Duplicate equal-valued effects with distinct occurrences", read the way §4's
own gloss suggests — "equal-valued demands retain multiplicity through distinct
occurrences", i.e. two outstanding at once — is provably unexhibitable by
`SequentialAdapter.elaborateMachine`. `elaborate_pending_card_le_one` is the
proof, and it follows from the one-outstanding bound in §10.24.

`Tests/Process/AdapterFixtures.lean` therefore exhibits both readings: the
temporal one at the elaboration (a retry loop issuing the same demand from the
same state on successive passes) and the simultaneous one at an explicitly
authored `DirectRelationalProgram`, which is §4's "lower-level multi-effect
relational escape hatch". Only the second makes
`DirectRelationalProgram.card_pending` an inhabited claim.

Recorded because the fixture family is an M4 exit criterion and a reader
checking it off against §4's sentence should know which reading landed where.
Needs no ruling if the intended reading was temporal; needs one if §4 meant the
fixture family to be discharged entirely by the sequential adapter, because then
it cannot be.

### 10.27 The Mazurkiewicz congruence is obtained by narrowing, not by proving

`Grass/Process/Trace/Linearization.lean` proves that two independent steps never
both emit, and a first draft reported that as making `docs/PROCESS.md` §7's
`BoundaryObservationsCommute` "contentless". Local adversarial review rejected
the framing and it was right to.

§7 asks for a congruence under which reordering independent steps preserves the
observed trace. This layer obtains it by making every pair that could reorder
two emissions *non-independent*, because `NetworkTransition.Independent` is scope
disjointness and one fragment carries every emission. The
obligation has been moved rather than discharged: a plan that wants two
subsystems to emit concurrently and to reason about the interleaving has no
statement available, and would need either a per-subsystem trace or an explicit
commutation argument about segments. Neither exists.

The same shape reaches `Grass/Process/Weave/Lens.lean`: two `Disjoint` lenses
cannot both own the trace, so at most one refinement in a weave may change what
the program observes. That is sound and it excludes §8's own graphics-and-disk
example if both refinements emit.

**The trace split did not change this.** `NetworkFragment.pending` and
`.observations` are now two fragments, and it is `.pending` that every emitting
constructor declares — so "one global fragment carries every emission" is still
true, of a different fragment. The narrowing is unchanged and this entry stays
open. What the split *did* change is that a commit now has provenance, which is
§10.60's story and not this one.

Needs a ruling on whether the corpus intends one global observation trace. If it
does, §7's observation-reordering congruence is trivial and should be recorded
as such rather than sought. If it does not, `LogicalProcessNetworkCore` needs a
per-origin trace and `docs/PROCESS.md` §3's "observation origin" becomes a field
rather than a word.

### 10.28 No transition can change the obligation ledger or any session

Found by review of the lens layer, by case analysis over the whole family:

```lean
theorem nothing_touches_obligations (transition : plan.NetworkTransition a b) :
    ¬ transition.scope .obligations := by
  cases transition <;> simp [NetworkTransition.scope]

theorem nothing_touches_session_cursors (transition : plan.NetworkTransition a b)
    (edge session) : ¬ transition.scope (.session edge session) := by
  cases transition <;> simp [NetworkTransition.scope]
```

`NetworkTransition.scope` never names `.obligations` and never names `.session`.
By `touchesOnly`, that does not mean those fragments are unconstrained — it
means they can **never move**. A session's status is fixed for the life of the
network, so no channel can be opened or closed; and the obligation ledger
`Grass/Process/Network/World.lean` deliberately parameterises can never be
discharged or extended.

Two consequences, both bad in the way this layer keeps finding:

* A weave mixin about the obligation ledger or a session cursor frames past
  every step of every program, vacuously and wrongly. That is exactly the defect
  `Tests/Process/WeaveFixtures.lean` records having caught for shared regions —
  `StepsLocally` could not touch a region at all — still live for these two.
* `docs/PROCESS.md` §7's `DisjointOrCommutingObligations` and §8's "Replacing it
  preserves … obligations" are satisfied by the whole family for free.

This is a defect in `Grass/Process/Network/Transition.lean`, which is mine.

**The session half is now fixed.** `receive` is built on a new `Delivers`
structure rather than on `ResolvesEscrow`, with a wider scope — this session's
escrow *and* this session's cursor — and a law that the cursor advances by
exactly one while the status does not change. `channelClose` is built on
`ClosesSession`, which moves the status to `.closed` and leaves the cursor
alone. `Tests/Process/TransitionFixtures.lean`'s `the_receive_touches_its_session`
and `the_cursor_advanced` are the anti-vacuity checks, and
`cannot_receive_twice` is now proved from the cursor law rather than from the
escrow, so the addition is load-bearing.

Two pieces of the session half remain. `channelDeath`, `senderDeath` and
`receiverDeath` still leave the status alone, so `SessionStatus.died` is
produced by nothing; and nothing opens a session, which is defensible only
because `sessions` is a total function and every `ChannelId` already has a
status — a fresh epoch's session being `open` is a fact about the initial
network, and there is no initial-network relation yet
(`Grass/Process/Weave/Mixin.lean`'s `HoldsInitially` names the same gap).

**The obligation half is fixed too.** `EndsInstance` carries a `custody`
parameter with `custodyDeclared` (the ledger moved that way) and `custodyExact`
(the declared relation admits nothing else, so `fun _ _ => True` is refuted at
any plan whose `Obligations` has two values).
`moving_the_ledger_ends_an_instance` is what it buys, by cases over all
twenty-three constructors.

`SessionStatus.died` is now producible as well: `channelDeath` is built on
`KillsSession` rather than on a bare `ResolvesEscrow`, which was the same defect
`ClosesSession` fixed for its sibling and which left a dead channel with an
`.open` status that `ChannelContract.sendOnOpenSession` still accepted sends on.

What remains open is §10.33: the ledger can only ever be *consumed*, because no
constructor can put an obligation into it.

### 10.29 `ProcessRefinementLens.Selects` cannot attribute a channel step to a role

`Grass/Process/Weave/Lens.lean`'s `Selects` says a transition's whole scope lies
inside the lens's interior. `Selected` — the roles the refinement replaces —
does not appear in it, and cannot: `NetworkTransition`'s twelve channel
constructors carry an edge and a session and never the role that took the step.

Two coupling fields now close the worst of it. `interiorChannelsTouchTheSelection`
stops a lens owning a channel between two roles it did not select, and in
particular stops a lens with `Selected := fun _ => False` selecting real steps.
`interiorRegionsAreWritable` stops it owning a region only unselected roles may
write.

What remains is that a lens selecting one endpoint of a channel may select steps
the *other* endpoint took on it. Closing it needs the transition family to
attribute channel steps to endpoints — the sending constructor would carry which
incarnation sent — which is the same `Transition.lean` change §10.28 needs and
should be made with it.

### 10.30 `RequirementSet` has no union, so deltas cannot accumulate

`docs/PROCESS.md` §8: "Requirement deltas accumulate in the explicit
`ProviderEnv`." `Grass/Specification/Boundary.lean`'s `RequirementSet` has
`Covers`, `Covers.refl` and `Covers.trans`, and nothing that combines two sets.

So a lens can carry the requirements the network faces *after* its replacement,
with a law that it covers the boundary's — which
`ProcessRefinementLens.refinementOnlyAdds` does — and two independently refined
regions' requirements cannot be added together. A first draft had a
`deltas_accumulate` theorem whose conclusion was literally a field of one of its
arguments; it has been deleted rather than kept.

`ProviderEnv` has no declaration anywhere in the tree. Needs a ruling on where
the union lives — `Grass/Specification/Boundary.lean` is `g-design`'s, and this
is a one-line addition there plus a `Nodup` merge.

### 10.31 A serial function's footprint is state-level, not fragment-level

`Grass/Process/Function/Serial.lean` carries `footprintAgrees : State → State →
Prop` and `postWithinFootprint`, and `footprintSeparates` forbids the degenerate
`fun _ _ => True` that discharged the latter by `trivial`.

That is weaker than the precedent it cites. `NetworkAssertion`'s agreement is
supplied by the *world owner* and constrained by `agreesSymm` and `agreesGlue`,
so an assertion author supplies only `holds` and `footprint`. Here the same
author supplies `Post` and `footprintAgrees`, so a wide-but-not-total footprint
is still self-certifying: an author who declares "everything except the third
field" and writes a `Post` that changes the third field fails, but one who
declares "everything except nothing in particular" does not.

Closing it needs the footprint to range over *fragments* of the process's
logical state — the analogue of `NetworkFragment` at the process-local level —
which `ProcessSpec.State` being an opaque `Type w` forbids. That is a question
about the process state model, not about serial calls. Needs a ruling; blocks
nothing today.

### 10.32 `SerialCallVisibility`'s exclusivity is not tied to the footprint

§3 writes `exclusive (owned : CallerExclusivelyOwns contract.footprint input
before)`. The implementation takes `Exclusive : Input → State → Prop` as a
parameter with no relation to `footprintAgrees`, so a plan choosing
`fun _ _ => True` gets `.exclusive trivial` for every call and §3's "a footprint
alone is insufficient" is typed rather than enforced — what is required is in
fact *weaker* than a footprint.

The tie needs a notion of the caller owning a region of the process's state,
which is the memory layer's resource algebra rather than this one's. Recorded
rather than approximated: a field asserting exclusivity implies something about
`footprintAgrees` would have been satisfiable by the same trivial choice.

### 10.33 A protocol step's issued demands are written nowhere

`StepsLocally.protocolStep` now requires `(protocol kind).Step fromState event
toState issued localEmitted`, which is the fix recorded above. But `issued` does
not land anywhere: `ProcessInstance` has no outstanding-demand field, and
`NetworkFragment` names no fragment for outstanding demands, so
`StepsLocally.scope` cannot mention one and the bag is discarded.

The consequence is sharp. `moving_the_ledger_ends_an_instance` says the
obligation ledger moves only at an ending, and no constructor can put an
obligation *into* it — so §2's "termination explicitly resolves, transfers, or
permits pending" quantifies over pending obligations that nothing in the family
can create. The ledger can shrink and never grow.

**The demand half is now fixed.** `ProcessInstance` carries `outstanding : Bag
(protocol kind).Demand` beside `localState` — §2's `ProcessRunState.running`
carries the same pair — and `StepsLocally.protocolStep` requires
`SettlesDemands`, which is §2's linear equation: an answering event removes
exactly one `cons` before the issued bag is added, a non-answering one adds
without removing. The field lives inside `NetworkFragment.instanceState`, so no
new fragment was needed and no scope widened.

`Tests/Process/ProcessStepFixtures.lean`'s
`answering_an_unissued_demand_is_unconstructible` is the check: a listener
holding nothing cannot be told its `tick` came back.

**What remains is the ending's disposition.** `EndsInstance` does not relate the
ending instance's `outstanding` bag to its `custody`, so §2's "termination
explicitly resolves, transfers, or permits pending" is still unstated at the
network — `Grass/Process/Run.lean`'s `TerminalDemandClassification` is the
per-process half and nothing carries it across. That needs `EndsInstance` to
take a classification of the ended instance's bag, which wants the
specification's `TerminalRemainderLaw` and therefore a plan-level link this
module does not have. Needs a ruling on where that link lives.

### 10.34 ~~`reroute` cannot write the session it reroutes to~~ — **closed on the second attempt**

The entry said `reroute` was a `ResolvesEscrow` scoped to the *source* session,
so it could not write the destination and `ReroutesLand` degenerated to
"satisfiable only where the destination was already non-empty". The fix it named
was "a dedicated structure whose scope names both sessions' escrows, with a field
putting the arrival in the destination".

`Reroutes` is that structure, and **the first version of the field was not that
field**. `arrives` read "the destination's ledger is non-empty afterwards", which
an already non-empty destination satisfies with its ledger bit-for-bit unchanged.
A reviewer built a reroute that delivers nothing and showed the after-world still
satisfies `ReroutesLand`, so the entry's own conclusion survived the repair meant
to close it.

It now says the destination *gained* an occurrence it did not have, carrying this
occurrence's message. That is as close to "the payload" as this layer reaches: a
`ChannelOccurrence` is indexed by its session, so an arrival at another session is
necessarily a different occurrence, and §10.36's identity question is what would
say *which* different one.

### 10.35 ~~`Delivers` has no `contractual` field~~ — **closed, and what it cost**

The entry said `ChannelContract.receive`, `receivePrecondition` and
`ReceiverPost` were unreachable from the transition family because `Delivers`
had no counterpart to `SendsEscrow.contractual`. It has one, and
`Delivers.establishes_receiverPost` is the theorem it buys.

**The first version of the tie was worth nothing**, which a reviewer proved.
`liveSteps.Receive` was restated for the field as "the occurrence was in flight
and the cursor advanced by one" — which is *literally* `Delivers.wasOutstanding`
and `Delivers.cursorAdvances`, so `contractual` was derivable from the
transition's own other fields and the reviewer rebuilt the fixture's `Delivers`
without mentioning `plan.steps` at all. The relation now also carries §3's
`ReceiverPre` — the receiver's cursor is at zero — which is a condition the
contract imposes and the family does not.

The original entry's other half stands: no channel step touches either
endpoint's *instance* slot, so a receive still cannot be tied to the receiving
process's own state.
### 10.36 `send`, `coalesce` and `reroute` are declared non-allocating

The transition module quotes §3: `allocatedNominals` "contains every new process
generation, channel epoch, local/child/message occurrence, restart identity, and
coalesced replacement". `allocatedNominals` returns `Allocation.empty` for
`send`, `coalesce` and `reroute`, and none of them scopes `.nominals`, so no
step that creates a message occurrence may move the nominal history.

`Grass/Process/Network/Channel.lean`'s `escrowLocal` admits `.nominals` in
`Escrow`'s footprint specifically for the affine resolve token, and
`EscrowLedger.rank` is documented as "the occurrence's position in the monotone
allocation history — §3's `usedNominals` ordering". Neither can be established.

Internally consistent — `allocatedNominals` and the scopes agree, and
`NetworkStep.historyExact` enforces it — so this is a disagreement with the
declared contents rather than an unsoundness. Needs a ruling on whether message
occurrences are nominals in the same history as process generations.

## 12. M4 status

What has landed on `agent/c-process/m4-weave-and-composition`, and what M4's
exit criteria still need. Written because §10 has grown to thirty-odd entries
and a reader needs to know which of them are open.

### Landed

| Module | What it proves |
|---|---|
| `Weave/Mixin.lean` | §8's mixin, with `frame` derived rather than a field |
| `Weave/Lens.lean` | §8's refinement lens and the generic contextual theorem |
| `Trace/Independence.lean` | scope-disjointness independence; the diamond named, not assumed |
| `Trace/Linearization.lean` | the trace only grows; two independent steps never both emit |
| `Sequential/Adapter.lean` | §4's elaboration, with `Pending` derived from occurrences |
| `Sequential/Standard.lean` | §4's realizer registry, and that selection is forced |
| `Function/Serial.lean` | §3's serial contract, with the collapse carrying its own frontier argument |
| `Network/Progress.lean` | §7's progress theorem, as a no-infinite-silent-run law, over what a run can reach |
| `Network/Initial.lean` | §3's `ExactInitialNetwork`, and `initial_is_wellformed` |
| `Progress.lean` | the per-process livelock theorem: no silent cycle, no infinite silent run |
| `Network/WellFormedness.lean` | §3's capstone: a step of a well-formed network reaches a well-formed one, all six clauses |

`Grass/Process/Network/Transition.lean` was reworked six times over the same
period and is where most of the defects were: the scope discipline it exports is
consumed by four of the modules above, and every one of them found something
wrong with it.

Each has a fixture file, and each fixture found at least one defect in the
module it was written against. That is the pattern worth keeping: nothing here
was found by reading.

### The records that had no witness, and now do

The exit criterion §10.54 proposed — every named record has a positive witness
before the layer is nominated — turned out to be the most productive rule in this
milestone. Seven records were inhabited for the first time, and each was empty for a
*different* reason that reading had not found:

| Record | Why it was empty | Witness |
|---|---|---|
| `ProcessCorrect` | `handlesEveryEvent` and `terminalNoStep` contradicted each other | `Tests/Process/M1CorrectFixtures.lean`, then `CountdownCorrectFixtures` and `PrefixFixtures` |
| `NetworkProgressMeasure` | `Commits` had no provenance, so no network could be at a frontier under any measure | `Tests/Process/FrontierFixtures.lean` |
| `ExactInitialNetwork` | nothing; it had never been built, and had absorbed two new fields with no proof breaking | `Tests/Process/FrontierFixtures.lean` |
| `EndsInstance` | nothing; it had absorbed three | `Tests/Process/EndingFixtures.lean` |
| `Restarts` | nothing | `Tests/Process/RestartFixtures.lean` |
| `WeaveInvariantFamily` | nothing | `Tests/Process/WeaveFixtures.lean` |
| `SendsEscrow` | its plan's own `Send` pinned an after-world no receive fixture started from | `Tests/Process/TransitionFixtures.lean` |
| `ClosesSession`, `KillsSession`, `RequestsCancel`, `ResolvesEscrow` | nothing | `Tests/Process/ChannelStepFixtures.lean` |
| `Reroutes` | a deferral argued from a false premise, §10.79 | `Tests/Process/RerouteFixtures.lean` |
| `Spawns`, `Joins` | nothing; between them they had absorbed five fields with no proof breaking | `Tests/Process/LifecycleStepFixtures.lean` |
| `Mailbox` (non-empty), `MailboxEntry`, `SelectiveReceive` | the whole module was an island nothing imported | `Tests/Process/MailboxFixtures.lean` |
| `ChildDemandBinding` | nothing | `Tests/Process/ChildBindingFixtures.lean` |
| `LogicalProcessNetworkCore.WellFormed`, `ProcessPlan.Sound` | nothing; `terminated_result_is_exact` took a `Sound` nothing had supplied | `Tests/Process/FrontierFixtures.lean` |

**A correction to an earlier version of this table.** It listed `Spawns` as
witnessed by `Tests/Process/FrontierFixtures.lean`. That file discusses `Spawns`
at length and builds none: an emptiness sweep run in Lean over the whole corpus
found the record uninhabited, and this table was wrong about the one thing it
exists to record. A table of witnesses assembled by reading is not a table of
witnesses. The sweep is the check; the table is its output.

The pattern is worth stating because it has now held every time it was tested:
**a record that absorbs a new field without a single proof breaking is a record
nothing inhabits.** `Spawns` and `Joins` took five fields between them over three
review rounds and nothing broke, because nothing was there. That is a cheap check
and it is the first one to run after any structural change — but running it by
reading is how the row above came to be wrong, so run it in Lean.

And four processes were shown *not* to inhabit `ProcessCorrect` — or, worse, to
inhabit it when they should not. `Tests/Process/SpinFixtures.lean`,
`OscillateFixtures.lean` and `ChatterFixtures.lean` are livelocks that each had a
full `ProcessCorrect`; the first two are now excluded and the third is §10.70.

### The capstone, and what proving it cost

`ProcessPlan.wellFormed_preserved` — a step of a well-formed network reaches a
well-formed one — is proved, all six clauses, axioms clean. It is worth a
paragraph here because of the ratio.

§10.73 was a clause-by-clause *argument* for it, filed with a warning that it
should be read as owed work. The warning was right four times over: the argument
had the layer wrong (`NominalsAllocated` is a law of `NetworkStep`, not of
`NetworkTransition`), the count wrong (four clauses reduce through
`instanceProperty_preserved`, not five — `RootUnique` relates two slots), the
evidence wrong for two clauses, and it did not know about §10.87 at all.

§10.87 is the finding: **no escrow constructor bounded which occurrences other
than its own it may resolve**, so a `drop` could append an unrelated occurrence,
resolve it `.rerouted`, and point it at a session it never touched — breaking
`ReroutesLand` with every field it had discharged. Six reworkings of
`Transition.lean` had not found it. Trying to prove one theorem did.

### The rule this milestone ends on: attack the repair

§10.90, §10.91, §10.92 and §10.93 are four entries in a row about *repairs that
were not attacked*, and they arrived in one review round:

* §10.87's field was the narrowest thing that made the proof go through, and it
  forbade the ordinary close that `ChannelResolution.channelClosed` exists for.
* It bounded what a step may *end* and left what a step may *create* wide open,
  so a `drop` could escrow a message nothing sent — and thereby establish an edge
  contract's `Escrow` assertion, which §3 gives only a send the power to do.
* `Reroutes.elsewhere` became *implied* by a field added beside it, and stayed a
  field, with a docstring that had stopped being true.
* §10.56's view fixture closed the gap with an acceptance whose obligation
  `⟨state, rfl⟩` discharges for any facet, any render and any specification.

§12's existing rule — a record that absorbs a field without a proof breaking is a
record nothing inhabits — catches empty records. It does not catch any of these.
The rule that does is the dual, and it is just as cheap: **after adding a field or
a clause, try to satisfy it badly.** Delete it and see whether anything breaks
(§10.92). Satisfy it with the wrong render, the wrong occurrence, an unrelated
message (§10.90, §10.91, §10.93). A repair deserves the round its subject got,
and none of these four survived one.

**And the next round found five more, in the repairs to those four** — §10.95
through §10.99. The rule works; the point is that it has to be applied every
time, not once. Three further checks fell out of that round and are worth naming
because each found something the others did not:

* **Which field of the step bounds this field of the state?** An `EscrowLedger`
  has three mutable fields. `created` was bounded by §10.91, `resolution` by
  §10.87, and `cancelRequested` by nothing at all until §10.97.
* **What would this obligation have to *see* in order to fail?** Two rounds of
  fixture repair could not fix §10.99, because the clause did not receive the
  state it was supposed to be about. Each repair refused *something*, which is
  what made them look like progress.
* **A repair can be worse than the defect.** §10.96's field made mandatory the
  step that the field it replaced made impossible.

### Still owed for M4 exit

* **`flatten_sequential_roundtrip`** — blocked on §10.42, which is the same
  gap stated properly: a `ProcessSpec` cannot take a silent step, and a
  network's internal transitions are silent. Needs a ruling before it can be
  built, and the same ruling unblocks the serial export and repairs the
  waiting-versus-spinning distinction both progress modules rely on.
* **`serialize_refines_flatten`** — downstream of the above.
* **The proof-economics acceptance rule** — not started.
* **`DirectProgramRealizes` transport** — §4 asks the adapter for it; the
  adapter delivers the syntax half only, and says so.
* **A second plan-level witness** — §10.88. `Sound`, `ExactInitialNetwork`,
  `NetworkProgressMeasure` and `WellFormed` have exactly one witness family
  between them, at a plan whose observation, demand and channel types are all
  empty. `wellFormed_preserved` holds of every plan; the clauses it preserves
  have only ever been *established* at that one. This is the largest gap the
  milestone leaves.

### Open findings by weight

§10.42 (no silent step) is the heaviest and blocks three deliverables. After it:
§10.33's second half (an ending does not dispose of the ended instance's
outstanding bag), §10.35 (no channel step touches either endpoint's slot), and
§10.51 (an ending does not have to be witnessed by the protocol). The rest are
recorded and none blocks building.

§10.27 is **partly closed**: the one global observation trace is now two, and
`NetworkFragment.pending` is where a process's emissions go. §7's congruence is
still obtained by making every pair that could reorder two emissions
non-independent rather than by proving they commute, which is what that entry is
really about; the trace split did not change that and the entry is updated to say
so.

Three retractions are worth counting separately, because they are the same
mistake: §10.46, §10.53 and part of §10.60 each recorded a defect that a later
reviewer refuted by *building* the thing the entry described. All three were filed
from a reading of a repair, describing what the repair did not yet cover, without
constructing it. §10.54 is the method note.

### What a reviewer found that reading did not

Nineteen rounds of local adversarial review, and the count is worth keeping
because it settles a question about method. **Every serious defect this milestone
was found by constructing something** — a witness, a counterexample, or an
alternative proof with a hypothesis deleted. Reading found stale prose and
nothing else, in either direction: reviewers reading found no defects, and five
ledger entries *I* filed from reading were later refuted by a reviewer who built
what the entry described (§10.46, §10.53, §10.65's second half, part of §10.60,
and §10.62's `Demanded` claim).

The three most expensive findings all came from one move — trying to inhabit a
record:

* `ProcessCorrect` was uninhabitable for every terminating process, after five
  review rounds had read the file.
* `NetworkProgressMeasure`'s `AtFrontier` was empty for every measure, which made
  the whole network progress module vacuous. Three attempts to repair the field
  were each refuted by a fixture built against them, and the answer was that a
  frontier is not something a measure declares at all (§10.68).
* Two of the four known livelocks were admitted by the *repair* for the previous
  one. `StepProgresses` went from three disjuncts to four and back to three, and
  what settled it was folding the outstanding bag into the measure so there is
  one well-founded order instead of two in a disjunction.

### Integrity

`#print axioms` on this branch's headline theorems reports only `propext`,
`Classical.choice` and `Quot.sound`. No `sorryAx`, no custom axiom, no
`native_decide`. `lakefile.toml`'s `warningAsError` already fails the build on a
`sorry`, but that check is about *warnings*; this one is about the kernel.

Several depend on no choice at all, which is worth naming because they are the
ones a livelock argument rests on: `MeetsProcessProgress.no_infinite_silent_run`,
`MeetsProcessProgress.no_silent_two_cycle`,
`ProcessPlan.NetworkProgressMeasure.no_infinite_descent`,
`SerialFunctionRealizes.post_is_determined`,
`SerialFunctionSource.exit_is_unique`,
`ExactStandardRealizerLookup.selection_is_determined`,
`DisjointWeave.routing_is_forced`, and the two fixture refutations
`Tests/Process/SpinFixtures.lean`'s `spin_is_not_correct` and
`Tests/Process/OscillateFixtures.lean`'s `osc_is_not_correct`.

### One open question about the facade

`Grass/Process.lean` is decision 134's bounded facade and imports four modules.
`Grass/Process/Sequential/Standard.lean` is author-facing by §4's own
description — "one expression at the application process boundary" — and is not
in it, so an author selecting a registered realizer needs a second import.
Widening the facade breaks `Tests/Process/FacadeFixtures.lean`'s guards
deliberately, which is the point of the design, so it is a ruling rather than a
change I should make. Recorded here rather than done.

Nine ledger entries — §10.20 through §10.42 — were opened by writing fixtures
rather than by reading, and four defects in `Transition.lean` were found by
consumers of its scope discipline rather than by its own tests. That is the
pattern this layer should keep: a module's own fixtures check what its author
already believed.

### 10.37 Only a terminated child can free its slot

`Joins.wasTerminated` demands `ProcessLifecycle.terminated`, so a slot holding a
`faulted`, `interrupted`, `violated`, `cancelled` or `died` incarnation can
never be emptied — only restarted. `Spawns.wasEmpty` therefore never applies to
it again, and a supervisor that wants to retire a crashed role rather than
restart it has no transition for that.

Defensible: `docs/PROCESS.md` §3 describes a join as collecting a *result*, and
a crashed child has none. But then §3 owes a separate reap for the other five
endings, and there is none. Needs a ruling on whether a slot can be retired.

### 10.38 A canonical custody exists for every ledger movement

`EndsInstance.custodyDeclared` requires the declared custody to admit the new
ledger and admit nothing else, which refutes `fun _ _ _ => True` at any plan
whose `Obligations` has two values. It does not stop an author writing
`fun _ _ after => after = network.obligations` — a canonical custody that exists
for *every* movement — so `moving_the_ledger_ends_an_instance`'s existential is
satisfiable whatever the ledger did.

What would close it is a law relating the declared custody to the ending's
*kind*: a termination's custody is not a fault's. That law is the specification's
`TerminalRemainderLaw` and its `Accepts`, which a `ProcessPlan` does not hold —
the same missing link as §10.33. Recorded together with it.

### 10.39 `NominalKind.restartIncarnation` is produced by nothing

`Grass/Process/Nominal.lean` declares it and the transition module quotes §3's
"restart identity" among what `allocatedNominals` contains, but `Restarts`
requires only that the allocation contain the incarnation's *generation*, which
is a `processGeneration`. Nothing ever allocates a `restartIncarnation`.

Either the kind is redundant with `processGeneration` — in which case §3's list
names one thing twice — or a restart owes a second identity that this layer does
not allocate. Needs a ruling. Low weight: no theorem depends on it either way.

### 10.40 §4's lookup uniqueness is derivable, if spec equality is transitive

`docs/PROCESS.md` §4 gives `StandardRealizerRegistry` a `unique` field — one
specification, one key — and gives `ExactStandardRealizerLookup` a second
`unique` of its own, over every entry matching the specification being looked
up.

`Grass/Process/Sequential/Standard.lean`'s `lookupUniquenessIsRedundant` derives
the second from the first, using symmetry and transitivity of the spec equality
and nothing else. So one of the two fields is noise — *if*
`DefinitionalOrCanonicalSpecEquality` is an equivalence.

It is named for a disjunction, and a disjunction of two equivalences need not be
transitive: "definitionally equal, or canonically equal" can relate `a` to `b`
one way and `b` to `c` the other with nothing relating `a` to `c`. If that is
the intended reading the two fields are independent and §4 is right to state
both. Needs a ruling on which.

Two corrections from a later review pass. **The redundancy is mutual**: given
`refl` and a lookup at each entry's own spec, `registry.unique` follows from the
lookup's field — under a *weaker* hypothesis than the other direction needs, so
if either is noise it is more likely the registry's. And **this module cannot
express the non-transitive case**, because every registry is parameterised by a
`SpecEquivalence`; the hedge in `lookupUniquenessIsRedundant` describes a
situation the types forbid. The question is foreclosed in the implementation and
open in the document, which is the wrong way round.

Also from that pass: `selection_is_determined`, the module's headline, uses
neither `registry.unique` nor any `SpecEquivalence` law. Its docstring said it
used both registry laws.

### 10.41 §4's registry law is about keys, not about programs

The same registry's `unique` says two entries for one specification share a
*key*. It does not say they are the same entry, so two entries may share a key,
share a specification, and register different realizations — and §4's stated
law holds.

`Tests/Process/StandardFixtures.lean`'s
`section_four_uniqueness_alone_permits_two_realizations` is that list.
`ProcessRealization.standard (lookupExact spec)` would then be one expression
denoting whichever of two programs the lookup returned, which is exactly what §4
introduces the registry to prevent.

`StandardRealizerRegistry.keysDistinct` is added here and is not in §4's
declaration. Needs ratification, or an argument that key uniqueness is meant to
be enforced by whatever produces the keys.

### 10.42 A `ProcessSpec` cannot take a silent step, and three things need one

`ProcessSpec.Step : State → ProcessEvent vocabulary → State → Bag Demand →
ObservationSegment → Prop` consumes an event on every transition, and
`ProcessEvent` has five constructors — external entropy, a demand result, an
interruption, a fault, an environment violation. Every one of them is something
the *outside* did. There is no constructor for a process computing.

Three things want one, and all three are stuck on it.

**Flattening.** `docs/PROCESS.md` §7: "The flattened process's private state is
`LogicalProcessNetwork r.plan`; one logical step is one exact
`NetworkTransition`." A network's internal steps — a send between two children,
a spawn, a join — correspond to no external event, so the flattened
`ProcessSpec.Step` has no event to consume for them. This is why
`flatten_sequential_roundtrip` is not built: §12 records it as needing a ruling
and this is the ruling it needs.

**Serial export.** §3: "A flattened process may also export a serial callable
contract when its serialization theorem proves a terminating, frontier-free
invocation for the selected request." `Grass/Process/Function/Serial.lean`'s
`SerialFunctionSource.decide` takes a machine state and no event, precisely
because a serial function computes. A `ProcessSpec` that computes has no
transition to offer it.

**Progress.** `Grass/Process/Progress.lean` and
`Grass/Process/Network/Progress.lean` both separate a process *waiting* from a
process *spinning* using `ProcessEvent.externalEntropy`. A computing process has
only one way to express itself today — `.external` over a `Unit` external event
— and it then looks exactly like a process waiting on the environment. Every
progress argument built on that predicate is defeated by the workaround the
absence forces.

The fix is a sixth `ProcessEvent` constructor, or a separate silent-step
relation beside `Step`. Which is a question about `ProcessVocabulary`, which is
mine, and about `SEMANTICS.md`'s execution model, which is not. Needs a ruling.
This is the largest open item on this layer, ahead of §10.33.

### 10.43 `EndsInstance` and `Detaches` do not preserve the incarnation either

Found by attempting `well_formedness_is_preserved` — the theorem that every
network reachable from an `ExactInitialNetwork` satisfies `WellFormed` — and
discovering `NominalsAllocated` is not preserved.

`StepsLocally.protocolStep` was corrected in the third review round to preserve
`ref`, `parentage` and `request`, because without it a tick could install a
generation nothing allocated. `EndsInstance.nowEnded` has exactly the same shape
and the same hole:

```lean
  nowEnded : ∃ incarnation, after.instances kind slot = some incarnation ∧
    ∃ sameKind : incarnation.kind = kind, sameKind ▸ incarnation.lifecycle = ending
```

It constrains the lifecycle and nothing else, so an ending may swap the
incarnation's generation, re-parent it, or change the request it was started
with — and `allocatedNominals` reports that the step allocated nothing.
`Detaches` needs checking for the same thing.

The fix is the same field, and it is why the well-formedness theorem is worth
attempting even before it can be proved: it is the consumer that finds these.
Held until the fourth review pass on `Transition.lean` returns rather than
rewriting the file under a reviewer for the third time.

`well_formedness_is_preserved` is the next substantial piece of work on this
layer once it lands. It would use nearly everything the last four rounds added —
identity preservation, `Restarts.authorized`, `Spawns.startsInitial`,
`allocatesTheGeneration`, `Reroutes.arrives` — which is the point of attempting
it: a theorem that consumes every field is the test of whether the fields are
the right ones.

### 10.44 `DrivenByEntropy` cannot tell a boundary demand from an internal one

`Grass/Process/Network/Transition.lean`'s `DrivenByEntropy` counts a
`processStep` on `.result` as driven from outside, because §7's frontier is
"external/**demand-result**" and a network blocked on a boundary demand must be
declarable at a frontier or no progress measure exists for a reactive plan.

But a `.result` may answer a demand a *child* satisfied, which is the network
acting on itself. Distinguishing them needs to know whether the demand is
boundary-exported, and `rootLocalDemandProjection` exists only for the root's
protocol — the same per-kind gap `ProcessGraph.observeAt` closed for
observations. So the predicate is slightly wider than "the outside must act",
and a plan can park a network at a frontier where a child could have moved it.

The fix is a per-kind demand projection beside `observeAt`. Needs a ruling on
whether every role's demands get one, or only the root's.

### 10.45 `ProcessSpec.Step` is request-blind, and §4's terminal law needs the request

`Initial` and `Terminal` take the request; `Step` does not. §4's
`NoProcessStepFromTerminal` therefore cannot be stated at the strength it reads:
"a state satisfying `p.Terminal request` has no `p.Step`" quantifies the request
away in the conclusion, and excludes every request-parameterised process — "read
`request` items, terminal when `state = request`" has no `ProcessCorrect` at all,
because state 3 being terminal for request 3 forbids it stepping for request 4.

`ProcessCorrect.terminalNoStep` now asks about states terminal for *every*
request, which is exactly what a request-blind relation can be held to. That is
a real weakening: a driver holding a specific request and a state terminal only
for it gets nothing from it.

The fix is to index `Step` by the request, as `Initial` and `Terminal` are. That
is a `ProcessSpec` change and therefore §2's, with consequences for the run
relation, the network transition family, and every fixture. Needs a ruling.
Related to §10.42 — both are places where `ProcessSpec`'s transition relation is
missing an index it needs.

### 10.46 ~~`countdownRemainder` makes `countdown` stuck~~ — **withdrawn**

The claim was that `countdown.Initial` issues `replicate request tick`, that
`countdownRemainder` permits at most two pending ticks, and that a run started
with three therefore reaches state 0 holding three ticks where it can neither
terminate nor step.

**It cannot reach that state.** A second review pass proved the run invariant:
`countdown` consumes exactly one occurrence per settling step and decrements the
state on the same step, `log` is never issued into the bag, and `.external
.wake` moves neither — so `outstanding.card = state` along every reachable run,
and at state 0 the bag is empty and the law grants the empty partition.

`Tests/Process/CountdownCorrectFixtures.lean` now carries that invariant as
`linked` and is built on `countdownRemainder` rather than
`TerminalRemainderLaw.unconstrained`. Until it was, the corpus proved `countdown`
correct under an acceptance *different from* the one all its linearity fixtures
use, so the headline "`countdown` is correct" was scoped to a law that permitted
everything — and `notStuck`'s terminal branch was discharged by `trivial` where
it could have been discharging the real bound.

Kept rather than deleted because the mistake has a shape worth remembering: an
entry was filed against the *specification's* law on the strength of a reading
of the process, with no run invariant proved and no counterexample built. The
reading was plausible and the invariant that refutes it takes twenty lines.

### 10.47 `DeterministicProcess` is unusable for any process that terminates

`toProcessSpec` derives `Step` from a total `update`, so the derived relation
holds by `rfl` at every state and event — including terminal ones. A
deterministic process that is ever terminal therefore cannot satisfy
`ProcessCorrect.terminalNoStep`, whatever else it does.

`toProcessSpec` is not faithful: it loses partiality on all three relations, and
the loss on `Step` is exactly the one that matters. The convenience §2 offers is
available only to processes that never finish.

The fix is for `update` to be partial — `State → Event → Option (…)` — or for
`DeterministicProcess` to carry its own terminality guard. Needs a ruling; it is
a small change and a visible one.

### 10.48 Three fields in the process core that nothing consumes

Found in the same pass, none of them unsound, all of them costs paid for no
exported consequence:

* ~~`MeetsProcessProgress.handlesEveryEvent`~~ — **closed, on the second
  attempt.** The first `transition_for_event` concluded
  `∃ after, ProcessRunTransition … after`, which never mentions the event — so it
  was `exists_transition`'s conclusion verbatim, provable by discarding the field
  it was supposed to spend, and a reviewer reproved it that way. It now concludes
  the *specific* successor: the state the step reaches, the bag `SuccessorBag`
  computes, and the trace extended by exactly what was emitted. A theorem is about
  the event it is handed only if the event appears in what it concludes.
* `ProcessAcceptance.DemandsWellFormed` — its own docstring's example is "at most
  one outstanding write per handle", and "outstanding" is a property of the run's
  bag. It is applied in exactly two places, both to a *per-transition* `issued`
  bag, and nothing derives well-formedness of an outstanding bag from them — it
  does not follow, since `outstanding` accumulates. Confirmed constructively: a
  process satisfying both fields against `DemandsWellFormed := card ≤ 1` reaches a
  run state whose bag has card 2, so the field's own motivating example is outside
  its expressive range rather than merely unproved. Making it load-bearing needs a
  closure law — `well-formed a → well-formed b → well-formed (a + b)`, plus
  downward closure under `ConsumeExactlyOneMatching` — which is a change to
  `ProcessAcceptance`, not a theorem about it.
* `ProcessTopologyCore.spawnAuthority` — exists to refine `maySpawn` to
  instances, "which stops connection 3 from spawning a stream belonging to
  connection 5", and neither `Spawns.authorized` nor `WellFormed.ParentageValid`
  reads it.

Each is either a law that should be spent or a field that should go. Needs a
ruling on which, per field.

### 10.49 `ProcessAcceptance.Demanded` is the free predicate the network fixed

`Grass/Process/Network/Progress.lean` closed its degenerate-measure hole with
`frontierIsExternal`, which makes a frontier a claim about which steps are
enabled rather than a predicate the author chooses. The per-process layer has no
analogue for its *third* disjunct: `ProcessAcceptance.Demanded` is a free
`p.Observation → Prop`, and `Demanded := fun _ => True` is admissible — which is
exactly the "every process could satisfy progress by logging" the field's own
docstring says it exists to prevent.

Moving the predicate from `ProcessSpec` to `ProcessAcceptance` does not prevent
it, because a standalone protocol supplies its own acceptance: one author on
both sides of the implication. Needs a ruling on what constrains `Demanded` —
the network's answer was to tie the analogous predicate to something the
transition family already decides, and there may be no such thing here.

Two additions from the second pass. **Every acceptance in this repository sets
`Demanded := fun _ => False`** — `ProcessAcceptance.trivial`, `oneShotAcceptance`,
`countdownAcceptance`, `spinAcceptance`, `uptoAcceptance` — so the third disjunct
is not merely under-constrained, it has never been exercised in either direction
by any fixture. And the degeneracy does *not* extend to the first disjunct:
`ProcessEvent.externalEntropy` is structural rather than author-chosen, so the
entropy escape recorded in §6 is about which events an author declares external,
which is a weaker freedom than choosing the predicate outright.

### 10.50 A weave's result renaming is unconstrained and unconsumed

`VocabularyEmbedding.result` maps a woven result back to the component's own,
and no theorem in `Grass/Process/Weave/Blend.lean` consumes it: local
adversarial review deleted the field and every theorem still held. It also built
a legal weave whose logger `result` fabricates a byte count for every `write`,
which is `docs/PROCESS.md` §5's "may not fabricate a result", unenforced at the
seam.

The field is kept because a weave must supply the renaming to be usable at all.
Constraining it needs the two components' *plans* — what the result means is a
fact about their step relations, not about their vocabularies — so the
obligation belongs wherever the woven `ProcessPlan` is constructed, and there is
no such place yet. Needs a ruling on where.

Same pass, smaller: `DisjointWeave` requires no joint surjectivity, so a woven
demand may belong to neither component and every theorem is silent about it; and
`externalEventsDisjoint` forbids one entropy waking both components, which rules
out broadcast — a clock tick delivered to two components at once is ordinary
parallel composition. Both are now disclosed in the module note; whether §8's
"disjoint nominal event namespaces" means to exclude broadcast is a document
question.

### 10.51 ~~`EndsInstance` does not require the ending it stores to be witnessed~~ — **half closed**

Found by attempting `well_formedness_is_preserved` — that every network reachable
from an `ExactInitialNetwork` satisfies `WellFormed` — and getting stuck on
`LifecyclesWitnessed`.

```lean
def LifecycleWitnessed (incarnation : ProcessInstance topology) : Prop :=
  ∀ result, incarnation.lifecycle = .terminated result →
    (topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState result
```

`EndsInstance.nowEnded` requires the after-instance to carry exactly the ending
the constructor names, and nothing requires that ending to be one the protocol
reaches. So `processTermination` can store `.terminated result` for a result the
protocol's `Terminal` does not admit at that state, and the network after it
fails `WellFormed`.

This is `docs/DECISIONS.md` decision 129's own requirement — "network
well-formedness ties a stored terminal result to the relational `Terminal`
witness" — and `WellFormed.lifecyclesWitnessed` states it of a *network* while
nothing makes a *step* preserve it. A law that only well-formed networks satisfy,
and that no transition maintains, is a law about the initial network alone.

The fix is a field on `EndsInstance` requiring `LifecycleWitnessed` of the
after-instance, which is checkable because `identityPreserved` now pins the
request and local state. Held until the fifth review pass on `Transition.lean`
returns rather than rewriting the file under a reviewer again.

**`well_formedness_is_preserved` is the capstone this layer should reach.** It
would consume nearly every field the five review rounds added — identity
preservation on four structures, `slotAgrees`, `Restarts.authorized`,
`Spawns.startsInitial`, `allocatesTheGeneration`, `Reroutes.arrives` — and each
clause it fails is a field that is missing. Two have been found that way already
(§10.43 and this one), before a line of the theorem was written.

**Two of the six endings are now checked**, by `EndsInstance.endingIsEarned`.
`.terminated result` must satisfy `ProcessSpec.Terminal` at the instance's own
request and state; `.interrupted reason` must have something outstanding to
abandon, which is `docs/PROCESS.md` §2's own words for it.
`Tests/Process/EndingFixtures.lean` is the record's first witness — it had none,
which is why it had absorbed three new fields across four review rounds without a
proof breaking — and carries both attacks: a process still counting at three,
tagged terminated, and a process holding nothing, said to abandon something.

The other four stay open and each for a different reason. `.cancelled` wants a
prior cancellation request and **no instance records one**:
`Grass/Process/Network/Escrow.lean`'s `cancelRequested` is per occurrence on a
channel, so checking it is a world change rather than a field. `.faulted` and
`.violated` carry a reason from the protocol's own vocabulary, so there is
nothing here to check them against. `.died` is the supervisor's word and §3
grants the supervisor that authority.

Needs a ruling on the cancellation half: whether a `ProcessInstance` should
record an unacknowledged cancellation request, which `ProcessLifecycle.running`'s
docstring already says it may be in ("includes a process with an outstanding,
unacknowledged cancel") without anywhere to put it.

### 10.52 `ReachesSafePointObligation` is free in two directions and cannot be made otherwise here

`Grass/Process/Termination.lean` states it over an author-supplied `Eventually`
and an author-supplied `Premises`, so `Eventually := fun _ _ => True` or
`Premises := fun _ _ => False` discharges it. Nothing in that module can
constrain `Eventually` to be a liveness modality, because this layer has no
fairness model — which is why it is a named obligation rather than a field.

A third freedom was a defect and is fixed: `outstanding` was bound *outside*
`Eventually`, so the obligation demanded a later state permitted while holding
*every* bag, which is unsatisfiable for the module's own contract. It is now
bound inside and existentially, which is weaker than the claim a reader wants —
the bag the process is actually holding when it gets there lives in
`Grass/Process/Run.lean`'s run state, not in `p.State`.

Needs a ruling on whether the termination contract should be restated over run
states, which would make the exact claim expressible and would move the module
below `Run.lean` in the import order.

### 10.53 ~~`StepProgresses`'s demand disjunct does not exclude a two-demand cycle~~ — **withdrawn, and replaced**

The entry claimed that a cycle through two demands — `d`'s result issues `e`,
`e`'s issues `d`, the bag never growing and the state never moving — evaded the
`issued.card = 0` condition, and that excluding it needed an order on the bag
that its cardinality could not supply.

**Both halves were wrong.** A third review pass built that process: every step of
it issues one demand, so `issued.card = 0` fails, the state does not move so the
measure disjunct fails, and it has no progress record at all. The cycle was
already excluded, one step at a time.

The real escape was the opposite shape, and the entry's diagnosis pointed away
from it. `Tests/Process/OscillateFixtures.lean`'s `osc` answers its demand and
issues **two** while a state rank falls, then answers and issues **none** while
the rank climbs back — returning the run state bit-for-bit, with a full
`ProcessCorrect`. The bag's cardinality is not constant along that cycle; it
oscillates, and so does the rank. What was wrong was having **two independent
well-founded orders in a disjunction**, which is not an order.

Fixed rather than recorded. `ProcessMeasure.rank` now takes the outstanding bag
beside the state, `StepProgresses` is back to §7's three disjuncts, and
`ProcessMeasure.not_decreases_both_ways` closes the cycle by asymmetry. `spin`
and `osc` are both kept as fixtures because neither is excluded by pinning the
other.

The method note: this entry was filed from a repair, describing what the repair
did not yet cover, without building the thing it described. That is the same
mistake as §10.46 and it produced the same kind of error — a plausible reading,
recorded as fact, pointing the next round in the wrong direction. Both were
caught by a reviewer who built the process the entry described and found it
already excluded.

### 10.54 A note on how three of this milestone's defects were found

All three of `ProcessCorrect`'s uninhabitability, the `StepProgresses`
regression, and the `countdownRemainder` retraction were found the same way: by
*building* the record for a small process, not by reading the definitions.

* Reading found none of them. `ProcessCorrect` had been reviewed five times
  before a reviewer tried to inhabit it for `countdown` and found that no
  terminating process could.
* The first repair of a defect found this way widened a definition until the
  unreachable case passed, which admitted a genuine livelock. The second repair
  narrowed the *quantifier* instead — `productive` moved to reachable, deliverable
  steps, matching the two fields already there — and both cases came out right.
* A negative-fixture corpus cannot notice that the record it is negative about is
  empty, and a positive fixture built from one process cannot notice what that
  process does not express. `countdown` exercises neither the request-dependent
  terminal law nor the well-founded measure; `Tests/Process/PrefixFixtures.lean`
  and `Tests/Process/M1CorrectFixtures.lean` are where those are checked.

Recorded as a method note rather than a defect. The exit criterion it suggests
for the remaining layers is that every named record have at least one *positive*
witness before the layer is nominated.

### 10.55 `ProcessCorrect` says nothing about a process with no initial state

Found by construction in the third pass on the M1 core. A process with
`Initial := fun _ _ _ _ => False` and `Step := fun _ _ _ _ _ => True` — every
state stepping to every state, emitting anything — has a complete
`ProcessCorrect`, against an acceptance whose `TraceAccepts` accepts no trace and
whose `DemandsWellFormed` admits no bag. `Reachable` is empty, so
`observationsAccept` and all three `MeetsProcessProgress` fields are vacuous, and
`Invariant := fun _ => False` makes the rest vacuous too.

Nothing in the record requires `p.Initial` to be inhabited. This is not caused by
quantifying `productive` over reachable run states — the same reviewer checked
that for a specification that *has* initial states, `preserved` forces
`Invariant` to contain every reachable state, so the reachability form is sound
there — but it is a class of "correct" process no driver can start.

The fix is a field, or an exit obligation on the fixture corpus rather than on
the record. Needs a ruling on which.

### 10.56 The view facet is an uninhabited class

`ProcessSpec.view` is `none` in every specification in the repository — `view :=
some` has zero occurrences — so `ProcessCorrect.viewAccepts` is discharged by
`absurd hasView (by simp […])` in all five correctness fixtures, and
`ProcessAcceptance.ViewAccepts` is `fun _ _ => True` in all five. `ViewFacet` is
constructed nowhere.

The same shape as §10.49's `Demanded`, and worse: `Demanded` is at least
*settable*, and this whole facet has never had an instance. `docs/PROCESS.md`
§2's "an optional view facet is pure — it may be evaluated, duplicated, coalesced
or discarded" has no witness that it can be any of those.

Needs a fixture with a real view, or a ruling that the facet is deferred to the
layer that consumes it. Recorded rather than fixed because building one is a
specification-layer question, not a process-layer one.

**Closed**, and the deferral was another argument. `ProcessSpec` *is* this layer,
and the fixture is `Tests/Process/ViewFixtures.lean`: `gauge` is `oneShot` with a
view and every other field verbatim, which is itself the point — a view facet is
pure, so acquiring one changes no behaviour, and the correctness record differs
from `oneShotCorrect` in exactly one field.

What took a moment's thought was making the *acceptance* non-vacuous, since
`ViewAccepts` sees only the facet and the rendered value and cannot mention the
process's state directly. The answer is the **image of the render**: an
acceptable view is one some state renders to. It is stateable for any facet, it
is exactly what `viewAccepts` can always discharge, and it refuses everything
outside the range — `a_view_no_state_renders_is_refused` turns away a view value
no state of `gauge` produces, which `fun _ _ => True` cannot.

The related half of §10.86 is still open: a demand whose result type is not a
singleton. That one is about vocabulary richness rather than about a facet
nothing had built.

### 10.57 `MeetsProcessProgress.productive`'s `Invariant` is redundant inside `ProcessCorrect`

`ProcessCorrect.invariant_of_reachable` already yields `Invariant state` at every
reachable run state, and `productive` is now quantified over reachable run
states, so the hypothesis buys nothing where the field is used inside a
correctness record. It is not redundant for a standalone `MeetsProcessProgress`,
which has no `preserved`.

Kept for now because removing it would make the progress record unusable on its
own. Needs a ruling on whether `MeetsProcessProgress` is meant to be stated apart
from `ProcessCorrect` at all; if it is not, the parameter should go and the two
records should merge.

### 10.58 The reconciler's render ledger and the world's pending trace are two accounts of the same thing

`Grass/Process/Network/Commit.lean`'s `Coalescing` splits *pending renders* into
committed and skipped; `NetworkFragment.pending` holds the observations processes
have produced and no commit has published. Nothing relates them, so
`CommitsRender.toCommits` takes `Commits.earned` — "what I publish is the front
of what is pending" — as a hypothesis its caller must supply.

That is honest and it is not finished. A `PendingRender` carries observations and
no provenance, so the reconciler cannot say which pending observations its
committed render corresponds to, and a plan could commit a render whose
observations are pending for an unrelated reason. Closing it means either giving
a render a position in the pending trace, or deriving the render ledger from the
pending trace rather than declaring it beside it.

Needs a ruling on which. `Grass/Process/Network/Commit.lean` is `docs/PROCESS.md`
§6's reconciler and the pending trace is §3's world; the two documents do not
say how they meet.

### 10.59 ~~`ExactInitialNetwork` has no witness~~ — **closed**

`Grass/Process/Network/Initial.lean` pins every fragment of a starting network,
including — since the trace split — that its committed trace is empty and its
pending trace is exactly the root's projected start emission. Nothing in the
corpus constructs one.

The record survived a change that added two fields without a single proof
breaking, which is the signature of an uninhabited class. §10.54's exit criterion
says every named record needs a positive witness before the layer is nominated;
this is the one that does not have one.

Not a defect in the record as far as anyone can tell — which was the problem.

`Tests/Process/FrontierFixtures.lean`'s `waiting_is_a_start` is the witness, and
building it spent both of the fields review had added: `nothingCommitted`, which
the trace split made statable, and `rootAllocated`, which forced the start's
nominal history to hold the root's generation rather than being the empty one.
A record that absorbs two fields with no proof breaking is a record nothing
inhabits, and that is what it was.

### 10.60 No `NetworkProgressMeasure` exists at the M2 fixture plan, and that is the plan's fault

Local adversarial review proved `AtFrontier` empty for every measure at
`serverPlan`, from `Commits` having no provenance. That cause is fixed
(`NetworkFragment.pending`), and `frontierIsExternal` has been weakened from "a
frontier is left only by entropy" to §7's actual claim — "by entropy **or** by a
step that descends the rank", which is what §7's own progress list ("process
steps, spawn, retry, cancellation, death, join, and restart") says of the steps
it names.

A measure still does not exist at `serverPlan`, and the remaining reason is about
that plan rather than about the definition: its connection population is
unbounded, so a spawn into a fresh slot is enabled at almost every network, is
not entropy-driven, and cannot descend a well-founded rank indefinitely. A plan
that can create unboundedly many children with no external event has no progress
measure, and should not.

What this costs today is that `Grass/Process/Network/Progress.lean`'s theorems
are checked against a class the corpus cannot inhabit.
`Tests/Process/ProgressFixtures.lean` states what every measure must pay and does
not exhibit one. The fixture owed is a *minimal* plan — one role, one slot, no
channels, an empty boundary observation type, a protocol that never terminates —
at which a network waiting on external entropy really is at a frontier and a
measure exists. Until that lands, §10.54's exit criterion is unmet for this
record.

### 10.61 `childCancelled` and `childDied` did not require a child

Both constructors take an `EndsInstance` and a reason, and neither required the
instance to be a child — so a *root* could be cancelled or killed through a
constructor whose name and docstring say "a child". `Joins.wasChild` had been
added for exactly this on the neighbouring constructor.

Fixed: both now carry `wasChild`. Found while building a minimal single-role
plan, where it had a second consequence — any live network could be ended by a
step that is not entropy-driven, so no network could be waiting on anything and
the frontier question was unanswerable.

`processTermination`'s docstring said "a non-child instance terminated", which is
also wrong and is corrected rather than enforced: `Joins.wasTerminated` requires
a child to be *already* terminated and nothing else can terminate one, so a child
terminates through that constructor and is then collected by `join`.

### 10.62 Five of nine `ProcessCorrect` fields have no non-vacuous instance

Confirmed by a fourth review pass, by inspection of every `ProcessAcceptance` in
the repository. `TraceAccepts`, `DemandsWellFormed`, `TerminalAccepts` and
`ViewAccepts` are `fun _ => True` everywhere, so `initialDemands`,
`demandsWellFormed`, `terminal`, `observationsAccept` and `viewAccepts` are
discharged by `trivial` or `absurd` in all five correctness fixtures.

`TerminalDemandClassification.transferred` is `0` at all six of its construction
sites: the middle label of §2's three-way partition has never been non-empty in
this corpus. And `silent_fault_decreases` has no applicable process — every
specification here has `LogicalFault := PEmpty` and
`EnvironmentViolation := PEmpty`, so the module note's motivating case ("a
process that faults in a loop") has no fixture in either direction.

Separate from §10.49 and §10.56, which are about predicates that *cannot* be
constrained. These are predicates nobody had yet chosen to constrain, which is a
corpus gap and was cheaper to close.

**Partly closed**, by `Tests/Process/RichAcceptanceFixtures.lean`, and the first
version of this paragraph overstated it in three places that a reviewer took
apart one at a time.

Genuinely closed: `LogicalFault` and `EnvironmentViolation` are both inhabited
for `hiccup` and both have steps, so `ProcessEvent.fault` and
`ProcessEvent.environmentViolation` have instances and
`MeetsProcessProgress.silent_fault_decreases` has an applicable process.
`DemandsWellFormed` now bounds a bag a step actually issues — `hiccup`'s fault
schedules a retry — which the first version did not: every step issued the empty
bag and the field was discharged for it exactly as before.
`TerminalDemandClassification.transferred` carries the outstanding bag at a
*reachable* terminal run state, which the first version stated as law algebra
and did not exhibit.

**Not closed: `Demanded`.** The claim that `hiccup`'s `.result` case fires
`StepProgresses`'s emission disjunct describes a proof style, not a property: a
reviewer rebuilt `productive` discharging all three cases from the measure, and
rebuilt `hiccupCorrect` against an acceptance with `Demanded := fun _ => False`.
See §10.70 for why picking a better `hiccup` cannot fix it.

**Not closed, and weaker than it looks: `TraceAccepts` and `TerminalAccepts`.**
No `hiccup.Step` can emit a `blip` at all, so `no_blips` is an honest induction
every case of which is settled by the shape of `emitted`; and
`TerminalAccepts request result := result = true` *is* `hiccup.Terminal`'s second
conjunct, so `ProcessCorrect.terminal` is discharged by `.2`. Both fields are
non-vacuously *stated* and neither separates anything this process can do.
`unwanted_results_are_refused` is what `TerminalAccepts` is actually for — a
refutation about the class, not a fact about `hiccup`.

`viewAccepts` stays open and is §10.56: `ProcessSpec.view` is `none` in every
specification here and `ViewFacet` is constructed nowhere, which no choice of
acceptance can fix.

### 10.63 `transition_for_event` and `accessible` have no consumers

`transition_for_event` is `handlesEveryEvent`'s only consumer and has none of its
own; `accessible` had none until `no_infinite_silent_run` was stated. Both are
"law 5 / §7 made checkable" rather than used.

Not a defect — a driver is the consumer and no driver exists at this milestone —
but worth the entry, because §10.48 was closed by adding a one-link chain and a
one-link chain is what a reviewer will find next time. One did: the conclusion's
third conjunct, the `ProcessRunTransition`, is derivable from the first two plus
deliverability, so the theorem is `handlesEveryEvent`'s conclusion repackaged with
the successor bag computed. That is a real convenience for a driver and it is not
a *consumption* of the field in the sense §10.48 was about.

What the same reviewer also proved is that the field is genuinely load-bearing:
a record with `handlesEveryEvent` deleted, every other hypothesis supplied, and
the conclusion false is constructible. The previous version of the theorem could
be reproved without the field; this one cannot.

### 10.64 `NetworkProgressMeasure` is quantified over every world, not over reachable ones

`descendsOrProduces` and `frontierIsExternal` both quantify over an arbitrary
`before : plan.LogicalProcessNetwork`. The world is a record type, so that
includes worlds no execution can produce — an empty slot, a dead incarnation, an
instance attached to a parent that was never spawned — and a measure must account
for a step from each of them.

That is what stops a measure existing for any plan that does interesting work.
`serverPlan`'s unreachable worlds admit an unbounded spawn/die/restart chain with
no external event, so no rank descends across it, whatever its reachable
executions do. §10.60 attributed that to the plan's unbounded connection
population; the sharper statement is that it is about the plan's *world type*.

`Tests/Process/FrontierFixtures.lean` exists in spite of this rather than because
of it: `waitingPlan` was built so that its unreachable worlds admit only finitely
many non-entropy steps, and its rank `slack` is a measure of exactly that
bookkeeping. Read as §7 content it says almost nothing; read as an inhabitance
proof it is the first `NetworkProgressMeasure` in the corpus and the first
non-empty `AtFrontier`.

**One sentence of this entry was wrong and is corrected in §10.67.** The
unbounded chain at `serverPlan` is not only among unreachable worlds: a spawn
into a fresh connection slot is available from a *start* of that plan, so the
chain is reachable and the reachability index does not help there.

**Fixed.** `NetworkProgressMeasure` is now indexed by the network a run begins
at and carries a `Reachable` predicate with `reachableStart` and
`reachableClosed`, and both obligations are quantified over it — the same repair
`MeetsProcessProgress` had one layer down for the same reason. `Reachable` is not
a free predicate: the two closure fields force it to contain everything an
execution from `start` reaches, so `fun _ => False` is unavailable and the least
choice is exactly `plan.StepsTo start`.

What is not fixed is §10.65: nothing requires `start` to be a network a run may
actually begin at.

### 10.65 ~~`ExactInitialNetwork` and the network measure are not connected~~ — **closed, with one question left**

Following from §10.59 and §10.64: `Grass/Process/Network/Initial.lean` says what a
start is and `Grass/Process/Network/Progress.lean` says what progress is, and
nothing relates them. Whichever way §10.64 is ruled, the reachability the measure
needs is reachability *from an `ExactInitialNetwork`*, which is the definition
that has no witness.

`Tests/Process/FrontierFixtures.lean` now says it — `waiting_is_a_start` and
`the_measure_starts_where_a_run_starts` — but says it *beside* the measure rather
than through it. `NetworkProgressMeasure` still takes any world as its `start`, so
a plan may index a measure by a world no run reaches and discharge
`reachableStart` vacuously.

`NetworkProgressMeasure.startIsInitial` is now that field, and the order it had
to land in is the entry's content: a field demanding an uninhabited record makes
the record demanding it uninhabited too, so §10.59 had to close first. It did,
and this followed in four lines.

**And the question I said was left is not one.** `startIsInitial` quantifies the
request existentially, and I recorded that as "a measure is about *some* start of
the plan rather than a named one — needs a ruling". A reviewer proved the network
determines it: `onlyTheRoot` forces one live slot, `rootPresent` forces one
incarnation in it, and `rootRequest` reads the request off that incarnation.
`Grass/Process/Network/Initial.lean`'s `request_is_determined` is the theorem.

That is the fourth entry in this ledger recording a defect that did not exist,
and the fourth filed the same way — from a reading of a repair, without building
what it described. §10.54 is the method note and this is another instance of it.

### 10.66 ~~Nothing says a world's pending trace is something a process produced~~ — **closed**

`NetworkFragment.pending` gave `Commits` the provenance it had none of, and the
provenance is exactly `before.pending = emitted ++ after.pending`: a commit
publishes what is pending, in order, once. That killed the defect that made
`AtFrontier` empty for every measure — the old `Commits` was enabled at *every*
network.

The residual, proved generically by a fifth review pass: `pending` is a plain
field of `LogicalProcessNetworkCore`, so a commit is enabled at every network
whose `pending` is non-empty, and nothing states that a non-empty `pending` is
something a step produced. `{network with pending := [observation]}` is a legal
world of any plan and a commit of that observation is a legal step of it.

The statement that closes it is about an *execution*, not a world, so it could
not be a field of the world or of a transition — which is why the entry existed
at all.

`LogicalProcessNetworkCore.produced` is `observations ++ pending`, and
`Grass/Process/Trace/Linearization.lean` carries the laws:
`produced_extends` (every step grows it by exactly what it emitted, and by
nothing else), `commit_preserves_produced` (publishing moves the boundary
between the two traces and does not change their total),
`execution_produced_extends`, and `commit_publishes_only_what_the_run_produced`.

The claim is relative to whatever the execution started from, which is the right
shape: a run begun at an `ExactInitialNetwork` starts with nothing committed and
the root's projected start emission pending, so there the produced trace is
exactly what the run emitted.
`NetworkProgressMeasure.startIsInitial` is what ties a progress claim to that
case, and `Tests/Process/LinearizationFixtures.lean` is the witness at a concrete
commit.

### 10.67 `serverPlan` has no start with a measure, and `ProgressFixtures` is about a hypothesis nothing satisfies

Two facts a fifth review pass proved, which together say what
`Tests/Process/ProgressFixtures.lean` is currently worth.

**Its networks are not reachable.** All three of its theorems take
`measure.Reachable beforeReceive` as a hypothesis, and `beforeReceive` holds no
incarnation of any kind. A start has a live root, and no constructor empties the
root slot — `Joins.wasChild` excludes it and `join` is the only constructor with
`nowFree` — so `beforeReceive` is in no `plan.StepsTo start`. The hypothesis is
satisfiable only by a measure whose `Reachable` is strictly wider than
reachability, which the record permits and does not require.

**And the plan has no measure anyway**, for a reason §10.64 attributed to
unreachable worlds and which is sharper than that: a spawn into a fresh
connection slot is available *from a start* of `serverPlan` — the slot type is
`Nat`, `maySpawn .listener .connection` holds, and the connection protocol's
`Initial` is satisfiable — so the unbounded non-entropy chain is among reachable
worlds. The reachability index does not help. What would is a bound on the
population, which `PopulationLaw.boundedByResourcePolicy` defers to a resource
certificate this layer does not have.

Needs a ruling on whether `ProgressFixtures` should be rebuilt at a start of
`serverPlan` — which requires the population bound — or retired in favour of
`Tests/Process/FrontierFixtures.lean`, which has a start, a measure, and a
non-empty silent-run class.

### 10.68 A frontier is not something a measure declares — three attempts

Recorded as a method note rather than an open defect, because it is closed and
the closing took three rounds on one field.

`NetworkProgressMeasure.AtFrontier` was a predicate the measure supplied, with
`frontierIsExternal` as the obligation attached to it.

1. **"A frontier is left only by entropy."** A reviewer proved the predicate
   empty for every measure: a commit was enabled at every network (no provenance)
   and a spawn is enabled at almost every network, and neither is entropy-driven.
   §7's escape was unreachable, so every theorem in the module was vacuous.
2. **"…or by a step that descends the rank."** This made the predicate
   inhabitable and admitted the opposite degeneracy: a measure could declare
   *every* network paused and discharge the obligation from a case analysis it
   needed anyway. `SilentRun` requires each step to start off-frontier, so the
   class was empty and the theorems were vacuous again. A reviewer built that
   measure at the corpus's only plan.
3. **A narrower predicate in the fixture** — "the slot holds a live incarnation"
   — was refuted the same round: a live *attached* child is a network the program
   detaches on its own initiative, so calling it an external frontier says the
   outside must act when the program need not wait.

The mistake in all three is one thing. "Only the outside can move this network"
is a fact about which steps are *enabled*; it is not a claim anyone gets to make.
`ProcessPlan.AtFrontier` is now a definition, `Useful` is a property of the plan
rather than of a measure, `descendsOrProduces` asks the per-step question — *was
this step the outside acting?* — and `SilentRun` asks it of each step rather than
asking a measure whether it paused the network.

`Grass/Process/Progress.lean` has never had a frontier predicate and reached the
same shape independently. The two layers agreeing is the check that the shape is
right rather than merely smaller.

### 10.69 The network measure's `demanded` is the process layer's `Demanded`, one layer up

`NetworkProgressMeasure.demanded` is a free `boundary.Observation → Prop`, and
`Tests/Process/FrontierFixtures.lean` — the only measure in the corpus — sets it
to the elimination of an empty type. So `descendsOrProduces`'s emission disjunct
is unreachable there and `SilentRun.produced` is vacuous.

Exactly §10.49 at the network: a permissive `demanded` makes any emission
progress, and a `False` one makes the disjunct dead. §10.49 was recorded for the
process layer and the network analogue was not, which a reviewer pointed out.

Needs the same ruling as §10.49, and probably the same answer.

### 10.70 Every livelock this corpus knows about escapes through an author-supplied predicate

`Tests/Process/ChatterFixtures.lean` is the fourth livelock with a full
`ProcessCorrect`, and the first that a reviewer rather than a repair produced.
`chatter` has no external events at all — so the entropy escape §6 records is
unavailable to it — and no demands, and never terminates. It faults forever,
emitting one observation, and its acceptance's `Demanded` picks out that
observation. Every step satisfies `StepProgresses`'s emission disjunct.

`ProcessAcceptance.Demanded`'s docstring says the field exists so that "every
process could satisfy progress by logging" is false. This is a process satisfying
progress by logging, with a logged value the specification demands.

**It is not fixable at this layer, and the reason is worth stating precisely.**
`Demanded` is a predicate on observation *values*, so re-emitting one demanded
observation is indistinguishable from emitting a new one. Distinguishing them
needs a claim about the trace — that the run is making progress a specification
can see — which is a liveness property over executions, and this layer has no
model for one.

**And it explains why §10.62's `Demanded` claim cannot be repaired by a better
fixture.** A step that *requires* the emission disjunct moves neither the state
nor the outstanding bag and is not entropy; a process that can take such a step
repeatedly is `chatter`. The disjunct can only be made load-bearing by something
the layer should be excluding.

The pattern across all four livelocks is the finding. Every one escapes through a
predicate the *specification's author* supplies — `ProcessVocabulary.ExternalEvent`
for the self-delivered tick, `ProcessAcceptance.Demanded` here — and none escapes
through the measure. That the measure is airtight cost two rounds and two
fixtures (`Tests/Process/SpinFixtures.lean`, `Tests/Process/OscillateFixtures.lean`);
that the two predicates are not is what is left.

Needs a ruling on whether §7's "independently specified observation" is meant to
be a per-observation predicate at all, or a property of the trace — which would
be a `ProcessAcceptance` change and would give §10.49, §10.69 and this entry one
answer.

### 10.71 A frontier and a deadlock are the same thing

`ProcessPlan.AtFrontier network` is "every step from here is driven by entropy",
which a network with **no steps at all** satisfies vacuously.
`Tests/Process/FrontierFixtures.lean`'s `emptyWorld` is one — nothing can spawn
into it because a spawn needs a parent, nothing can restart because the slot is
empty, and every other constructor is uninhabited at that plan — and
`the_empty_world_is_a_frontier` is the consequence.

§7 excuses an infinite run that "remains at a declared external frontier". A run
that reaches a deadlock is not remaining at a frontier; it has stopped, and §7's
theorem has nothing to say because there is no infinite run to be about. So this
is not unsound as far as the progress theorem goes — but it means `AtFrontier` is
two things wearing one name, and a consumer that reads it as "this network is
waiting for the environment" would be wrong.

The narrower definition is "every step is entropy-driven **and** there is one":
`∀ step, DrivenByEntropy step` together with `∃ after, Nonempty (NetworkStep …)`.
Whether that is what §7 means is a question about the document — a program that
has genuinely finished all its work and is waiting for a request it will never
receive is, arguably, at a frontier and stuck at the same time.

Found while attempting `well_formedness_is_preserved`, which is what produced
§10.72 as well.

### 10.72 A spawn could install a root

`Spawns.authorized` reads the permitted-parent law off the new incarnation's own
`knownParent`, so an incarnation recording *no* parent discharged it vacuously —
and `docs/PROCESS.md` §3's spawn is a parent creating a child, not a program
beginning.

Two things it made possible. A run's beginning is
`Grass/Process/Network/Initial.lean`'s `ExactInitialNetwork`, not a transition, so
a spawned root is a start modelled as a step. And
`LogicalProcessNetworkCore.RootUnique` is a well-formedness law that a second
root breaks, so a spawn could take a well-formed network to an ill-formed one —
the shape `Spawns.slotAgrees` was added to close, one field over.

Fixed: `Spawns.spawnsAChild` requires `currentParent ≠ none`, the same predicate
`Detaches.wasAttached` and `Joins.wasChild` ask.

`Tests/Process/FrontierFixtures.lean` was the only `Spawns` witness and it was
exactly this defect: it spawned the root to model the program starting. It now
uses a detach instead, which is a real network step, and `emptyWorld` becomes a
network nothing can move — which is §10.71.

**`Restarts` had the same hole**, and working the capstone's `RootUnique` clause
settled it rather than leaving it to a ruling: a restart installing a root into a
slot whose previous incarnation had ended breaks that law exactly as a spawn does,
and a supervisor restarting a *root* is not a step under any reading — a root has
no supervisor, and if it ends the program is over. `Restarts.restartsAChild` is
the field.

`Restarts` was the sixth record with no witness, and it was found the same way as
the other five: the field went in and not one proof broke.
`Tests/Process/RestartFixtures.lean` is the witness — connection 7 dies and its
supervisor starts a fresh incarnation at a new generation — with the two
refusals the structure is for: reusing the dead incarnation's generation (law
22, refused by `NetworkStep.admissible`) and installing a root.

### 10.73 `well_formedness_is_preserved` is argued and not proved

`Grass/Process/Network/WellFormedness.lean` carries the two lemmas a proof of it
would be built from — `instanceProperty_preserved`, which is where the scope
discipline is spent, and `instanceFragment_inj` — and a clause-by-clause plan for
the six clauses of `LogicalProcessNetworkCore.WellFormed`.

Working that plan is what found §10.72's two defects, so it earned its keep
before it was finished. But the plan is an *argument*, and this ledger has five
entries recording defects that did not exist, every one filed from an argument
rather than a construction. It should be read as owed work, not as a result.

**Closed.** `ProcessPlan.wellFormed_preserved` is the theorem, all six clauses,
`#print axioms` clean. Reading the entry back against what it took:

* The plan had the **layer wrong**. It said "transition"; `NominalsAllocated` is
  a law of `NetworkStep`, because `usedNominals` moves by `historyExact`, which
  is a field of the step and not of the transition. A reviewer built the `restart`
  transition that wipes the history and strands the root's own generation.
* It had the **count wrong**. It said five of six clauses reduce through
  `instanceProperty_preserved`. `RootUnique` quantifies over two slots and does
  not have that shape; it is four, plus `root_was_there` used once per slot.
* It had **two clauses' evidence wrong**. `declared_slot_outcome`'s first payload
  reported the reference and the known parent, which settles neither
  `LifecyclesWitnessed` nor `RootUnique`. Both gaps were found by construction,
  by a reviewer, not by re-reading the plan.
* And it did not know about §10.87 at all, which is the one real defect the proof
  found.

Four errors in six clauses of argument. The entry's own warning was right, and
the record of it stays here rather than being tidied away: an argued plan is
worth writing because working it finds things, and worth distrusting because
what it finds is not what it says it found.

### 10.74 Three defects the trace split left behind in the weave layer

The `pending`/`observations` split gave `Commits` provenance and left stale
claims one module over, which a reviewer found by construction:

* `Grass/Process/Weave/Lens.lean`'s `emitting_steps_need_the_trace_inside` named
  `.observations`, which after the split only `commit` declares — so it
  constrained *driver* steps and said nothing about a role emitting, and a lens
  excluding `.observations` could select an emitting `processStep` and get the
  trace framed for free. It is now
  `emitting_steps_need_the_produced_trace_inside` over `.pending`, with
  `committing_steps_need_the_committed_trace_inside` kept for the narrower claim.
* `at_most_one_lens_may_emit` was "at most one lens may *commit*". Same repair.
* `Tests/Process/LensFixtures.lean`'s `the_connection_refinement_is_silent` was
  negative about a class no receive could be in: after the split, "this
  non-commit step does not declare `.observations`" is true of every non-commit
  step of every plan.

**Fixed, and the shape is the point.** A cross-module claim about another
module's fragment discipline is worth exactly as much as the last time someone
checked it — which is the same lesson `Grass/Process/Run.lean`'s "no replay"
qualification taught twice.

### 10.75 A lens could select no role at all

`ProcessRefinementLens.interiorChannelsTouchTheSelection` ties an interior
*escrow* fragment to a selected endpoint, and its docstring said that without it
"a lens with `Selected := fun _ => False` could still select real channel steps".
It closed the escrow route and left `.observations`, `.pending`, `.nominals`,
`.obligations` and `.session` unguarded, so the empty-selection lens was still a
full lens — a reviewer built one that owns the two trace fragments and selects a
real commit, with all four coupling fields discharged vacuously.

`selectsSomething` is the field. It is the cheap half of the repair and it is
honest about what is left: the *global* fragments — the two traces, the nominal
history, the obligation ledger — have no role attribution at this layer, so a
non-empty lens can still own one and select a step that has nothing to do with
the roles it named. That is §10.29's neighbourhood and is not closed.

### 10.76 `WeaveInvariantFamily.complete` asserted nothing

A field typed `(NetworkFragment → Prop) → Prop` with no law, whose docstring said
the structure "can refuse to let a family claim coverage it has not stated, which
is what making this a field does". Making it a field did nothing: a reviewer
built a family with `Key := Empty`, no mixins, and `complete := fun _ => True`.

It is now `Covers` plus `coversMeansCovered`: a claim of coverage obliges a mixin
for every fragment in the scope claimed.
`Tests/Process/WeaveFixtures.lean`'s `routeTableFamily` is the record's first
witness — the seventh record found empty this milestone, and found the same way —
and `the_family_may_not_claim_more` is the refusal.

What is still not required is that the claimed scopes be the ones the
*application* needs, which is the half `Grass.Process` genuinely cannot know.

### 10.77 Three named obligations in the weave and sequential layers that nothing discharges

Found by a reviewer running deletion tests. None is unsound; all three are costs
paid for no exported consequence, which is §10.48's shape one layer up.

* `Grass/Process/Weave/Mixin.lean`'s `HoldsInitially` takes an arbitrary
  `Initial` predicate because it predates
  `Grass/Process/Network/Initial.lean`'s `ExactInitialNetwork`. It is superseded
  by `HoldsAtEveryStart` and has no consumer. Deleting a named obligation is a
  decision about what §8 owes rather than a tidy-up, so it is recorded here
  instead.
* `Grass/Process/Weave/Mixin.lean`'s `ResourceOwnershipObligation` applies the
  caller's own predicate to the mixin's own fields, so `fun _ _ => True`
  discharges it. That is the same freedom §10.52 records for
  `ReachesSafePointObligation`, and the same answer applies: the predicate is
  another layer's and this one cannot audit it.
* `Grass/Process/Sequential/Adapter.lean`'s `DispositionIsEarned` occurs nowhere
  outside its own declaration, and is *free* where it is stated: `elaborate`'s
  terminal disposition is the all-zero partition at every terminal point, so the
  obligation reduces to `Accepts 0 0 0`, which every remainder law in this corpus
  grants. Both witnesses in the corpus make it vacuous.

`ProcessRefinementLens.selectedStateInterior`, `refinedRequirements` and
`refinementOnlyAdds` are in the same category and are *not* recorded as defects:
each constrains what a lens author may supply even though no theorem reads it,
which is a real thing for a coupling field to do. `refinedRequirements` is the
weakest of the three — it is data with no consumer since `deltas_accumulate` was
deleted, which is §10.50's exact shape — and is the one to remove if any go.

Needs a ruling per item on whether a named obligation with no consumer should
stay named or go.

### 10.78 One occurrence, two resolutions, in a two-step program

`Delivers` carries `onItsSession` — the occurrence's own `ChannelId` is the
session the step is about — because "session and occurrence were independent
parameters". Its five siblings did not: `ResolvesEscrow`, `ClosesSession`,
`KillsSession`, `Reroutes` and `RequestsCancel` took the same two independent
parameters with no such field, and nothing in `WellFormed` tied them either.

A reviewer built the consequence. `EscrowLedger.atMostOneRecordedEnding` is a
fact about *one ledger*, and §3's affine resolve token is not — so one occurrence
can be resolved once on each of two sessions and neither ledger notices. The
program is two steps: reroute an occurrence from `wire` to `away`, where the old
`Reroutes.arrives` let the destination acquire the occurrence itself, then drop
it there. Both are legal transitions, and the world afterwards records
`.rerouted away` on `wire` and `.dropped` on `away` for one occurrence.
`ResolvesEscrow.cannot_resolve_twice` and `resolution_is_exact` are both about
one ledger and were both evaded.

Fixed: all five carry `onItsSession`, and `Reroutes.arrives` now requires the
destination to gain a new occurrence rather than to be non-empty (§10.34).

Not one proof broke when the five fields went in, which is the seven-for-seven
signal: none of the five structures has a witness. §10.79.

### 10.79 Ten of the eleven channel constructors have never been inhabited

`SendsEscrow`, `ClosesSession`, `KillsSession`, `RequestsCancel` and `Reroutes`
had no witness anywhere in the corpus, and of `NetworkTransition`'s channel
constructors only `.receive` was ever built. A reviewer built witnesses for
`send`, `channelClose`, `channelDeath`, `requestCancel`, `acknowledgeCancel`,
`drop` and `reroute` in scratch, so none is uninhabitable — the corpus simply did
not exercise them.

**Four of the five are now built**, at the world `the_send` reaches:
`Tests/Process/ChannelStepFixtures.lean` carries a close, a channel death, a
cancellation request and a drop, together with
`a_close_on_the_wrong_session_is_refused`, which is what `onItsSession` buys.

`Reroutes` was the one left, "for a reason worth stating: it needs two sessions
on one edge and this topology names one, so building it is a change to the
fixture *world* rather than an addition beside it".

**That reason was false, and it was an argument rather than a construction.** A
`ChannelId` is two endpoints *and an epoch*, and §3 put the epoch there precisely
so one edge between one pair of incarnations can carry more than one session —
"dropping the epoch and identifying a session by its endpoints would let a
closed-and-reopened channel inherit the old session's in-flight messages". A
second session is `wire` with a later epoch.
`Tests/Process/RerouteFixtures.lean` is the witness, and it is an addition beside
the fixture after all.

**And "eleven of eleven channel constructors now have one" was wrong twice**, as
a later claims audit found. There are *twelve* channel constructors, and what has
a witness is not the same as what is exercised. At the `NetworkTransition` level,
four are ever applied — `.send`, `.receive`, `.reroute`, `.channelClose`, all in
`Tests/Process/PreservationFixtures.lean`. At the step-record level `ResolvesEscrow`
is witnessed only at `.dropped`, so `timeout`, `acknowledgeCancel`, `senderDeath`,
`receiverDeath` and `coalesce` have no positive witness at their own
`ChannelResolution`; `Tests/Process/CloseFixtures.lean` takes an acknowledgement
as a hypothesis rather than building one. §10.105.

An independent emptiness sweep reached the same conclusion at the same time,
which is worth recording: two readers who each *built* the thing agreed, and the
argument that neither could was made by a reader who had not.

Two consequences it found, both worth more than the count:

* **No `SendsEscrow` could reach `beforeReceive`.** `liveSteps.Send` pinned its
  after-world, and that world's pending trace is empty where `beforeReceive`'s is
  not. So the corpus's only delivery started from a world its own plan's send
  relation could not produce, and the send/receive pair did not compose.

  **Closed.** `liveSteps.Send` is a relation rather than a world equation — the
  same repair `Receive` needed for the same reason — saying what §3 asks of a
  send: the session is open, the occurrence was not already escrowed here, and it
  is outstanding afterwards. `Tests/Process/TransitionFixtures.lean`'s `the_send`
  is the corpus's first `SendsEscrow`, `the_send_puts_it_in_flight` is
  `ProcessPlan`'s two tie fields composed at a step that actually happened, and
  `the_receive_after_the_send` is the delivery that follows it at the world the
  send reached.

  `beforeReceive` keeps its pending `beep` and is still a manufactured world, for
  the same reason `afterClose` is: producing a pending observation needs a live
  instance, and that world has none. The diamond fixture is stated there and the
  composed chain is stated at `sent`/`received`.
* **`afterClose` is unreachable by `channelClose`**, and its docstring said it
  was reachable. It keeps `beforeReceive`'s ledgers, in which nothing is
  resolved, so `ClosesSession.nowResolved` can never hold there. The docstring is
  corrected; `nothing_can_be_sent_on_the_shut_wire` is a real theorem stated at a
  manufactured world.

`ProcessPlan.Sound` and `LogicalProcessNetworkCore.WellFormed` were also
inhabited nowhere — `terminated_result_is_exact` took a `Sound` hypothesis
nothing had ever supplied. `Tests/Process/FrontierFixtures.lean`'s
`waiting_is_wellFormed` and `waiting_is_sound` are the witnesses, and the fixture
says plainly that five of the six clauses cannot fail at that plan:
`nominalsAllocated` is the one with content. Inhabited, not exercised — the same
distinction §10.59 drew for `ExactInitialNetwork` at the same plan.

Needs the fixtures, and the send/receive pair is the one to build first: it is
the only one whose absence hides a *composition* failure rather than a coverage
gap.

### 10.80 A plan can send without sending

`ChannelContract.SendPre := NetworkAssertion.pure False` makes
`ChannelContract.send` vacuous while `steps.Send` relates every pair of worlds on
an open session — including a send that puts nothing in flight. Every field of
`ChannelContract`, the whole footprint discipline, and both of `ProcessPlan`'s tie
fields are still discharged.

`escrowImpliesOutstanding`'s docstring discloses a narrower escape — "a plan
whose relations are empty satisfies every tie" — and this is wider: the relation
is *total*, and it is the precondition that is empty. `send_puts_it_in_flight`
and `send_establishes_escrow` are unreachable at such a plan, so it is degenerate
rather than unsound, but a reader of that docstring would not expect it.

Closing it means requiring a plan's `SendPre` to be satisfiable somewhere, which
is a `ProcessPlan` field of the same shape as `NetworkProgressMeasure.Useful`
before that became a definition. Needs a ruling.

### 10.81 The cancellation policy layer governs nothing a network can do

`ChannelResolution.cancelAcknowledged` carries a `CancelReason`, which is a
`CancellationPointId` — and no file under `Grass/Process/Network/` mentions
`CancellationPolicy`, `PointsDeclared`, `ScopedCancellationCertificate`,
`CancellationSequence` or `CancellationRegion`. `EscrowLedger`'s
`acknowledgedWasRequested` checks that a request was made and not that the point
acknowledging it was ever declared.

A reviewer built the acknowledgement at a point in a scope no policy names.
`Grass/Process/Cancellation/` is a self-contained algebra with no consumer in the
transition family, which is the same shape as §10.77's named obligations one
layer up.

Needs a ruling on whether a plan should carry a cancellation policy that
`acknowledgeCancel` checks against.

### 10.82 `ProcessPlan.Sound` adds nothing, and its docstring said it would

`Sound` has one field, `core : WellFormed`, and its docstring said
`Transition.lean` "will add the clauses a plan can state and a bare network
cannot — that a step's channel transitions are the ones this plan's contracts
govern, and that the escrow resolutions are the transition family's".

`Transition.lean` landed and added neither. It made both clauses fields of the
*transition* structures instead — `SendsEscrow.contractual` and
`Delivers.contractual` — which is the better place: they are facts about a step
and `Sound` is a predicate on a network. A reviewer pointed out that the forward
reference was to a module that had already shipped without doing what it said.

So `Sound` is `WellFormed` under another name. It is kept because
`terminated_result_is_exact` is stated over it and a plan is where a future
network-level clause would go. If none arrives it should be collapsed.

Needs a ruling: is there a network-level soundness clause a plan can state that
the world cannot? The two named have found a better home, and no third has been
proposed.

### 10.83 `Spawns` and `Joins` had never been inhabited

The two constructors that create and reap a child, ten and four Prop fields
between them, built nowhere in the corpus. Both had absorbed fields over several
review rounds — `Joins` took `wasTerminated` and `wasChild`, `Spawns` took
`slotAgrees`, `startsInitial` and `spawnsAChild` — with, by their own docstrings,
no proof breaking. That is this milestone's seven-for-seven signal and it fired
twice.

**Closed** by `Tests/Process/LifecycleStepFixtures.lean`. `the_join` went through
first try; `the_spawn` needed the existing `holding` world and one allocated
generation. Neither was hard, which is the finding: they were empty for want of
trying, and every field either structure gained had been checked by nothing.

The negative halves are what make them worth more than a count.
`a_spawn_may_not_install_an_orphan` shows `spawnsAChild` refusing a parentless
incarnation, and `a_spawn_may_not_prestock` shows `startsInitial` refusing one
already holding a demand it never issued.

**One docstring correction owed.** `Spawns.spawnsAChild` says the field stops a
spawn installing a *root*. At the fixture topology that is not what stops it:
`ProcessParentage.root` is indexed at the graph's root kind, so `.root` does not
typecheck for a `.connection` at all. The reachable attack is the *orphan*. The
field is right; its stated justification is one case wider than the type permits.
Recorded, not yet edited, because the general claim is true at a topology whose
root kind has instances and the docstring should say which case it means.

### 10.84 `StructuralProcessNetwork.CompositionLaw` asserted nothing

One field, `holds : Prop`, and no proof fields — a `Prop` with a constructor.
Holding one carried no information: `⟨False⟩` inhabits it, nothing anywhere
required `holds`, and an emptiness sweep found the structure constructed nowhere
in the corpus. The same shape as §10.76's `WeaveInvariantFamily.complete`, one
module over.

The docstring's justification — "a network with no law attached is honestly a
network with no law attached" — is sound and the wrapper did not serve it: a
network *with* a `CompositionLaw` was also a network with no law attached.

**Closed** by deleting it. A composition law is a `Prop`, and callers state
propositions. `EveryRolePopulated` stays and now says so. The `docs/SEMANTICS.md`
argument for splitting laws out of the network structure is untouched and still
right.

### 10.85 `Grass/Process/Network/Mailbox.lean` was an unwitnessed island

`MailboxEntry` constructed nowhere, `Mailbox` inhabited anywhere only by
`Mailbox.empty`, and `SelectiveReceive` — nine fields, five of them Props —
never built. So `Mailbox.distinct` had never been discharged at a non-empty list,
`PerSenderPair` had never been evaluated at a mailbox with an entry, and all five
selective-receive laws were claims about a relation with no inhabitants. Nothing
else in `Grass/Process` imports the module.

**Closed** by `Tests/Process/MailboxFixtures.lean`, deliberately not at the
smallest inhabitant: a one-entry mailbox whose entry matches would discharge
`skippedRejected` and `exhaustedIfNone` vacuously with `scanWork = 0`.
`theReceive` scans past a rejected entry to take the second.

### 10.86 `ChildDemandBinding` was never built, and one law still cannot fail

Seven fields, five of them Props, constructed nowhere — so
`successAnswersThisDemand`, `pendingDoesNotAnswer` and `reflectsEveryAnswer` were
claims about an empty relation, and `Drops`, the predicate that stops a failure
being silently discarded, had never been evaluated at an outcome.

**Closed** by `Tests/Process/ChildBindingFixtures.lean` for the inhabitation.
`theBinding` routes all six child outcomes and `death_is_named` evaluates `Drops`.

An earlier version of this entry said: "`reflectsEveryAnswer` is cheap whenever
the demand's result type is a singleton, and **every demand in this corpus has a
singleton result type**, so the law has never been asked a question it could
fail." **That was false, and a reviewer refuted it in one line.** `Demand.log`'s
result type is `Bool`, in `Tests/Process/M1Fixtures.lean` — the file the binding
fixture imports. The law could have been asked a real question at any point; the
fixture had bound `.tick`, whose result is `Unit`, and the entry generalised from
the fixture to the corpus without looking.

**Closed.** `theLogBinding` binds `.log`, and the shape of it is forced rather
than chosen: `the_terminal_result_is_a_singleton` shows a `.succeeded` outcome
carries no information at this child, so success can supply at most one of the
two answers and `pendingDoesNotAnswer` forbids pending supplying the other. The
second answer comes from a supervised death. Delete either branch and
`reflectsEveryAnswer` fails.

One docstring corrected with it. `Drops` was described as "what stops a binding
routing a failure to nothing at all"; it stops nothing, since
`ChildDemandBinding` has three laws and none is about failure outcomes. What
rules out silent discarding is that `classify` is *total*, plus
`routed_or_dropped`. `Drops` names the choice; it does not constrain it.

### 10.87 A step could resolve an occurrence it never mentioned

`LedgerExtends` says nothing was *erased*: a resolution once written is
permanent, occurrences are only appended, a cancellation request does not
evaporate. It says nothing about what was *added*. So a step that legally
resolves one occurrence could, in the same move, append an unrelated occurrence
and resolve it too, with no field of any constructor mentioning it.

Found by construction while trying to prove `WellFormed`'s sixth clause.
`Tests/Process/RerouteFixtures.lean` builds a `drop` that discharges every field
`ResolvesEscrow` had — `onItsSession` and `nowResolved` are about its own
occurrence, `ledgerExtends` permits the append, `scope` is one session's escrow —
and appends a second occurrence resolved `.rerouted` to a session whose ledger
the step never touches. It takes a network satisfying
`LogicalProcessNetworkCore.ReroutesLand` to one that does not, so the sixth clause
was **not preserved by the transition family**.

**Closed** by `ResolvesNothingElse`, on all seven structures that write an escrow
ledger, and by its stronger sibling `ResolvesNothing` for the three that end
nothing at all — a send escrows, a cancellation request records, a reroute's
destination receives. Eight witnesses had to be re-discharged, which is the
signal the field is not vacuous. The stranding drop is now
`the_stranding_drop_is_refused`, and `the_stranding_ledger_extends` and
`the_stranding_scope` show the other fields really were satisfiable at those
worlds, so the refusal is the field's doing rather than an accident of the
fixture.

Two general points this one is worth keeping for. First: **a prefix law is not a
step law.** `LedgerExtends` is exactly right about what it says and says nothing
about the step's own reach, and every escrow constructor was relying on it for
both. Second: it was found by trying to prove a theorem, not by reading the
structures — five review rounds over `Transition.lean` had not found it, and the
proof found it in one.

### 10.88 The progress layer rests on one emptied plan

An emptiness sweep observed that `Sound`, `ExactInitialNetwork`,
`NetworkProgressMeasure` and `LogicalProcessNetworkCore.WellFormed` have exactly
one plan-level witness family between them:
`Tests/Process/FrontierFixtures.lean`'s `waitingPlan`, which sets `Demand`,
`Observation`, `InterruptReason`, `LogicalFault`, `EnvironmentViolation`,
`TerminalResult`, `SharedRegion` and `ChannelKind` all to `PEmpty` and
`ProcessKind`, `InstanceId` and `Carrier` all to `Unit`. So `rootUnique` holds by
`rfl` because there is one slot, `lifecyclesWitnessed` and `reroutesLand` are
`.elim`, and `NetworkProgressMeasure.demanded` is `observation.elim`, which means
the "or produces a demanded observation" disjunct of `descendsOrProduces` can
never fire.

The fixture's own docstrings concede most of this. What none of them says is that
it is the **only** instance, so `Network/Progress.lean` and `Network/Plan.lean`
are known to hold of exactly one `Unit`-slotted, channel-less, observation-less
world.

**A correction to the paragraph above, made the same way the rest of this ledger
gets corrected — by looking rather than by agreeing.** `WellFormed` does not
belong on that list. `Tests/Process/WorldFixtures.lean`'s `quiet_is_wellFormed`
is a second witness, at `serverPlan`. It is *vacuous* — all six clauses are
`absurd found`, the empty network being well formed because there is nothing to
be wrong about — which is a different complaint from having no witness, and the
sweep's own table said so. Stating it as "no witness" would have been the same
overclaim §12's table made about `Spawns`.

**And `WellFormed` now has a non-vacuous one.**
`Tests/Process/PreservationFixtures.lean`'s `spawned_is_wellFormed` is
`quiet_is_wellFormed` carried across one spawn by `wellFormed_preserved`, and the
network it certifies holds a child: `the_newborn_has_a_permitted_parent`,
`the_newborn_generation_is_allocated` and `the_newborn_is_where_it_says` are read
out of it, and none is statable at `quiet`.

**And that paragraph is itself now stale**, which a claims audit caught: since
`Tests/Process/PreservationFixtures.lean` landed, `serverPlan` has
`withRoot_is_a_start : ExactInitialNetwork`, `withRoot_is_wellFormed`,
`withRoot_is_sound` and `spawned_is_sound`. Three of the four records named above
have a second witness family, at the plan with real channels, slots and
observations.

What remains is **`NetworkProgressMeasure`**, which still has only `waitingPlan`
— a plan whose `Observation` type is empty, so the "or produces a demanded
observation" disjunct of `descendsOrProduces` can never fire. That is the largest
single gap this milestone leaves, and it is a gap in the *progress* layer alone.

### 10.90 `ResolvesNothingElse` forbade the close it was meant to enable

§10.87's repair was too strong. `ChannelResolution.channelClosed` exists because
"an occurrence in flight at an ordinary close has no ending, and would either
strand live forever or have to be misrecorded as a death" — so an ordinary close
must end *every* message in flight on the session. `ResolvesNothingElse` on
`ClosesSession` forbade exactly that.

Local adversarial review built the world: two ordinary sends on one session, then
a close. The close could end one message; the second is left `Outstanding` on a
`.closed` session, and `ClosesSession.wasOpen` and `KillsSession.wasOpen` refuse
every later close or death, so it strands or a `drop` misrecords it. The field
defeated the reason the resolution is in the language.

`ChannelResolution.coalesced` is the second case, and its own docstring names it:
a coalesce merges a carrier's "fellow sources", plural.

**Closed** by `ResolvesOnlyAs`, which bounds the *kind* of ending rather than the
count — a step may end several occurrences, and every one ends the way the step
says. That is all §10.87 needed, and `stood_or_declared` is the reading
`WellFormedness.lean` takes of it, which made the sixth clause's proof shorter:
the case split on which occurrence the step named disappears.

`Delivers` keeps the narrow form, and that is not an oversight: `cursorAdvances`
says the receiver consumed *exactly one* message, so a delivery recording a
second occurrence `.received` would be recording a delivery that did not happen.

And the positive obligation that had been missing all along went in with it:
`ClosesSession.closesEverything` and `KillsSession.killsEverything`.
`Tests/Process/CloseFixtures.lean` is both halves, at a world `the_second_send`
proves reachable.

**What this pair of entries is really about.** §10.87 was found by trying to
prove a theorem and §10.90 by attacking the repair, one round apart. The first
field was the narrowest thing that made the proof go through, and narrowest-that-
works is not the same as right. A repair deserves the same adversarial round as
the thing it repairs.

### 10.91 A step could escrow a message nothing sent

The create-side twin of §10.87, missing for the same reason.
`LedgerExtends.createdPrefix` says occurrences are only *appended*, and appending
is the hole: `ResolvesOnlyAs` bounds what a step *ends* and nothing bounded what
it *creates*.

Local adversarial review built a `drop` discharging every field
`ResolvesEscrow` had which conjures an unrelated occurrence into flight, and then
proved the thing that makes it serious: at the after-world the edge contract's
`Escrow` assertion **holds** of a message nothing sent. `docs/PROCESS.md` §3
gives only a send that power, and `SendsEscrow.contractual` is the only field
tying a step to a plan's own `Send` relation. It was being bypassed.

**Closed** by `CreatesNothing` on `Delivers`, `ClosesSession`, `KillsSession` and
`RequestsCancel` — a delivery consumes, a close and a death end, a request
records, and none sends — by `SendsEscrow.createsOnlyTheMessage`, by
`Reroutes.destinationCreatesOnlyArrivals`, and by
`ResolvesEscrow.createsOnlyTheCarrier`, which carries the one exception:
`ChannelResolution.coalesced`'s carrier, which `coalesceCarrierLater` requires to
be in this ledger and strictly later and which `NominalKind.coalescedReplacement`
says is fresh.

`Tests/Process/CloseFixtures.lean`'s `a_drop_that_conjures_a_message_is_refused`
is the refusal.

### 10.92 `Reroutes.elsewhere` was a field and is a theorem

`wasOutstanding` says the occurrence is unresolved on its own session,
`destinationResolvesNothing` says the destination's ledger resolves nothing this
step, and `nowResolved` says it *is* resolved afterwards. A reroute to its own
session needs all three, so `destination ≠ session` follows and does not need
asserting. A reviewer proved it generically, at every plan and every pair of
worlds.

The field's docstring claimed something else — that without it "resolving an
occurrence as `.rerouted` to the session it is already on would satisfy `arrives`
from the ledger it is leaving". That was true of an earlier `Reroutes`. It stopped
being true when `destinationResolvesNothing` went in, and nothing noticed, because
a field that is *implied* still elaborates and its fixture still discharges it.

**Closed**: the field is gone and `Reroutes.elsewhere` is the theorem, so
`a_reroute_to_the_same_session_is_refused` still reads the same and now rests on
something.

**The general lesson, which is the reason to keep this one.** §12's rule is that a
record absorbing a field without a proof breaking is a record nothing inhabits.
This is the dual: a record absorbing a field that *nothing breaks when you delete*
is a record with a redundant field, and the only way to find one is to try
deleting it. Nothing in the build detects it — a redundant field costs a line in
each fixture and buys nothing, and the docstring explaining why it is needed goes
on being read as if it were true.

### 10.93 A view obligation that could not fail

`Tests/Process/ViewFixtures.lean` closed §10.56 with an acceptance whose view
clause was the *image of the render*: a rendered view is acceptable when some
state renders to it. The predicate refused values outside the range, and the file
claimed that made the obligation non-vacuous.

It did not. `ProcessCorrect.viewAccepts` is asked for
`ViewAccepts facet (facet.render state)`, and `⟨state, rfl⟩` discharges that for
*any* facet, *any* render and *any* specification. A reviewer compiled a bogus
facet the spec does not carry and had it accepted, re-proved the file's own
theorem without the `gauge.view = some facet` hypothesis, and mutated `render` to
a constant without breaking the build. It was `fun _ _ => True` wearing an
existential.

**Closed** by making the clause a *bound* — a view of `gauge` reports at most one
step of remaining work — checked by mutating `render` to `fun _ => 2` and
confirming `gaugeCorrect` stops elaborating.

`the_bound_is_only_about_this_facet` records the honest limit: `ViewAccepts`
receives a facet and a value of that facet's view type and nothing else, so a
bound on a particular view has to name the facet before it can say anything about
the value, and at any other facet the clause asks nothing.

**Third entry in a row about the same mistake.** §10.90, §10.92 and this one are
all repairs that were not attacked. The check that would have caught all three is
the same one: after adding a field or a clause, try to satisfy it *badly* — with
the wrong render, the wrong occurrence, the field deleted — and see whether
anything notices.

### 10.94 The strongest field of a reroute was spent and thrown away

`Reroutes.arrives` was strengthened after review built a reroute that delivers
nothing: it now says the destination *gained* an occurrence, and that what it
gained carries this occurrence's message. `LogicalProcessNetworkCore.ReroutesLand`
— the well-formedness clause that field feeds — said only that the destination's
ledger holds *something*.

So the strengthening bought a fact about the *step* and nothing about the
*network*. A reviewer built the world: fully `WellFormed`, an occurrence resolved
`.rerouted` to a session, and nothing on that session carrying the payload.
`wellFormed_preserved` propagates the clause faithfully, and the clause was the
weak one — which matters because `WellFormed` is what every module downstream
assumes, not `Reroutes`.

**Closed.** `EscrowLedger.ReroutedElsewhere`'s `landsAt` now takes the rerouted
occurrence as well as the destination and the arrival, and `ReroutesLand` asks
`arrival.1 = occurrence.1`. `reroutesLand_preserved` carries it: a standing
reroute keeps its arrival by `ledgers_extend`, and a new one is this step's, with
`arrives` supplying both halves.

One consequence worth recording, because it reverses part of §10.90.
`Reroutes` had been given the wide `ResolvesOnlyAs` along with its siblings, and
under the strengthened clause that is wrong: `arrives` witnesses *one* arrival, so
a reroute marking several occurrences `.rerouted` to one destination would satisfy
the clause for one of them and fail it for the rest. `Reroutes` takes the narrow
`ResolvesNothingElse`, like `Delivers`, and for a reason of the same shape — the
constructor's other fields are singular, so its resolution bound has to be too.

**Three entries, one field.** §10.34 asked for an arrival field; §10.78's round
strengthened it; this one connected it to the clause it exists to serve. Each
round was right about what it fixed and silent about the seam beyond it. What
finds a seam is asking what a *consumer* of the invariant can conclude — not what
the constructor guarantees.

### 10.95 `ResolvesOnlyAs` was too wide for five of the six it covered

§10.90 replaced `ResolvesNothingElse` with `ResolvesOnlyAs` on `ResolvesEscrow`,
justifying it by `ChannelResolution.coalesced` merging a carrier's "fellow
sources, plural". That conflated two things: the *carrier* collects several
sources, and each source is consumed by its own `coalesce` step. §3's disposition
acts on "that exact reply occurrence".

A reviewer compiled the consequence: a `drop` that disposes of two in-flight
messages while naming one. The same shape works for `timeout` and
`acknowledgeCancel`. Beyond untidiness, `NetworkTransition.drop`'s occurrence
parameter no longer determines what the step did, which is the property the
transition family's own module header claims for its constructors.

**Closed**: `ResolvesEscrow` is back to `ResolvesNothingElse`. `ClosesSession`
and `KillsSession` keep `ResolvesOnlyAs`, because ending the whole session *is*
what they are for, and `Delivers` and `Reroutes` keep the narrow form for reasons
of the same shape — `cursorAdvances` and `arrives` are both singular.

### 10.96 `closesEverything` mandated the defect `onItsSession` refuses

§10.90's new field quantified over every outstanding occurrence on the session
with **no on-session guard**, and `Reroutes.arrives` asked only that the arrival
carry the rerouted occurrence's *message* — not that it belong to the destination
session.

A reviewer put the two together and compiled a two-step program: a reroute whose
destination acquires the source session's own occurrence, then a close of that
destination. `closesEverything` *obliges* the close to write a second
`ChannelResolution` for it, while the reroute's own resolution still stands on
the source ledger. One occurrence, two endings, at one world —
`ResolvesEscrow.onItsSession`'s docstring names this exact program as the thing
it exists to refuse, and the new field reached it by a path that field does not
cover. The reviewer proved it generically: *every* close of that destination
double-resolves.

**Closed** at both ends. `closesEverything` and `killsEverything` take
`other.2.1 = session`, and `Reroutes.arrives` pins `arrival.2.1 = destination`, so
the acquiring reroute is unbuildable in the first place.

The sharpest thing about this one: the pre-§10.90 field made it *impossible*, and
the repair made it *mandatory*. A repair can be worse than the defect, and the
only thing that catches that is attacking the repair.

### 10.97 An acknowledgement could write the request it acknowledged

`EscrowLedger.acknowledgedWasRequested` is a law of *one ledger*: an
acknowledgement in it must have a request in it. Nothing said the request was
there *before the step*, and no constructor bounded `cancelRequested` at all — so
an `acknowledgeCancel` could write the request and the acknowledgement in the
same move. A reviewer compiled one from a world where `cancelRequested` is `false`
for every occurrence.

`ProcessPlan.RequestsCancel`, with its `wasNotRequested`, `stillOutstanding` and
`ledgerExtends` guards, was bypassable entirely, and `docs/PROCESS.md` §3's affine
cancellation request was enforced by nothing. The same step could prime *other*
occurrences, setting up later acknowledgements.

**Closed** by `RequestsNothing` on every escrow constructor that does not request,
`RequestsCancel.requestsNothingElse` for the one that does, and
`ResolvesEscrow.acknowledgesARequest`, which requires the request to have been
made before the step.

This is §10.87 and §10.91 a third time, at a third ledger field: `created` was
bounded, then `resolution` was bounded, and `cancelRequested` — the third mutable
field of an `EscrowLedger` — was bounded by nothing. The general form of the
check is: **for each field of a state a step may write, which field of the step
bounds it?**

### 10.98 A reroute could multiply the payload

`arrives` bounded the arrival's existence and its message. It bounded neither the
arrival's *session* (§10.96) nor the *count*, so one reroute of one occurrence
could put two distinct occurrences carrying the same payload in flight at the
destination — a reviewer compiled it, and proved the resulting world still
satisfies `ReroutesLand`.

**Closed**: `arrives` pins the arrival uniquely — every occurrence the destination
gains is *that* arrival. `SendsEscrow.createsOnlyTheMessage` and
`ResolvesEscrow.createsOnlyTheCarrier` had this shape already; the reroute's
destination did not.

### 10.99 `ViewAccepts` could not see the state, so no view clause could bite

Two attempts at §10.56's fixture failed the same way, and the cause was in
`ProcessAcceptance` rather than in the fixture.

`ViewAccepts` received a facet and a rendered value and nothing else.
`ProcessCorrect.viewAccepts` is handed exactly `ViewAccepts facet
(facet.render state)`, so *any* predicate satisfied by the render's own image
discharges it for free:

* the **image of the render** — a reviewer discharged the obligation at a bogus
  facet the specification does not carry, and re-proved the fixture's own theorem
  without the `view = some facet` hypothesis;
* a **bound** (`≤ 1`) — a second reviewer mutated the render to the constant zero
  and the bound survived, so a view reporting "no work remains" at the working
  state was accepted. The fixture's docstring claimed at that point that mutating
  `render` breaks the obligation; only mutating it *upward* did.

Neither clause could say a view *reflects* anything, because neither could see
what it was supposed to reflect.

**Closed** by giving `ViewAccepts` the state.
`Tests/Process/ViewFixtures.lean` now writes down an `intendedView` — what the
specification says a view of this process should report — and the clause asks the
rendered value to equal it at that state, so `viewAccepts` obliges the process's
`render` to implement the specification's intent. Both the constant and the
swapped mutation break it; I checked rather than argued.

**What this one is really about.** Two rounds of fixture-level repair could not
fix a signature-level defect, and each repair looked like progress because it
refused *something*. The question that would have found it in one round is not
"does the predicate refuse anything?" but "**what would the obligation have to see
in order to fail?**" — and `ViewAccepts` could not see it.

### 10.100 A coalesce could import a carrier from another session

The worst thing found on this branch, and every part of it was compiled.

`ChannelResolution.coalesced`'s docstring says the carrier is "this occurrence of
the same session". Nothing enforced it: `ResolvesEscrow.onItsSession` constrains
the *source*, `EscrowLedger.coalesceCarrierLater` asks only that the carrier be in
this `created` with a later rank, and §10.91's `createsOnlyTheCarrier` asks only
that a created occurrence *be* the carrier.

So a coalesce may install a carrier whose own `ChannelId` is a different session.
That carrier is outstanding on this ledger, and §10.96's on-session guard on
`ClosesSession.closesEverything` cannot see it. A reviewer compiled the
consequences in both directions:

* **The payload strands and no transition can ever end it.** Close, death,
  disposition, delivery and reroute all carry `onItsSession`, and none of them can
  name an occurrence belonging to another session. That is precisely the
  disjunction `ChannelResolution.channelClosed` was added to break, and it is
  reached by the one path the guard skips.
* **And the session becomes unclosable**, because a close must end everything
  outstanding and the only thing outstanding is the thing the guard excludes.

**Closed** by `ResolvesEscrow.carrierOnItsSession`, the twin of the
`arrival.2.1 = destination` conjunct §10.98 gave `Reroutes.arrives`.

**Why it went unnoticed for a round.** The field that would have caught it —
`ClosesSession.resolvesNothingElse`, before §10.90 widened it — was weakened in
the same round that §10.96's guard created the hole. Two changes to adjacent
fields, each defensible alone; the gap was between them. The check that finds
this is not about either field: it is *for each occurrence a step can leave in a
ledger, which constructor can end it?*

### 10.101 A reroute could deliver into a closed session

A reroute puts a live payload into a session, which is what a send does, and
`SendsEscrow.sendOnOpenSession` has guarded a send since `ChannelContract`
acquired the law. `Reroutes` had no such guard: its scope names two escrow
fragments, and no field of it mentioned `sessions` at all. A reviewer compiled a
complete reroute delivering into a session already `.closed` — after which no
close or death of that session is possible either, since both demand `wasOpen`.

**Closed** by `Reroutes.destinationWasOpen`. Reading a session's status is not
writing it, so the field needs nothing from `scope`.

The general shape: **two constructors that do the same thing to the world should
carry the same preconditions**, and `send` and `reroute` both put a payload in
flight. Nothing in the module layout makes that visible, because they are
different structures in different parts of one file.

### 10.102 `ViewAccepts` still admits a clause that cannot fail

§10.99 gave `ViewAccepts` the state, which made a real obligation *possible*. It
did not make a vacuous one impossible, and a reviewer showed the vacuous one
survives the anti-vacuity test this codebase uses elsewhere.

`ViewAccepts := fun facet state view => view = facet.render state` — the *render
graph* — discharges `ProcessCorrect.viewAccepts` by `rw` for every specification,
facet and render. And it is *single-valued* in `view` at each state, which is the
property `EndsInstance.custodyDeclared`'s second conjunct uses to rule out
`fun _ _ _ => True`. So the standard test passes it.

The reason single-valuedness does not help here: `custodyDeclared` is quantified
over *candidate* after-states, so pinning the outcome is content;
`ViewAccepts` receives the render's output as an argument, so pinning it to that
argument is not.

Not closed, and it may not be closable at this layer.
`Tests/Process/ViewFixtures.lean`'s `intendedView` is textually identical to
`remaining.render`, so that fixture passes by *intent* rather than by
construction — a reader has to trust that the author wrote the intent first.

This is the same family as §10.49 (`Demanded`), §10.56's original form, and
§10.70: **an author-supplied predicate can always be made vacuous, and no field
of the record can stop it.** What distinguishes the ones this milestone closed is
that the vacuity was forced by the *signature* rather than chosen by the author.
Needs a ruling on whether that distinction is worth a mechanism.

### 10.103 Two things a step may write that nothing bounds

The check §12 records — *for each field of a state a step may write, which field
of the step bounds it?* — was run family-wide by a reviewer. `EscrowLedger`'s
`created`, `resolution` and `cancelRequested` are bounded (§10.91, §10.87,
§10.97); `ChannelSession.status` and `.delivered` are bounded at all three
constructors that scope `.session`; `ProcessInstance`'s seven fields are bounded
everywhere except `outstanding` at an ending, which is deliberate and recorded
(§10.33). Two are not.

**Shared region content.** `StepsLocally.writesPermitted` bounds *which* regions
may move — those with `mayWrite` — and nothing bounds the *value* written.
`protocolStep` relates `localState`, `outstanding`, `ref`, `parentage` and
`request`; `shared` appears in `Grass/Process/` only in scope and capability
positions. A `processStep` may set any writable region to any value whatever,
unrelated to the event it is handling.

Nothing breaks today, because no clause of `WellFormed` is about shared regions —
which is exactly the shape §10.87, §10.91 and §10.97 each had at a ledger field
before something downstream needed them. Closing it needs `ProcessSpec.Step` to
mention shared state, which it does not, so this is a ruling rather than a patch.

**`EscrowLedger.rank`.** No field of any structure mentions it and `LedgerExtends`
says nothing about it, so a step may renumber freely. The reviewer tried and could
not break it: `rankOrdersCreated` at the after-ledger forces rank to increase
along `created`, `created` only grows, and `coalesceCarrierLater` is re-checked
against every standing resolution at every ledger, so a cross-step rank cycle is
refused. Recorded because it is pinned *indirectly*, and the next change to any of
those three laws could unpin it without anything noticing.

### 10.104 Coalescing is one transition in §3 and several here

`docs/PROCESS.md` §3: "Coalescing consumes every source token and creates one
fresh occurrence" — one transition. §10.95 reverted `ResolvesEscrow` to the narrow
resolution bound on the reasoning that a carrier collects its sources over several
`coalesce` steps, and a reviewer confirmed that decomposition is constructible:
two `ResolvesEscrow` steps into one carrier, the first creating it, the second
creating nothing.

It is not *atomic*, though, and the intermediate worlds are visible: the carrier
is outstanding alongside sources that have not yet merged into it. Whether §3
requires atomicity here is a ruling. If it does, `coalesce` needs its own
structure taking a list of sources, and §10.95's revert is right for the wrong
reason.

### 10.105 Three more fields that had become theorems, and twenty false claims

A claims-auditing reviewer swept every docstring on the branch. Thirty-one
findings, and the shape of them is worth as much as the list.

**Three fields were derivable**, §10.92's defect three more times.
`ClosesSession.nowResolved` and `KillsSession.nowResolved` follow from
`closesEverything`/`killsEverything` (§10.90) plus the on-session guard
(§10.96); `RequestsCancel.stillOutstanding` follows from `ledgerExtends` and
`resolvesNothing`, both of which post-date it. Each is one line, each is now a
theorem, and each was found by the same check: **after adding a field, try
deleting the ones beside it.** A field that has quietly become implied still
elaborates, its fixture still discharges it, and its docstring goes on explaining
why it is needed.

**Five docstrings named declarations that do not exist** — `commits_anywhere`,
`an_unprojected_observation_is_unconstructible`,
`overlapping_names_have_two_routings`, `the_send_then_the_receive`,
`retained_contract_forbids_arbitrary_death` — and one of those,
`an_unprojected_observation_is_unconstructible`, also described a claim its file
does not make.

**Two hung a live argument on a deleted field.** `Assertion.lean` and
`Transition.lean` both reasoned "…so `NetworkProgressMeasure.frontierIsExternal`
forbids any network from being at a frontier", and §10.68 replaced that field
with a definition. The arguments were sound when written; a reader following them
now hits a name that is not there.

**Eight counts were wrong**, all of them stale rather than careless: seven
network fragments that are eight (`pending`, from the §10.27 trace split), three
indexed fragments that are four, two divergences from §3's record that are three,
eleven channel constructors that are twelve, nine `ProcessCorrect` fields that
are ten, eight fixture-world fields that are nine, "the other six" sharing
`ResolvesEscrow` that is the other five, and a `ChannelContract` field count this
document is cited as recording and does not.

**The rest were this document's own** — §12's tables and several §10 entries
describing a corpus two rounds out of date. Those are corrected in place, and §12
now says what its tables are for.

**Why this is a finding and not housekeeping.** Every one of these is a claim a
reader would act on. The ones about counts and names cost a reader time; the
three derivable fields cost a reader *correctness*, because a docstring saying
"without this field, <attack>" is evidence about the design, and three of them
were false. This corpus's whole method is that prose earns its place by being
checkable — and nothing checks it. Rerunning this sweep is the cheapest review
round available.

### 10.106 `ExactInitialNetwork` was missing the field a spawn has

`ProcessPlan.Spawns.slotAgrees` exists because local adversarial review built a
spawn installing an incarnation naming slot 3 into slot 7. `ExactInitialNetwork`
had `rootKind` and no counterpart, so a *start* could do the same thing at the
first network of a run.

The tell was in `initial_is_wellformed`'s signature: it took `SlotsAgree` as a
**hypothesis**. A reviewer read that and said what it means — a clause passed in
rather than discharged is what a missing field looks like from the caller's side.
The module's own prose had been claiming for two rounds that "the remaining two
come from the root's own record", and one of the two was being handed in.

**Closed** by `rootSlotAgrees`. `initial_is_wellformed` now takes no hypothesis,
and exactness buys five of `WellFormed`'s six clauses rather than four.

**The check**: a theorem about a structure that takes a hypothesis the structure
*could* carry is either a deliberate parameterisation or a missing field, and the
docstring should say which. Nothing in the build distinguishes them.

### 10.89 A spawn can satisfy every field it has and not be a step

`Tests/Process/LifecycleStepFixtures.lean`'s `the_spawn` is a complete `Spawns` —
ten Prop fields, all discharged — reaching `Ending.holding newborn`, which is
`quiet` with the slot filled and **`quiet`'s empty nominal history**. So the
generation the spawn hands out is in no history, that world fails
`NominalsAllocated`, and no `NetworkStep` wraps the transition at all:
`historyExact` cannot hold.

`Spawns.allocatesTheGeneration` says the new incarnation's generation is in the
*allocation the step declares*, and that is all it can say — a
`LogicalProcessNetwork` and a `Spawns` between two of them know nothing about
`NetworkStep.historyExact`. This is §10.87's shape again at a different seam: a
law stated where it can be stated, relied on for something it does not say.

Not a defect in the transition family; it is exactly why
`nominalsAllocated_preserved` is a law of `NetworkStep`. It *is* a defect in the
fixture, which claimed a spawn and built a transition no execution can contain.
`a_spawn_that_records_nothing_is_not_well_formed` records it and
`the_allocating_spawn` is the corrected one — whose scope has to declare
`.nominals`, which the original's proof discharged with `rfl` because nothing had
moved.

**The general check this suggests**, and it is cheap: for every `NetworkTransition`
witness in the corpus, is there a `NetworkStep` wrapping it? A transition nothing
can wrap is a transition no execution contains, and every theorem stated over
steps passes it by. Owed.
