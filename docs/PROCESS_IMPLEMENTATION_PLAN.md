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
two emissions *non-independent*, because `.observations` is a single global
fragment and `NetworkTransition.Independent` is scope disjointness. The
obligation has been moved rather than discharged: a plan that wants two
subsystems to emit concurrently and to reason about the interleaving has no
statement available, and would need either a per-subsystem trace or an explicit
commutation argument about segments. Neither exists.

The same shape reaches `Grass/Process/Weave/Lens.lean`: two `Disjoint` lenses
cannot both own the trace, so at most one refinement in a weave may change what
the program observes. That is sound and it excludes §8's own graphics-and-disk
example if both refinements emit.

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

### 10.34 `reroute` cannot write the session it reroutes to

`reroute` is a `ResolvesEscrow`, whose scope is `fragment = .escrow edge
session` — the *source* session. `ChannelResolution.rerouted` names a
destination and says the payload "is re-created as a fresh occurrence this
ledger does not hold", and the destination's ledger is a different fragment the
step may not touch.

So `WellFormed.ReroutesLand` degenerates: it can only be satisfied at a
destination that was already non-empty before the step, and the reroute itself
can never make one so. `reroute` is a drop with a forwarding address.

The fix is the `Delivers` shape again — a dedicated structure whose scope names
both sessions' escrows, with a field putting the arrival in the destination.
Not done here because it wants the destination occurrence's identity, which is
§10.36's question too.

### 10.35 No channel step may touch either endpoint's instance slot

`Delivers`, `SendsEscrow` and every `ResolvesEscrow` scope the escrow (and now,
for delivery and the two closings, the session cursor) and nothing else. So a
delivery moves the ledger and the cursor and reaches no process:

```lean
theorem delivery_never_reaches_the_receiver
    (delivered : plan.Delivers a b edge session occurrence) (kind slot) :
    a.instances kind slot = b.instances kind slot
```

`Grass/Process/Network/Channel.lean`'s `receiverPreLocal` was deliberately
widened to admit the receiver's own `instanceState`, and
`ReceiverEventEmbedding.arrives` maps a message to the receiver's `Event` — but
nothing applies that event to anything. `Delivers` also has no `contractual`
field where `SendsEscrow` has one, so `ChannelContract.receive`,
`receivePrecondition` and `ReceiverPost` are unreachable from the transition
family.

Whether a delivery should move the receiver in the same step, or whether the
receiver's `processStep` consumes the arrival separately, is a ruling. The
second reading is defensible and is probably intended — but then §3's receiver
contract needs a law relating the two steps, and there is none.

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
| `Function/Serial.lean` | §3's serial contract, with the collapse carrying its own frontier argument |
| `Network/Progress.lean` | §7's progress theorem, as the cycle law a rank forbids |
| `Network/Initial.lean` | §3's `ExactInitialNetwork`, and `initial_is_wellformed` |

Each has a fixture file, and each fixture found at least one defect in the
module it was written against. That is the pattern worth keeping: nothing here
was found by reading.

### Still owed for M4 exit

* **`flatten_sequential_roundtrip`** — blocked. `ProcessRealization.flatten`
  produces a `ProcessSpec` whose `Step` consumes an event per transition, and a
  network's internal steps correspond to no external event. Either the
  flattened spec's `ExternalEvent` gains a scheduling event or flattening is a
  different relation; §7 does not say which. Needs a ruling before it can be
  built.
* **`serialize_refines_flatten`** — downstream of the above.
* **The proof-economics acceptance rule** — not started.
* **`DirectProgramRealizes` transport** — §4 asks the adapter for it; the
  adapter delivers the syntax half only, and says so.

### Open findings by weight

§10.33's second half (an ending does not dispose of the ended instance's
outstanding bag), §10.35 (no channel step touches either endpoint's slot), and
§10.27 (one global observation trace makes §7's congruence trivial) are the
three that a ruling would most change. The rest are recorded and none blocks
building.

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
