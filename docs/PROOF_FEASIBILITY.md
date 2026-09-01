# Proof feasibility and constructive sketches

## 1. Purpose

This document answers the charge that a proposed Grass library is “proof
fantasy.” A name, tactic invocation, or analogy is not an answer. For each
disputed mechanism this document fixes:

1. the exact theorem family being claimed;
2. the proof-relevant input which a caller must supply;
3. a constructive proof route;
4. the boundary of reusable automation;
5. a finite acceptance fixture which can falsify the proposed interface; and
6. the narrower design Grass will adopt if the construction fails.

Nothing here claims that the library has been implemented. “Believable” means
that the theorem follows by a displayed induction, simulation, algebraic law, or
kernel-checked composition from explicit premises. It does not mean that Lean
will discover those premises or that engineering the reusable proof is cheap.

The feasibility labels are:

- **standard construction**: the proof shape is routine in a proof assistant;
- **research engineering**: the proof shape is known, but scale and interface
  quality must be demonstrated by the spikes; and
- **conditional commitment**: Grass retains the interface only if the stated
  fixture succeeds within the proof/build budget.

## 2. Standard sequential presentation

### Claim

`SequentialAdapter` does not accept an arbitrary relation and synthesize an
actor decomposition or invariant. It accepts either an ordinary
`SequentialMachine`, whose typed decisions expose zero or one exact effect
frontier, or the following lower-level relational escape hatch for transitions
which issue or resolve several effects together:

```lean
structure DirectRelationalProgram (boundary : DriverBoundary) where
  State Request TerminalResult : Type
  Initial : Request -> State ->
    AbstractDemandBag (EffectDemand boundary) ->
    List boundary.Observation -> Prop
  Step : State -> DirectEvent boundary -> State ->
    AbstractDemandBag (EffectDemand boundary) ->
    List boundary.Observation -> Prop
  Pending : State -> AbstractDemandBag (EffectDemand boundary)
  initialEquation : EveryInitialOutputEqualsPending Initial Pending
  transitionEquation : EveryStepHasExactConsumedIssuedPendingEquation Step Pending
  sites : FiniteDependentEffectSiteInventory Initial Step
  binding : forall occurrence,
    occurrence \u2208 DynamicOccurrences Initial Step ->
    ExactSiteProtocolAndChildBinding occurrence
  terminal : Request -> State -> TerminalResult -> Prop
  terminalDisposition : EveryTerminalStateClassifiesEveryPendingOccurrence

structure DirectProgramRealizes {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources)
    (program : DirectRelationalProgram spec.driverBoundary) where
  invariant : program.State -> Prop
  initial : DirectInitialSimulation spec program invariant
  step : DirectStepSimulation spec program invariant
  terminal : DirectTerminalSimulation spec program invariant
  complete : FiniteInfiniteFaultAndPendingCoverage spec program
  progress : DirectProgressRefinement spec program
```

and produces one conventional, replaceable process presentation. The input
already contains the program decomposition and correctness proof; neither the
adapter's topology nor its chosen child placement becomes precious.

### Construction

The adapter uses one root process whose local state is `program.State`. Each
dynamic occurrence named by an `Initial` or `Step` witness becomes either:

- an internal serial transition;
- one standard child-protocol demand at a declared effect site; or
- one root external event.

The generated network state is the direct state plus a finite map from live
dynamic effect occurrences to standard child states and channel escrows. The
simulation relation says:

```text
root.local = direct.state
erase(live child occurrences) = direct.pending effects
root observations = direct observations
every physical/logical loan and obligation is in exactly one declared custody
```

### Proof sketch

Initial states follow from `DirectProgramRealizes.initial`; the adapter creates
exactly the initial children returned by `Initial`. `initialEquation` proves
that erasing those children is `Pending initialState`, including multiplicity
when two demands have equal payloads.

For a direct internal step, the root makes the corresponding process step and
the occurrence map is unchanged. For an effect issue, the adapter allocates one
fresh occurrence, inserts one child and escrow, and the demand-bag equation
follows by multiset insertion. For a result, interruption, failure, or
cancellation resolution, it consumes the exact occurrence and uses that
standard child protocol's result projection. A transition may consume a result
and issue further demands in the same step; `transitionEquation` gives the
single exact bag equation relating consumed, issued, and before/after
`Pending`. Terminal correspondence follows from the supplied terminal
simulation plus `terminalDisposition` for the live map. Induction gives every finite prefix. The supplied complete-execution
coverage and a standard coinductive lifting give infinite, divergent, pending,
fault, and terminal shapes.

The reverse direction is not guessed: canonical network transitions are
generated only by the cases above, so inversion on the transition constructor
recovers the corresponding direct step. This is why a canonical adapter can
prove complete execution correspondence while an arbitrary user-authored
network normally proves only the refinement direction its specification needs.

### Automation boundary

The library generates bookkeeping for declared effect sites. It does not find a
loop invariant, decide which arbitrary subexpression is an effect, invent a
child protocol, prove `DirectProgramRealizes`, or infer a simulation relation
from an arbitrary `Prop`.

For `SequentialMachine`, the library also generates the declared effect sites:
they are a structural fold over the finite typed decision syntax. Its proof is
one induction over `SequentialDecision`. `.internal` preserves the live
occurrence map, `.effect demand resume` allocates exactly one fresh occurrence
whose result type fixes the continuation, and `.terminal` requires the map to
be empty or to have the explicitly selected terminal disposition. This covers
novel state machines, headers, pass structures, and failure policies built from
known effects. Manual multiset equations begin only when the author selects the
lower-level multi-effect relational escape hatch.

That boundary is not the application interface.  A standard specification
constructor packages the direct program and proof in a registry entry.  Hello,
sort, and gzip therefore select their complete realization with
`ProcessRealization.standard (lookupExact spec)`.  The larger structure above
is inspected when implementing or auditing the generic constructor, not filled
once per application.

For the gzip fixture, standard byte-input, byte-output, allocation, and
terminal combinators derive the effect sites, exact occurrences, pending
equations, bindings, and dispositions.  The meaningful reusable proof inputs
are exactly the streaming transducer relation, exhaustive failure behavior,
bounded resource theorem, and conditional-progress theorem.  The compressor's
algorithmic correctness and assembly refinement remain separate lower-layer
proofs.  Requiring gzip application code to expose any generated process
bookkeeping fails this section even if the theorem is provable.

### Acceptance fixture

Hello, sort, and fixed-gzip must use the same closed standard-realizer registry,
and each application fixture must select its realization with one expression.
Adding a new result constructor to a used effect must leave one local unmatched
case. Removing an effect site must remove its generated child. Reordering two
independent declared sites must not require an application proof edit. A custom
relation without `DirectProgramRealizes` must fail immediately rather than start
proof search. Dedicated fixtures cover a zero-effect transition; two equal
demand values issued as distinct occurrences; an initially pending demand; an
issue followed by cancellation; and a result consumption plus new issue in one
transition. Mutating any issued/consumed multiplicity or dependent child binding
must break the local bag equation rather than a later global theorem.

### Status and fallback

**Standard construction**, with proof-economy risk. If the generated goals are
not stable, the fallback is an explicit process realization for that program,
not a second semantics or a claim of automatic invariant synthesis.

## 3. Plain serial functions inside processes

### Claim

A terminating local function can be called directly inside a process step. The
process algebra does not turn every ABI call into an actor.

### Proof sketch

The contract has an indexed `ExitState`. Its disposition is either
`returned output` or `raised fault`; its `Post`, resource transform, and
obligation transform are relations indexed by that exact exit. The fault case
also records the exact partial mutation and custody left by the fault.
`exitsComplete` proves that every maximal internal execution reaches exactly
one declared exit. There is no catch-all exceptional return.

Let the function prove `{P} f {Post exit}` for every exit, with footprint `F`
and the exit-indexed custody equations. Let a process rule use an abstract
transition `T` whose premises include `P` and whose normal and fault conclusions
follow from the corresponding `Post`. Sequential Hoare composition gives one
process-rule proof per exit. The ABI theorem connects the call instruction,
arguments, clobbers, stack frame, every machine exit edge, and the returned exit
tag to the function contract.

The termination witness exposes a well-founded `Rank` and strict decrease for
every internal CFG edge and every recursive edge inside an SCC. An acyclic call
may use the callee's independent rank; a recursive SCC uses a lexicographic pair
of SCC/caller rank and local rank, decreasing the first on recursive descent or
the second on an intra-procedure edge. Mutual recursion therefore cannot hide
behind an opaque termination name. If the process promises quantitative
responsiveness, `workBound input before` additionally bounds all internal and
recursive steps.

The finite-stuttering simulation relates each represented pre-state to function
entry, maps every non-exit machine step to silent stuttering, maps every machine
exit to exactly one contract exit, reflects every contract-permitted exit by a
machine execution, and preserves exit-indexed resources, obligations, and
partial mutation. Its trace-collapse lemma converts that finite machine segment
to the one logical `T` transition without erasing an outcome or observable
write.

Atomicity is a separate premise. Exclusive ownership of `F` makes intermediate
writes private and frameable. If `F` overlaps shared state, the implementation
instead names a linearization point and proves that every intermediate shared
effect is hidden or linearizes there, together with environment
noninterference. A footprint declaration alone proves neither fact.

Allocation from already-owned deterministic arena state can be part of that
local transform. A system allocator call whose success, address, or output is
external entropy is a child demand and therefore does not satisfy the local
function's `noFrontier` premise.

No channel theorem is involved. If the call can wait on external entropy,
remain pending, or be independently cancelled, the premise “finite local
execution” is false and the operation must instead cross a process frontier.

### Automation boundary

The library generates frame applications, ABI entry/exit plumbing,
lexicographic rank composition for a declared call graph, and finite-stuttering
closure once local edge lemmas are supplied. It does not invent a rank,
classify an unmentioned fault, infer ownership, select a linearization point,
prove noninterference, or derive a work bound from termination.

### Acceptance fixture

The fixture contains a pure helper, arena allocation from exclusively owned
storage, mutual recursion with an explicit SCC rank, a declared fault after
partial mutation, and a shared-state helper with a named linearization point.
Mutations must reject hidden provider entropy, an unranked recursive edge, an
intermediate shared write outside the linearization proof, omitted partial
mutation on fault, unrecorded resource or obligation transfer on any exit, and
an execution exceeding its claimed work bound.

### Status and fallback

**Standard construction** when the exit, rank, and visibility premises are
present. The honest fallback is multiple explicit process steps when
intermediate states are observable, or a child frontier when the computation
can await entropy, remain pending, or be independently cancelled. A missing
atomicity or rank proof never falls back to an opaque one-step call.
Systems such as [Compositional CompCert](https://www.cs.princeton.edu/~appel/papers/compcomp.pdf)
demonstrate machine-checked module-local simulations and linking; Grass's exact
contracts differ, but the compositional proof shape is established precedent.

## 4. Plan-specific process weaving and `FixedPool.weaveCorrect`

### Claim

There is no universal theorem which proves an arbitrary worker pool correct.
The reusable theorem composes local process/channel proofs **after** the plan
supplies its cross-protocol invariant family.

For Spike 4 the plan-specific witness must contain at least:

```lean
structure ServerCompositionWitness where
  socketGeneration : SocketIdentityAndGenerationInvariant
  listenerAuthority : ExactlyOneListenerAuthority
  admissionPermits : ActiveConnectionsCorrespondToFourPermits
  workerSlots : DisjointWorkerSlotOwnership
  receiveCancelRace : ReceiveLoanHasOneRaceWinner
  sendCancelRace : SendSuffixHasOneRaceWinner
  deadlineCorrelation : DeadlineTargetsExactConnectionGeneration
  workerReuse : ReuseRequiresPriorJoinAndFreshGeneration
  shutdown : ShutdownPublicationAndCustodyInvariant
  routeSharing : ImmutableBodySharedReadOnly
  obligations : ExactNetworkObligationPartition
  resources : ExactServerResourcePartition
```

This record is a thin facade, not a monolithic invariant. Each field is an
independently exported `WeaveInvariantMixin` with its own scope, assertion,
initial proof, affected-transition proof, frame rule, resource fragment, and
obligation fragment. `ServerCompositionWitness` proves compatibility and
completeness of that family. Editing the deadline policy reopens the deadline
and generation mixins and the transitions which touch them; it does not reopen
route immutability, slot separation, or socket custody.

### Proof sketch

Define `ServerGlobalInvariant network machine` as the separating conjunction of
the witness clauses plus each live process's local invariant and every channel's
escrow assertion. Prove it initially from listener creation, four distinct slot
ranges, four permits, an empty connection map, and the initial obligation
ledger.

Preservation is exhaustive over the actual `NetworkTransition` constructors.
For Spike 4 the constructor-indexed case table is:

| Constructor | Preservation case or exact unreachability premise |
|---|---|
| `processStep` | apply the selected process's local invariant; frame every mixin whose scope is disjoint; listener accept-state changes consume the named permit only through its local rule |
| `spawn` | fresh connection generation, one consumed admission permit, one disjoint worker slot, socket/deadline custody initialized exactly |
| `send` | move the exact retained output suffix and send obligation into the occurrence escrow |
| `receive` | move the exact writable buffer loan and receive obligation into the occurrence escrow |
| `commit` | append only the boundary observation authorized by the committing process and leave all resource mixins framed |
| `requestCancel` | mark the exact generation/occurrence cancelling without consuming its affine resolve token |
| `acknowledgeCancel` | consume that token and return the escrowed loan/custody exactly once |
| `timeout` | generation equality selects the live request; mismatch is proved unreachable from deadline correlation, not treated as a stutter |
| `interrupt` | route the declared shutdown interrupt to the supervisor transition; every other interrupt constructor instance is unreachable by the closed server boundary |
| `fault` | transfer the faulting instance's slot, socket, occurrences, resources, and obligations to its unique supervisor custodian |
| `environmentViolation` | enter the declared non-continuable terminal policy with the complete custody disposition; no normal continuation case exists |
| `childLifecycle` | result/failure/cancel/death consumes the exact child occurrence and applies its `ChildDemandBinding` lifecycle classification |
| `processTermination` | require all owned occurrences classified, then transfer or discharge the terminal process's remaining fragments according to policy |
| `channelClose` | close only after queued/in-flight items have their declared drain/drop/reroute disposition |
| `senderDeath` | transfer sender-owned endpoint and outstanding sends to supervision; peer observations follow the channel death policy |
| `receiverDeath` | transfer receiver endpoint, queued loans, and outstanding receives to supervision under the same exact policy |
| `channelDeath` | combine the two endpoint-death fragments once and classify every queued/in-flight item |
| `drop` | consume the item's affine disposition authority and apply the declared resource/obligation return equation |
| `reroute` | consume the old route occurrence and create the exact fresh destination occurrence with custody conserved |
| `coalesce` | unreachable for the Spike 4 byte/socket channels because their registry entries declare `NoCoalescing` |
| `join` | recover a dead worker's supervised custody and establish the joined state required before slot reuse |
| `detach` | unreachable because the fixed-pool plan contains no detach-capable lifecycle edge |
| `restart` | use the supervision restart rank, require prior join, allocate a fresh worker generation, and transfer the recovered slot fragment to it |

Every row is a field of `ServerTransitionCases`, indexed by the exact before and
after networks. A row is inhabited either by preservation for that constructor
or by a proof that no transition of that constructor is reachable in this
closed plan. There is no wildcard case. Within a row, unrelated invariant
mixins discharge by their exported frame rules; only mixins whose scopes are
touched are reopened.

Unmentioned processes and regions frame by disjoint ownership. The resulting
induction proves safety and the global invariant for finite prefixes.
Coinduction over maximal executions plus the named fairness, clock, and provider
responsiveness assumptions proves the conditional settlement clauses.

The generic `weaveCorrect` theorem only performs the induction skeleton,
channel framing, occurrence bookkeeping, and pointwise mixin composition. The
twelve facade fields and the exhaustive constructor table above are Spike 4
inputs. Calling those inputs “automatic” is prohibited.

Concurrent separation logics use the same general strategy: local specifications
compose through explicit resource ownership and invariants; logically atomic
specifications isolate linearization points rather than synthesize them. See the
[Iris project](https://iris-project.org/) and its
[lecture notes on authoritative resource algebras](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf).

### Acceptance fixture

The proof must reject: socket-value reuse without generation change, returning a
permit before close, two winners of cancel/completion, deadline delivery to a
recycled slot, worker reuse before join, a mutable route-body share, and shutdown
with an unowned pending occurrence. Each mutation must produce a goal naming the
broken witness clause.

### Status and fallback

**Research engineering.** The logic is constructive; proof economy is unproven.
If the named witness remains mostly per-transition boilerplate after two distinct
server plans, Grass narrows the generic combinator and banks a server-specific
library. It does not claim zero-annotation concurrency.

## 5. Asynchronous byte flow and partial completion

### Claim

Partial blocking, readiness-based, and completion-based I/O can refine one
ordered-byte protocol without pretending call boundaries are semantic message
boundaries.

### Proof sketch

For ingress, maintain the exact conservation equation:

```text
providerProduced = adapterQueue ++ channelEscrow ++ delivered
delivered = parserConsumed ++ parserRemainder
```

For egress, maintain:

```text
offered = committed ++ inFlightPrefix ++ queuedSuffix
```

An issue transition creates one occurrence and moves a loan and capacity credit
to `inFlight`. Readiness changes no bytes or custody. Every resolution carries
an exact transferred prefix and residual-loan disposition. Completion appends
the prefix and returns or reissues the suffix; cancellation, close, failure, and
death use the same equation and affine resolve token. Terminal phases have no
transition constructor.

Induction on legal transitions proves conservation and exactly-once resolution.
A functional rechunking theorem then erases call/capacity timing and compares
only completed byte streams. Stronger cancellation/resource theorems retain and
map all cut points; they do not claim that arbitrary provider outcomes are
equal.

### Acceptance fixture

Model a completion which transfers three bytes and reports failure, a cancelled
write which wins after a two-byte commit, an oversized read completion split by
channel capacity, zero-byte success, peer close, and stale completion after
session reuse. Every byte and loan must have one location after every case.

### Status and fallback

**Standard construction**, with a deliberately small protocol. Failure of the
functional rechunk theorem narrows the observation projection or adds the
missing outcome coupling; it never discards partial effects.

## 6. Resource metrics, capacity credit, and subtree bounds

### Claim

Grass does not infer finite resource bounds for arbitrary graphs. Given local
bounds, a reachable-state resource invariant, exact ownership partitions, and
boundary-flux limits, it composes and extracts a bound.

### Proof sketch

Owned holdings form a partial commutative resource algebra. A metric valuation
maps disjoint union to axis-specific combination, maps empty to zero, is
monotone, and respects explicit shared attribution and affine transfer. These
are fields of `ResourceMetric`, not tactic assumptions.

For each network transition, prove an exact holdings equation. Allocation adds
its charged physical layout; free removes it only after custody ends; a channel
send moves slot, payload, record, and occurrence credit from free to escrow;
receive releases record cost and moves retained payload cost to the receiver.
The total capacity ledger is invariant. Induction yields the global budget.

For a scope, partition every holding into inside, outside, inbound escrow,
outbound escrow, or one attributed shared class. The general theorem uses no
subtraction:

```text
scopeUse ⊕ creditedOutbound
  ≤ localInitial
    ⊕ populationBound
    ⊕ channelLayoutBound
    ⊕ maximumAdmittedInbound
```

The boundary-flux transition law preserves that partition across spawn,
transfer, termination, and restart. Projecting the global invariant through the
partition and applying valuation monotonicity proves the subtree bound. Memory,
stack, file descriptors, handles, threads, sockets, GPU objects, and work are
separate axes; physical representation certificates connect them to concrete
layout and provider resources.

Composition alone cannot show that a convenient metric implements the resource
policy selected by the precious specification. For every required axis,
`ResourceAxisRealization spec plan axis` additionally supplies:

1. the exact axis semantics from `spec.resourceSemantics`, never a newly
   inferred capability dictionary;
2. the concrete metric axis and representation relation;
3. initial-state correspondence;
4. a constructor-indexed proof that allocation, transfer, release and
   exhaustion implement the selected operations and policy; and
5. terminal-state correspondence to the selected lifecycle disposition.

`ProcessPlanRealizes.resources` contains this family. Consequently a
constant-zero dummy metric cannot establish a four-connection specification:
its representation or exhaustion transition case fails before the algebraic
bound theorem is available. Fixture projections such as `rootBound` and
`subgraphBound` are methods of that exact family, not unrelated lemmas found by
instance search.

An axis may expose a smaller residual bound only through an additional
`ResiduatedResourceAxis` certificate supplying a residual operation, its
existence side condition, cancellation/order laws, and proof that the credited
outbound quantity is available. Natural-number sums can use truncated
subtraction only after proving the subtrahend inequality. Max, shared-once, and
noncancellative product axes retain the relational inequality above. No generic
resource theorem silently imports group structure.

Authoritative and affine resource reasoning is established proof technology;
Grass's risk is engineering an economical interface, not the existence of the
algebraic induction. The [Iris lecture notes](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf)
give a mechanized account of authoritative resource algebras.

### Acceptance fixture

Instantiate the theorem for natural-number sum, maximum, shared-once
attribution, affine transfer, and a product containing a noncancellative axis.
The generic theorem must elaborate for all five without residuals. A residual
corollary must succeed for the cancellative natural axis and reject a missing
availability proof and the maximum axis.

Spike 4 must derive, not assume, a per-connection resident-byte bound and a
whole-server Windows-handle bound. Tests must reject a zero-cost control-message
loop, double-counted shared body, uncharged queue header/alignment, payload cost
which disappears on dequeue, and resource return before physical release.

### Status and fallback

**Research engineering.** If a proposed generic composition rule cannot expose
its exact holdings equation, it is removed. No opaque `ResourceBound` oracle is
accepted.

## 7. Flattening, serialization, and trace commutation

### Claim

Flattening always hides a proved network behind one protocol. Serial execution
of a genuinely concurrent graph is permitted only with an explicit complete
relational scheduler proof.

### Proof sketch

`flatten` uses the entire logical network as one process's private state. One
flattened step is exactly one network transition; therefore finite execution
correspondence is constructor-by-constructor identity modulo state packaging.
The coinductive execution theorem preserves infinite, pending, fault,
cancellation, terminal, observation, and obligation behavior.

Flattening inversion has one generated clause for each constructor:

| Network constructor | Flattened constructor witness |
|---|---|
| `processStep` | the identical exact local-process transition |
| `spawn` | the identical bound-child spawn and fresh nominals |
| `send` / `receive` | the identical endpoint, occurrence, escrow, and payload transition |
| `commit` | the identical boundary observation segment |
| `requestCancel` / `acknowledgeCancel` / `timeout` / `interrupt` | the identical correlated lifecycle/race transition |
| `fault` / `environmentViolation` | the identical fault classification and custody equation |
| `childLifecycle` / `processTermination` | the identical result and terminal disposition |
| `channelClose` / `senderDeath` / `receiverDeath` / `channelDeath` | the identical endpoint and queued/in-flight disposition |
| `drop` / `reroute` / `coalesce` | the identical item authority and replacement occurrence equation |
| `join` / `detach` / `restart` | the identical supervision transition, generation, and rank evidence |

The grouped rows are generated pattern matches, not shared semantic cases: the
Lean theorem still has one branch per constructor, so adding a constructor
leaves both directions unproved.

Serialization requires the following local evidence rather than assuming that
“the scheduler chooses”:

```lean
structure LocalSchedulerCoverage (r : ProcessRealization spec)
    (scheduler : RelationalSerialScheduler r.plan) where
  enabled : forall (transition : NetworkTransition r.plan before after),
    IsEnabled transition ->
    Exists fun serialStep =>
      scheduler.Step before serialStep after /\
      serialStep.networkWitness = transition
  sound : forall (step : scheduler.Step before serialStep after),
    IsEnabled step.networkWitness
  constructors : ConstructorIndexedCoverageForAllNetworkTransitions enabled sound

structure ProductiveSchedulerExtension (scheduler) where
  finiteStutterRank : WellFoundedRankForFiniteSchedulerBookkeeping scheduler
  extend : forall prefix,
    SchedulerPrefixIsNonmaximal prefix ->
    Exists fun suffix => Nonempty suffix /\ SchedulerPrefix scheduler (prefix ++ suffix)
  infinite : EveryInfiniteGraphExecutionHasProductiveSerialCoextension scheduler
```

`constructors` contains a separate enabled/sound pair for `processStep`,
`spawn`, `send`, `receive`, `commit`, `requestCancel`, `acknowledgeCancel`,
`timeout`, `interrupt`, `fault`, `environmentViolation`, `childLifecycle`,
`processTermination`, `channelClose`, `senderDeath`, `receiverDeath`,
`channelDeath`, `drop`, `reroute`, `coalesce`, `join`, `detach`, and `restart`.
A closed plan may discharge an entry by proving that constructor unreachable;
there is no default branch.

For graph-to-serial finite executions, induct on the graph trace. The empty
trace maps to the empty scheduler trace. In the successor case, `enabled`
supplies a serial step carrying the exact head network witness, and the
induction hypothesis maps the tail. For serial-to-graph finite executions,
induct on the scheduler trace and project each exact network witness using
`sound`. End-state, observation, occurrence, resource, obligation, and
lifecycle equations follow from witness identity at each step.

For infinite executions, guarded coinduction applies `enabled` to the next graph
transition, emits at least one semantically productive serial transition, and
recurs on the tail. Scheduler-only bookkeeping is finite because
`finiteStutterRank` decreases; it cannot create an infinite silent execution.
The converse coinduction projects the exact witness from each serial step.
`extend` proves that a nonmaximal finite prefix cannot be mistaken for a maximal
serial execution.

The complete-execution theorem then splits explicitly:

- finite terminal: induction ends at the identical terminal disposition;
- finite fault or environment violation: induction ends at the identical fault
  and custody record;
- finite pending/external frontier: no internal transition is invented, and the
  same named frontier remains enabled by the environment;
- infinite productive execution: the guarded constructions above produce an
  infinite counterpart with the same projected observations;
- internal divergence: it is preserved only when it is a declared graph
  execution shape; finite scheduler stuttering cannot manufacture it;
- maximal nonterminal execution: `extend` plus local coverage shows maximality
  iff the corresponding graph prefix has no enabled transition except its
  declared pending frontier.

Independent transitions use a footprint/escrow disjointness theorem to form a
diamond. Overlapping operations require a supplied linearizability witness.
Fairness and conditional progress are proved for a selected scheduler after
behavioral completeness; they are not smuggled into bisimulation.

Classical process-network results show why this shape is plausible for useful
subclasses, but Grass does not assume every graph is deterministic or
serializable. Kahn-style networks model concurrent compositions of sequential
processes and establish schedule-independent stream meanings under their
restrictions; see [Dataflow Process Networks](https://ptolemy.berkeley.edu/publications/papers/95/processNets/).

### Acceptance fixture

Prove serialization of the lexer/parser pipeline and one bounded codec graph.
Reject a graph with an unlinearizable shared write race. For Spike 4, prove only
the commutations actually used for scheduling equivalence; do not assert the
whole concurrent server is serializable unless both execution directions and
progress are supplied. Mutation fixtures include starvation despite an enabled
transition, an infinite bookkeeping-only stutter, an infinite internal graph
execution truncated to a finite serial trace, a pending child treated as
terminal, a dropped fault, and a nonmaximal prefix labelled maximal. Each must
fail in local coverage, productivity, or the named execution-shape branch.

### Status and fallback

Flattening is a **standard construction**. General serializability is an
explicit property, not an automation promise. The fallback for a nonserializable
graph is a concurrent physical realization.

## 8. Fixed-gzip construction-prefix correctness

### Claim

`ValidGzipConstructionPrefix` is not proved directly over arbitrary x86 register
states. It is the image of a small streaming writer model through local
representation refinements.

### Proof sketch

The pure model state contains the gzip header phase, DEFLATE block/token state,
CRC, input length modulo `2^32`, bit accumulator/count, and completed logical
output. Its invariant states that flushing the accumulator and finishing the
currently open syntactic construct yields a prefix of one well-formed member
whose eventual decode is the consumed input.

Prove separate lemmas for header emission, fixed literal, length/distance pair,
end-of-block, bit append, byte flush, CRC update, and trailer. Each lemma changes
one model component and preserves the construction invariant. The LZ77 model
proof establishes that a selected match refers to equal prior bytes; fixed-code
tables establish prefix-code decoding.

Assembly blocks refine those component operations through a representation
relation. The partial-write loop exposes only bytes already moved to the
committed prefix; unflushed accumulator bits remain private state. A provider
failure freezes the construction trace and publishes exactly its committed
prefix. Composition therefore derives `ValidGzipConstructionPrefix` without a
single global register-level induction.

### Acceptance fixture

Check every bit count `0..63`, output flush at every byte boundary, empty input,
maximum fixed literal, every length/distance code boundary, trailer split at
every output byte, partial write plus failure, and CRC/ISIZE wrap. Fuzzing may
challenge the model, but the theorem is universal.

### Status and fallback

**Research engineering.** The public and audit observations always retain every
byte the provider physically committed. If the construction-prefix property
makes ordinary block proofs nonlocal, either carry the exact writer state which
proves that the complete committed byte sequence is extendable to a valid
member, or buffer transactionally until a complete public unit can be committed.
A projection may additionally expose a largest completed syntactic subunit, but
it cannot hide or retract a longer physical stdout effect. Do not assert
validity for an arbitrary byte prefix.

## 9. First-class assembly verification and certified macros

### Claim

Grass can verify literal and macro-generated assembly locally while keeping the
exact expansion connected to emitted bytes. It does not promise invariant
synthesis for arbitrary assembly.

### Proof sketch

An instruction supplies a complete relational transformer over registers,
flags, memory events, faults, and ghost state. Forward symbolic execution folds
these relations across a straight-line block. At calls and jumps, entailment
checks the target entry contract; local block exits establish their typed exit
conditions. Loops cut the CFG at an author-supplied invariant and
measure/frontier law. `SubCFG.plug` composes block theorems by edge entailment
and frames disjoint ownership.

A certified macro is a function from typed operands to syntax plus a theorem
that its **exact returned syntax** has the advertised local contract. The parent
source stores a macro invocation and expansion identity; review may open the
expansion, while proof and build reuse consume the macro contract. Decision 42
requires the expansion to be available and connected, not textually copied into
every parent module.

This proof shape has strong precedent. [Vale](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/08/Vale.pdf)
represents annotated assembly as an AST and verifies high-performance x86/ARM
implementations; [Jasmin](https://acmccs.github.io/papers/p1807-almeidaA.pdf)
combines structured control with assembly-level instructions and machine-checked
compiler/verification infrastructure. Grass still must validate its own exact
models and artifact chain.

### Acceptance fixture

For every spike, replace one proved macro invocation with its literal expansion
and derive the same contract and raw instructions. Replace it with custom
equivalent assembly and require only the local proof. Mutate a clobber, stack
alignment, memory footprint, branch target, or instruction operand and require a
local failure.

### Status and fallback

Straight-line/block composition is a **standard construction**. The claimed
automation level is a **conditional commitment** measured by residual goals and
build cost. Unsupported code always falls back to explicit local lemmas, never
an unsafe promotion.

## 10. Exact source, erasure, encoding, and artifact connection

### Claim

The program proved is the program emitted and loaded.

### Proof sketch

`SourceElaboratesExactlyTo` records the authored syntax tree and transparent
macro expansions. Ghost erasure is a structural recursion which removes only
ghost constructors and proves a coupled step theorem. Instruction encoding
returns bytes plus a proof that decoding at the selected profile reconstructs
the exact raw instruction and relocation request. Linking resolves symbols and
relocations under an abstract image base; the PE writer/parser proves structural
round trips. The loader theorem maps each serialized section and applies
relocations, and decoding loaded executable ranges recovers the linked raw
program. Transitivity connects `VerifiedProgram.sound` to `emitProgram v`.

Each adjacency is dependent on the exact prior value. A theorem about an
extensionally equivalent lookalike cannot fill the field.

### Acceptance fixture

Mutate an opcode byte, displacement, relocation, import, section permission,
unwind record, image base, macro expansion, or source operand. The exact chain
must break at the first affected adjacency. Every writer has a parser round trip;
the x86 decoder may use a weaker canonicalization theorem only where multiple
encodings prevent literal instruction round trip.

### Status and fallback

**Standard construction**, substantial in breadth. There is no weaker fallback
for verified emission; unsupported artifacts remain unsafe.

## 11. Hierarchical proof reuse

### Claim

Grass uses ordinary Lean modules and kernel checking. Content hashes locate
candidate imported certificates; they do not prove applicability or bypass the
kernel.

### Proof sketch

A leaf module exports a theorem indexed by canonical source, boundary, and
semantic environment. A manifest node records imported child module identities
and a composition theorem. On reuse, the build locates a candidate by hash,
imports its kernel-checked declaration, and checks actual normalized theorem
type, canonical source/boundary equality, imported declaration environment,
toolchain options, and axiom-audit policy. The stored theorem then applies by
ordinary equality transport. A collision produces a mismatch and cache miss.

Subtree roots locate candidate replay certificates and identify where discovery
must descend; they are not negative logical evidence by themselves. The build
may still read and hash every source byte to establish the current canonical
source. After discovery, an unchanged sibling is reused only when its imported
certificate is applied to kernel-visible current source/boundary/environment
values through the equalities above. A persistent file watcher or build database
may reduce source discovery work, but that is an operational optimization in the
performance/trust ledger and never a premise of the logical certificate.

The build chooses measured module/coarsening boundaries. It does not require one
`.olean` per basic block or sub-declaration kernel caching. Verified separate
compilation and linking are established proof patterns; for example,
[CompCert's compiler theorem](https://compcert.org/doc/html/compcert.driver.Compiler.html)
includes a separate-compilation case, and
[Compositional CompCert](https://www.cs.princeton.edu/~appel/papers/compcomp.pdf)
uses module-local structured simulations.

Source closure follows the same hierarchy. Each authored raw fragment, static
data fragment, and transparent macro definition/instance has a local
`SourceFragmentClosure` proving exact expansion, references, imports,
boundaries, and machine behavior. Shard and component nodes consume only child
summaries plus exact export/import matching; the root proves coverage and no
unresolved reference by tree induction. Recursive child concatenation produces
the exact writer listing. A whole-expansion boolean proof may be a debugging
check for a small fixture, but it is neither the target-scale closure theorem
nor a substitute for missing fragment bodies.

### Acceptance fixture

Mutation tests must demonstrate required sibling reuse and exact invalidation
cones. Cache substitution, collision simulation, changed imports, changed
options, and changed audit policy must cause rejection. Clean reconstruction
must recover identical exported theorem types and artifacts. Peak memory, bytes
scanned, file count, equality-construction work, module imports, elaboration
work, kernel-check work, composition visits, serialization work, and wall time
are measured separately at several shard sizes before choosing defaults.

The scale fixture has two mandatory sizes: at least 1,000,000 and at least
10,000,000 source instructions, with at least 1,000 distinct block-boundary
shapes and every instruction family selected by the fixture profiles. It also
contains one composed long-running process/resource system; repeating one
identical certified block does not satisfy the gate. For a leaf edit preserving
its exported boundary, the report must show zero sibling certificate
elaborations and kernel checks, at most the changed leaf shard plus the nodes on
its hierarchical composition path recomputed, and no unrelated spec/provider
certificate action. Full source hashing and full artifact regeneration are
allowed but reported as separate byte counts. A boundary change is judged
against its declared semantic dependent cone rather than this leaf bound.

Source-closure mutations replace one macro body, remove one static symbol,
change one child export, and alter one fragment instruction. The first affected
leaf or interface-composition certificate must fail. Unchanged sibling fragment
certificates remain imported; no test may close a source containing a named but
unimplemented macro, setup path, callback, cleanup path, or data object.

### Status and fallback

Kernel-checked module reuse is a **standard construction**. Fine-grained
hierarchical build economics are a **conditional commitment**. The fallback is
coarser ordinary Lean modules and more rechecking, never trusting hashes.

**Current evidence status: not measured and therefore not passed.** The design
spikes contain neither the reproducible 1M/10M+ corpora nor retained execution
reports. They establish interfaces and mutation expectations only. Grass must
not describe target-scale locality, memory use, or build speed as achieved until
the generated corpora, machine-readable plans/reports, clean runs, incremental
runs, and boundary-preserving mutations have been checked in and reproduced.

## 12. Orthogonal staged subsystem refinement

### Claim

One selected subgraph can be replaced by a lower-level portable realization while every
unselected node remains at its current abstraction level. Repeating the theorem
permits, for example, graphics refined to the abstract Vulkan API model beside
abstract storage and simulation, followed later by storage refinement to the
abstract IOCP model. Portable closure checks every schema parametrically and
accumulates exact provider/resource/obligation requirements. After projection
and platform selection, an analogous machine blend independently supplies the
x86/SPIR-V graphics source and x86 IOCP source; the final machine certificate
consumes that exact complete blend.

This is a semantic locality claim, not an unconditional build-time `O(1)`
claim. Reuse of a sibling certificate requires that the selected replacement
preserve the sibling's exported boundary and every shared invariant on which it
depends.

### Caller inputs

For a lens selecting subgraph `S` from `S ⊗ C`, the caller supplies:

- a local forward simulation from replacement `S'` to `S`, including finite,
  infinite, terminal, fault, cancellation, and environment-frontier behavior;
- exact equality of the typed channel boundary, or explicit proved adapters;
- preservation of projected observation origins, linear custody, obligation
  transfer, and gross resource flux at that boundary;
- preservation or named strengthening of the local progress assumptions;
- a finite requirement delta introduced by `S'`; and
- compatibility witnesses for every shared invariant or resource axis opened
  by both `S'` and `C`.
- an initial-state relation, a well-founded rank for finite silent matching,
  productive infinite-extension/divergence reflection, frontier preservation,
  and a concrete-to-abstract fairness projection.

### Construction and proof sketch

Initialization maps each replacement initial state through the supplied local
initial relation and retains the exact context initial state. Spawned dynamic
instances use a certificate quantified over the role schema's `Instance` type;
no runtime identity is enumerated.

Define the mixed-state relation as the product of the local simulation relation
for `S'` and identity on context state `C`. A total dependent classifier assigns
every `NetworkTransition` constructor one of `replacementLocal`, `contextLocal`,
`crossBoundary`, `shared`, or `unreachable`, retaining the evidence for that
classification. Its defining equations cover:

| Constructor family | Required local proof |
| --- | --- |
| `processStep` | replacement/context owner, or shared-state coupling |
| `spawn`, `childLifecycle`, `join`, `detach`, `restart` | schema-parametric child relation, population/resource equation, custody and lifecycle |
| `send`, `receive`, `commit` | exact boundary occurrence, ordering, multiplicity, observation origin and resource flux |
| `requestCancel`, `acknowledgeCancel`, `timeout` | cancellation/race authority and obligation disposition |
| `interrupt`, `fault`, `environmentViolation` | projected environment/fault relation and admissible-frontier classification |
| `processTermination`, `channelClose`, `senderDeath`, `receiverDeath`, `channelDeath` | terminal/death rule, retained buffered occurrences, custody and obligations |
| `drop`, `reroute`, `coalesce` | exact disposition law and occurrence conservation |

The classifier itself is exhaustive by constructor recursion; a claimed
`unreachable` branch contains a contradiction from the lens boundary and
transition precondition. There is no default case. The simulation proof then
dispatches on the classifier:

1. A replacement-local transition is matched through the supplied local
   simulation. The context is unchanged; its frameable invariant certificates
   are reused definitionally.
2. A context-local transition is matched by identity. The replacement relation
   is framed because the transition declares that it does not open the
   replacement-owned invariant families.
3. A boundary send, receive, response, cancellation, or custody transfer uses
   boundary exactness to identify the same logical occurrence on both sides.
   The channel law supplies order and multiplicity; the custody and resource
   laws supply the corresponding ledger equation.
4. A genuinely shared transition uses the named coupling witness. Absence of
   that witness is a construction error, not an automation search problem.
5. Terminal, fault, cancellation, population, and death cases use the local lifecycle simulation
   and the context's unchanged lifecycle rule. Newly adopted or escaped
   obligations are visible in the requirement delta.

Induction over finite executions gives prefix safety and finite projected-trace
refinement. Each concrete step either produces an abstract step or strictly
decreases the supplied silent rank; therefore one abstract match cannot hide an
infinite concrete stutter. The productive-extension field constructs the next
abstract step for every infinite concrete suffix, while divergence reflection
permits only divergence already admitted by the abstract protocol. The fairness
projection maps concrete scheduling/environment premises to the exact abstract
premises, and frontier preservation distinguishes a legitimate pending
environment wait from internal nonprogress. These fields construct infinite-
trace refinement coinductively rather than deriving it from finite-prefix
matching alone. Observation-origin preservation composes transitively, so a
low-level syscall or GPU observation remains attributable to the abstract
process transition which licensed it.

Two refinements at disjoint lenses commute up to graph isomorphism when their
requirement deltas and all shared axes are disjoint. When they overlap, the
claim is deliberately weaker: either order may be used only after proving an
explicit compatibility/diamond witness. No theorem infers provider coherence
from typeclass priority.

`blend` is repeated application of `refineSubgraph` plus an exact union of the
introduced requirement deltas. `close` traverses the finite static role-schema
set while each realized schema certificate quantifies over every dynamic
instance and recursively proves every reachable internal frontier realized.
Each abstract schema makes `EverySchemaRealizedParametrically` uninhabited.
Portable closure composes resource ledgers and obligations and yields an
indexed `ClosedBlend` whose `realization.origin` is the `.blended` constructor
carrying the exact graph, local certificates, recursive closure evidence, and
demand union. It does not select a platform or claim machine artifacts.

After one target projection and coherent platform plan discharge that demand
union, machine blending is indexed by that same `ClosedBlend` and uses its
retained closed scopes. Each scope contributes
its exact heterogeneous source certificate; the coverage theorem proves every
reachable scope occurs exactly once, and global coherence checks provider
versions/features, ABI, ISA, shared resources and cross-ISA edges. The final
`MachineCertificate` consumes this exact value, preventing source A's local
proof from licensing source B.

### Automation boundary

The library may generate the product relation, the exhaustive constructor
classifier skeleton, frame unchanged invariant
families, discharge exact-boundary congruence, compose simulations, and compute
the finite requirement union. Authors provide local simulations, boundary
adapters, shared-state coupling lemmas, and any provider/resource coherence
facts, initialization relation, silent rank, divergence/fairness mapping, and
unreachability proofs whose truth depends on the implementation. Automation must not unfold a
sibling realization to recover a missing boundary fact.

### Acceptance and mutation fixtures

The fixture suite must include:

- an abstract graphics/storage/simulation graph, then graphics-only,
  storage-only, and fully closed refinements;
- an x86 host plus SPIR-V child artifact with exact cross-ISA channel custody;
- two disjoint refinements applied in both orders with equal projected traces;
- a replacement that changes internal topology while preserving its boundary;
- rejection for one remaining abstract node, conflicting Vulkan/Metal provider
  deltas, an unframed shared invariant, changed channel multiplicity, increased
  boundary resource flux, and newly introduced silent divergence; and
- a boundary-preserving leaf mutation whose sibling semantic certificates are
  byte-identical inputs to the kernel cache, together with separately reported
  source hashing and artifact regeneration work.

The last fixture is the evidence required before making a blast-radius claim.
The architectural target is zero sibling re-elaboration and zero sibling kernel
checks for a boundary-preserving leaf change; path-to-root composition and
artifact work are measured separately.

`Spikes/5_Spinning_Cube/Staged.lean` is presently a design-level inventory of
the intended cube and engine-blend terms. Its undeclared witness names are not a
positive fixture and supply no closure evidence. This acceptance item remains
open until those terms elaborate against the actual definitions, the positive
values construct an indexed `ClosedBlend`, the machine blend is indexed by its
retained origin, and each negative mutation fails at the intended boundary.

### Status and fallback

This is a required pre-implementation theorem family. If the local step cases
cannot be expressed without opening the context implementation, the process
boundary is not adequate and must be revised. If provider or resource deltas do
not compose, the partial blend remains a useful proof artifact but cannot be
passed to `VerifiedProgram`. A proved mock is a realization; an unresolved
abstract node is not.

## 13. Typed process termination and cancellation

### Claim

A process may terminate only through declared terminal transitions; this
ordinary safety fact comes from the existing terminal/lifecycle proof. When a
process exports a cooperative cancellation, bounded shutdown, restart, or
version-handoff capability, an opt-in `TerminationFacet` can additionally guarantee eventual arrival
at a safe terminal point under named scheduler, environment, and child-settlement
premises. Termination transfers or disposes every state fragment, resource,
loan, pending occurrence, and obligation exactly once. Failure to reach a safe
point selects a named escalation/isolation outcome; it does not authorize
arbitrary instruction-boundary death.

### Caller inputs

Only for a non-ordinary termination demand, the author or reusable protocol supplies a safe-point predicate, exhaustive
termination causes and modes, the exact terminal disposition for each permitted
case, a finite-stuttering rank between cancellation observation and the next
frontier, child-cancellation/settlement premises, and any deadline/escalation
policy. A lower realization additionally identifies which machine boundaries
implement each safe point and proves interrupts, callbacks, API pendings, and
faults cannot enter the terminal block with unaccounted custody.

### Construction and proof sketch

`NetworkTransition.processTermination` and the terminal child-lifecycle
constructors require a `permitted` witness from the exact live incarnation's
ordinary terminal disposition or, when the transition claims a stronger
capability, its exact `ProcessTerminationContract`. Constructor inversion therefore proves the
no-arbitrary-death safety property for every execution prefix.

For cooperative cancellation, start from the exact cancellation request
occurrence. Each internal step either reaches a declared frontier, settles one
pending child, or strictly decreases the supplied rank. Fair scheduling and
the named environment/child settlement premises construct the next step; rank
well-foundedness excludes infinite internal avoidance. Induction over the
finite pending-child population reaches a safe point, and the terminal
transition consumes the cancellation authority. The disposition equation
partitions local state into returned parent custody, transferred supervisor
custody, externally adopted obligations allowed by policy, and discharged
resources. No residual is dropped.

Timeout and normal-result races use the same affine resolve token: exactly one
wins, while the loser becomes a classified late occurrence that must be drained,
dropped, or rerouted. Restart allocates a fresh incarnation only after the old
terminal disposition and any join/release condition; historical nominal
freshness rejects late completions from the old incarnation.

A forced-at-safe-point transition reuses the same disposition proof but adds a
lower-layer theorem that control can be redirected only at the represented safe
machine boundary. A fault transition provides only the maximal safe prefix
unless a specific containment envelope proves more. If neither cooperative
settlement nor safe forced termination is available—such as an arbitrary stuck
native thread in shared memory—the supervisor must isolate or fail a larger
scope whose terminal contract owns all remaining custody. `TerminateThread`-like
behavior is not a generic proof constructor.

Supervisor shutdown follows child order by induction. `oneForOne`, `oneForAll`,
and `restForOne` compute their exact affected finite schema instances; dynamic
instances are handled by the current bounded population witness. Reverse
shutdown and forward restart compose child terminal/initial relations. Restart
intensity consumes time-window credit; exhaustion selects the supervisor's
declared terminal outcome, ruling out silent restart divergence.

Sequential cancellation summaries are proved by case analysis on the unique
pending-cancellation occurrence at the component boundary. If none is pending,
the right component receives its ordinary entry state. If one is pending, the
left disposition has either already consumed it or transfers its exact custody
to the right; there is no third case. This proves conservation and yields the
safe-point union and composed delay bound. Extensional equality of these two
cases, plus associativity of ordinary process sequencing and affine transfer,
proves `CancellationSummary.seq_assoc`.

The weakest uncancellable summary exports no cooperative contract. A composed
summary exports `some contract` only after its safe-point reachability,
disposition, and pending-custody facts have all been constructed; equality of
that stored contract with those summary fields is the premise of
`toCooperativeTerminationFacet` or `toSupervisedTerminationFacet`. Consequently
an author cannot obtain a rich facet merely
by naming a policy, and consumers can depend on the facet without reopening the
composition proof.

For `uncancellable |> cancelpoint |> uncancellable`, the first segment's
termination/frontier theorem reaches the cancellation point. The point resolves
the pending-request race: a present occurrence is consumed by the cancellation
disposition; absence enters the final segment. A later request remains pending
until its terminal boundary. Thus the composition has an exact cancellation
policy without imposing a cancellation proof on either uncancellable segment.
Its latency theorem is conditional on the named termination bounds or
environment-progress premises of those segments; if either can block forever,
the construction deliberately cannot produce bounded or eventual cancellation.

Choice is proved by constructor inversion and takes the meet of unconditional
branch guarantees. A stronger dependent result may retain the selected branch's
policy. A loop proof supplies either a well-founded exit argument or a theorem
that every fair continuing cycle crosses a cancellation point; induction gives
every finite cycle, and the productive frontier theorem covers infinite runs.
Parallel and supervisor composition index affine request occurrences by live
incarnation, so settlement is a finite-population conservation proof rather
than an untyped broadcast assumption. Flattening preserves the summary by
induction over graph composition and the sequencing associativity law.

### Automation boundary

The ordinary facet is generated from existing terminal/lifecycle facts and adds
no application field. For selected richer facets, the library can generate constructor inversion, affine race bookkeeping,
finite-population shutdown induction, exact partition framing, standard monitor/
link notification, and standard supervisor-strategy sets. Authors provide safe
points, implementation-specific rank/frontier facts, nonstandard terminal
custody, environment settlement premises, and escalation policy. Automation may
not infer that a blocking foreign call is cancellable or that killing a thread
releases shared obligations.

### Acceptance and mutation fixtures

Fixtures include normal completion, cancellation before work, cancellation
during a partial read/write, cancellation racing a result, a late result from an
old generation, a child that settles at its next frontier, a child that requires
whole-process isolation, all three supervisor restart strategies, reverse-order
shutdown, restart-intensity exhaustion, and version handoff with queued
occurrences. Mutations must reject termination between a write and committed-
prefix accounting, reuse before join, a dropped pending obligation, an
unbounded restart loop, an uncharged selective-receive backlog, and an asserted
forced termination with no machine safe-point proof.
They also include the positive composition
`uncancellable |> cancelpoint |> uncancellable`, both request/no-request races,
a request arriving after the point, reassociation of three sequential
components, branch-policy weakening, and a loop with one point per fair cycle.
Negative mutations remove the point, make a preceding uncancellable call block
forever, duplicate the affine request, discard a late request at ordinary
termination, or claim the stronger policy from only one reachable branch.

Spike 4 attaches richer facets to its cancellable streams, connections, HPACK
decoder, writer, and supervisor. Spike 5's ordinary application terminal proof
already covers user exit and failure; a richer device-work cancellation facet
is required only where the selected realization promises it.

### Status and fallback

This is a required pre-implementation theorem family for every exported richer
termination capability, not for every process. A process without a
cooperative progress proof may still expose safety and a weaker
environment-pending result, but it may not promise cancellation termination. A
realization with no safe forced primitive must escalate to a larger owned scope
or declare the demanded termination property unrealizable on that platform.

## 14. Composable DSL capture into one root SpecProcess

### Claim

A finite suite of well-formed specification-language fragments connected by
typed, total semantic junctions can be captured into one root `SpecProcess`.
Every external trace of the root is exactly a trace of the composed fragments
after hiding internal ports, and conversely every productive composed trace has
a root trace. An abstract `ProcessRequirement` remains universally quantified
until refinement supplies a satisfying witness.

### Construction and proof sketch

Each fragment denotes a small labeled transition system over typed ports. Form
their dependent product state and tagged disjoint union of enabled fragment
steps. A junction step consumes one output occurrence and creates the matching
input occurrence under its `JunctionRelation`; affine occurrence identity makes
the transfer unique. Internal ports and component states are existentially
hidden in the root state. Public input/output ports become root events,
commands, outcomes, and observations.

Finite-prefix soundness is induction over root steps. Constructor inversion
selects a component or junction transition; its local denotation theorem and
junction preservation theorem extend the composed trace. Custody and resource
facts frame untouched components. Completeness is induction over a productive
composed schedule after quotienting adjacent independent internal steps by the
diamond theorem. Each selected transition constructs the corresponding root
step. Internal finite stuttering is bounded by component ranks; an infinite run
uses the existing frontier/productivity coinduction and cannot vanish entirely
under hiding.

A process requirement is interpreted as a universally quantified boundary
relation in this proof. None of its private state is added to precious syntax.
When refinement supplies `witness : SpecProcess` and
`acceptable witness`, relational substitution replaces the abstract boundary;
parametricity plus the acceptability theorem preserves the root trace contract.
Substitution composes and is insensitive to whether the witness is a primitive
process, a captured subgraph, a sequentially adapted function, or assembly.

Associativity follows from dependent-product reassociation, occurrence-tag
renaming, and relational composition associativity. Hiding fusion proves the
fractal law: capturing sub-suites and then the parent is trace-equivalent to one
capture, with identical public observations and requirements. Conflicting
guarantees, unmatched ports, uncovered cases, nullable internal cycles, and
resource-semantic disagreement make suite construction fail before capture.

### Automation boundary and fixtures

Libraries generate product-state plumbing, occurrence renaming, standard
framing, and the associativity/hiding transports. Authors provide novel DSL
denotations, nonstandard junction relations, ambiguity decisions, and any
progress fact not inherited from components. Fixtures cover relation + grammar,
grammar + protocol, trace + temporal, and resource fragments; two parser
witnesses with different process topologies; reassociated and nested capture;
and staged substitution of one abstract process demand. Mutations reject an
unconnected port, duplicated occurrence, missing invalid-input case,
contradictory failure outcome, hidden infinite silent cycle, witness selected by
ambient instance search, or a process whose contract is only similar rather
than accepted by the exact requirement.

### Status and fallback

This construction must be prototyped before the DSL family is treated as stable.
If fully generic dependent ports make elaboration or proof terms impractical,
the fallback is a small closed set of junction shapes—sequence, tagged choice,
product, feedback with guarded progress, and hiding—while retaining the same
one-root theorem. The fallback may narrow extensibility but may not introduce
parallel correctness towers or put an execution topology in the root spec.

## 15. What remains genuinely unproved

The corpus still owes implementation evidence for all of the following:

- that the process interfaces elaborate without dependent-type pathologies;
- that generated sequential bookkeeping remains smaller than the proof it
  replaces;
- that plan-specific concurrency witnesses compose with tolerable goals;
- that byte-flow and resource ledgers remain tractable under real IOCP,
  `io_uring`, interrupt, Vulkan, and device-loss races;
- that x86/SPIR-V symbolic execution has predictable memory use;
- that exact artifact connection covers every selected relocation and loader
  behavior; and
- that ordinary Lean modules provide acceptable clean and incremental build
  performance at representative repository scale.

The five spike source corpora are interface fixtures, not evidence that these
debts are paid. Implementation may simplify an interface after review, but may
not replace a displayed premise with an oracle, weaken an execution direction,
or move program-specific invariant discovery behind a library name.
