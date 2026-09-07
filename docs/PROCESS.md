# Portable process and reactive application model

Status: normative interface draft for adversarial review.

This document owns Grass's portable process-authoring shape. Execution traces,
nondeterminism, safety, and liveness remain owned by [SEMANTICS.md](SEMANTICS.md);
providers and commits by [PLATFORM_ABI.md](PLATFORM_ABI.md); refinement by
[REFINEMENT.md](REFINEMENT.md). This layer is inspired by Elm/Redux and the pure
part of React, not by React's runtime semantics.

This document states the semantic interfaces using finite registry and plan
parameters. A large realization must not instantiate them as one public closed
whole-program value. Module-local open registries, facet-indexed certificates,
scoped cancellation, SCC boundaries, and balanced process-certificate DAGs are
normative in [PROCESS_SHARDING.md](PROCESS_SHARDING.md).

## 1. Why a process layer exists

Every program has one precious root `SpecProcess`, and `VerifiedProgram` is
indexed by it. Domain DSLs may construct semantic child processes or demand an
existential process satisfying a contract; semantic composition captures and
hides them into that root. Their public contracts and meaning-bearing junctions
are precious. A particular lexer/parser, listener/connection/stream,
graphics/storage, or other decomposition is not.

A replaceable `ProcessPresentation` supplies logical roles, typed channels,
linear custody, shared logical state, causal attribution, and a theorem that its
network denotes the root exactly. A lower process realization supplies the
chosen physical state partition, population, weave, and driver. Neither layer
may enter the root merely because it is convenient for a proof. The root must
not contain a Win32 message pump, OS worker topology, console loop, Vulkan
scheduler, concrete queue, or callback mechanism.

The reusable driver theorem is proved once:

```text
external event / correlated demand result
                    |
                    v
             pure process step
                    |
       new state + abstract demand set
                    |
                    v
       verified driver executes/commits
```

The exact driver still lowers through authored assembly and exact artifact
emission. The process layer removes repeated application proofs, not physical
modeling.

## 2. Semantic interface

The general form is relational so nondeterministic specifications remain first
class. A deterministic convenience constructor accepts an `update` function and
derives the relation.

```lean
structure ProcessVocabulary where
  ExternalEvent : Type
  Demand : Type
  Result : Demand -> Type
  Observation : Type
  InterruptReason : Demand -> Type
  LogicalFault : Type
  EnvironmentViolation : Type

inductive ProcessEvent (v : ProcessVocabulary)
  | external (event : v.ExternalEvent)
  | result (demand : v.Demand) (result : v.Result demand)
  | interrupted (demand : v.Demand) (reason : v.InterruptReason demand)
  | fault (fault : v.LogicalFault)
  | environmentViolation (violation : v.EnvironmentViolation)

structure ViewFacet (State : Type) where
  View : Type
  render : State -> View

structure ProcessSpec where
  vocabulary : ProcessVocabulary
  Request : Type
  State : Type
  TerminalResult : Type
  Initial : Request -> State -> AbstractDemandBag vocabulary.Demand ->
            List vocabulary.Observation -> Prop
  Terminal : Request -> State -> TerminalResult -> Prop
  Step : State -> ProcessEvent vocabulary ->
         State -> AbstractDemandBag vocabulary.Demand ->
         List vocabulary.Observation -> Prop
  view : Option (ViewFacet State)

structure DeterministicProcess (v : ProcessVocabulary) where
  Request : Type
  State : Type
  TerminalResult : Type
  initial : Request -> State × AbstractDemandBag v.Demand × List v.Observation
  terminal : Request -> State -> Option TerminalResult
  update : State -> ProcessEvent v ->
           State × AbstractDemandBag v.Demand × List v.Observation
  view : Option (ViewFacet State)
```

Reusable protocol or network constructors select all seven associated families
once and pass one `ProcessVocabulary` to their process clients. Convenience
constructors such as `ProcessVocabulary.quiescent` fill the three exceptional
families with empty types when the route is proved unreachable. An ordinary
`ProcessSpec` literal therefore names one `vocabulary`; it never restates the
families and cannot discard an unclassified exceptional event.

Grass uses explicit terminology:

```lean
structure StructuralProcessNetwork (Protocol : Type u) where
  RoleSchema : Type
  finiteSchemas : Fintype RoleSchema
  Instance : RoleSchema -> Type
  protocol : RoleSchema -> Protocol
  instances : forall schema,
    Instance schema -> ProtocolInstance (protocol schema)
  composition : AbstractNetworkCompositionLaw protocol instances
  abstraction : UsesNoPlatformThreadSchedulerBufferHandleLayoutOrISAIdentity
```

`ProtocolInstance` and `AbstractNetworkCompositionLaw` are neutral typed
junctions parameterized by the supplied `Protocol`; they do not interpret a
semantic contract. `StructuralProcessNetwork` consequently contains no
`SpecProcess`, `BehaviorContract`, selected trace, denotation, transported
requirements, or exactness proof. `Semantics` instantiates `Protocol` with its
own semantic process type and selects meaning separately.

A `ProcessSpec` selected by a network is a **spec process**. A
`ProcessPlan`, `ProcessRealization`, or driver network is a **process
realization**. Only the former may be part of precious specification source;
the latter and its proof are reviewed, bankable, and disposable. Different
physical or logical realization topologies may refine the same spec-process
network.

The finite demand multiset contains neither occurrence identities nor execution
order. A demand is a precious abstract interaction only when program behavior
depends on it—for example “commit these bytes,” “finish with this outcome,” or
“present this view.” Its dependent result schema contains every permitted
result. The selected realization turns demands into fresh occurrences and
chooses a dependency DAG, batching, routing, child topology, supervision, and
cancellation mechanism. Those choices are not encoded back into `ProcessSpec`.

When semantic causality matters, it is represented by state: a later demand is
not enabled until the transition which accepts the prerequisite result. The
specification does not prescribe whether independent enabled demands execute
sequentially or concurrently. A product-level cancellation requirement is an
abstract demand/result law; queue removal, interrupt delivery, and child death
handling remain realization choices.

The final argument of `Step` is the finite observation segment emitted by that
exact transition. A process run concatenates these segments. Processes do not
carry their complete observation history in local state, and revisiting or
rendering a state cannot duplicate an observation. Empty segments are ordinary
silent/stuttering transitions. `view := none` is the normal choice for filters,
servers, API calls, and other processes with no pure desired-state projection.

### Serial calls inside a process

A process step may call a proved serial function directly. It does not create a
child instance, channel, demand occurrence, or scheduling point merely because
the machine realization uses an ABI `call`. The function contract supplies a
local state/representation transformation and the process step proof composes
that transformation into its own before/after relation:

```lean
inductive SerialCallDisposition (output fault : Type)
  | returned (value : output)
  | raised (value : fault)

structure SerialFunctionContract where
  Input Output Fault : Type
  ExitState : Type
  Pre : Input -> LogicalState -> Prop
  disposition : ExitState -> SerialCallDisposition Output Fault
  Post : Input -> ExitState -> LogicalState -> LogicalState -> Prop
  footprint : LogicalFootprint
  obligations : Input -> ExitState ->
    LocalObligationState -> LocalObligationState -> Prop
  resources : Input -> ExitState ->
    LocalResourceState -> LocalResourceState -> Prop
  faults : forall input exit before after,
    disposition exit = .raised fault -> Post input exit before after ->
    ExactDeclaredPartialMutationAndCustody fault before after
  Rank : Type
  rankOrder : WellFoundedRelation Rank
  entryRank : Input -> LogicalState -> Rank
  recursiveEdgeDecreases : EveryInternalAndRecursiveSCCEdgeStrictlyDecreases
    rankOrder entryRank
  exitsComplete : EveryMaximalInternalExecutionHasExactlyOneDeclaredExit
    disposition Post obligations resources
  workBound : Option (Input -> LogicalState -> Nat)
  noFrontier : NoExternalPendingCancellationOrInterleavingFrontier

inductive SerialCallVisibility (contract : SerialFunctionContract)
    (input : contract.Input) (before : LogicalState)
  | exclusive
      (owned : CallerExclusivelyOwns contract.footprint input before)
  | linearized
      (point : LinearizationPoint)
      (atomic : EveryIntermediateSharedEffectIsHiddenOrLinearizesAt point)
      (noninterference : EnvironmentInterferencePreservesCallSimulation point)

structure FiniteStutteringCallSimulation
    (contract : SerialFunctionContract)
    (source : FunctionMachineSource abi) where
  entry : EveryRepresentedPreStateEntersAtContractState source contract
  internal : EveryNonexitMachineStepIsFiniteSilentStuttering source contract
  exit : EveryMachineExitMapsToExactlyOneContractExit source contract
  converse : EveryContractExitAllowedByPostHasAMachineExecution source contract
  partialMutation : FaultExitsPreserveExactIntermediateMutation source contract
  custody : EveryExitImplementsExactResourceAndObligationTransform source contract
  rank : MachineInternalAndRecursiveEdgesImplementRank source contract
  visibility : forall input before, contract.Pre input before ->
    SerialCallVisibility contract input before
  bounded : OptionalMachineWorkBoundImplemented source contract.workBound

structure SerialFunctionImplementation
    (contract : SerialFunctionContract) where
  abi : AbiProfile
  source : FunctionMachineSource abi
  correct : FiniteStutteringCallSimulation contract source

structure ProcessStepUsingContract
    (p : ProcessSpec) (contract : SerialFunctionContract) where
  input : contract.Input
  before : LogicalState
  pre : contract.Pre input before
  normal : forall exit output,
    contract.disposition exit = .returned output ->
    forall after, contract.Post input exit before after ->
      ExactProcessNormalTransition p before after output
  fault : forall exit value,
    contract.disposition exit = .raised value ->
    forall after, contract.Post input exit before after ->
      ExactProcessFaultTransition p before after value
  resources : EveryExitResourceTransformIsConsumedByProcessTransition contract input
  obligations : EveryExitObligationTransformIsConsumedByProcessTransition contract input
  observations : EveryExitHasExactProcessObservationSegment contract input

theorem ProcessStep.callSerial
    (function : SerialFunctionImplementation contract)
    (step : ProcessStepUsingContract p contract) :
    ProcessStepImplementedByCall p step function
```

The call may allocate from already-owned deterministic storage, mutate owned
memory, use loops, or contain arbitrary authored assembly; those effects are summarized by the explicit local contract
and remain checked in the function CFG. Its footprint is framed against other
process state, and its termination proof supplies the finite internal-work fact
needed between process frontiers. Callers consume the contract and do not reopen
the body. Normal return and every declared fault are separate `ExitState`
values. Each exit fixes the logical post-state, resource custody, obligation
custody, and any partial mutation; there is no generic exceptional edge whose
state is left implicit.

Collapsing the machine call to one process transition is permitted only by
`FiniteStutteringCallSimulation`. Exclusive ownership makes every intermediate
write private. A call touching shared state instead supplies a linearization
point and a noninterference proof; a footprint alone is insufficient. The
well-founded rank covers ordinary CFG edges and recursive SCC call edges. If a
product responsiveness theorem needs a numeric amount of work between
frontiers, `workBound` is present and proved; bare termination is not silently
promoted to a latency bound.

The boundary is semantic. A computation which can wait for external entropy,
remain pending, be independently cancelled, transfer resources or obligations
to another custodian, or interleave observably must expose the corresponding
demand/child/frontier. A synchronous platform API is still modeled by a child
protocol because its return is external entropy, even when its selected machine
realization is one blocking ABI call. Conversely, a pure parser helper, CRC
routine, allocator-internal arena/tree operation, or proved serial sort can remain a
plain function call inside one process transition.

A flattened process may also export a serial callable contract when its
serialization theorem proves a terminating, frontier-free invocation for the
selected request. This is the fractal bridge from a graph used for proof
composition to one ordinary function used for execution; it does not introduce
a second execution semantics.

Occurrence identities are absent from `Step`, but demand multiplicity is linear
in the run semantics:

```lean
inductive ProcessRunState (p : ProcessSpec) (request : p.Request)
  | running (local : p.State) (outstanding : AbstractDemandBag p.Demand)
      (observations : Trace p.Observation)
  | terminal (local : p.State) (result : p.TerminalResult)
      (observations : Trace p.Observation)

inductive ProcessRunInitial (p : ProcessSpec) (request : p.Request) :
    ProcessRunState p request -> Prop
  | running
      (initial : p.Initial request local issued emitted) :
      ProcessRunInitial p request (.running local issued emitted)
  | terminal
      (initial : p.Initial request local issued emitted)
      (isTerminal : p.Terminal request local result)
      (disposition : ClassifiesEveryOutstandingDemand issued) :
      ProcessRunInitial p request (.terminal local result emitted)

inductive ProcessRunTransition (p : ProcessSpec) (request : p.Request) :
    ProcessRunState p request -> ProcessRunState p request -> Prop
  | stepExternal
      (step : p.Step local (.external event) afterLocal issued emitted)
      : ProcessRunTransition p request
          (.running local outstanding observations)
          (.running afterLocal (outstanding + issued) (observations ++ emitted))
  | stepResult
      (consume : ConsumeExactlyOneMatching outstanding demand remainder)
      (step : p.Step local (.result demand result)
        afterLocal issued emitted)
      : ProcessRunTransition p request
          (.running local outstanding observations)
          (.running afterLocal (remainder + issued) (observations ++ emitted))
  | stepInterrupted
      (consume : ConsumeExactlyOneMatching outstanding demand remainder)
      (step : p.Step local (.interrupted demand reason)
        afterLocal issued emitted)
      : ProcessRunTransition p request
          (.running local outstanding observations)
          (.running afterLocal (remainder + issued) (observations ++ emitted))
  | stepFault
      (step : p.Step local (.fault fault) afterLocal issued emitted)
      : ProcessRunTransition p request
          (.running local outstanding observations)
          (.running afterLocal (outstanding + issued) (observations ++ emitted))
  | stepEnvironmentViolation
      (step : p.Step local (.environmentViolation violation)
        afterLocal issued emitted)
      : ProcessRunTransition p request
          (.running local outstanding observations)
          (.running afterLocal (outstanding + issued) (observations ++ emitted))
  | terminate
      (terminal : p.Terminal request local result)
      (disposition : ClassifiesEveryOutstandingDemand outstanding)
      : ProcessRunTransition p request
          (.running local outstanding observations)
          (.terminal local result observations)
```

Equal demand values remain indistinguishable at the precious level, but their
bag multiplicity cannot be fabricated, replayed, jointly consumed by one result,
or silently lost. A result/interruption requires and consumes exactly one live
matching item; termination explicitly resolves, transfers, or permits pending
for every remainder according to the specification's progress/lifecycle law.
Only `running` states step. A terminal transition requires the protocol's exact
request-indexed `Terminal` witness, produces a typed result, and has no outgoing
transition. `ProcessRunInitial` is the only initial form: it begins from an empty
prior history and exactly the state, initial demands, and observations emitted by
`Initial`. Its terminal constructor is available only when that same state also
satisfies `Terminal` and every initially issued demand has a terminal
disposition. Thus a zero-transition terminal run is genuinely terminal rather
than a running state followed by a hidden transition.
`ProcessPlanRealizes` proves a prefix-by-prefix bijection between live concrete
occurrences after private-identity erasure and this abstract bag. Product-visible
request identity may be a field of `Demand`; scheduling/correlation identities
remain realization-private.

## 3. Replaceable process topology and state ownership

The primary modeling question is: **which processes exist, and over what logical
state do they act?** The answer is a reviewed replaceable construction input,
not automatically part of the precious specification. A complete realization is
a process plan rather than one giant state record:

```lean
structure ProtocolRegistry where
  Key : Type
  protocol : Key -> ProcessSpec

structure DriverBoundary where
  ExternalEvent : Type
  Demand : Type
  Result : Demand -> Type
  Observation : Type
  requirements : RequirementSet

structure ProcessGraph (registry : ProtocolRegistry)
    (boundary : DriverBoundary) where
  ProcessKind : Type
  SharedRegion : Type
  SharedState : SharedRegion -> Type
  protocolKey : ProcessKind -> registry.Key
  root : ProcessKind
  rootBoundary : ProtocolExposesBoundary
    (registry.protocol (protocolKey root)) boundary
  maySpawn : ProcessKind -> ProcessKind -> Prop
  sharedAccess : ProcessKind -> SharedRegion -> LogicalAccess
  population : PopulationLaw ProcessKind

structure ProcessTopologyCore (registry : ProtocolRegistry)
    (boundary : DriverBoundary) extends ProcessGraph registry boundary where
  ChannelKind : Type
  endpoints : ChannelKind -> ProcessKind × ProcessKind
  spawn : SpawnAuthorityAndParenthood toProcessGraph

structure ProcessTopology (registry : ProtocolRegistry)
    (boundary : DriverBoundary) extends ProcessTopologyCore registry boundary where
  facets : SelectedTopologyFacetFamily toProcessTopologyCore
    (requiredTopologyFacets boundary)
  facetsExact : FacetsMeetExactlyDemandedCancellationAndSupervisionContracts
    toProcessTopologyCore (requiredTopologyFacets boundary) facets

theorem ProcessTopology.allCancellationContracts
    (topology : ProcessTopology registry boundary) :
    EveryDemandedCancellationContractHolds topology := ...

theorem ProcessTopology.allSupervisionContracts
    (topology : ProcessTopology registry boundary) :
    EveryDemandedSupervisionContractHolds topology := ...

structure ProcessRef (topology : ProcessTopology registry boundary)
    (kind : topology.ProcessKind) where
  id : ProcessId kind
  generation : Generation

structure ChannelId (topology : ProcessTopology registry boundary)
    (edge : topology.ChannelKind) where
  sender : ProcessRef topology (topology.endpoints edge).1
  receiver : ProcessRef topology (topology.endpoints edge).2
  epoch : SessionEpoch

structure MessageOccurrence (topology : ProcessTopology registry boundary)
    (edge : topology.ChannelKind) (channel : ChannelId topology edge)
    (Message : Type) (message : Message) where
  id : OccurrenceId channel message

abbrev ChannelOccurrence (topology : ProcessTopology registry boundary)
    (edge : topology.ChannelKind) (Message : Type) (message : Message) :=
  Sigma fun channel : ChannelId topology edge =>
    MessageOccurrence topology edge channel Message message
```

`ProcessGraph` exists separately so topology and channel contracts can quantify over the
endpoint protocols, spawn/population laws, shared-state interference, and
process-network assertions without a self-referential structure declaration.
The completed `ProcessPlan` below adds the channel edges.

The precious root may require independently cancellable requests or tenant
isolation as behavior, and may demand child processes satisfying named
contracts. It does not require that a realization represent those guarantees
with particular roles or populations. Worker count, pipeline shape, helper
ownership, sequential versus parallel execution, batching, and event routing
belong to `ProcessPresentation`/`ProcessPlan`. Another plan may realize the same
root with a different topology and state partition.

`population` describes static, bounded, or generative instances and their stable
identities. It can say “one root and one child call at a time,” “four supervised
worker instances,” “one request process per accepted connection up to a resource
policy,” or “one host process plus queue/submission/presentation child
processes.” Creation and termination are typed transitions, not changes to an
uninterpreted global bag.

Local state belongs to one process instance. Shared logical state is named
separately with read/write/atomic capabilities and interference invariants.
Nothing is shared merely because two transitions mention the same Lean value.
The later memory realization maps this logical ownership/access graph to
provenance, loans, synchronization, allocation identity, and race-freedom
proofs; the process plan does not mention addresses or allocators unless it is
already a lower realized plan.

Event channels name sender, receiver, ordering, buffering/coalescing, delivery,
cancellation, and observation laws. Direct child responses use a standard
identity-correlated channel. This makes callback reentrancy and concurrent
workers explicit process interactions rather than special cases hidden in a
single `update` function.

Channels have Hoare-style contracts over process-network state. Their central
object is an **escrow assertion**: after send commits, the channel—not either
endpoint—owns the exact occurrence and every resource, capability, provenance
fact, and obligation transferred with it until receive or an explicitly modeled
cancellation/disposition transition consumes it.

The assertion must name the world it describes. That world cannot depend on a
completed `ProcessPlan`, because channel contracts are themselves fields of the
plan. Grass breaks the dependency at the smallest useful seam: the plan declares
its per-edge message family before its contracts; topology plus that family is
enough to define the whole logical-network carrier. Contracts are then stated
over that carrier. There is no second topology-level escrow carrier and no
self-referential structure.

```lean
inductive ProcessLifecycle (p : ProcessSpec)
  | running
  | terminated (result : p.TerminalResult)
  | cancelled (reason : CancelReason)
  | interrupted (reason : p.InterruptReason)
  | faulted (fault : p.LogicalFault)
  | violated (violation : p.EnvironmentViolation)
  | died (reason : ProcessDeathReason)

inductive ProcessParentage (topology : ProcessTopology registry boundary) :
    topology.ProcessKind -> Type
  | root : ProcessParentage topology topology.root
  | attached {kind : topology.ProcessKind}
      (parentKind : topology.ProcessKind)
      (parent : ProcessRef topology parentKind) : ProcessParentage topology kind
  | detached {kind : topology.ProcessKind}
      (formerParentKind : topology.ProcessKind)
      (formerParent : ProcessRef topology formerParentKind) :
      ProcessParentage topology kind

structure ProcessInstance (topology : ProcessTopology registry boundary) where
  kind : topology.ProcessKind
  ref : ProcessRef topology kind
  parentage : ProcessParentage topology kind
  request : (registry.protocol (topology.protocolKey kind)).Request
  local : (registry.protocol (topology.protocolKey kind)).State
  lifecycle : ProcessLifecycle (registry.protocol (topology.protocolKey kind))

structure LogicalProcessNetworkCore
    (topology : ProcessTopology registry boundary)
    (Message : topology.ChannelKind -> Type) where
  instances : (kind : topology.ProcessKind) ->
    ProcessId kind -> Option (ProcessInstance topology)
  shared : (region : topology.SharedRegion) -> topology.SharedState region
  inFlight : ChannelEscrowLedger topology Message
  sessions : ChannelSessionLedger topology Message
  obligations : LogicalObligationLedger
  observations : Trace boundary.Observation
  usedNominals : MonotoneNominalHistory

structure WorldAgreement (topology : ProcessTopology registry boundary)
    (World : Type) where
  Agrees : NetworkFragment topology -> World -> World -> Prop
  agreesRefl : forall fragment world, Agrees fragment world world
  agreesSymm : forall fragment left right,
    Agrees fragment left right -> Agrees fragment right left
  agreesTrans : forall fragment a b c,
    Agrees fragment a b -> Agrees fragment b c -> Agrees fragment a c
  agreesGlue : forall (inside : NetworkFragment topology -> Prop) (left right : World),
    exists mixed,
      (forall fragment, inside fragment -> Agrees fragment mixed left) /\
      (forall fragment, not (inside fragment) -> Agrees fragment mixed right)

structure NetworkAssertion {topology : ProcessTopology registry boundary}
    {World : Type} (agreement : WorldAgreement topology World) where
  holds : World -> Prop
  footprint : NetworkFragment topology -> Prop
  framed : forall left right,
    (forall fragment, footprint fragment -> agreement.Agrees fragment left right) ->
    (holds left <-> holds right)

def logicalWorldAgreement
    (topology : ProcessTopology registry boundary)
    (Message : topology.ChannelKind -> Type) :
    WorldAgreement topology (LogicalProcessNetworkCore topology Message) := ...

structure ChannelContract (topology : ProcessTopology registry boundary)
    (Message : Type) {World : Type}
    (agreement : WorldAgreement topology World)
    (edge : topology.ChannelKind) where
  senderOutput : SenderDemandEmbedding topology (topology.endpoints edge).1 Message
  receiverInput : ReceiverEventEmbedding topology (topology.endpoints edge).2 Message
  SendPre : Message -> NetworkAssertion agreement
  SenderPost : (message : Message) ->
    ChannelOccurrence topology edge Message message -> NetworkAssertion agreement
  Escrow : (message : Message) ->
    ChannelOccurrence topology edge Message message -> NetworkAssertion agreement
  ReceiverPre : (message : Message) ->
    ChannelOccurrence topology edge Message message -> NetworkAssertion agreement
  ReceiverPost : (message : Message) ->
    ChannelOccurrence topology edge Message message -> NetworkAssertion agreement
  send : forall message,
         HoareTransition
           (SendPre message)
           (fun occurrence =>
             SenderPost message occurrence * Escrow message occurrence)
  receive : forall message occurrence,
            HoareTransition
              (ReceiverPre message occurrence * Escrow message occurrence)
              (ReceiverPost message occurrence)
  escrowStable : StableUnderUnrelatedProcessSteps Escrow
  prefixConservation : NoFabricationDuplicationOrLoss Escrow
  atMostOneResolution : ResolveTokenIsAffine Escrow
  resolutions : ExhaustiveResolutionTransitions
  transferExact : ExactLogicalStateAndObligationTransfer
  session : ChannelSessionLaw Message
  frame : UnmentionedProcessesAndRegionsPreserved

structure ProcessPlan (registry : ProtocolRegistry) (boundary : DriverBoundary)
    extends ProcessTopology registry boundary where
  Message : ChannelKind -> Type
  channel : (edge : ChannelKind) ->
    ChannelContract toProcessTopology (Message edge)
      (logicalWorldAgreement toProcessTopology Message) edge
  boundaryProjection : RootLocalDemandProjection toProcessTopology boundary

abbrev LogicalProcessNetwork (plan : ProcessPlan registry boundary) :=
  LogicalProcessNetworkCore plan.toProcessTopology plan.Message
```

`ProcessTopologyCore` is the graph, population, channel-endpoint, and spawn
object every plan needs. `requiredTopologyFacets` derives its result from the
already selected `boundary.requirements`; an author cannot choose a convenient
second demand set. `ProcessTopology` adds only that derived cancellation and
supervision facet family, and the two aggregate theorems recover all and only
its selected contracts. When the derived family is empty, the library supplies
the unique empty selection automatically, so a simple plan authors no
cancellation or supervision field. The unqualified topology never silently
assumes a facet absent from `requiredTopologyFacets boundary`.

`LogicalProcessNetworkCore` is a construction dependency, not a second public
network semantics; authors and later theorems use `LogicalProcessNetwork plan`.
The canonical `logicalWorldAgreement` decomposes exactly the named network
fragments and proves the gluing law, so an assertion footprint is meaningful
rather than a decoration. A reusable lower module may quantify over an arbitrary
`WorldAgreement`; the completed plan always instantiates its channel contracts
at the full logical network shown above. Because footprints are arbitrary
predicates—including non-finite families over generative populations—the
canonical mix used to prove `agreesGlue` may depend on the reviewed
`Classical.choice` foundation constant. That dependency is localized to the
logical-world supplier and is visible to the transitive axiom audit; the generic
assertion and framing library neither chooses worlds nor acquires a broader
admission mechanism. Requiring a Boolean footprint merely to avoid that reviewed
constant would make every author supply decidable membership and would exclude
useful proposition-indexed families without improving the verified gate.

The definitions above make each occurrence nominally indexed by the exact
channel edge, sender and receiver incarnations, session epoch, message, and
pre-send world.

`ProcessLifecycle` is indexed by the instance protocol because an ending must
remain recoverable from network state without replaying the parent transition.
The terminal tag stores the exact `TerminalResult`; the other ending tags store
their exact cancellation, interruption, fault, violation, or death reason. A
well-formed network separately proves that `.terminated result` satisfies the
protocol's `Terminal request local result` relation and that every ending tag is
the exact payload committed by its lifecycle transition. Carrying the payload
does not duplicate an independent fact: the transition owns one value and
records that same value in the child event, parent projection when applicable,
and resulting instance state through equality proofs.

`ProcessParentage` preserves both current authority and the history needed to
justify its loss. `.root` is indexed at exactly the topology's root kind;
`.attached parent` names the current parent incarnation; and
`.detached formerParent` records the exact incarnation from which the process
was detached without granting that incarnation any continuing parent authority.
The detach transition changes only `.attached parent` to
`.detached parent`, proves the references identical, and establishes the
corresponding non-returning child disposition. Thus a root and a detached child
are distinguishable from network state, and an audit can validate detachment
without replaying the transition history. Root uniqueness and the validity of
attached parent/spawn relationships remain network well-formedness laws rather
than proof fields paid by each instance author.

`usedNominals` contains every process generation, channel epoch, child demand,
message occurrence, and coalesced replacement ever allocated in the execution
prefix, including resolved/tombstoned identities. Freshness means absence from
that monotone history, not merely absence from the current live set. A stale
completion can therefore never regain authority after numeric reuse. The
`MessageOccurrence` carries only its nominal identity; the unique affine
`ResolveToken occurrence.id` is an owned assertion inside `Escrow`, not a field
whose Lean value is assumed noncopyable.

The request is retained to index dependent response and terminal facts; it does
not make child-private state visible to the parent. `ProcessPlanRealizes`
supplies initial/shared invariants, access/interference laws, unique live
identities, lifecycle consistency, and the relationship between emitted process
observations and `boundary.Observation`. Physical addresses, locks, handles, and
queues enter only in the later representation relation.

Here `*` is separating conjunction over the logical process network, not
physical heap separation. `SendPre` is the sender's exit condition for the
communication edge. `Escrow` contains only the transferred payload and affine
resolve token. `ReceiverPre` owns the receiver's independently evolving
local/session cursor. Receive consumes `ReceiverPre * Escrow` and establishes
`ReceiverPost`; the sender never fabricates receiver state. Send and receive can
therefore be checked locally while their composition is a library theorem.

The send triple may move logical ownership, create a child/cancellation
obligation, or append an ordered message occurrence. The receive triple consumes
that exact occurrence once and transfers precisely the escrowed state to the
receiver. Unrelated transitions must preserve `Escrow`; this makes buffered
delay sound. Conservation and at-most-one resolution are unconditional prefix
laws; an unrestricted infinite-pending execution may retain live escrow forever.
Eventual delivery/disposition requires named responsiveness assumptions.
Requesting cancellation does not reclaim escrow; acknowledged cancellation,
timeout, endpoint/channel death, drop, reroute, and coalescing are exhaustive
competing resolution transitions. Coalescing consumes every source token and
creates one fresh occurrence. Session state evolves on those same transitions.

### Byte-flow protocols and partial I/O

Reads and writes are standardized as asynchronous byte-flow processes, not as
the fiction that one API call transfers one requested buffer. The logical
payload is an ordered stream of bytes; physical completion boundaries are not
part of that stream's meaning:

```lean
structure NonemptyByteChunk where
  bytes : Vec Byte
  nonempty : 0 < bytes.length

inductive ByteIngressEvent
  | chunk (value : NonemptyByteChunk)
  | eof
  | failed (cause : ProviderFailure)

inductive ByteIngressPhase
  | idle
  | inFlight (occurrence : ReadOccurrence) (loan : ReadBufferLoan occurrence)
  | cancelling (occurrence : ReadOccurrence) (loan : ReadBufferLoan occurrence)
      (reason : CancelReason)
  | draining (outcome : IngressTerminalOutcome)
  | terminal (outcome : IngressTerminalOutcome)

structure ByteIngressResolution (occurrence : ReadOccurrence)
    (loan : ReadBufferLoan occurrence) where
  transferred : Vec Byte
  initializedPrefix : RepresentsCompletedReadPrefix loan transferred
  disposition : ReadCompletionDisposition
  residual : ExactReadLoanAndCreditDisposition loan transferred disposition

structure ByteIngressState where
  phase : ByteIngressPhase
  providerProduced : Vec Byte
  adapterQueue : Vec Byte
  channelEscrow : Vec Byte
  parserConsumed : Vec Byte
  parserRemainder : Vec Byte
  conservation : ExactOrderedIngressPartition providerProduced
    parserConsumed parserRemainder channelEscrow adapterQueue
    (InFlightCompletedBytes phase)

inductive ByteEgressDemand
  | write (value : NonemptyByteChunk)
  | finish

inductive ByteEgressPhase
  | idle
  | inFlight (demand : ByteEgressDemand)
      (occurrence : WriteOccurrence demand) (loan : WriteBufferLoan occurrence)
  | cancelling (demand : ByteEgressDemand)
      (occurrence : WriteOccurrence demand) (loan : WriteBufferLoan occurrence)
      (reason : CancelReason)
  | terminal (outcome : EgressTerminalOutcome)

structure ByteEgressResolution (demand : ByteEgressDemand)
    (occurrence : WriteOccurrence demand) (loan : WriteBufferLoan occurrence) where
  transferred : Vec Byte
  exactPrefix : transferred.IsPrefixOf (RequestedBytes demand)
  disposition : WriteCompletionDisposition
  residual : ExactWriteLoanCreditAndSuffixDisposition
    loan transferred disposition
  providerLaw : ProviderAllowsTransferredPrefixOnDisposition
    disposition transferred

structure ByteEgressState where
  phase : ByteEgressPhase
  offered : Vec Byte
  committed : Vec Byte
  queued : Vec Byte
  conservation : offered = committed ++ InFlightRequestedBytes phase ++ queued

inductive ByteIngressTransition : ByteIngressState -> ByteIngressState -> Prop
  | start
      (idle : before.phase = .idle)
      (allocation : EnclosingNetworkStepAllocatesFresh occurrence)
      (loaned : FreshReadLoanForWritableSpare before occurrence loan)
      (exact : after = StartIngressRead before occurrence loan) :
      ByteIngressTransition before after
  | pending
      (active : before.phase = .inFlight occurrence loan)
      (exact : after = before) : ByteIngressTransition before after
  | readiness
      (active : before.phase = .inFlight occurrence loan)
      (sameOccurrence : ReadyOccurrence = occurrence)
      (exact : after = before) : ByteIngressTransition before after
  | requestCancel
      (active : before.phase = .inFlight occurrence loan)
      (authority : MayCancelRead occurrence reason)
      (exact : after = BeginIngressCancellation before occurrence loan reason) :
      ByteIngressTransition before after
  | resolveActive
      (active : before.phase = .inFlight occurrence loan)
      (token : ResolveToken occurrence)
      (resolution : ByteIngressResolution occurrence loan)
      (exact : after = ApplyIngressResolution before resolution) :
      ByteIngressTransition before after
  | resolveCancellation
      (active : before.phase = .cancelling occurrence loan reason)
      (token : ResolveToken occurrence)
      (resolution : ByteIngressResolution occurrence loan)
      (race : ResolutionMatchesCancellationRace reason resolution)
      (exact : after = ApplyIngressResolution before resolution) :
      ByteIngressTransition before after
  | enqueue
      (chunk : NonemptyByteChunk)
      (prefix : chunk.bytes.IsPrefixOf before.adapterQueue)
      (credit : ExactIngressChannelCredit chunk)
      (exact : after = MoveIngressQueueToEscrow before chunk credit) :
      ByteIngressTransition before after
  | deliver
      (chunk : NonemptyByteChunk)
      (prefix : chunk.bytes.IsPrefixOf before.channelEscrow)
      (occurrence : ExactIngressChannelOccurrence chunk)
      (exact : after = DeliverIngressEscrowToParser before chunk occurrence) :
      ByteIngressTransition before after
  | consume
      (chunk : NonemptyByteChunk)
      (prefix : chunk.bytes.IsPrefixOf before.parserRemainder)
      (exact : after = ConsumeParserPrefix before chunk) :
      ByteIngressTransition before after
  | terminate
      (draining : before.phase = .draining outcome)
      (empty : IngressInternalBuffersEmpty before)
      (exact : after = FinishIngress before outcome) :
      ByteIngressTransition before after

inductive ByteEgressTransition : ByteEgressState -> ByteEgressState -> Prop
  | offer
      (chunk : NonemptyByteChunk)
      (accepting : EgressAcceptsOffer before.phase)
      (exact : after = AppendOfferedEgress before chunk) :
      ByteEgressTransition before after
  | start
      (idle : before.phase = .idle)
      (queued : NextQueuedDemand before = some demand)
      (allocation : EnclosingNetworkStepAllocatesFresh occurrence)
      (loaned : FreshWriteLoanForDemand before demand occurrence loan)
      (exact : after = StartEgressWrite before demand occurrence loan) :
      ByteEgressTransition before after
  | pending
      (active : before.phase = .inFlight demand occurrence loan)
      (exact : after = before) : ByteEgressTransition before after
  | readiness
      (active : before.phase = .inFlight demand occurrence loan)
      (sameOccurrence : ReadyOccurrence = occurrence)
      (exact : after = before) : ByteEgressTransition before after
  | requestCancel
      (active : before.phase = .inFlight demand occurrence loan)
      (authority : MayCancelWrite occurrence reason)
      (exact : after = BeginEgressCancellation
        before demand occurrence loan reason) :
      ByteEgressTransition before after
  | resolveActive
      (active : before.phase = .inFlight demand occurrence loan)
      (token : ResolveToken occurrence)
      (resolution : ByteEgressResolution demand occurrence loan)
      (exact : after = ApplyEgressResolution before resolution) :
      ByteEgressTransition before after
  | resolveCancellation
      (active : before.phase = .cancelling demand occurrence loan reason)
      (token : ResolveToken occurrence)
      (resolution : ByteEgressResolution demand occurrence loan)
      (race : ResolutionMatchesCancellationRace reason resolution)
      (exact : after = ApplyEgressResolution before resolution) :
      ByteEgressTransition before after
  | finish
      (idle : before.phase = .idle)
      (empty : before.queued = #[])
      (complete : before.offered = before.committed)
      (exact : after = FinishEgress before outcome) :
      ByteEgressTransition before after

theorem ingress_resolution_phase_table
    (resolution : ByteIngressResolution occurrence loan) :
  IngressPhaseAfter resolution =
    match resolution.disposition with
    | .continue => .idle
    | .eof => .draining (IngressOutcomeOf resolution)
    | .failed _ => .draining (IngressOutcomeOf resolution)
    | .cancelled _ => .draining (IngressOutcomeOf resolution)
    | .closed _ => .draining (IngressOutcomeOf resolution)
    | .died _ => .draining (IngressOutcomeOf resolution)

theorem egress_resolution_phase_table
    (resolution : ByteEgressResolution demand occurrence loan) :
  EgressPhaseAfter resolution =
    match resolution.disposition with
    | .continue => .idle
    | .failed _ => EgressDispositionPhase resolution
    | .cancelled _ => EgressDispositionPhase resolution
    | .closed _ => EgressDispositionPhase resolution
    | .died _ => EgressDispositionPhase resolution

theorem ingress_transition_preserves_conservation
    (step : ByteIngressTransition before after) :
  after.conservation

theorem egress_transition_preserves_conservation
    (step : ByteEgressTransition before after) :
  after.conservation

theorem ingress_resolution_consumes_exact_token
    (step : ByteIngressTransition before after) :
  ResolvingIngressStep step -> ConsumesExactlyOneResolveToken step

theorem egress_resolution_consumes_exact_token
    (step : ByteEgressTransition before after) :
  ResolvingEgressStep step -> ConsumesExactlyOneResolveToken step

theorem no_ingress_step_after_terminal :
  state.phase = .terminal outcome -> ¬ByteIngressTransition state after

theorem no_egress_step_after_terminal :
  state.phase = .terminal outcome -> ¬ByteEgressTransition state after
```

An ingress adapter turns each positive partial read into one `chunk`; EOF and
failure are distinct terminal events, while a zero-byte nonterminal completion
is a provider frontier and fabricates no byte. An egress process retains the
unaccepted suffix. A positive partial write moves exactly that prefix from its
pending ledger to its committed ledger; retry addresses only the remaining
suffix. `pending` moves no byte and requires an external readiness/completion
frontier before another internal attempt. It is an intermediate child-lifecycle
event, not a completed dependent result; the outstanding occurrence and its
suffix remain live while pending.

The transition constructors are phase indexed: `start` is idle-to-in-flight;
`pending` and `readiness` preserve the exact occurrence and loan; `resolve`
consumes its resolve token once; queue/delivery steps conserve the displayed
ingress partition; and terminal steps require no live occurrence plus an exact
terminal disposition. Failure, cancellation acknowledgement/race, close,
interruption, fault, and death resolve through `Byte*Resolution`. Each carries
the exact completed prefix plus residual loan/credit/suffix disposition; a
provider which guarantees zero transfer on one outcome supplies that stronger
`providerLaw`. No model invents a prior success to account for a partial effect.

The standard contracts prove prefix conservation, order, no fabrication,
duplication or loss, exact-once terminal disposition, bounded buffering, and a
carefully scoped functional chunking law:

```lean
theorem ingress_completed_functional_rechunk
    (completed : CompletedFunctionalFlows left right)
    (sameBytes : Concat left = Concat right)
    (sameTerminal : Terminal left = Terminal right) :
    EqualAfterErasingTimingCapacityAndCancellationCuts left right

theorem capacity_aware_ingress_rechunk
    (source : IngressExecution) (capacity : PositiveCapacity) :
    EveryChunkFitsCredits (splitForCapacity source capacity) capacity ∧
    RefinesWithMappedPrefixAndCancellationCuts
      (splitForCapacity source capacity) source

theorem egress_functional_rechunk :
    SameOfferedBytes left right ->
    CoupledWriteOutcomePrefixAndCancellationHistories left right ->
    EqualCommittedByteProjectionUnderMappedCuts left right

theorem egress_possible_projections :
    SameOfferedBytes left right ->
    SameProviderOutcomeSpace left right ->
    PossibleCommittedProjections left = PossibleCommittedProjections right

theorem egress_partial_conservation (s : ByteEgressState) :
  s.offered = s.committed ++ InFlightRequestedBytes s.phase ++ s.queued

theorem parser_chunking_invariant
    (parser : StreamingParser alpha) (extensional : ChunkExtensional parser) :
    SameFunctionalByteProjection left right ->
    SameParseResultAndRemainder parser left right
```

Concatenated bytes and a terminal marker do **not** imply asynchronous
bisimulation: chunk boundaries change capacity, readiness and cancellation cut
points, and peak resource use. The functional theorem erases exactly those
facets. Capacity-aware theorems instead map every prefix/cancellation point and
permit an adapter to split a large provider completion before bounded enqueue;
their resource certificate accounts for the transformed slots and bytes.
Parsers which expose feed-call boundaries or per-feed diagnostics are not
`ChunkExtensional`; they use the full mapped-cut theorem instead of the
functional parser corollary.

This is a process/channel contract even when the selected provider uses a
blocking call. Overlapped Win32 I/O, readiness loops, completion ports, socket
fragments, file reads, and a synchronous loop refine the same byte flow. Line
splitting, UTF decoding, parsing, compression, and framing are ordinary child
processes above it. Consequently changing the I/O strategy does not change a
precious parser or codec specification, and a later asynchronous realization
does not require inventing a second semantics.

Network semantics has one exhaustive transition family. No driver or proof may
invoke a channel triple outside its matching constructor:

```lean
inductive NetworkTransition (plan : ProcessPlan registry boundary) :
    LogicalProcessNetwork plan -> LogicalProcessNetwork plan -> Type
  | processStep (step : ExactLocalProcessTransition plan before after)
  | spawn (step : ExactBoundChildSpawnTransition plan before after)
  | send (step : ExactChannelSendTransition plan before after)
  | receive (step : ExactChannelReceiveTransition plan before after)
  | commit (step : ExactBoundaryCommitTransition plan before after)
  | requestCancel (step : ExactCancellationRequestTransition plan before after)
  | acknowledgeCancel (step : ExactCancellationResolutionTransition plan before after)
  | timeout (step : ExactTimeoutRaceTransition plan before after)
  | interrupt (step : ExactInterruptTransition plan before after)
  | fault (step : ExactFaultTransition plan before after)
  | environmentViolation
      (step : ExactEnvironmentViolationTransition plan before after)
  | childLifecycle (step : ExactChildLifecycleTransition plan before after)
  | processTermination (step : ExactProcessTerminationTransition plan before after)
  | channelClose (step : ExactChannelCloseTransition plan before after)
  | senderDeath (step : ExactSenderDeathTransition plan before after)
  | receiverDeath (step : ExactReceiverDeathTransition plan before after)
  | channelDeath (step : ExactChannelDeathTransition plan before after)
  | drop (step : ExactDropDispositionTransition plan before after)
  | reroute (step : ExactRerouteTransition plan before after)
  | coalesce (step : ExactCoalescingTransition plan before after)
  | join (step : ExactJoinTransition plan before after)
  | detach (step : ExactDetachTransition plan before after)
  | restart (step : ExactRestartTransition plan before after)

def NetworkTransition.allocatedNominals :
    NetworkTransition plan before after -> Finset LogicalNominal

structure NetworkStep (plan : ProcessPlan registry boundary)
    (before after : LogicalProcessNetwork plan) where
  transition : NetworkTransition plan before after
  fresh : Disjoint transition.allocatedNominals before.usedNominals
  historyExact : after.usedNominals =
    before.usedNominals ∪ transition.allocatedNominals
```

Each constructor carries exact pre/post worlds, endpoint incarnations, the
demand/channel embedding, occurrence and resolve token, lifecycle authority,
and obligation equation. Routing coverage proves every endpoint input/output
enters through exactly one constructor: no fabrication, bypass, or unclassified
death is possible.

`allocatedNominals` is definitionally empty for nonallocating transitions and
contains every new process generation, channel epoch, local/child/message
occurrence, restart identity, and coalesced replacement for allocating ones.
Thus freshness is a fact about the exact before/after transition and every other
step preserves history by `historyExact`; no ambient predicate can reinterpret
it as current-live freshness. A finite physical ID namespace may reuse numeric
slots only with a fresh logical generation and a driver proof that stale physical
events fail the generation/session check.

Channel contracts therefore give process basic blocks their entry and exit
conditions. A process transition may be authored as arbitrary assembly, a
standard driver path, or a proved macro; its local proof ends at
`SenderPost * Escrow` or begins at `ReceiverPre * Escrow`. It need not reopen the whole
network invariant.

These contracts are the process-level peer of typed basic-block edges. Lowering
maps them to queue memory, atomics, callbacks, API completions, or direct jumps
and proves the physical transition realizes the same pre/post relation. Channel
types may mention logical shared state and obligations, never unproved physical
aliasing.

### API calls as child processes

The standard library models an API operation as a nominal child protocol, not an
atomic function with an oversized result sum. Protocol values are stored in a
universe-stratified registry; child requests carry keys, never recursively embed an
arbitrary `ProcessSpec`. A realization plan may start, cancel, or supervise a
child occurrence and maps its exhaustive lifecycle back to one abstract demand
result, interruption, fault, or environment violation.

```lean
structure ChildRequest (registry : ProtocolRegistry) where
  key : registry.Key
  request : (registry.protocol key).Request

structure LocalDemandOccurrence
    (plan : ProcessPlan registry boundary)
    (parentKind : plan.ProcessKind)
    (parent : ProcessRef plan.toProcessTopology parentKind)
    (demand : (registry.protocol (plan.protocolKey parentKind)).Demand) where
  id : ParentLocalDemandId parent demand

structure ChildDemandBinding
    (plan : ProcessPlan registry boundary)
    (parentKind : plan.ProcessKind)
    (parent : ProcessRef plan.toProcessTopology parentKind)
    (demand : (registry.protocol (plan.protocolKey parentKind)).Demand)
    (occurrence : LocalDemandOccurrence plan parentKind parent demand)
    (request : ChildRequest registry) where
  childInitial : Nonempty
    (ExactInitialProtocolRun (registry.protocol request.key) request.request)
  realizesDemand : ChildRequestRealizesParentDemand parent occurrence request
  classify : forall outcome : ExhaustiveProtocolLifecycleOutcome
      (registry.protocol request.key) request.request,
    ParentEventOrNonreturningDisposition
      (registry.protocol (plan.protocolKey parentKind)) demand outcome
  preservesReflects : PreservesAndReflectsEveryAllowedChildResultChoice classify
  resources : ExactChildResourceObligationAndCancellationTransfer
    parent occurrence request classify

structure ChildOccurrence (plan : ProcessPlan registry boundary)
    (request : ChildRequest registry) where
  parentKind : plan.ProcessKind
  parent : ProcessRef plan.toProcessTopology parentKind
  parentDemand : (registry.protocol (plan.protocolKey parentKind)).Demand
  occurrence : LocalDemandOccurrence plan parentKind parent parentDemand
  binding : ChildDemandBinding plan parentKind parent parentDemand occurrence request
  kind : plan.ProcessKind
  protocol : plan.protocolKey kind = request.key
  ref : ProcessRef plan.toProcessTopology kind
  live : LiveChildAt plan ref parent occurrence

inductive ChildLifecycleEvent (occurrence : ChildOccurrence plan request)
  | pending
  | intermediate (event : IntermediateEvent request.key)
  | succeeded (result : TerminalSuccess request.key request.request)
  | failed (failure : TerminalFailure request.key request.request)
  | cancellationAcknowledged (reason : CancelReason)
  | interrupted (reason : InterruptReason)
  | faulted (fault : ChildFault)
  | environmentViolation (violation : EnvironmentViolation)
  | died (disposition : ChildDeathDisposition occurrence)
```

Internal children are correlated to the exact local demand of their exact
parent incarnation. They are not indexed by the exported root demand namespace.
`ProcessPlan` carries a partial `boundaryProjection` from selected root-local
occurrences to `DriverBoundary` occurrences; nested and flattened internal
demands remain private. Result routing, cancellation authority, outstanding-
child accounting, and lifecycle custody use the parent-local occurrence. The
execution-complete simulation proves the exported projection is exact.

The binding—not a child key alone—authorizes spawn. It proves the exact request
is initially valid and realizes the parent demand, exhaustively classifies every
child terminal result, failure, interruption, cancellation acknowledgement/race,
fault, violation, and death as the precise parent result/event or a named
non-returning disposition, preserves and reflects result choices, and carries
the matching resource/obligation/cancellation equation. Spawn, routing,
occurrence erasure, simulation, and physical lowering all consume this same
binding.

`start` consumes spawn authority and a proved initial request, allocates a fresh
`ChildOccurrence`, and produces its private initial state. Only a terminal
lifecycle transition produces a terminal projection. Cancellation operations
require the exact live occurrence and cancellation authority; a mere request
does not prove acknowledgement or recover its resources.

`NetworkTransition.childLifecycle` is indexed by the complete
`ChildLifecycleEvent` family. Success/failure/ordinary termination consumes live
lifecycle authority, establishes the exact terminal state and parent event,
transfers or disposes every resource and obligation, and only then enables join
or restart. The event's exact terminal result, cancellation reason, interruption
reason, fault, or violation is stored in the resulting protocol-indexed
`ProcessLifecycle`; a death disposition supplies its exact `ProcessDeathReason`.
Joins, supervisors, and audits therefore do not reconstruct an ending from a
possibly nondeterministic terminal relation or search another process's history.
`processTermination` performs the corresponding operation for a non-child/root
instance; ordinary close is distinct from endpoint death. This storage is
transition-generated and imposes no additional payload bookkeeping on an
ordinary protocol author.

A `WriteFile` process can remain pending, commit a partial effect, return a
dependent count, fail, be cancelled/interrupted, violate its environment
contract, or terminate. A Vulkan submission process can acquire resources, wait
on semaphores, become device-lost, and transfer obligations. A pure zlib process
can consume and yield chunks without platform vocabulary.

A synchronous API suspends its parent until the child reaches a terminal
projection. An asynchronous API exposes intermediate observations and
cancellation. High-level monadic notation is sequential child-process
composition; parallel weaving starts independent children; platform ABI calls
and custom assembly routines are lower realizations of the same protocol.

An optional view facet is pure. It may be evaluated, duplicated, coalesced, or
discarded without changing platform resources or producing an observation.
Processes without a desired-state projection use `view := none`.

Step emissions name only portable logical observations. Pure state transitions
do not silently emit physical effects. A driver commit is the sole transition
allowed to change provider resources or append a committed external observation.

### Erlang/OTP-derived lifecycle and mailbox patterns

Grass adopts precise OTP ideas where they provide reusable process semantics;
it does not model the BEAM. The source anchors are listed in
[REFERENCES.md](REFERENCES.md).

**Signal order and mailbox selection.** A channel profile states its ordering
guarantee explicitly. The Erlang-shaped profile preserves send order only from
one sender incarnation to one receiver incarnation; it invents no global order
between senders. Every signal has a fresh occurrence even when payloads are
equal. Selective receive consumes the oldest matching occurrence while every
skipped occurrence retains order, escrow, obligations, and resource charge:

```lean
structure SelectiveReceive (mailbox : Mailbox channel) (accepts : Message -> Prop) where
  selected : Option (Occurrence channel)
  firstMatching : selected = mailbox.findFirst accepts
  residual : Mailbox channel
  exactResidual : residual = mailbox.eraseSelected selected
  skippedPreserved : EverySkippedOccurrenceRetainsOrderCustodyAndCharge
  scanWork : ResourceCharge .requestWork mailbox.scannedPrefixLength
```

Postponement moves the current event to a typed queue and retries it only on a
named state change. Neither mechanism is free: unbounded mailboxes or postponed
sets fail resource/progress gates. Capacity credit supplies backpressure or an
explicit overflow disposition. Priority delivery, if selected, is a distinct
channel profile and cannot silently weaken ordinary ordering.

**Correlated calls and late replies.** A synchronous call is one child-demand
occurrence plus an affine reply reference. A timeout resolves the caller's wait
race but does not prove the callee stopped or prevent a late reply. The winner
must cancel, monitor, drain, reroute, or drop that exact reply occurrence under
a declared disposition. A cast merely lacks a reply obligation; it still has
failure, capacity, custody, and effect obligations.

**Links, monitors, and supervision.** Monitors are asymmetric observation;
links are symmetric failure coupling; trapping an exit converts only declared
exit classes into mailbox occurrences. Distinct monitors produce distinct
`DOWN` occurrences. `oneForOne`, `oneForAll`, and `restForOne` are reusable weave
combinators with exact kill/restart sets, child start/reverse-shutdown order,
fresh incarnations, dynamic-child schemas, shutdown escalation, and a bounded
restart-intensity window. Exceeding the window is a supervisor outcome, not an
infinite silent restart loop.

The valuable principle is typed termination, not “let it crash”:

```lean
inductive TerminationMode
  | cooperative
  | forcedAtSafePoint
  | faulted

structure ProcessTerminationContract (p : ProcessSpec) where
  SafePoint : p.State -> Prop
  Cause : Type
  premises : TerminationPremiseFamily p Cause
  requested : Cause -> p.State -> Prop
  permitted : TerminationMode -> Cause -> p.State -> Prop
  noArbitraryDeath : forall mode cause state,
    permitted mode cause state -> SafePoint state ∨ mode = .faulted
  disposition : forall mode cause state,
    permitted mode cause state -> TerminalDisposition p state
  exactTransfer : DispositionTransfersAllStateResourcesLoansAndObligations disposition
  observable : DispositionProducesExactTerminalObservations disposition
  reachesSafePoint : forall cause run,
    requested cause run.current ->
    TerminationPremises p cause run ->
    Eventually run (fun state => SafePoint state ∧ permitted .cooperative cause state)
  escalation : forall cause run,
    CancellationDeadlineExceeded p cause run ->
    NamedEscalationOrIsolationDisposition p cause run

inductive TerminationDemand (p : ProcessSpec)
  | ordinary
  | cooperative (causes : Type) (premises : TerminationPremiseFamily p causes)
  | supervised (policy : SupervisorPolicy)
  | versioned (versions : VersionFamily)

```

This supports theorems of the form “this process may terminate only at these
points, and under these scheduler/environment/callee-settlement premises it will
reach one.” Cooperative cancellation is therefore a liveness theorem plus an
exact terminal custody theorem. Forced termination is legal only at a proved
safe point, or else uses a separately modeled fault containment/escalation path;
it never retroactively validates arbitrary partially executed instructions.
Supervisors consume this contract when shutting down, restarting, or isolating
children.

This sophistication is capability-driven. `ProcessCorrect` itself retains only
ordinary invariant, terminal, observation, demand, and progress facts. A
process plan attaches `TerminationFacet` only when the process exports a
cancellation/restart/upgrade promise or another component relies on one. The
ordinary facet is derived from the existing terminal/lifecycle proof. Pure
serial functions, straight-line helpers, and uncancellable leaf processes gain
no new author obligation; standard I/O, timer, worker, and supervision protocols
reuse library facets.

Cancellation policy is compositional metadata, not a mandatory field of every
process. A cancellation request is an affine occurrence: while execution is in
an uncancellable region it may be latched as `PendingCancellation`, but it may
not be silently dropped or acted upon at an arbitrary instruction. A declared
cancellation point observes the exact request/result race and either consumes
that occurrence into a proved terminal disposition or proves that no request is
pending and continues. The summary exposed by a process is intentionally small:

```lean
inductive CancellationMask
  | uncancellable
  | cancellationPoint
  | interruptible

structure CancellationSummary (p : ProcessSpec) where
  entryMask : CancellationMask
  exitMask : CancellationMask
  SafePoint : p.State -> Prop
  pendingCustody : PendingCancellationCustody p
  delay : CancellationDelayBoundOrEnvironmentPending p SafePoint
  disposition : CancellationDispositionAt p SafePoint
  exportedContract : Option (ProcessTerminationContract p)
  exportedContractExact : forall contract,
    exportedContract = some contract ->
    ContractExactlySummarizesCancellation
      contract SafePoint pendingCustody delay disposition

structure CancellationBackedContract (p : ProcessSpec) where
  summary : CancellationSummary p
  contract : ProcessTerminationContract p
  exact : ContractExactlySummarizesCancellation
    contract summary.SafePoint summary.pendingCustody
      summary.delay summary.disposition

inductive TerminationFacet (correct : ProcessCorrect p) : TerminationDemand p -> Type
  | ordinary : TerminalTransitionsHaveExactDisposition correct ->
      TerminationFacet correct .ordinary
  | cooperative (backed : CancellationBackedContract p) :
      TerminationFacet correct
        (.cooperative backed.contract.Cause backed.contract.premises)
  | supervised (backed : CancellationBackedContract p)
      (policy : SupervisorPolicy) :
      SupervisorConsumesTerminationContract policy backed.contract ->
      TerminationFacet correct (.supervised policy)
  | versioned (handoff : VersionHandoff p versions) :
      TerminationFacet correct (.versioned versions)

def CancellationSummary.seq
    (left : CancellationSummary p) (right : CancellationSummary q) :
    CancellationSummary (p |> q) :=
  composeCancellationAcrossBoundary left right

theorem CancellationSummary.seq_assoc ... :
  seq (seq a b) c = transportProcessAssoc (seq a (seq b c)) := ...

def CancellationSummary.toCooperativeTerminationFacet
    (summary : CancellationSummary p) (correct : ProcessCorrect p)
    (contract : ProcessTerminationContract p)
    (exports : summary.exportedContract = some contract) :
    TerminationFacet correct (.cooperative contract.Cause contract.premises) :=
  by
    have exactSummary := summary.exportedContractExact contract exports
    exact .cooperative { summary, contract, exact := exactSummary }

def CancellationSummary.toSupervisedTerminationFacet
    (summary : CancellationSummary p) (correct : ProcessCorrect p)
    (policy : SupervisorPolicy)
    (exports : exists contract, summary.exportedContract = some contract)
    (compatible : forall contract,
      summary.exportedContract = some contract ->
      SupervisorConsumesTerminationContract policy contract) :
    TerminationFacet correct (.supervised policy) := by
  rcases exports with ⟨contract, exactContract⟩
  exact .supervised
    { summary, contract,
      exact := summary.exportedContractExact contract exactContract }
    policy (compatible contract exactContract)
```

The constructor for an ordinary serial function supplies the weakest summary:
it is uncancellable, has no internal safe point, and promises only to return or
fault according to its ordinary process contract; its `exportedContract` is
`none`. This creates no additional proof field for its author. Standard
combinators calculate stronger summaries and export `some contract` only when
their composed progress and disposition premises are sufficient.
The cooperative and supervised facet constructors retain the complete
`CancellationBackedContract`, including the exact summary witness. Runtime and
proof-level cancellation transitions consume that retained summary to identify
the affine request occurrence, safe state, delay premise and disposition; the
bridge cannot discard it after manufacturing a liveness contract.
In particular,

```text
uncancellable |> cancelpoint |> uncancellable
```

is a process with a cancellation policy. A request arriving in the first
region is retained until the middle point. At that point cancellation can
terminate with its exact custody disposition; if no request is pending, the
second region runs and the process next terminates normally. A request arriving
after that point is retained until the process's terminal boundary, where the
ordinary terminal disposition must classify it. A bounded-cancellation claim
therefore also needs the two uncancellable regions to terminate within named
bounds or under named environment premises. A forever-blocking uncancellable
region cannot acquire eventual cancellation merely by being sequenced with a
later point.

The same algebra covers choice, loops, parallel composition, and supervision:

- a branch join exposes only the safe points and delay guarantee common to all
  reachable branches, unless the branch result proves which stronger policy
  applies;
- a loop promises cooperative cancellation only if every fair continuing cycle
  crosses a cancellation point, or the loop has an independent termination
  proof;
- parallel composition retains one occurrence per addressed live incarnation
  and joins only after every required child disposition is proved;
- a supervisor may strengthen a cooperative policy with a deadline and named
  escalation, but cannot manufacture a safe forced stop;
- inlined and fractally flattened process graphs preserve the calculated
  summary, so cancellation reasoning does not depend on whether a component was
  authored as a function, process, macro, or subgraph.

First-class assembly participates by identifying CFG control points at which
registers, stack, loans, resources, and obligations satisfy a terminal or
continuation contract. Instructions between such points are simply an
uncancellable region. The lowering proof maps each logical cancellation point
to one of those typed block boundaries and proves that callbacks, faults, and
interrupts cannot counterfeit it.

**State-machine actions and timeout races.** Reusable combinators cover
state-entry actions, internal events, named timeouts, state-scoped timeouts,
event timeouts canceled by any event, and postponed-event retry. Timers are
fresh child occurrences. Cancellation races with expiry; late timeouts are
rejected by reference/generation mismatch or handled explicitly. A zero timeout
is a queued internal event with declared priority, not wall-clock simultaneity.

**Version handoff.** OTP hot-code upgrade suggests a useful explicit Grass
boundary. `VersionHandoff` proves state migration, mailbox occurrence
preservation/disposition, resources and obligations, protocol compatibility,
and finite/infinite continuation. Old and new artifacts remain exact identified
values; code-pointer replacement and rollback are lower platform operations.

Grass rejects unbounded mailboxes, “let it crash” as proof, implicit distributed
delivery, and scheduler reductions as fairness. Ports and native calls remain
child/provider protocols with explicit interruption and nonreturning behavior.
These patterns enrich one process algebra rather than create an Erlang backend.

## 4. Application proof package

The application author supplies only semantic facts specific to the process:

```lean
structure ProcessCorrect (p : ProcessSpec) where
  Invariant : p.State -> Prop
  initial : ∀ request s issued emitted,
    p.Initial request s issued emitted -> Invariant s
  initialDemands : ∀ request s issued emitted,
    p.Initial request s issued emitted -> DemandsWellFormed issued
  preserved : ∀ s event s' demands emitted,
    Invariant s -> p.Step s event s' demands emitted -> Invariant s'
  terminal : ∀ request s result,
    Invariant s -> p.Terminal request s result -> TerminalAccepts p result
  terminalNoStep : NoProcessStepFromTerminal p
  viewAccepts : OptionalViewAccepts p Invariant
  observationsAccept : ∀ run,
    ProcessRun p run -> TraceAccepts p run.observations
  demandsWellFormed : ∀ step, StepOf p step -> DemandsWellFormed step.demands
  progress : MeetsProcessProgress p

theorem ProcessRun.observationCausality
    (run : ProcessRun p request) :
    EveryObservationOccurrenceIn run.observations
      (fun occurrence =>
        UniqueGeneratingInitialOrStepSegment p run occurrence) :=
  ProcessRun.concatSegments_has_unique_origin run

structure ProcessNetworkAdequate {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources)
    (plan : ProcessPlan registry boundary) where
  initial : ∀ input, AdmissibleInput spec input ->
    Nonempty (ExactInitialNetworkAndRootRun plan input)
  zeroStepTerminal : EveryInitiallyTerminalRequestHasExactZeroStepRun plan
  transitionCoverage : EveryEnabledNetworkTransitionRepresented plan
  childChoiceComplete : EveryReachableChildResultAndLifecycleRepresented plan
  maximalExecutions : EveryInitialNetworkHasMaximalExecution plan
  networkProgress : MaximalNetworkExecutionsMeetProgressOrFrontier spec plan

structure ProcessNetworkSimulation {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources)
    (plan : ProcessPlan registry boundary) where
  coupledExecutions : CoupledExecutionRelation plan spec
  preservesAndReflectsChoices : EnvironmentAndOccurrenceChoicesCoupled
  finiteInfiniteDivergent : CompleteExecutionShapesCoupled
  terminalFaultCancellationDeath : CompleteLifecycleOutcomesCoupled
  observations : ProjectedObservationsCoupled
  obligations : ObligationBehaviorCoupled

structure ResourceAxisRealization
    {R : Type u} [ResourceModel R] {resources : R}
    (spec : SpecProcess resources)
    (plan : ProcessPlan registry boundary)
    (axis : ResourceAxisName)
    (required : axis \u2208 spec.resourceSemantics.requiredAxes) where
  abstractSemantics : SelectedAxisSemantics resources axis :=
    spec.resourceSemantics.lookup axis required
  metric : ResourceMetric plan
  metricAxis : metric.Axis
  metricAxisExact : metric.axisName metricAxis = axis
  representation : AbstractResourceValueRepresentedByMetric
    abstractSemantics metric metricAxis
  initial : EveryInitialHoldingRepresentsSelectedResourceState
  transitions : EveryResourceTransitionImplementsSelectedPolicy
  exhaustion : ConcreteExhaustionIffSelectedExhaustionPolicy
  terminal : TerminalHoldingsImplementSelectedLifecycle

structure ResourceAxisRealizationFamily
    {R : Type u} [ResourceModel R] {resources : R}
    (spec : SpecProcess resources)
    (plan : ProcessPlan registry boundary) where
  realizes : forall axis,
    (required : axis \u2208 spec.resourceSemantics.requiredAxes) ->
    ResourceAxisRealization spec plan axis required
  concreteKeyInjective : Function.Injective
    (fun key : ConcreteMetricKey plan => key.axisName)
  requiredKeyExact : EveryRequiredAxisHasExactlyOneConcreteMetricKey
    spec.resourceSemantics.requiredAxes realizes concreteKeyInjective
  noDummyAxes : EveryConcreteMetricAxisHasNamedAbstractOrAuditPurpose plan
  rootBound : ConcreteRootBoundFollowsFromSelectedLimits spec plan realizes

structure ProcessPlanRealizes {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources)
    (plan : ProcessPlan registry boundary) where
  processProofs : ∀ kind,
    ProcessCorrect (registry.protocol (plan.protocolKey kind))
  composition : WeaveCorrect plan
  adequate : ProcessNetworkAdequate spec plan
  simulation : ProcessNetworkSimulation spec plan
  demandMultiplicity : ConcreteOccurrencesEraseBijectivelyToAbstractBags plan spec
  childBindings : EverySpawnTransitionCarriesExactChildDemandBinding plan
  requirementSubstitution : RequirementSubstitution spec
  demands : MeetsAllIndependentDemands plan spec
  resources : ResourceAxisRealizationFamily spec plan
```

`observationCausality` is generic bookkeeping, not an application proof field.
It retains the exact initial/transition segment which generated each observation
occurrence through later weaving, flattening, serialization, machine
simulation, and projection. Application invariants establish facts about those
segments; channel ordering and composition lift them to whole-trace claims such
as exact in-order stdout. Physical effects hidden from the product projection
remain in the audit trace and retain the same origin relation.

Libraries provide induction/coinduction principles, irrelevant-event stuttering,
result correlation, cancellation, invariant framing, and deterministic
`update` simplification. A functional update proof normally reduces to initial
invariant, invariant preservation, view correctness, and process progress.

Safety of memory, ABI, platform resources, concurrency, and raw instructions is
not smuggled into `Invariant`; those remain independent lower-layer demands.

### One algebra, two plan-authoring modes

The process network is Grass's universal internal semantic form, but an explicit
network is not mandatory application ceremony. Every authoring source elaborates
to the same `ProcessRealization` and expose the same stable `DriverBoundary` to
platform and assembly proofs:

```lean
structure ClosedBlendProvenance {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources)
    (boundary : DriverBoundary)
    (registry : ProtocolRegistry)
    (plan : ProcessPlan registry boundary)
    (correct : ProcessPlanRealizes spec plan) where
  Presentation : Type
  Graph : Presentation -> Type
  shaped : Presentation
  graph : Graph shaped
  localCertificates : ExactLocalCertificatesForGraph shaped graph
  portableClosure : EveryReachableAbstractFrontierClosed shaped graph
  requirementUnion : ExactRequirementResourceAndObligationUnion shaped graph
  elaboratesExact : ExactClosedBlendElaboration
    shaped graph registry plan correct

inductive ProcessPlanSource {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources)
    (boundary : DriverBoundary)
  | sequential
      (program : DirectRelationalProgram boundary)
      (correct : DirectProgramRealizes spec program)
  | explicit
      (registry : ProtocolRegistry)
      (plan : ProcessPlan registry boundary)
      (correct : ProcessPlanRealizes spec plan)
  | blended
      (registry : ProtocolRegistry)
      (plan : ProcessPlan registry boundary)
      (correct : ProcessPlanRealizes spec plan)
      (provenance : ClosedBlendProvenance spec boundary registry plan correct)

structure ProcessRealization {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources) where
  boundary : DriverBoundary
  registry : ProtocolRegistry
  plan : ProcessPlan registry boundary
  correct : ProcessPlanRealizes spec plan
  requirementSubstitution : RequirementSubstitution spec
  origin : ProcessPlanSource spec boundary
  originSound : ElaboratesTo origin registry plan correct
```

The `.blended` case is the only origin produced by staged portable closure. It
retains the exact dependent presentation, graph, local certificates, recursive
frontier closure, accumulated requirements, and elaboration into this very
`registry`, `plan`, and `correct` value. An extensionally similar graph cannot
donate its provenance. Sequential and explicitly authored plans retain their
own origins and do not pretend to have blend scopes.

The ordinary authoring interface is a typed sequential effect machine:

```lean
inductive SequentialDecision
    (boundary : DriverBoundary) (State Terminal : Type)
  | internal (next : State) (observations : List boundary.Observation)
  | effect (demand : EffectDemand boundary)
      (resume : EffectResult demand -> State)
  | terminal (result : Terminal)

structure SequentialMachine (boundary : DriverBoundary) where
  State Request Terminal : Type
  initial : Request -> State
  decide : State -> SequentialDecision boundary State Terminal
  invariant : State -> Prop
  initialInvariant : forall request, invariant (initial request)
  internalPreserves : EveryInternalDecisionPreserves invariant decide
  effectResumes : EveryEffectResultPreserves invariant decide
  progress : SequentialDecisionProgress decide
```

Custom headers, multi-pass algorithms, retry policy, and custom error handling
normally change `State` and `decide`; they do not require an actor graph or bag
equations. Standard typed effect operations are extensible. Adding a new effect
protocol requires one reusable dependent result/boundary constructor, not a new
proof for every program using it.

`SequentialAdapter.elaborateMachine` translates this syntax to the more general
relational representation below. Because a sequential decision has at most one
newly issued effect and its continuation is indexed by that exact effect's
result, occurrence identity, pending multiplicity, child binding, and terminal
disposition are generated structurally. Its generic theorem transports a
`SequentialMachineRealizes spec machine` proof to
`DirectProgramRealizes spec (elaborateMachine machine)`.

The lower-level sequential source consumed by the adapter has structured dynamic effects;
an inventory of possible sites is not treated as the effects issued by a
particular execution:

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
```

`Initial` and `Step` return the exact dynamic demand multiset and observation
segment for that execution. `initialEquation` and `transitionEquation` connect
those outputs to `Pending`; equal-valued demands retain multiplicity through
distinct occurrences supplied by the dependent binding. The adapter generates
nominal identities, child records, escrows, and topology from this evidence. It
does not infer demand issuance from a finite syntactic inventory.

Sequential authoring is intended for straight-line and ordinary sequential
CFGs. It composes standard relational API Hoare contracts and an extensional
trace contract without asking the author to name process kinds, channels,
population, or escrow. `SequentialAdapter` elaborates it to the canonical
one-root network with identity-correlated API children and proves the complete
`ProcessPlanRealizes`; that graph and proof are generated, inspectable, and not
application-maintained.

Small spikes may request this route with one explicit closing clause:

```lean
structure StandardSequentialDerivation (spec : SpecProcess resources) where
  machine : SequentialMachine spec.driverBoundary
  realizes : SequentialMachineRealizes spec machine
  syntaxOrigin : machine = SequentialSyntax.elaborate spec.suite
  unique : ∀ other : SequentialMachine spec.driverBoundary,
    SequentialSyntax.ValidDerivation spec.suite other ->
    other = SequentialSyntax.elaborate spec.suite

def SequentialAdapter.deriveStandard
    (spec : SpecProcess resources) :
    Except NonCanonicalSequentialSuite (StandardSequentialDerivation spec)

def verified : VerifiedProgram spec := by
  verify_assembly plan
    deriving_standard_process_from spec
    with source
```

This is not ambient typeclass search. It is a total inspection of the exact
captured suite and succeeds only when the suite's DSL junctions select one
canonical sequential machine with a uniqueness theorem. Ambiguous concurrency,
scheduling, subprocess partition, or failure routing returns
`NonCanonicalSequentialSuite`; the author must then supply an explicit process
presentation. The generated `ProcessRealization.standard` retains
`syntaxOrigin`, so the final certificate cannot silently use a different graph.

The adapter does not discover boundaries, invariants, or correctness for an
arbitrary Lean relation. Its input is the structured effect/control vocabulary
of `DirectRelationalProgram` plus an already proved `DirectProgramRealizes`
witness. It maps each declared effect frontier through standard protocol/
channel combinators and transports the supplied proof. A standard spec builder
can register that package; a novel relation must supply it. If a use requires
inventing decomposition facts by tactic search, it is outside the adapter's
contract and needs an explicit plan or reusable combinator.

The canonical adapter fixture family includes a zero-effect transition,
duplicate equal-valued effects with distinct occurrences, initially pending
effects, issue-then-cancel, and result-plus-new-effect in one transition. Each
fixture checks the exact `Pending` equation and child binding in both execution
directions. Failure of those equations falls back to explicit process
authoring; no adapter proof may weaken them to set membership or site
possibility.

Explicit authoring is selected when independent state machines, supervision,
callbacks, cancellation, concurrency, or heterogeneous engines make the network
invariant economically useful. After elaboration there is no alternate direct
semantics, theorem path, or TCB. A program can move from synthesized degeneracy
to an explicit plan without changing `spec` or the stable assembly
`DriverBoundary`; a progress bar, Ctrl+C handler, or worker thread therefore
extends the same proof algebra rather than forcing a rewrite.

Standard specification constructors may register a unique canonical sequential
realizer:

```lean
structure StandardSequentialRealization {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources) where
  program : DirectRelationalProgram spec.driverBoundary
  correct : DirectProgramRealizes spec program

structure StandardRealizerEntry where
  R : Type u
  model : ResourceModel R
  resources : R
  key : StandardRealizerKey
  spec : @SpecProcess R model resources
  realization : @StandardSequentialRealization R model resources spec

structure StandardRealizerRegistry where
  entries : Array StandardRealizerEntry
  unique : forall left right,
    left ∈ entries -> right ∈ entries ->
    DefinitionalOrCanonicalSpecEquality left.spec right.spec -> left.key = right.key

structure ExactStandardRealizerLookup {R : Type u} [ResourceModel R]
    (registry : StandardRealizerRegistry) {resources : R}
    (spec : SpecProcess resources) where
  entry : StandardRealizerEntry
  member : entry ∈ registry.entries
  exactSpec : DefinitionalOrCanonicalSpecEquality entry.spec spec
  unique : EveryMatchingEntryHasKey registry spec entry.key

def ProcessRealization.standard
    (selected : ExactStandardRealizerLookup registry spec) :
    ProcessRealization spec :=
  ProcessRealization.sequential
    (selected.realization.transport selected.exactSpec).program
    (selected.realization.transport selected.exactSpec).correct
```

This interface has two deliberately different audiences.  The implementor of a
new standard constructor proves the `DirectRelationalProgram` equations once.
An application selecting that constructor does not rebuild or even name those
equations.  Its complete process-authoring surface is one expression:

```lean
def processRealization : ProcessRealization spec :=
  ProcessRealization.standard (Grass.Std.Realizers.lookupExact spec)
```

For a streaming filter such as gzip, the standard-library proof is itself
assembled from typed sequential-effect combinators.  Read, write, allocation,
and terminal combinators determine their dynamic demand occurrences, pending
bag equations, exact child bindings, and terminal dispositions by construction.
The constructor author supplies the filter's relational correctness, failure
coverage, resource bound, and progress proof; it does not hand-author process
identities, channels, escrow, or multiset arithmetic.  The selected compressor
then separately proves that its algorithm realizes that filter relation.

This is a proof-economics acceptance rule, not merely intended ergonomics:

- using a registered standard sequential specification must require one
  expression at the application process boundary;
- a standard typed effect combinator must generate its own occurrence and
  pending-effect bookkeeping;
- diagnostics may expand the generated process plan, but applications do not
  maintain it; and
- if an ordinary sequential application must fill the fields of
  `DirectRelationalProgram` directly, the relevant constructor or adapter is
  incomplete.

Novel sequential effect vocabularies still owe one reusable constructor proof.
Novel program semantics still owe `DirectProgramRealizes`.  Neither fact
justifies a second execution semantics or transfers generic adapter ceremony to
each application.

The low-level `DirectRelationalProgram` escape hatch is for genuinely
relational sequential machines that can issue or resolve several effects in one
transition. Ordinary serial programs use `SequentialMachine`; they do not fall
from a one-line registry lookup directly to manual multiset proofs.

This is proof-strategy inference, never platform/provider inference. The
platform plan remains an explicit value. The short closing form performs an
exact lookup in the named, closed `Grass.Std.Realizers.registry`, records the key
in the build manifest and certificate, and fails on absence. Registry construction
or extension proves key/spec uniqueness; open typeclass priorities play no role.
A project may name another proved merged registry explicitly. `using
sequential_process proof` remains available for a novel relational program.
Changing the standard realizer may rebuild replaceable proofs but cannot change
the precious specification or silently select an API provider.

### Flattening and fractal composition

Every proved process realization can be hidden behind one process protocol:

```lean
def ProcessRealization.flatten (r : ProcessRealization spec) : ProcessSpec

theorem flatten_correct (r : ProcessRealization spec) :
  ProcessCorrect r.flatten ∧
  BoundaryBisimilar r.flatten r.boundary ∧
  PreservesFiniteInfiniteFaultTerminalCancellationAndObligations r.flatten r

structure RegisteredProcess
    (r : ProcessRealization spec) (registry : ProtocolRegistry) where
  extended : ProtocolRegistry
  includeExisting : RegistryEmbedding registry extended
  key : extended.Key
  exact : extended.protocol key = r.flatten

def ProcessRealization.register
    (r : ProcessRealization spec) (registry : ProtocolRegistry) :
    RegisteredProcess r registry
```

The flattened process's private state is `LogicalProcessNetwork r.plan`; one
logical step is one exact `NetworkTransition`. Internal process identities,
channel occurrences, escrow, supervision, and scheduling are hidden. Only the
original external events, abstract demands/results, observations, faults, and
terminal behavior cross the boundary. `register` returns an extended registry,
an embedding of every existing key, and a fresh key whose protocol is exactly
the flattened process; it cannot pretend to insert into an arbitrary closed
registry. The returned key lets a subsystem be developed as a
network, flattened to a component, and composed fractally without exposing its
weave to its parent.

The canonical sequential adapter and flattening are inverse up to the complete
execution relation:

```lean
theorem flatten_sequential_roundtrip
    (program : DirectRelationalProgram boundary)
    (correct : DirectProgramRealizes spec program) :
  Bisimilar
    (ProcessRealization.sequential program correct).flatten
    program
```

This theorem, not a second semantic track, is why serial programs have a small
author surface.

### Why the process algebra is not restricted to runtime concurrency

Grass deliberately rejects a split in which sequential CFGs terminate their
semantic proof chain before the process model and only concurrent subsystems use
process semantics. The concern behind that proposal is valid—straight-line and
ordinary sequential authors must not maintain actor graphs, channel ledgers, or
scheduler proofs—but the split solves ceremony by sacrificing composition.

Sequential parsers, compilers, codecs, database plans, device setup, and error
pipelines still need local state ownership, typed intermediate boundaries,
failure/cancellation propagation, whole-pipeline progress, resource bounds, and
replacement theorems. If they use a different semantic substrate, composing
them with threads, callbacks, APIs, interrupts, or GPUs requires boundary
adapters and duplicates the failure, liveness, obligation, and observation
theory. Turning a serial subsystem concurrent later would reopen its proof chain
precisely when the system becomes large.

The adopted answer is one algebra with three independent choices:

- a sequential routine is authored and cached as an ordinary local Hoare CFG;
- its degenerate process realization is generated rather than authored; and
- a process proof graph may be serialized away, retained as runtime
  concurrency, or flattened as one child according to a proved lowering.

Thus no runtime queue or actor tax follows from using the graph as proof IR, and
no process annotation appears inside an ordinary straight-line block. Build
benchmarks must measure normalization and certificate replay; if the canonical
adapter is expensive, its representation/caching is defective. That is not a
reason to introduce a second execution, safety, liveness, or obligation
semantics.

Before flattening, the graph supplies a stronger partial-order theorem:

```lean
def Independent (world : LogicalProcessNetwork plan)
    (left right : EnabledTransition plan world) : Prop :=
  DisjointLocalInstances left right ∧
  CompatibleSharedAccess left right ∧
  DisjointChannelEscrows left right ∧
  DisjointOrCommutingObligations left right ∧
  ProviderEffectsCommute left right ∧
  BoundaryObservationsCommute left right

theorem independent_diamond
    (independent : Independent world left right) :
  ∃ afterRight afterBoth,
    Step world right afterRight ∧
    Step afterRight left.transport afterBoth ∧
    NetworkWorldEquivalent afterBoth (step (step world left) right.transport) ∧
    TraceRelatedBySwap independent

theorem syscall_linearizations_equivalent
    (a b : PhysicalRealization plan)
    (sameOrder : LinearizeSameProcessPartialOrder a.syscalls b.syscalls) :
  StrongObservedExecutionEquivalence a b
```

`ProviderEffectsCommute` is proved from the exact provider operation footprints,
handles/session identities, result dependencies, interruption laws, and
obligation transfers. Two calls do not commute merely because they have
different source labels. Same-handle operations, clock reads, cancellation
races, shared writes, ordered observations, or obligation handoffs normally
make `Independent` false.

The trace congruence is generated by adjacent independent swaps (a nominal
partial-order/Mazurkiewicz trace), preserving dependent result and occurrence
identity through each transport. Consequently two authored assembly programs
may use different schedules, worker assignments, batching, or syscall order and
still receive an economical strong-equivalence proof by refining the same
process graph. Optimization proves only that its syscall trace is another
linearization; it does not rediscover commutation after flattening. The
flattening and serial-scheduler theorems consume this graph-level result.

Flattening logical semantics does not by itself authorize a single-threaded
physical implementation of an arbitrary concurrent graph. That requires:

```lean
structure CompleteSerializations (r : ProcessRealization spec)
    (scheduler : RelationalSerialScheduler r.plan) where
  graphToSerial : forall graphExecution,
    ExistsCoupledSerialExecution scheduler graphExecution
  serialToGraph : forall serialExecution,
    ExistsCoupledGraphExecution r.plan serialExecution
  choices : PreservesOccurrenceResultAndLifecycleChoicesBothWays scheduler
  shapes : PreservesFiniteInfiniteDivergentAndMaximalExecutions scheduler
  obligations : PreservesObligationBehaviorBothWays scheduler
  observations : PreservesBoundaryObservationsBothWays scheduler
  independent : IndependentTransitionsFormDiamonds r.plan
  overlap : EveryOverlappingSerializedOperationHasLinearizabilityWitness r.plan

structure SerializablePlan (r : ProcessRealization spec) where
  scheduler : RelationalSerialScheduler r.plan
  complete : CompleteSerializations r scheduler
  progress : UnconditionalProgressCorrespondence scheduler r.plan

structure ResponsiveSerialSelection (serial : SerializablePlan r) where
  assumptions : NamedTimingAndFairnessAssumptions spec
  selection : ConcreteSerialScheduler serial.scheduler
  scheduleComplete : CompleteForEveryScheduleSatisfying assumptions selection
  responsive : PreservesConditionalNetworkProgress selection

def ProcessRealization.asSerialFunction
    (r : ProcessRealization spec)
    (serial : SerializablePlan r)
    (closed : FrontierFreeTerminatingRequestFamily r) :
    SerialFunctionContract

theorem asSerialFunction_correct
    (r : ProcessRealization spec)
    (serial : SerializablePlan r)
    (closed : FrontierFreeTerminatingRequestFamily r) :
    SerialExecutionRefinesFlattenedProcess
      (r.asSerialFunction serial closed) r.flatten

def ProcessRealization.serialize
    (r : ProcessRealization spec) (serial : SerializablePlan r) :
    DirectRelationalProgram r.boundary

theorem serialize_correct
    (r : ProcessRealization spec) (serial : SerializablePlan r) :
    DirectProgramRealizes spec (r.serialize serial)

theorem serialize_refines_flatten
    (r : ProcessRealization spec) (serial : SerializablePlan r) :
    Bisimilar (r.serialize serial) r.flatten

theorem serialize_as_child
    (r : ProcessRealization spec) (serial : SerializablePlan r) :
    ProcessRealization.sequential
      (r.serialize serial) (serialize_correct r serial)
      ≈ r
```

A genuinely serial graph discharges this canonically because at most one
internal transition is enabled. Concurrent graphs may discharge it through
execution-complete relational scheduling, commutation, and explicit
linearizability for overlap; otherwise they may still be
flattened as a specification component but must retain a concurrent physical
driver.

`serialize_correct` is the canned proof for a serial implementation of a
process graph. `serialize_refines_flatten` says that the generated executor has
the graph's complete external behavior, not merely the same successful result.
`serialize_as_child` is the fractal law: serialize a proved subsystem, normalize
that serial program through `SequentialAdapter`, and it can replace the original
subsystem in any larger network up to the same boundary equivalence. Standard
compiler pipelines normally discharge `SerializablePlan` from an acyclic stage
order plus bounded feedback/recovery edges; an author supplies only the unusual
dependency or progress argument.

The serial semantics is relational and retains every permitted schedule,
dependent result, lifecycle outcome, fault, cancellation, obligation behavior,
and maximal execution. Fairness is absent from unconditional bisimulation;
`ResponsiveSerialSelection` introduces only the named conditional assumptions.
A concrete deterministic scheduler generally proves directed refinement, not
bisimulation, unless all schedules it discards are connected by the supplied
independence/linearizability and observation-quotient theorems. Overlapping
operations never commute merely because a serial order was chosen.

### Process graphs as a proof-composition IR

A process plan describes proof decomposition, not a required runtime actor
architecture. Parsers, compilers, codecs, database operators, and other
sequential software may be developed as communicating logical subprocesses and
then flattened/serialized before machine lowering.

For example, a compiler plan may give a lexer ownership of source position and
token production, a parser token escrows and syntax/recovery results, an
elaborator typed-IR and obligation production, and optimization/lowering passes
extensional before/after contracts. The graph proves local invariants,
backpressure, exact error propagation, pass progress, and channel ownership.
`flatten_correct` exposes one compiler process; `SerializablePlan` yields an
ordinary single-threaded loop or CFG; no runtime queue, actor, or scheduler need
survive emission.

The language, accepted/rejected parse relation, diagnostics demanded by the
product, and compiler input/output equivalence may be precious. Lexer/parser
fusion, pass grouping, buffer sizes, pipeline scheduling, and physical queue
representations normally are not. A fused implementation and a staged pipeline
can prove strong equivalence by refining the same process partial order and
flattened boundary. This is the intended fractal use of the model: process
graphs are a compositional intermediate proof structure which may disappear
completely from execution.

## 5. Driver contract

A driver realizes a process using selected providers:

```lean
structure ProcessDriver {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources)
    (processes : ProcessPlan registry boundary)
    (realizes : ProcessPlanRealizes spec processes)
    (platform : PlatformPlan boundary.requirements)
    (program : GhostProgram boundary platform) where
  boundaryExact : DriverExposesExactly boundary processes realizes
  eventRefinement : PhysicalEventsRefine platform processes
  demandRefinement : DemandOccurrencesRefine processes platform
  resultCorrelation : CorrelatesEveryResult processes platform
  commitRefinement : PhysicalCommitsRefine processes spec platform
  cancellation : CancellationRefines processes platform
  reentrancy : CallbackInterleavingsRefine processes platform
  strategyBridge : ProcessStrategyBridge processes platform
  obligations : DriverObligationsClosed processes platform program
  channelRealization : ∀ edge, ChannelRealization
    (processes.channel edge) platform program
```

Each `ChannelRealization` is separately inspectable and cached. It contains the
physical queue/callback/direct-edge representation, send and receive
linearization points, staged partial-operation authority, the bijection between
logical occurrences and physical pending records, the resource-ledger equation,
ordering/race proof, and interruption/cancellation/death recovery. It cannot be
replaced by a driver-wide “channels correct” proposition.

Every realized demand has a dependent result type and a fresh occurrence. The driver
may batch, reorder independent demands, retry where the realization policy permits,
or coalesce pure renders. It may not fabricate a result, attach one result
to another occurrence, drop an externally observable demand, or commit an
unrequested effect. Commands which create resources or linear obligations name
their transfer/cancellation/disposition laws.

Callbacks and system messages enter only as typed events. Reentrancy is an
explicit interleaving theorem, never an implicit assumption that `update` cannot
be interrupted.

### Total cancellation and scoped-realization interfaces

Cancellation policy is indexed by the exact process graph and source occurrence
map. Names alone are insufficient:

```lean
structure CancellationPolicy
    (network : ProcessNetwork root)
    (source : MachineSource plan) where
  points : (id : network.cancellationDemand.Key) -> CancellationPointPolicy id
  sourceOccurrence : (id : points.Key) -> UniqueSourceOccurrence source id
  atomicRegions : FiniteMap AtomicRegionId BoundedAtomicRegion
  blockingCalls : (call : source.discoverPotentiallyBlockingCalls.Key) ->
    BlockingCallCancellationDisposition call points atomicRegions
  pointsExact : points.keys = network.cancellationDemand.keys
  callsExact : blockingCalls.keys = source.discoverPotentiallyBlockingCalls.keys
  routesTotal : EveryCancelFaultInterruptRouteClassified network source points
  progress : EveryRequestedCancellationReachesDispositionUnderDeclaredPremises
```

A call may be uncancellable only inside a named bounded atomic region. A
finish-current-frame policy states the exact completion premise and its
timeout/teardown alternative. Adding `Sleep`, a provider wait, a new retry loop,
or a cancellation point changes a discovered key family and rejects the old
policy. The elaborator checks occurrence identity; it never matches unscoped
strings.

Staged subsystem refinement receives a canonical scoped projection, not the
whole plan plus an advisory scope:

```lean
structure ScopedProcessPlan (whole : ProcessPlan root) (scope : ScopeId) where
  graph : whole.graph.induced scope
  imports : BoundaryImports whole scope
  exports : BoundaryExports whole scope
  demands : ScopedDemandFamily whole scope
  projectionExact : graph = whole.graph.induced scope

structure SubsystemRealization (scoped : ScopedProcessPlan whole scope) where
  implementation : ProcessImplementation scoped
  refines : implementation.Refines scoped
  boundaryExact : implementation.summary = scoped.exports.summary
  cacheInputsExact : CacheInputs implementation =
    {scoped.graph, scoped.imports.summaries, scoped.demands}

theorem SubsystemRealization.siblingInsensitive
    (edit : WholePlanEditOutside whole scope) :
    ScopedProcessPlan.project (edit.apply whole) scope =
      ScopedProcessPlan.project whole scope
```

This theorem is structural: an outside-scope edit leaves the induced nodes,
edges, imported summaries, and demand keys definitionally equal. An edit to a
shared boundary changes an imported summary and correctly invalidates the
subsystem.

### Derived global-loop invariant

The process decomposition supplies the interior proof for large global loops:

```lean
structure ProcessLoopInvariant
    (processes : ProcessPlan registry boundary)
    (realizes : ProcessPlanRealizes spec processes)
    (driver : ProcessDriver spec processes realizes platform program)
    (network : LogicalProcessNetwork processes) (machine : MachineState) where
  localStates : EveryLiveInstanceSatisfiesLocalInvariant network
  population : PopulationLawHolds processes network
  sharedState : SharedAccessAndInterferenceLawsHold processes network
  channels : EveryChannelWellFormedAndCorrelated processes network
  children : OutstandingChildrenMatchDemandOccurrences network
  obligations : NetworkObligationsAccountedFor network machine
  authorityPartition : CompleteExclusiveAuthorityPartition network machine
  occurrenceBijection : LogicalEscrowsIffPhysicalPendingRecords network machine
  sessionConsistency : PhysicalAndLogicalSessionCursorsAgree network machine
  lifecycleCustody : EveryDyingInstanceHasUniqueCustodian network machine
  representation : MachineRepresentsProcessNetwork driver network machine
  observations : CommittedTraceMatches spec network machine
  progress : SchedulerAndFrontierStateMatches network machine
```

A reusable driver theorem proves initial construction and one exhaustive
preservation/coverage case for every `NetworkTransition`, including spawn,
send, receive, commit, child/root success or failure, ordinary close,
cancellation resolution, fault, interruption, death, join, and restart,
and the relationship between loop SCCs and process frontiers/measures. A large
assembly loop does not restate the entire application semantics. Each dispatch
path proves only that it implements one named transition of one process instance
and re-establishes `ProcessLoopInvariant`; channel routing and untouched process
state are framed automatically.

This is a strong proof of the loop interior, not an abstraction which assumes it
correct. The exact dispatcher branches, queue operations, synchronization,
callback entries, demand commits, and raw instructions remain verified against
the derived invariant. Novel loop organizations may replace the standard driver
by proving the same network relation and transition coverage.

### Compositional quantitative theorems

Processes and process compositions expose theorem projections, not only a final
behavioral refinement. Network holdings form an owned resource algebra and a
metric is a valuation of that state. Disjoint holdings add by default; explicit
attribution, phase-exclusion, and transfer witnesses justify shared-once,
maximum, or affine-transfer equations:

```lean
structure NetworkResourceState (plan : ProcessPlan registry boundary) where
  instances : InstanceHoldings plan
  sessions : SessionHoldings plan
  occurrences : OccurrenceRecordHoldings plan
  obligations : ObligationHoldings
  sharedAttribution : SharedRegionAttribution plan
  layoutOverhead : PhysicalLayoutHoldings plan
  owned : OwnedResourceAlgebraState
  wellFormed : HoldingsRepresentExactlyNetworkAuthority owned

structure ResourceMetric (plan : ProcessPlan registry boundary) where
  Axis : Type
  Value : Axis -> Type
  zero : forall axis, Value axis
  combine : forall axis, Value axis -> Value axis -> Value axis
  le : forall axis, Value axis -> Value axis -> Prop
  valuation : forall axis, NetworkResourceState plan -> Value axis
  laws : forall axis,
    OrderedCommutativeResourceAlgebra
      (Value axis) (combine axis) (zero axis) (le axis)
  empty : forall axis, valuation axis EmptyNetworkResourceState = zero axis
  monotone : forall axis left right,
    OwnedSubstate left right -> le axis (valuation axis left) (valuation axis right)
  disjointUnion : forall axis left right,
    OwnedDisjoint left right ->
    valuation axis (left ∪ᵣ right) =
      combine axis (valuation axis left) (valuation axis right)
  attribution : SharedAttributionValuationLaw valuation
  affineTransfer : AffineTransferPreservesTotalValuation valuation

structure ResourceInvariant
    (plan : ProcessPlan registry boundary) (metric : ResourceMetric plan)
    (axis : metric.Axis) (budget : metric.Value axis)
    (network : LogicalProcessNetwork plan) : Prop where
  holdings : NetworkResourceState plan
  represents : holdings.wellFormed ∧ HoldingsRepresentNetwork holdings network
  bounded : metric.le axis (metric.valuation axis holdings) budget

structure ChannelCapacity where
  slots : Nat
  payloadBytes : Nat
  recordBytes : Nat

structure CapacityCredit (channel : ChannelId topology edge)
    (capacity : ChannelCapacity) where
  slots : AffineCreditToken channel .slots
  payload : AffineCreditToken channel .payloadBytes
  records : AffineCreditToken channel .recordBytes

structure ChannelCapacityLedger (channel : ChannelId topology edge)
    (capacity : ChannelCapacity) where
  free senderReserved escrowRecord receiverRetained terminalDisposition :
    ProductCreditHolding channel
  totalExact : free + senderReserved + escrowRecord + receiverRetained +
    terminalDisposition = capacity
  ownedExactlyOnce : AffinePartition
    [free, senderReserved, escrowRecord, receiverRetained, terminalDisposition]

structure CapacityTransitionLaw (step : NetworkStep plan before after) where
  beforeLedger : ChannelCapacityLedger channel capacity
  afterLedger : ChannelCapacityLedger channel capacity
  exactCase : CapacityEquationForNetworkTransition step.transition
    beforeLedger afterLedger

def EveryNetworkStepHasExactCapacityTransitionLaw
    (plan : ProcessPlan registry boundary) : Prop :=
  forall before after (step : NetworkStep plan before after),
    EveryAffectedBoundedChannelHasCapacityTransitionLaw step

structure NetworkResourceCertificate
    (plan : ProcessPlan registry boundary)
    (driver : ProcessDriver spec plan realizes platform program)
    (metric : ResourceMetric plan) (axis : metric.Axis)
    (budget : metric.Value axis) where
  initial : forall input network,
    InitialNetwork plan input network ->
    ResourceInvariant plan metric axis budget network
  step : forall before after,
    ResourceInvariant plan metric axis budget before ->
    NetworkStep plan before after ->
    ResourceInvariant plan metric axis budget after
  capacity : EveryNetworkStepHasExactCapacityTransitionLaw plan
  representation : forall network machine
      (invariant : ResourceInvariant plan metric axis budget network),
    MachineRepresentsProcessNetwork driver network machine ->
    PhysicalCost metric axis machine <=
      metric.valuation axis invariant.holdings

inductive HoldingCompositionRule (axis : metric.Axis)
  | additive (disjoint : OwnedDisjoint left right)
  | sharedOnce (token : ExactSharedOverlapAttribution left right)
  | phaseMaximum (exclusive : MutuallyExclusiveHoldingsWitness left right)
  | affineTransfer (conserves : ExactAffineTransferEquation left right)

structure ResourceCompositionDerivation
    (axis : metric.Axis) (left right result : NetworkResourceState plan) where
  classes : HoldingClassPartition left right
  rule : forall holdingClass, HoldingCompositionRule axis
  resultExact : result = ComposeHoldingsByRules classes rule
  leftBudget rightBudget resultBudget : metric.Value axis
  budgetExact : resultBudget = EvaluateBudgetExpression
    metric axis classes rule leftBudget rightBudget
  sound : metric.le axis (metric.valuation axis result) resultBudget

structure ScopePartition (scope : ProcessScope plan)
    (holdings : NetworkResourceState plan) where
  inside outside inboundEscrow outboundEscrow shared : NetworkResourceState plan
  exact : holdings = PartitionUnion inside outside inboundEscrow outboundEscrow shared
  disjoint : ExactOwnedPartition inside outside inboundEscrow outboundEscrow
  attribution : SharedHoldingsAttributedExactlyOnce shared

structure ScopeBoundaryFlux (scope : ProcessScope plan)
    (metric : ResourceMetric plan) (axis : metric.Axis) where
  lineage : IncludesAllDescendantsAcrossGenerations scope
  partition : forall network holdings,
    HoldingsRepresentNetwork holdings network -> ScopePartition scope holdings
  localInitial population channelLayout maxInbound creditedOutbound : metric.Value axis
  grossBudget : metric.Value axis
  grossBudgetExact : grossBudget = metric.combine axis localInitial
    (metric.combine axis population
      (metric.combine axis channelLayout maxInbound))
  scopeUse : NetworkResourceState plan -> metric.Value axis
  scopeUseExact : forall network holdings
      (represents : HoldingsRepresentNetwork holdings network),
    scopeUse holdings =
      metric.valuation axis (partition network holdings represents).inside
  scopeUsePlusOutbound : forall network holdings,
    (represents : HoldingsRepresentNetwork holdings network) ->
    metric.le axis
      (metric.combine axis (scopeUse holdings) creditedOutbound)
      grossBudget
  transition : TemporalInsideOutsideAndBoundaryFluxConservation scope partition
  shared : SharedAttributionTokensFollowPartition partition
  terminationCustody : CustodyAfterTerminationAndRestart scope

theorem subgraph_bound
    (scope : ProcessScope plan) (flux : ScopeBoundaryFlux scope metric axis)
    (certificate : NetworkResourceCertificate
      plan driver metric axis budget) :
    EveryExecutionUsesAtMostWithOutboundCredit
      scope metric axis flux.grossBudget flux.creditedOutbound

structure ResiduatedResourceAxis
    (metric : ResourceMetric plan) (axis : metric.Axis) where
  residual : metric.Value axis -> metric.Value axis -> metric.Value axis
  available : metric.Value axis -> metric.Value axis -> Prop
  residualLaw : forall gross credit,
    available gross credit ->
    metric.combine axis (residual gross credit) credit = gross
  cancellation : LeftCancellationLaw (metric.combine axis)
  orderReflection : ResidualReflectsOrder metric.le metric.combine residual

theorem subgraph_residual_bound
    (flux : ScopeBoundaryFlux scope metric axis)
    (residuated : ResiduatedResourceAxis metric axis)
    (available : residuated.available flux.grossBudget flux.creditedOutbound)
    (certificate : NetworkResourceCertificate
      plan driver metric axis flux.grossBudget) :
    EveryExecutionUsesAtMost scope metric axis
      (residuated.residual flux.grossBudget flux.creditedOutbound)

theorem compose_resource_bounds
    (left : ResourceBound leftScope leftBudget)
    (right : ResourceBound rightScope rightBudget)
    (witness : ResourceCompositionDerivation
      axis left.holdings right.holdings resultHoldings) :
    ResourceBound (weave leftScope rightScope)
      witness.resultBudget

theorem nested_scope_bound
    (inner : ScopeBoundaryFlux innerScope metric axis)
    (outer : ScopeBoundaryFlux outerScope metric axis)
    (contained : ScopeContained innerScope outerScope) :
    NestedScopeBudgetsComposeExactly inner outer contained

theorem insufficient_credit_disables_send
    (short : ¬RequiredCredit message <= ledger.free) :
    ¬Nonempty (NetworkStep plan before after ∧ Sends before after message)

theorem insufficient_credit_is_backpressure_frontier
    (short : ¬RequiredCredit message <= ledger.free) :
    AtDeclaredBackpressureFrontier producer before
```

`Axis` is not fixed to memory. Standard axes include live owned bytes, committed
virtual bytes, stack bytes, Unix file descriptors, Windows kernel/user handles,
sockets, threads, GPU objects and bytes, pending I/O bytes, process population,
obligations, and bounded work. Product and finite-map metric combinators prove
several bounds at once—for example resident bytes, file descriptors, and threads—
while allowing a different composition law on each coordinate. Provider
profiles connect logical tokens to the applicable physical resource namespace;
a Unix FD theorem neither counts a Windows handle nor pretends they share one
global integer namespace.

The axes are deliberately distinct: a theorem about Grass-owned resident
memory does not claim a bound on undocumented provider-internal memory. Shared
read-only storage is counted once; an affine loan moving through escrow is
transferred rather than counted at both endpoints; concurrently live private
buffers add; mutually exclusive phases may use a maximum. Physical layout
certificates connect logical byte counts to padding, headers, alignment, and
allocator overhead.

Bounded channels use product credit for slots, payload bytes, and exact physical
record/layout cost. Enqueueing a chunk consumes one positive slot plus its byte,
header, alignment, and occurrence-record charge and places those credits in
escrow with the bytes. Dequeue releases the physical channel-record charge but
transfers payload/ownership credit into receiver state; it does not pretend the
retained bytes vanished. Terminal disposition returns the corresponding credits
only when the physical record/payload is actually released. Control and
zero-payload lifecycle messages still consume a positive slot/record charge, so
finite byte credit cannot hide an unbounded record population. With insufficient credit, send is not
enabled and the producer reaches a declared backpressure frontier. Thus a proof
such as

```lean
theorem one_web_request_memory_bound :
  EveryExecutionUsesAtMost
    (ProcessScope.descendantsOf connection)
    .grassOwnedResidentBytes
    (Http2.connectionBytes policy)
```

is extracted by induction/coinduction over reachable network executions from
local state, channel, child-population, and physical-layout
certificates. It covers the entire request-handling subtree—including parser,
timeouts, partial socket I/O, pending response chunks, cancellation, and cleanup—
and forces bounded backpressure across the graph. The same machinery gives peak
memory theorems for compiler pipelines and codecs. Library combinators calculate
ordinary sums/maxima automatically; authors prove only aliasing, interference,
or lifecycle facts that prevent the bound from composing mechanically.

Scopes follow origin/parent lineage across terminated and restarted generations.
Their explicit boundary-flux contract accounts for inbound/outbound escrow,
shared attribution, and custody after termination. General nested composition
retains outbound credit and shared overlap as explicit relational terms. A
smaller residual number is derived only for an axis with a proved residuation,
availability, and cancellation law; max and shared-once axes are not silently
treated as subtractive.
Fault, cancellation, death, restart, and infinite pending are ordinary
preservation cases of the same `ResourceInvariant`.

## 6. Commit and desired view

An enabled view facet describes desired logical view. A platform reconciler proves that
each physical commit refines that view under an observation filter. It may skip
an intermediate render or replace several pending renders by the latest one only
when no skipped render has a demanded commit observation.

A commit transition is indexed by:

- exact pre/post process states and desired views;
- demand and result occurrence identities which enabled it;
- physical pre/post worlds and affected resource identities;
- observations appended by the commit;
- obligations created, discharged, transferred, or retained; and
- interruption, fault, cancellation, and concurrency behavior.

Console output commits bytes, a server commits accepted/request/result events,
and graphics commits a presented frame. Pure parsing, sorting, compression,
state update, and speculative render evaluation do not commit.

## 7. Nondeterminism, progress, and liveness

The unrestricted driver execution retains all allowed external values, result
orders, failures, cancellation races, callbacks, faults, and infinite pending
behaviors. Universal prefix safety quantifies over that model.

Conditional responsiveness is separate. Its coherent strategy may constrain
only named timing/scheduling dimensions and remains complete for every allowed
result value, as required by [SEMANTICS.md](SEMANTICS.md). A process cycle must:

- decrease a well-founded internal measure;
- reach a law-bearing external/demand-result frontier in finite internal
  work; or
- produce an independently specified observation.

Long-lived processes need not terminate. They prove productivity/reactivity and
conditional quiescence or user-requested shutdown. A terminal CLI process proves
conditional or unconditional termination according to its declared frontiers.

Local progress is necessary but insufficient. `ProcessNetworkAdequate` proves
the corresponding theorem over every maximal network execution. An infinite
network run must produce a specification-demanded observation or remain at a
declared external frontier; otherwise a global well-founded rank decreases
across process steps, spawn, retry, cancellation, death, join, and restart.
Supervision therefore carries a restart bound/rank or a separately demanded
productivity law. Fresh-child restart loops cannot evade the global theorem,
and scheduler fairness is used only when named by the specification.

## 8. Composition and weaving

`weave` constructs or refines a non-precious `ProcessPlan` from process machines
with disjoint nominal event, demand, result,
and observation namespaces. Composition may be sequential, parallel, routed,
supervised, or view-composed. It proves:

- how events are routed and whether irrelevant events stutter;
- realized-demand dependency/concurrency compatibility;
- noninteraction or explicit shared-state synchronization;
- observation ordering/filtering;
- cancellation and obligation propagation; and
- progress preservation or newly introduced progress obligations.

Cross-process invariants are exported as small frameable mixins, not maintained
as one application-sized proof term:

```lean
structure WeaveInvariantMixin (plan : ProcessPlan registry boundary) where
  Scope : NetworkScope plan
  assertion : LogicalProcessNetwork plan -> Prop
  initial : ExactInitialNetwork plan network -> assertion network
  affected : forall (step : NetworkStep plan before after),
    TouchesScope step Scope -> assertion before -> assertion after
  frame : forall (step : NetworkStep plan before after),
    Disjoint (TransitionScope step) Scope ->
    assertion before -> assertion after
  resources : ExactResourceFragmentOwnedBy Scope assertion
  obligations : ExactObligationFragmentOwnedBy Scope assertion

structure WeaveInvariantFamily (plan : ProcessPlan registry boundary) where
  Key : Type
  mixin : Key -> WeaveInvariantMixin plan
  disjointOrShared : PairwiseCompatibleResourceFragments mixin
  complete : EveryCrossProcessDependencyNamedBySomeMixin plan mixin

def WeaveInvariantFamily.aggregate (family : WeaveInvariantFamily plan) :
    LogicalProcessNetwork plan -> Prop :=
  fun network => forall key, (family.mixin key).assertion network
```

Each component library exports its local mixins—generation identity, permit
accounting, escrow ownership, cancellation race, immutable sharing, deadline
correlation, or another independently meaningful fact. `weave` imports those
certificates and proves only compatibility plus the new routing facts. Changing
timeout routing reopens the timeout/generation mixins and their constructor
cases, not socket ownership or immutable-body sharing. A plan-specific aggregate
record is therefore a thin named facade over independently kernel-checked
mixins; its fields do not contain or reconstruct unrelated proofs.

The generic induction is constructor-indexed. For every constructor of
`NetworkTransition`, each imported mixin supplies either `affected` preservation
or `frame`; a plan may instead supply an exact unreachability proof for that
constructor. The aggregate theorem is just pointwise application of those
certificates. It cannot turn a missing constructor case into a default frame
case.

A coherent provider selection remains global. Weaving cannot realize half of
one graphics demand vocabulary through Vulkan and half through Metal unless the
portable process intentionally uses two distinct provider keys and proves their
compatibility.

Refinement itself is local. A `ProcessRefinementLens` selects one abstract role
or subgraph and its complete typed boundary. Replacing it preserves observation
origin, channel order, linear/shared custody, obligations, resource flux, and
progress at that boundary while introducing a finite requirement delta. The
generic contextual theorem frames every nonselected process. Thus one proof may
replace only the graphics role with Vulkan protocols while leaving disk I/O
abstract; a later proof may replace only disk I/O with Win32 asynchronous-file
and IOCP protocols. Neither reopens the other's internal proof.

Requirement deltas accumulate in the explicit `ProviderEnv`. Local refinement
cannot perform ambient instance selection. At closure, nominal provider keys,
API/ISA/platform compatibility, and every remaining abstract frontier are
checked globally. Two independently refined regions which accidentally choose
incompatible meanings for one provider key fail coherence rather than being
silently woven.

Only the resource-parameterized portable specification function is precious.
The selected resource value, process protocols, their correctness proofs, and a particular weave are reviewed and
bankable because they determine the program being built, but are disposable in
the same sense as authored assembly: deletion and reconstruction require new
satisfaction/refinement proofs, not a change to the specification.

## 9. How the spikes fit

- Hello World is authored as a serial relational write and normalized to the
  canonical one-root process with API children; flattening round-trips to the
  authored relation.
- Sort is a collecting process followed by pure decode/stable-sort and buffered
  commit. Input fragments and EOF are events; no stdout commit is enabled before
  the allocation/sort barrier.
- Gzip is a streaming transducer process. Read fragments advance compressor
  state; output-buffer flushes are explicit demands; the zlib/gzip model proves
  the logical stream relation.
- The HTTP server is a supervised parallel composition of listener and request
  processes. Accept, receive, timeout, cancellation, send, and shutdown are
  correlated events/demands.
- The cube is an interactive process with window, frame-opportunity,
  image-available, GPU-complete, resize, failure, and user-exit events. Vulkan
  resource reconciliation is a driver, not application update logic.

These mappings are architectural hypotheses for the spikes to test. A spike may
force this interface to change; the process abstraction is not ratified merely
because it is elegant on paper.

## 10. Assembly and artifact connection

The application theorem composes with one proved driver contract. The selected
driver is then realized by a complete authored machine CFG (and any device ISA
modules), ghost-erased, encoded, linked, loaded, and related to the exact emitted
bytes under [VERIFIED_PROGRAM.md](VERIFIED_PROGRAM.md).

No `ProcessDriver` field is external trust. A reusable driver proof can remove
application ceremony, but its raw implementation, macros, callbacks, scheduler,
resource protocols, and artifact connection remain inspectable. Novel authored
assembly may replace any driver sub-CFG by satisfying the same extensional
boundary contract.

## 11. Explicit non-goals

Grass does not model React hooks, virtual DOM identity, concurrent render lanes,
stale closures, effect cleanup conventions, component class lifecycles, or web
DOM reconciliation unless a future target actually requires them. The process
model is not permission to hide effects in `render`, callbacks in closures, or
platform state in the precious specification.
