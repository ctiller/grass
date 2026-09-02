# Execution semantics

This document owns execution, nondeterminism, observations, safety, progress,
and liveness. Memory-event validity is owned by [MEMORY_MODEL.md](MEMORY_MODEL.md).

## 1. Relational authority and executable runner

The normative semantics is relational. Given one complete state, it may admit
multiple next transitions for scheduling, interrupts, weak-memory choices,
spurious wakes, allocation addresses, API results, and specified implementation
choice.

Conceptually, a modeled execution packages the state/event sequence with one
coherent global execution witness:

```lean
Execution : InitialState -> Trace -> ExecutionGraph -> Prop
StepExtension : ExecutionPrefix -> ExternalChoice -> ExecutionPrefix -> Prop
```

`StepExtension` monotonically extends the same graph witness. It may not choose
independent per-step reads-from or ordering facts that compose into a forbidden
cycle. Every finite runner prefix carries a proof that it is extendable to an
admitted finite terminal execution or infinite execution. Infinite executions
have a profile-defined limit condition whose finite restrictions agree with the
monotonic graph and whose complete graph satisfies global consistency.

A `ProcessPlan` induces a logical interleaving semantics over live process
instances, Hoare-channel sends/receives, child lifecycle transitions, and
commits. Driver refinement relates each physical step or finite internal stutter
segment to one logical process transition. Process decomposition never selects
one favorable schedule or result; unrestricted execution retains every allowed
interleaving and child response.

The executable interpreter consumes a `ChoiceOracle` and fuel. It must prove
that every produced prefix is admitted and remains extendable; local choices
that lead to no coherent complete execution are not permitted runner prefixes.
The oracle makes runs replayable; it does not reduce the universal proof demand.
`VerifiedProgram` quantifies over all modeled executions, not only executions
selected by one runner.

Malformed, unavailable, or exhausted environment/oracle responses are explicit
outcomes. The interpreter must never invent a friendly default.

Environment interaction is a dependent request/response protocol. For each
request `q`, its profile defines `Response q` and `Allowed q r`. A permitted
execution may choose any `r` satisfying `Allowed q r`; subsequent memory and
control state may depend on that exact response. This covers return values,
output buffers, partial I/O, callbacks, and cancellation without separating a
value stream from the state changes it authorizes.

The choice oracle has namespaced channels for environment responses, scheduler
selection, interrupt/fault delivery, allocation/layout choice, and
architecture-specific consistency witnesses. Consumers cannot read another
channel accidentally. Fixing all channels makes the runner deterministic;
proofs remain universal over every well-formed oracle.

## 2. Execution forms

Executions may be finite or infinite. A finite execution ends in exactly one:

- successful program result;
- specified program failure;
- handled or terminal architectural fault;
- environment-contract violation;
- no admitted transition from a state declared terminal;
- fuel exhaustion in the executable runner only.

Fuel exhaustion is not a semantic program outcome. It returns a proved safe
finite prefix and is otherwise inconclusive.

Architectural faults are events with specified control behavior. A fault may
terminate, transfer to a handler, or be returned by an API. Audit violations are
separate monotonic evidence that a modeled safety demand was broken. Verified
programs prove that no reachable conforming execution appends such a violation
and that no disallowed fault occurs.

An environment-contract violation is a modeled execution boundary but is not a
conforming environment behavior. The fundamental theorem gives full guarantees
to conforming executions and only a matched safe prefix ending immediately
before the first contract violation. It must not project or normalize the
post-violation suffix as if it satisfied the specification.

Violations are result-indexed, not one unconstrained escape constructor. Broad
classes include value-domain, output-memory, ABI/control, and arbitrary external
misbehavior. A profile may provide
`ViolationReturnEnvelope occurrence preWorld postWorld callId loanIds r class`
for a
narrow class. The envelope states exactly which boundary facts survived—for
example, ordinary ABI return, completed in-bounds output-slot write, returned
loans, and intact residual frame while one numeric range predicate failed. It
does not restore functional conformance or the full assurance theorem.

The envelope is an affine token produced by the exact violating boundary-step
witness. It carries the first-violation proof, consumes the pending invariant for
that call occurrence and those loan identities exactly once, and cannot be
reused at another equal request/result. Classification is exclusive: a value-only
class proves that memory effects, ABI/control return, and loan return all
conformed; a compound violation cannot masquerade as `.excessWriteCount`.

Verified post-violation containment is a separate local theorem that consumes
such an envelope. An arbitrary memory, ABI, or control violation has no envelope
and supports only the maximal pre-violation safe prefix. Thus a trap tail can be
proved for a narrow returned-value violation without pretending that arbitrary
external corruption is safe or recoverable.

## 3. Observations

The complete audit trace may include:

- input and API return values;
- output requests and partial completions;
- syscalls and API calls;
- memory and synchronization events;
- allocation and provenance events;
- faults, interrupts, cancellation, and process/thread lifecycle;
- obligation creation, transfer, discharge, and terminal disposition;
- program results and exit codes.

A specification owns an `ObservationProjection` selecting and normalizing only
the functional events it cares about. Projections may coalesce permitted partial
writes or hide internal calls only when a theorem establishes that normalization
is lawful. They cannot suppress safety, ABI, applicability, connection, or
obligation demands; those are independent `VerifiedProgram` fields.

For an input routine or imported call, equivalence quantifies over every result
allowed by its profile, including short operations, interruptions, failure
codes, and dependent output memory.

### Tripartite specification

Grass gives three independently reviewable owners to the product boundary:

```lean
class ResourceModel (R : Type u) where
  algebra : ResourceAlgebra R

class HasResourceAxis (R : Type u) [ResourceModel R] (axis : ResourceAxisName) where
  Value : Type
  combine : Value -> Value -> Value
  le : Value -> Value -> Prop
  laws : OrderedPartialCommutativeResourceLaws combine le

class HasResourceLimit (R : Type u) [ResourceModel R]
    (axis : ResourceAxisName) extends HasResourceAxis R axis where
  limit : R -> Value
  exhaustion : R -> ResourceExhaustionPolicy axis
  lifecycle : R -> ResourceLifecyclePolicy axis

class WebServerResources (R : Type u) [ResourceModel R]
    extends HasResourceLimit R .residentBytes,
            HasResourceLimit R .connections,
            HasResourceLimit R .sockets,
            HasResourceLimit R .requestWork where
  requestDeadline : R -> Duration
  responseDeadline : R -> Duration
  fixedAfterReady : R -> Prop

structure ConstructionCapturedCapabilityMap
    {R : Type u} [ResourceModel R] (resources : R) where
  Key : Type
  finite : Fintype Key
  axis : Key -> ResourceAxisName
  axisInjective : Function.Injective axis
  entry : forall key : Key, SelectedAxisSemantics resources (axis key)
  construction : ExactSnapshotOfEntireCapabilityMap resources axis entry

structure SelectedResourceSemantics
    {R : Type u} [ResourceModel R] (resources : R) where
  capabilities : ConstructionCapturedCapabilityMap resources

def SelectedResourceSemantics.requiredAxes
    (selected : SelectedResourceSemantics resources) :
    FiniteKeySet ResourceAxisName :=
  FiniteKeySet.range selected.capabilities.axis

def SelectedResourceSemantics.lookup
    (selected : SelectedResourceSemantics resources)
    (axis : ResourceAxisName)
    (required : axis \u2208 selected.requiredAxes) :
    SelectedAxisSemantics resources axis :=
  selected.capabilities.entry
    (selected.capabilities.keyOfMembership axis required)
    |>.transport (selected.capabilities.axisOfKeyOfMembership axis required)

structure SpecProcess {R : Type u} [ResourceModel R]
    (resources : R) where
  suite : SpecificationSuite resources
  resourceSemantics : SelectedResourceSemantics resources :=
    suite.resourceSemantics
  resourceSemanticsExact : resourceSemantics = suite.resourceSemantics
  boundary : AbstractProcessBoundary
  contract : BehaviorContract resources
  contractExact : contract = suite.contract
  boundaryExact : boundary = ContractBoundary contract
  requirements : FiniteKeyedProcessDemandFamily resources resourceSemantics
  requirementsExact : requirements = suite.processDemands

def SpecProcess.driverBoundary (spec : SpecProcess resources) :
    DriverBoundary :=
  DriverBoundary.ofContract spec.boundary spec.contract spec.requirements

def SpecProcess.progress (spec : SpecProcess resources) :
    AbstractProgressContract := spec.contract.progress

def MeetsAllSpecificationTheorems (spec : SpecProcess resources) : Prop :=
  forall key : spec.suite.theorems.Key,
    spec.suite.theorems.statement key

structure AbstractSpecificationProcessNetwork
    {R : Type u} [ResourceModel R] (resources : R) where
  RoleSchema : Type
  finiteSchemas : Fintype RoleSchema
  Instance : RoleSchema -> Type
  protocol : forall schema,
    SpecProcess resources
  instances : forall schema,
    Instance schema -> ProtocolInstance (protocol schema)
  composition : AbstractNetworkCompositionLaw protocol instances

def SpecProcess.capture
    (suite : SpecificationSuite resources) : SpecProcess resources :=
  { suite := suite
    resourceSemantics := suite.resourceSemantics
    resourceSemanticsExact := rfl
    boundary := ContractBoundary suite.contract
    contract := suite.contract
    contractExact := rfl
    boundaryExact := rfl
    requirements := suite.processDemands
    requirementsExact := rfl }

def SpecProcess.ofRelational
    (contract : BehaviorContract resources) :
    SpecProcess resources :=
  SpecProcess.capture (SpecificationSuite.singletonRelational contract)

structure ProcessPresentation (spec : SpecProcess resources) where
  network : AbstractSpecificationProcessNetwork resources
  denotationExact : network.traceDenotation = spec.contract
  requirementsExact : TransportedProcessRequirements network denotationExact =
    spec.requirements

structure RequirementSubstitution
    (spec : SpecProcess resources) where
  selected : forall key : spec.requirements.Key,
    SelectedProcessRequirementWitness (spec.requirements.entry key)
  occurrences : ExactRequirementOccurrenceSubstitution spec selected
  preservesContract : SubstitutionPreservesContract spec selected occurrences
  preservesResources :
    SubstitutionPreservesSelectedResourceSemantics spec selected occurrences

def SpecProcess.appendFragment
    (spec : SpecProcess resources) (fragment : SomeSpecComponent resources) :
    SpecProcess resources :=
  SpecProcess.capture (spec.suite.append fragment)

theorem SpecProcess.appendFragment_recaptures_exactly
    (spec : SpecProcess resources) (fragment : SomeSpecComponent resources) :
    (spec.appendFragment fragment).suite = spec.suite.append fragment := rfl

def SpecProcess.withProgress
    (spec : SpecProcess resources) (fragment : ProgressFragment) :
    SpecProcess resources :=
  SpecProcess.capture (spec.suite.appendProgress fragment)

theorem SpecProcess.withProgress_recaptures_exactly
    (spec : SpecProcess resources) (fragment : ProgressFragment) :
    (spec.withProgress fragment).suite = spec.suite.appendProgress fragment := rfl

def SpecProcess.withOutcomes
    (spec : SpecProcess resources) (Outcome : Type) : SpecProcess resources :=
  SpecProcess.capture (spec.suite.appendOutcomeLanguage Outcome)

theorem SpecProcess.withOutcomes_recaptures_exactly
    (spec : SpecProcess resources) (Outcome : Type) :
    (spec.withOutcomes Outcome).suite =
      spec.suite.appendOutcomeLanguage Outcome := rfl

def SpecProcess.withLiveness (spec : SpecProcess resources)
    (contract : LivenessContract) : SpecProcess resources :=
  SpecProcess.capture (spec.suite.appendLiveness contract)

def SpecProcess.withFailures (spec : SpecProcess resources)
    (contract : FailureContract) : SpecProcess resources :=
  SpecProcess.capture (spec.suite.appendFailures contract)

def SpecProcess.acceptInput (spec : SpecProcess resources)
    (accepted : AcceptedInputLanguage spec.contract) : SpecProcess resources :=
  SpecProcess.capture (spec.suite.appendAcceptedInput accepted)

def SpecProcess.onResourceExhaustion (spec : SpecProcess resources)
    (outcome : AbstractOutcome spec.contract) : SpecProcess resources :=
  SpecProcess.capture (spec.suite.appendResourceExhaustionOutcome outcome)

theorem every_spec_modifier_appends_and_recaptures :
    EveryPublicSpecModifierIsSuiteAppendThenCapture

structure RelationalSpec (resources : R) where
  Input Output : Type
  admits : Input -> Prop
  relates : Input -> Output -> Prop
  failure : RelationalFailureContract Input Output

structure StreamSpec (resources : R) where
  InputChunk OutputChunk : Type
  relation : Stream InputChunk -> Stream OutputChunk -> Prop
  causal : CausalStreamRelation relation
  rechunking : OptionalRechunkingLaw relation

structure TraceSpec (resources : R) where
  State InputEvent OutputEvent : Type
  initial : State -> Prop
  step : State -> InputEvent -> State -> List OutputEvent -> Prop
  progress : TraceProgressContract step

structure ProtocolSpec (resources : R) where
  SessionSchema : Type
  SessionId : SessionSchema -> Type
  protocol : forall schema, SessionProtocol resources (SessionId schema)
  composition : ProtocolCompositionLaws protocol

def SpecProcess.fromRelationalSpec : RelationalSpec resources -> SpecProcess resources
def SpecProcess.fromStreamSpec : StreamSpec resources -> SpecProcess resources
def SpecProcess.fromTraceSpec : TraceSpec resources -> SpecProcess resources
def SpecProcess.fromProtocolSpec : ProtocolSpec resources -> SpecProcess resources

theorem natural_frontends_denote_one_contract :
  EveryNaturalSpecificationFrontendDenotesBehaviorContract

structure TargetProjection
    {R : Type u} [ResourceModel R]
    {resources : R}
    (spec : SpecProcess resources)
    (profile : PlatformProfile) where
  project : AbstractObservation spec.contract -> PlatformObservation profile
  outcome : AbstractOutcome spec.contract -> PlatformOutcome profile
  capabilities : CapabilityProjection resources spec profile
  faithful : ProjectionPreservesConfiguredClaims
    resources spec project outcome capabilities
```

There is one captured resource-semantics value. Axis keys are derived from the
dependent map's finite key type, and selected semantics are obtained only by
proof-indexed lookup into that same map. Limits, combination, ordering,
exhaustion, and lifecycle are fields of the returned
`SelectedAxisSemantics`; none can be supplied by a neighboring dictionary.
`construction` attests the complete dependent map—key-to-axis association and
entry—not merely its payload array.

1. The **resource model** is an explicit selectable value whose typeclasses name
   only the quantitative and lifecycle capabilities a specification needs over
   extensible axes such as resident bytes, allocation capacity, handles, file
   descriptors, threads, GPU objects, pending work, and obligations. It is
   independent of any one application. There is no closed universal axis list or
   god record. These typeclasses are construction-time dictionary builders.
   `SpecProcess.resourceSemantics` snapshots their exact, finite, uniquely
   keyed semantic data; every downstream theorem projects from that snapshot
   and is forbidden to rerun instance search.
2. The **specification family** accepts that model as a parameter and may use
   either a direct portable relation or an abstract process protocol to name
   domain values, admitted inputs, observations, outcomes, safety, progress,
   and functional relations under those resource semantics. Defining
   `webServerSpec {R} [WebServerResources R] (resources : R)` once permits separate
   microcontroller, workstation, and data-center instantiations.
3. The **target projection** maps abstract observations, outcomes, capabilities,
   and provider boundaries to one coherent platform/API/ISA profile. It may map
   a logical text line to CRLF, an abstract success/failure to target exit
   statuses, or an abstract clock to a cited platform provider. Its `faithful`
   theorem prevents it from weakening or inventing product behavior.

The precious portable program meaning is the specification **function**, not
one selected resource value. A resource model is a reviewed build parameter:
it is theorem-relevant and must be discharged, but replacing it instantiates the
same program definition. Because the specification depends on the resource
model, exhaustion, admission, backpressure, and lifecycle observations are
stated rather than retrofitted by an external contract. A target
projection is another reviewed selection unless the product explicitly promises
a named target representation.

Two lawful capability dictionaries over the same carrier and equal resource
value may construct two different specification values, because their exact
snapshots differ. Since all later certificates are indexed by the selected
`spec`, they cannot borrow capacity, deadline, exhaustion, or lifecycle facts
from a third ambient instance. Typeclass proof irrelevance is used only for laws
about the captured operations, never to identify competing semantic operations.

The one root `SpecProcess` stores the precious suite of DSL components and
semantic junctions, its captured transition/observation semantics, selected
resource-semantics snapshot, and theorem demands. `VerifiedProgram` is indexed
by that exact process. A `ProcessPresentation` is a
replaceable proof lens over that value. It may name abstract logical roles,
typed channels, linear custody, shared logical state, and causal ordering, but
its `denotationExact` theorem must recover the already selected contract. It is
not stored inside the specification and changing its topology cannot change the
precious value. OS threads, worker counts, polling/completion mechanisms,
concrete queues/buffers/handles, layouts, registers, and schedulers remain still
lower realization choices.

`RelationalSpec`, `StreamSpec`, `TraceSpec`, and `ProtocolSpec` are natural
authoring front ends, not four competing semantic foundations. Batch algorithms
normally use a relation; codecs use a causal stream relation; interactive
applications use a transition trace; multiplexed services use session
protocols. Their constructors elaborate to the same `BehaviorContract`
denotation and the same observation, resource, failure, progress, refinement,
and artifact theory. An author therefore need not invent process roles for a
sort. A web server can then choose a product-significant stream presentation to
prove attribution, flow control, and isolated cancellation without freezing
that presentation into its precious contract. A convenient modality must not
introduce a second end-to-end correctness theorem.

Resource typeclasses are bounded customization surfaces with laws, not ambient
provider selection. The resource value is passed explicitly; the instance only
states what its type means and which theorems it supports. A sort asks for
allocation/buffering capabilities, a Unix service may add file descriptors, a
kernel may add pages and interrupt work, and a graphics application may add host
bytes, device bytes, handles, and in-flight submissions. Spec-specific classes
may extend the common axes without changing unrelated specifications.

This is a semantic split, not a rule about filenames: small programs may
colocate the layers, while corpus fixtures use `Spec.lean`, `Resource.lean`, and
`Projection.lean` so ownership and invalidation are visible.

Each layer has a separately bankable proof. Ideally a portable model proves the
specification family for every resource model satisfying explicit premises;
otherwise it proves named supported instances. Resource certificates establish
those premises without target facts. A target plan
proves projection faithfulness and provider adequacy. Assembly proves
refinement to the projected model. The final artifact theorem composes all
three; none is permitted to stand in for another.

### Independent theorem demands and invalidation facets

Functional observation is one demand, not the container for every guarantee.
Specifications carry a finite keyed family of independently stated theorem
demands:

```lean
inductive RequirementKind
  | functional | safety | memory | concurrency | progress | termination
  | resource | obligation | diagnostic | applicability | artifact
  | extension (owner : Name) (kind : Name)

structure TheoremDemand where
  key : RequirementKey
  kind : RequirementKind
  statement : SpecificationContext -> Prop
  dependencies : Finset SemanticFacet

structure RequirementFamily where
  demands : FiniteMap RequirementKey TheoremDemand
  unique : demands.Keys.Nodup
```

`VerifiedProgram` discharges every key separately and records the semantic
facets actually consumed by its proof. Composition may derive a new demand from
several old ones, but it cannot conflate them into one opaque “program correct”
field. This is the basis for surgical invalidation and for diagnostics which
name the unmet guarantee.

Grass deliberately does not freeze all future requirements into four permanent
functional/resource/time/diagnostic buckets. Memory provenance, race freedom,
ABI applicability, liveness, obligation custody, and exact-artifact connection
have different composition and trust laws; placing them in a broad tuple does
not isolate their dependencies. `RequirementKind.extension` permits new
independent axes while stable keys and dependency facets retain locality.

Product policy belongs in the precious family when it changes admitted external
behavior. A four-connection admission limit, silence on allocation failure,
deadline, exact newline bytes, or required fixed-after-ready storage is not
“platform leakage” merely because an implementation must work harder to honor
it. Conversely, worker count, `WSAPoll`, IOCP, buffer layout, provider error
codes, and register choices remain realization or audit facts unless the product
explicitly observes them.

## 4. Safety over prefixes

Safety is prefix-closed. `PrefixSafe p` states that a finite execution prefix:

- contains no memory, race, provenance, initialization, or permission violation;
- takes only applicable instructions and APIs;
- follows typed CFG edges and ABI contracts;
- preserves the obligation ledger;
- has only declared faults, interrupts, and effects.

`VerifiedProgram` proves `PrefixSafe` for every finite prefix of every permitted
execution. This establishes infinite-run safety because any safety violation has
a first event in a finite prefix.

## 5. Progress and liveness

Safety does not imply progress. Each reachable nonterminal state and every
permitted continuation must establish one explicit `ProgressCase`:

- it reaches a terminal state in finitely many internal steps;
- it reaches a law-bearing environmental frontier in finitely many internal
  steps and transfers agency or performs a specification-meaningful interaction;
- it is currently waiting at such a frontier under a specified protocol; or
- it transfers control to a separately verified component with an equivalent
  progress demand.

Every reachable cyclic CFG strongly connected component must either have a
well-founded decreasing rank or necessarily cross a declared frontier. Nested
reactive loops satisfy the rule recursively. Merely having an exit condition is
insufficient if execution can spin internally before observing it.

A frontier is a protocol state, not a user-applied label. Its laws identify the
external request/yield, the party receiving agency, its possible responses, and
the resulting trace event. A synthetic no-op or yield that immediately returns
control cannot certify a cycle unless a separate productivity theorem connects
it to a specification observation. The rule is universal: one good branch does
not excuse another permitted branch that spins.

A reactive contract proves:

- safety for all finite and infinite input histories;
- productivity under stated platform/fairness assumptions;
- finite handling between frontiers; and
- conditional termination, for example `EventuallyQuit input -> Terminates`.

Unconditional termination is required for programs whose specification demands
it. Interactive programs may instead use the reviewed reactive contract.

Fairness and responsiveness are never global axioms. A liveness theorem names
the precise scheduler, API, device, or user-response assumptions it consumes.
Safety must not depend on them. If an environment never answers a permitted
blocking request, a program may remain at that frontier without violating local
progress; it cannot claim conditional termination unless its assumption requires
that response.

`AbstractEnvironmentStrategy spec` is a coherent branching strategy: it
constrains choices but denotes the complete set of abstract histories compatible
with those choices, not one favorable run. `EnvironmentResponsive spec σ` has
one fixed meaning in specification vocabulary. For every finite history
reachable under `σ`, every nonterminal frontier settles with an allowed response
on every maximal continuation compatible with `σ`, and every terminal-status
frontier eventually produces its declared terminal observation. It grants no
particular success result, value, schedule, or stronger functional behavior.
A platform provider may state more concrete sufficient assumptions only by
proving they imply this fixed predicate; it cannot redefine or strengthen the
author's liveness premise.

Responsiveness is packaged with strategy adequacy:

```lean
structure ResponsiveStrategyWitness {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources) where
  strategy : AbstractEnvironmentStrategy spec
  adequate : StrategyAdequate strategy
  scheduleComplete : SchedulingComplete spec strategy
  resultComplete : FrontierComplete spec strategy
  responsive : EnvironmentResponsive spec strategy
```

`StrategyAdequate` proves that the compatible-history set is prefix closed, the
root/empty history is compatible, every
reachable nonterminal history has a nonempty compatible continuation set, and
maximal compatible executions exist. A strategy with no histories or an empty
continuation tree is therefore not a witness, even when universal response
clauses would otherwise be vacuous.

`SchedulingComplete spec σ` states the exact timing/scheduling dimensions named
by the liveness premise and requires every base schedule satisfying those
constraints to have a represented compatible history. A strategy cannot select
one favorable fair schedule and discard the other fair schedules. Schedules
which violate the named premise remain in unrestricted safety semantics but are
not liveness-compatible.

`FrontierComplete spec σ` separately handles value nondeterminism: at every
frontier reachable under a strategy-compatible schedule, every
response value allowed by that frontier's law appears in the strategy tree with
its dependent post-state. A responsive strategy may constrain only the named
timing/scheduling dimensions used by its premise; it cannot prove termination
by pruning success, failure, partial-result, cancellation, or other difficult
value branches. It is prefix closed. Concrete/abstract strategy refinement
preserves and reflects this response completeness as well as histories and
maximality.

The unrestricted execution/profile adequacy theorem—not a responsive strategy—
proves that every API contract which permits indefinite pending has an actual
infinite pending execution. This separation is essential: a strategy satisfying
`EnvironmentResponsive` may rule out perpetual waiting by assumption, whereas
the universal safety model must retain that behavior. Requiring the same
responsive strategy both to include an infinite pending maximal branch and to
settle every maximal branch would make the witness contradictory.

Conditional liveness also carries `Nonempty (ResponsiveStrategyWitness spec)`:
an explicit adequate coherent branching strategy witnessing that the predicate can hold
universally across all reachable frontier kinds and compatible maximal
continuations. This is distinct from per-request response adequacy, which need
not assemble its individually allowed replies into one strategy, and
from unconditional safe-pending behavior. Provider diagnostics expose the
concrete assumptions, an inhabitant of one joint concrete provider/scheduler
strategy, an explicit projection to its abstract branching strategy, a
refinement coupling their complete generated-history sets, choices,
events/frontiers/eventual-settlement facts, and responsiveness of that exact
projection. A function that can return an unrelated abstract strategy—or
a separately inhabited abstract strategy alone—is not enough.

Strategy refinement preserves and reflects the root, continuation totality,
maximality, scheduling completeness, and concrete-to-abstract history coverage. In particular, every
concrete compatible maximal execution projects to an abstract compatible
maximal execution, and every reachable concrete prefix has the coupled abstract
prefix; empty-to-empty inclusion is insufficient.

Conditional termination is universal: for every conforming execution compatible
with a strategy satisfying `EnvironmentResponsive`, the implementation
terminates as specified. Existence of one terminating compatible history never
discharges the demand.

## 6. Refinement

For a deterministic specification, every conforming execution must produce its
specified projected observation for the same environmental choices. For a
permissive specification, implementation observations must be a subset of the
allowed behavior relation. Infinite traces use coinductive/trace refinement;
finite terminating cases may use ordinary equality or simulation.

Optimization may change instruction traces, layout, timing, or internal API
structure only if it preserves the selected functional observation and every
independent mandatory demand.

## 7. Adequacy and non-vacuity

Every execution profile supplies an adequacy package:

- the set of valid initial states is nonempty;
- each valid initial state has at least one admitted finite or infinite modeled
  execution;
- a terminal initial state admits a zero-step conforming execution carrying its
  terminal result, observation, ABI state, and obligation ledger/dispositions;
- each reachable environment request has an allowed response or a modeled
  pending/infinite-wait execution;
- the initial empty execution prefix exists and is extendable;
- oracle well-formedness has witnesses for every admitted choice pattern
  required by the profile.

Universal safety/refinement theorems do not count if their execution or response
domains are empty. Adequacy is a separate `VerifiedProgram` requirement so a
proof cannot hide non-emptiness inside an opaque semantic predicate.
