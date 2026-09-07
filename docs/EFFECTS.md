# Law-bearing effects

This document owns Grass's high-level sequential effect vocabulary, its laws,
its requirement propagation, and the interface for replacing one abstract effect
family with another. It does not own process scheduling, physical API calls,
memory access, or the obligation ledger.

The purpose of `Grass.Effect` is proof economy. A library author should be able
to state a small computation using abstract operations, prove it once against
portable operation theories, and later replace graphics, storage, console, or
allocation operations independently. A first-class assembly author may bypass
this syntax and refine the same requirements directly. No verified program is
required to possess a decorative monadic source.

**Implementation status.** This is the normative target for the Effect
milestone, not a claim about the current Lean skeleton. At the reviewed baseline
there is no `Grass/Effect/**`; the landed `DriverBoundary`, sequential adapter,
`SpecProcess`, and `VerifiedProgram` do not yet carry the authority-indexed
provider origins, general progress junction, certified direct-program wrapper,
or final closure displayed here. Consequently the current emitter cannot accept
an Effect-derived program as satisfying this design. Before the first Effect
implementation may merge, those exact connections must reach the actual
`VerifiedProgram.endToEnd` theorem and removing one provider origin or progress
premise must make a negative fixture fail to elaborate. A green build of the
pre-Effect skeleton is not evidence for that gate.

## 1. Dependency and authority boundary

`Grass.Effect` imports only `Core`, `Std.Logical`, and neutral
`Specification` vocabulary. It imports neither `Semantics`, `Process`, `Memory`,
`Obligation`, a platform, nor an ISA. `Process` may consume Effect signatures and
programs; `Refinement` and `Weave` connect them to a precious `SpecProcess`, a
process presentation, or a provider.

The layer owns:

- open, dependent operation families and finite effect rows;
- a well-founded sequential request/continuation program;
- finite prefix/complete denotation and ordered interaction traces;
- monad laws stated under that relation;
- family laws and finite requirement summaries;
- explicit sub-row weakening;
- source-to-target handlers and their composition laws; and
- checked normalization and traversal-order theorems.

It does not own:

- a second execution model for complete programs;
- process identities, occurrence identities, queues, channels, cancellation,
  supervision, scheduling, or global-loop progress;
- allocation/provenance, physical resource custody, or memory safety;
- obligation identities, ledger mutations, or terminal dispositions;
- ambient provider selection;
- exception semantics that silently swallow process faults or interruption; or
- emission, encoding, or assembly correctness.

The last exclusions are semantic. An effect theory may *demand* a named memory,
resource, or obligation property through neutral requirement keys. Only the
owning later layer can prove and realize that property.

## 2. Operation families and rows

An effect family is an open nominal interface with dependent results:

```lean
structure EffectFamily where
  key : ScopeId
  Demand : Type u
  Result : Demand -> Type v
  requirements : ProviderDemandFamily
```

Examples are console writes, monotonic time, storage reads, Vulkan device
operations, or a project-local database transaction vocabulary. Families should
be narrow enough that selecting one communicates a useful requirement. A
single universal `SystemEffect` sum is prohibited.

A row is a finite, duplicate-free registry of families:

```lean
structure EffectRow where
  Key : Type u
  keys : List Key
  complete : forall key, key ∈ keys
  unique : keys.Nodup
  family : Key -> EffectFamily
  keysInjective : Function.Injective (fun key => (family key).key)
  requirementOriginsCompatible : PairwiseFamilyRequirementOriginsCompatible
    keys family

def EffectRow.Demand (row : EffectRow) :=
  Sigma fun key => (row.family key).Demand

def EffectRow.Result (row : EffectRow) (demand : row.Demand) :=
  (row.family demand.1).Result demand.2

def EffectRow.Contains (row : EffectRow) (family : EffectFamily) : Prop :=
  exists key, row.family key = family
```

This is a closed value for one selected program and an open extension mechanism
for the ecosystem. A new family is defined in a new module and inserted into a
row without editing an existing master inductive. Row constructors derive
`requirementOriginsCompatible` from hierarchical origin scopes; it is the exact
premise used by the total requirement-envelope fold. A collision with a
different descriptor fails when the row is built, not during later lowering.

Membership evidence embeds one family into one row and preserves its dependent
result exactly:

```lean
structure EffectEmbedding (family : EffectFamily) (row : EffectRow) where
  key : row.Key
  sameFamily : row.family key = family

class HasEffect (family : EffectFamily) (row : EffectRow) where
  embedding : EffectEmbedding family row

theorem EffectEmbedding.unique
    (left right : EffectEmbedding family row) : left.key = right.key := ...
```

`HasEffect` is authoring evidence, not provider selection. A reusable function
may quantify over `[HasEffect ConsoleWrite row]`; this says which abstract
operation it needs. It does not choose Win32, WASI, a mock, or a syscall. Row
construction, local lowering, and the later platform provider environment are
explicit values. Duplicate family keys or two incompatible embeddings are
rejected.

Typeclass synthesis may fill membership proofs after a row is explicitly
selected. It must not search a global registry to choose a provider, platform,
ABI, or effect semantics.

## 3. Portable operation theories

Syntax alone is not law-bearing. A family obtains portable meaning from a
separate theory, and the specification selects a finite suite of independently
keyed propositions about that theory:

```lean
structure EffectTheory (family : EffectFamily) where
  Context : Type w
  Observation : Type x
  enabled : family.Demand -> Context -> Prop
  History : (demand : family.Demand) -> Context -> Type y
  root : {demand : family.Demand} -> {before : Context} ->
    enabled demand before -> History demand before
  state : {demand : family.Demand} -> {before : Context} ->
    History demand before -> Context
  emitted : {demand : family.Demand} -> {before : Context} ->
    History demand before -> List Observation
  outcome : {demand : family.Demand} -> {before : Context} ->
    History demand before -> Option (family.Result demand)
  AllowedResult : (demand : family.Demand) -> Context ->
    family.Result demand -> Prop
  Extends : {demand : family.Demand} -> {before : Context} ->
    History demand before -> History demand before -> Prop
  historyEnabled : forall {demand before},
    History demand before -> enabled demand before
  rootState : forall {demand before} (enabledProof : enabled demand before),
    state (root enabledProof) = before
  rootEmitted : forall {demand before} (enabledProof : enabled demand before),
    emitted (root enabledProof) = []
  rootPending : forall {demand before} (enabledProof : enabled demand before),
    outcome (root enabledProof) = none
  prefixOrder : EveryOperationHistoryIsARootedPrefixOrder root Extends
  emittedPrefix : forall {demand before}
      {earlier later : History demand before},
    Extends earlier later -> emitted earlier <+: emitted later
  terminalMaximal : forall {demand before}
      {history later : History demand before} {result},
    outcome history = some result -> Extends history later -> later = history
  outcomeSound : forall {demand before}
      {history : History demand before} {result},
    outcome history = some result -> AllowedResult demand before result
  outcomeComplete : forall {demand before result},
    AllowedResult demand before result ->
    exists history : History demand before, outcome history = some result
  pendingRequirement : forall {demand before}
      (history : History demand before), outcome history = none ->
    PendingFrontierRequirement family.requirements demand before history
  infiniteAllowed : forall {demand before},
    InfinitePendingExtensionChain
      (History demand before) (@Extends demand before) (@outcome demand before) -> Prop
  infiniteRequirement : forall {demand before}
      (chain : InfinitePendingExtensionChain
        (History demand before) (@Extends demand before) (@outcome demand before)),
    infiniteAllowed chain ->
    PendingFrontierRequirement family.requirements demand before chain
  behaviorNonempty : forall {demand before}, enabled demand before ->
    Or (exists result, AllowedResult demand before result)
       (exists chain, infiniteAllowed chain)
  pendingContinues : forall {demand before}
      (history : History demand before), outcome history = none ->
    Or (exists later, ProperExtension Extends history later)
       (exists chain : InfinitePendingExtensionChain
          (History demand before) Extends outcome,
          chain.startsAt history /\ infiniteAllowed chain)

structure EffectLawSuite {family : EffectFamily}
    (theory : EffectTheory family) where
  demands : DemandFamily

structure CertifiedEffectTheory (family : EffectFamily) where
  theory : EffectTheory family
  laws : EffectLawSuite theory
  certificates : DemandCertificateFamily laws.demands

structure EffectRowTheory (row : EffectRow) where
  package : forall key, CertifiedEffectTheory (row.family key)
```

The displayed shape is a dependency contract, not a demand that every family
use one record literal. DSL-specific constructors may derive it.

`Context` is logical state belonging to the theory: bytes written so far, an
abstract file map, a clock history, or a graphics resource state. Composition
places it in a larger logical world through an explicit lens and proves overlap
or noninteraction. An Effect family never smuggles physical addresses, handles,
threads, or provider objects into a portable theory unless those values are
themselves part of the product contract.

`History` is the rooted finite-prefix tree of one logical operation from one
starting context. A nonterminal history records the logical state and
observations already visible while no result exists; a terminal history carries
the dependent result in `outcome`. A streaming write may therefore expose a
proper byte prefix before it returns. `Extends`, rather than pointwise membership
in unrelated `inflight` and `responds` relations, forces every later prefix to
belong to the same coherent operation witness. Emitted observations grow by
prefix, and a returned history cannot extend further.

The enabled root is inhabited, unchanged, silent, and nonterminal. Every
nonterminal history carries a neutral typed `PendingFrontierRequirement` whose
key and origin are members of `family.requirements`. The Process adapter must
realize that exact progress policy; an anonymous `Unit`/`True` reason cannot make
a vacuous effect lawful. Whether the policy requires a response or permits an
environment-controlled infinite wait belongs to the selected requirement and
later Process proof. `AllowedResult` is explicit; `outcomeSound` forbids extra
results and `outcomeComplete` prevents a theory from silently omitting an
allowed failure or nondeterministic branch. Every enabled request has an allowed
result or a constructive infinite pending chain whose exact pending policy is in the
requirement envelope. More strongly, every admitted nonterminal history either
has a proper coherent extension or begins an allowed infinite chain. Thus a
theory cannot hide a dead finite sibling behind a different successful branch.
Every theorem about a caller ranges over every history branch. A test run,
oracle, or selected successful response cannot prove the universal theorem.

Expected operational failure is normally a constructor of
`family.Result demand`. For example a write result distinguishes accepted
prefix, a returned zero-progress or would-block outcome where the contract has
one, and documented failure. An asynchronous request which has not responded is
instead a pending frontier and has no fabricated result. A process interruption,
logical fault, environment violation, or cancellation is not automatically
turned into an ordinary result. Those exits remain visible to the surrounding
process vocabulary unless a separately proved adapter converts one into an
explicit result demanded by the specification.

Each keyed theorem in an `EffectLawSuite` states a real proposition over the
theory; it is not a string tag. `CertifiedEffectTheory.certificates` is its
separate proof object and may be opaque downstream. Common laws include:

- result-space completeness and no fabricated result;
- exact logical pre/post-state change;
- observation order and projection;
- partial-transfer prefix conservation;
- compatibility and prefix closure between in-flight and returned behavior;
- permitted nondeterminism;
- commutation under a stated independence relation;
- progress to result or a genuine environmental frontier; and
- laws relating returned failures, partial transfer, and logical state.

The theory and selected law suite are precious when the specification selects
them. The kernel cannot infer that an arbitrary suite contains every desirable
product law; that is specification adequacy and review. What it does enforce is
that every selected keyed proposition has a separate certificate and survives
all later requirement projections. A record must not discharge its own laws
merely because those laws were fields chosen by the same author.
An `EffectLawSuite` enters an `EffectRowTheory`, DSL-capture junction, or handler
only through `CertifiedEffectTheory`; deleting one keyed proof therefore breaks
the local package before lowering begins.

## 4. Sequential effect programs

The core program is the free well-founded request/continuation tree over a selected
row:

```lean
inductive EffectProgram (row : EffectRow) (Result : Type v)
  | pure (result : Result)
  | request (demand : row.Demand)
      (resume : row.Result demand -> EffectProgram row Result)
```

`pure`, `map`, `bind`, `seq`, `traverse`, and `mapM` are ordinary constructors
and functions over this type. Structurally recursive or terminating recursive
Lean functions may produce programs. An unbounded reactive loop does not:
long-running state, cancellation, supervision, and environmental waiting belong
to `Process` or its `SequentialMachine` adapter.

An `EffectProgram` may be selected as a precious DSL fragment whose denotation
is captured into the one `SpecProcess`, or it may be a replaceable model or
construction witness for an independently stated contract. The datatype does
not decide preciousness; the specification suite's typed junction does. It is
never a second precious root and is not required on a direct assembly route.

The program is a well-founded W-type: each execution branch is finite, but an
infinite result type may make the tree infinitely branching, and branch depths
need not have one finite uniform bound. Proofs therefore use structural
induction and quantify over results rather than enumerate nodes or test cases.
“Finite” below describes rows, traces, and individual prefixes—not the total
cardinality of this syntax tree.

## 5. Relational syntax denotation

One selected row model embeds the family theories and their rooted operation
histories into a common logical world and observation type. It cannot replace
them with friendlier semantics:

```lean
structure EffectRowModel (row : EffectRow) where
  theories : EffectRowTheory row
  World : Type w
  Observation : Type x
  enabled : row.Demand -> World -> Prop
  History : (demand : row.Demand) -> World -> Type y
  state : {demand : row.Demand} -> {before : World} ->
    History demand before -> World
  emitted : {demand : row.Demand} -> {before : World} ->
    History demand before -> List Observation
  outcome : {demand : row.Demand} -> {before : World} ->
    History demand before -> Option (row.Result demand)
  Extends : {demand : row.Demand} -> {before : World} ->
    History demand before -> History demand before -> Prop
  realizes : EveryFamilyHistoryIsExactlyEmbedded
    theories enabled History state emitted outcome Extends

structure EffectInteraction (model : EffectRowModel row) where
  demand : row.Demand
  before : model.World
  history : model.History demand before
  result : row.Result demand
  completed : model.outcome history = some result

inductive EffectFrontier (model : EffectRowModel row) (alpha : Type v)
  | returned (value : alpha)
  | waiting (demand : row.Demand) (before : model.World)
      (history : model.History demand before)
      (pending : model.outcome history = none)

inductive EffectProgram.Prefixes
    (model : EffectRowModel row) : model.World -> EffectProgram row alpha ->
    List (EffectInteraction model) -> model.World ->
    EffectFrontier model alpha -> Prop
  | pure : Prefixes model before (.pure value) [] before (.returned value)
  | pending :
      (history : model.History demand before) ->
      (stillWaiting : model.outcome history = none) ->
      Prefixes model before (.request demand resume) [] (model.state history)
        (.waiting demand before history stillWaiting)
  | request :
      (history : model.History demand before) ->
      (completed : model.outcome history = some result) ->
      Prefixes model (model.state history) (resume result) rest after frontier ->
      Prefixes model before (.request demand resume)
        (⟨demand, before, history, result, completed⟩ :: rest) after frontier

def EffectProgram.Runs (model : EffectRowModel row) before program trace after result :=
  Prefixes model before program trace after (.returned result)

def PrefixObservations (trace : List (EffectInteraction model))
    (frontier : EffectFrontier model alpha) : List model.Observation :=
  (trace.flatMap fun interaction => model.emitted interaction.history) ++
  match frontier with
  | .returned _ => []
  | .waiting _ _ history _ => model.emitted history

structure EffectPrefixWitness
    (model : EffectRowModel row) (before : model.World)
    (program : EffectProgram row alpha) where
  trace : List (EffectInteraction model)
  after : model.World
  frontier : EffectFrontier model alpha
  valid : program.Prefixes model before trace after frontier

inductive EffectPrefixExtends :
    EffectPrefixWitness model before program ->
    EffectPrefixWitness model before program -> Prop
  | waiting : SameCompletedInteractions first second ->
      model.Extends firstWaitingHistory secondWaitingHistory ->
      EffectPrefixExtends first second
  | resumes : secondCompletesAnExtensionOf firstWaitingHistory ->
      RemainingInteractionsExtendFromThatExactCompletion ->
      EffectPrefixExtends first second
  | returned : SameReturnedPrefix first second -> EffectPrefixExtends first second
```

The exact lens/overlap certificate behind `realizes` belongs with the row/weave
bridge. It preserves and reflects root/history extension, state, observations,
allowed outcomes, constructive infinite histories, and pending-requirement
identity for every family while accounting for shared context deliberately. A
model cannot satisfy it merely by choosing its own unrelated laws.

`Prefixes` is a finite denotation of the syntax, not Grass's whole-program
execution semantics. It carries the actual rooted operation-history witness, so
successive prefixes and handler simulations preserve one coherent branch rather
than choosing unrelated pointwise states. `Runs` is only the returned-frontier
projection. Pending is not failure, termination, or permission to choose a
friendly result. A request which is not enabled has no rooted history and is a
failed proof obligation, not a pending environment frontier.

Every observation correspondence consumes `PrefixObservations`, not a fold over
completed interactions alone. This makes a completed operation followed by a
partially visible waiting operation retain both observation segments at a
cancellation cut or adapter boundary.

`EffectPrefixExtends` is the only legal relation between two snapshots of the
same program denotation. It preserves the completed interaction prefix and, at
the live operation, requires the later rooted history to extend the exact
earlier history; resumption begins only from a terminal extension of that same
history. Hence separately valid snapshots from two nondeterministic branches
cannot be spliced into one execution. Infinite pending denotation is a chain of
finite witnesses under this relation whose every frontier remains pending;
terminal histories cannot masquerade as infinite behavior by reflexive
repetition. A constant pending chain is permitted only when `infiniteAllowed`
names that exact environment-controlled wait policy. It is never a bag of
pointwise prefixes.

The trace is proof vocabulary, not necessarily a product observation. A
specification selects an observation projection. Safety, obligation, provider,
and applicability facts may never be erased by that projection.

No universal claim is made over an empty denotation. Capturing a program as a
DSL fragment or portable model requires:

```lean
structure EffectProgramAdequate
    (model : EffectRowModel row) (Initial : model.World -> Prop)
    (program : EffectProgram row alpha) where
  initialInhabited : exists world, Initial world
  reachableRequestsEnabled :
    EveryRequestReachedFrom Initial program HasAnEnabledRootHistory

structure EffectProgramMeetsProgress
    (adequate : EffectProgramAdequate model Initial program)
    (required : MaximalExecutionPolicy (EffectMaximalExecution adequate)) where
  exact : EveryMaximalEffectPrefixExecutionMeetsExactly required adequate
```

The second field quantifies through every permitted dependent result and every
reachable continuation. Root/history inhabitation, coherent extension, and the
typed pending requirement are then supplied structurally by the selected model.
Standard combinators synthesize adequacy compositionally; a genuinely
state-sensitive precondition remains an authored proof rather than a friendly
test run. `MaximalExecutionPolicy` is a generic neutral constructor from
`Specification`, parameterized by any execution-witness type; it has no Effect
dependency. Here it is instantiated with `EffectMaximalExecution adequate` and
names termination or permitted external frontiers without importing `Semantics`
or a `SpecProcess`. The later DSL-capture/model junction in `Refinement` proves
that this policy is exactly the selected specification progress demand and
carries the `EffectProgramMeetsProgress` certificate. A maximal
execution is either returned or a coherent infinite `EffectPrefixExtends` chain;
the theory's per-history continuation law and program adequacy make a finite
stuck waiting prefix unconstructible. A terminating contract universally rules
out admitted infinite chains and proves completion for every admitted
initial/environment branch; a reactive contract maps each allowed infinite
chain to its named external frontier. Mere existence of one returned run never
proves termination.

## 6. Monad and traversal laws

The monad laws are stated under relational equivalence, not assumed from a Lean
`Monad` instance and not proved by testing:

```lean
def EffectEquivalent (left right : EffectProgram row alpha) : Prop :=
  forall model before trace after frontier,
    left.Prefixes model before trace after frontier <->
    right.Prefixes model before trace after frontier

theorem bind_pure_left  : EffectEquivalent (pure x >>= f) (f x)
theorem bind_pure_right : EffectEquivalent (p >>= pure) p
theorem bind_assoc      : EffectEquivalent ((p >>= f) >>= g) (p >>= fun x => f x >>= g)
```

This core equivalence is deliberately strong: it retains every pending frontier,
request, result, emitted logical observation, and their sequential order.
Complete-run equivalence is a derived weaker theorem and must not be substituted
where progress, cancellation, or handler composition consumes prefixes. A
selected effect law may additionally define an observation congruence—for
example, coalescing
adjacent same-stream byte writes inside one input-free segment—and prove a
rewrite under that congruence. There is no universal coalescer. Reads and other
entropy-bearing inputs are causal anchors by default, and no rewrite moves an
output across one without an explicit independence theorem from the selected
theories. Process-level concurrent equivalence lifts these laws to its labelled
partial order; it does not mistake this list trace for a concurrency model.

The constructive proof is induction over `p`, with the request case applying
the induction hypothesis to every permitted dependent result. The implementation
may additionally prove definitional equalities where they happen to hold, but
public clients use the relational theorem.

`Vec.traverse` and `Vec.mapM` are left-to-right. Their proof package states that
the produced interaction trace is the ordered concatenation of the element
program traces in ascending index order and that pure traversal agrees with
`Vec.map`. No bare Lean `Monad` instance is sufficient evidence for this claim.

Effects may be reordered, eliminated, duplicated, or fused only by a theorem of
the selected family theories. A commutation theorem names exact footprints,
observations, shared state, resources, and abstract obligation requirements. Two
operations do not commute merely because their result types are independent.

## 7. Requirements

Effect law demands and lowering requirements are different objects. The neutral
typed lowering-requirement vocabulary is owned by `Specification`, below
Effect, Process, and Platform. An
`EffectLawSuite.demands` is a finite family of propositions proved about the
portable theory. An `EffectFamily.requirements` is a dependent
`ProviderDemandFamily`: every entry carries its nominal key, exact statement,
origin, and `RequirementAuthority`. The former is discharged by a
`DemandCertificateFamily`; the latter is certified against the exact neutral
`ProviderBindingView` exported by the selected platform environment. It flows
down until a handler or owning provider bridge discharges or forwards it.
Neither can be used as the other merely because both have stable diagnostic
keys.

Their key wrappers remain nominally distinct. A theorem-demand key, an abstract
effect requirement, a platform provider requirement, and an obligation protocol
key do not become interchangeable because each is ultimately scoped by a Core
identifier. Bridges carry typed origin evidence rather than casts between names.

An effect row's requirement envelope is definitionally the
membership-extensional union of its families' `requirements`. It is an ordinary
definition over the row's complete duplicate-free key list, not an
author-populated `requirementsExact` proof about an opaque extractor. A program
may use a sub-row and be lifted explicitly into a larger row:

```lean
structure EffectSubrow (small large : EffectRow) where
  embed : forall family, HasEffect family small -> EffectEmbedding family large

def EffectProgram.weaken
    (embedding : EffectSubrow small large) :
    EffectProgram small alpha -> EffectProgram large alpha

structure EffectRowModelEmbedding
    (rows : EffectSubrow small large)
    (smallModel : EffectRowModel small)
    (largeModel : EffectRowModel large) where
  worldRelation : smallModel.World -> largeModel.World -> Prop
  enabledExact : EmbeddedEnabledPredicatesAgree rows worldRelation
  historiesExact : EmbeddedOperationHistoriesAgree rows worldRelation
```

Dependent-result transport and requirement inclusion are derived from the exact
family embeddings; authors do not fill proof fields restating them. Syntax
weakening needs only `EffectSubrow`. A theorem preserving `Prefixes`/`Runs`
additionally consumes `EffectRowModelEmbedding`, because family membership alone
cannot prove that two independently chosen worlds and rooted histories agree.

The row is a declared capability envelope, not a claim that every possible
execution reaches every family. This distinction avoids an impossible finite
enumeration of continuations over arbitrary result types. It remains exact as a
declaration: every request is in the row, every row family contributes its named
requirements, and every introduced requirement is visible.

Reusable functions should remain row-polymorphic and request only their narrow
families. Whole-program construction chooses an explicit row. Unused broad rows
are an adequacy/proof-economy smell and may select needless providers, but they
do not justify unsound reachability inference in the kernel.

Requirement union is membership-extensional and canonically serialized.
Insertion order and duplicate insertions are not semantic identity. The raw
source/target envelopes are computed from the rows, but set subtraction is not
evidence that a requirement was discharged. Each handler certificate therefore
contains a typed `EffectRequirementSubstitution`: every source key is either
forwarded to a named target key with a semantic implication proof, or discharged
by a handler proof carrying authority to discharge that exact requirement; every
new target key cites its source or reviewed introduction authority. Only an
Effect-owned abstract-operation requirement has an Effect-level discharge
constructor, and that constructor requires the demand itself and its opaque
origin scope to be indexed by `.builtin .effect`; it does not inspect a
caller-filled authority tag. There is no generic
`discharge : Prop -> ...` constructor. Memory,
resource, platform/provider, ABI, and obligation keys must be forwarded until
their owner-specific later bridge supplies its distinct typed constructor.
Common identity and family-to-family substitutions are generated, but residual
semantic implications are real proof obligations. No requirement disappears
because an operation was hidden by notation.

## 8. Handlers and staged replacement

A handler replaces one source family with programs over a target row:

```lean
structure EffectHandler
    (source : EffectFamily) (target : EffectRow) where
  handle : (demand : source.Demand) ->
    EffectProgram target (source.Result demand)

structure RefiningEffectHandler
    (sourcePackage : CertifiedEffectTheory source)
    (targetModel : EffectRowModel target)
    (handler : EffectHandler source target) where
  relation : sourcePackage.theory.Context -> targetModel.World -> Prop
  initial : ...
  adequate : EveryRelatedEnabledSourceRequestProducesAnAdequateHandlerProgram ...
  implementationSound : EveryTargetPrefixPreservingHistoryExtension
    ProjectsToAnAllowedSourcePrefix ...
  observations : ExactFilteredPrefixObservationCorrespondence ...
  frontiers : EveryTargetWaitingRequirementMapsToAnAllowedSourceOrForwardedPendingRequirement ...
  requirements : ExactEffectRequirementSubstitution
    source.requirements target.requirementEnvelope handler

structure EquivalentEffectHandler ... extends
    RefiningEffectHandler sourcePackage targetModel handler where
  sourceCoverage : EveryAllowedSourcePrefixHasATargetPrefix
    PreservingHistoryExtension ...
```

`RefiningEffectHandler` is ordinary implementation refinement: the target
introduces no behavior forbidden by the source. `sourceCoverage` is additionally
required wherever Grass claims strong equivalence or exact preservation of the
source's result nondeterminism. A merely refining handler may deliberately
resolve underspecification to a subset; it may never introduce a target outcome
which the source forbids. The claimed relation determines which direction later
composition is allowed to consume. Both certificates quantify over pending and
returned `Prefixes`; a proof only about `Runs` cannot certify a handler.
Their simulations preserve `EffectPrefixExtends` along every target extension;
equivalence-strength coverage also reflects it.
At this layer a target wait maps only to a source history or an exactly forwarded
neutral pending requirement. The later adapter/refinement certificate alone may
realize that requirement as a Process frontier.

The source and target sets are derived rather than supplied. The substitution
between them is checked because semantics cannot be inferred from matching or
missing names. A handler needing another lower capability must put it in a
target family instead of hiding it in its proof. Partial plans derive identity
substitutions for the families they retain. Platform, ABI, memory, and obligation
requirements first introduced after this layer belong to the later
process/provider binding and its own typed origin map.

Identity handlers are equivalent. Certified handlers compose, and their
simulations, observation filters, and requirement deltas compose associatively;
the result is equivalent only when every composed leg supplies coverage, and is
otherwise refinement. The proof is relational composition plus induction over
the source program; no compiler is trusted to rediscover it.

A partial handler produces a blended row: handled source families are replaced,
unhandled families remain abstract, and the row records which is which. This is
the effect-level form of orthogonal staged refinement. A graphics proof may
replace an abstract graphics family with Vulkan/SPIR-V requirements while
storage remains abstract; a later proof may replace storage with IOCP without
reopening the graphics theorem.

## 9. Local lowering coherence and provider handoff

Effect lowering selects one local disposition for every source family. It does
not select physical API providers:

```lean
def EffectRequirementOriginScope
    (key : ScopeId) (target : EffectRow) :
    RequirementOriginScope (.builtin .effect)

structure EffectLoweringPlan
    (source : EffectRow) (sourceModel : EffectRowModel source) where
  key : ScopeId
  Target : EffectRow
  targetModel : EffectRowModel Target
  selected : forall key : source.Key,
    SelectedCertifiedDisposition (sourceModel.theories.package key) targetModel
  originFresh : RequirementOriginScopeFreshFor
    (EffectRequirementOriginScope key Target)
    (RequirementsOfSelection selected)
  targetCoverage : forall family,
    Target.Contains family <-> FamilyIntroducedOrRetained selected family
  Relation : sourceModel.World -> targetModel.World -> Prop
  initial : EveryAdmittedSourceInitialHasRelatedTargetInitial Relation
  step : EverySelectedDispositionPreservesRelationAndFramesUnmentionedState
    selected Relation
  overlap : EveryDeclaredSourceOverlapIsRealizedCoherently selected Relation
  observations : ExactComposedPrefixObservationCorrespondence selected Relation
  pendingAndExtension : EverySelectedDispositionPreservesPendingIdentityAndPrefixExtension
    selected Relation
```

The plan's nominal `key` scopes its finite provider-demand origin slots; it is a
construction identity, not a content hash or provider selection. Independent
plans use distinct hierarchical scopes, so their demands compose without losing
either exact origin even when both need the same provider capability.
`originFresh` is the checked premise used to derive
`EffectRequirementOriginsCompatible`; ordinary hierarchical plan constructors
generate it, while a reused/colliding scope fails locally.

The plan is indexed by the exact source row model, not merely by a bag of
per-family theories. `Relation` is the one whole-row simulation invariant.
`step` prevents independently valid handlers from clobbering another family's
representation, while `overlap` handles deliberately shared logical state. The
observation and pending fields make induction compose across successive
requests. The whole-program lowering theorem is derived from this certificate;
authors never assert a second unrelated global simulation.

The dependent function already gives each source key exactly one disposition;
there is no second `exactlyOne` field. `targetCoverage` is extensional family
membership rather than equality between structures containing types, functions,
lists, and proof fields. Public constructors build `Target` from the selection
and derive this witness; ordinary authors do not prove it by hand. The plan's
requirement delta is the checked union of each handler substitution and each
retained family's identity substitution; it is never plain set subtraction.

The Act 3 handoff is indexed by this exact plan, not just its requirement keys:

```lean
structure EffectProviderHandoff (plan : EffectLoweringPlan source sourceModel) where
  theoryPackages : forall key, CertifiedEffectTheory (plan.Target.family key)
  model : EffectRowModel plan.Target
  requirements : ProviderDemandFamily

def EffectLoweringPlan.handoff
    (plan : EffectLoweringPlan source sourceModel) : EffectProviderHandoff plan :=
  { theoryPackages := fun key => plan.targetModel.theories.package key
    model := plan.targetModel
    requirements := DerivedRequirementsOf plan }

def EffectLoweringPlan.realizationDemands
    (plan : EffectLoweringPlan source sourceModel) : ProviderDemandFamily :=
  ProviderDemandFamily.ofScope
    (EffectRequirementOriginScope plan.key plan.Target)
    (EffectProviderDemandDescriptor plan.handoff)

def EffectLoweringPlan.providerDemands
    (plan : EffectLoweringPlan source sourceModel) : ProviderDemandFamily :=
  ProviderDemandFamily.union plan.handoff.requirements plan.realizationDemands
    (EffectRequirementOriginsCompatible plan)

structure EffectPlanRealizedByView
    (plan : EffectLoweringPlan source sourceModel)
    (view : ProviderBindingView) where
  dictionariesExact : EverySelectedViewDictionaryRealizesExactTheoryPackage
    view plan.handoff.theoryPackages
  historiesSound : EveryViewOperationPrefixAndExtensionProjectsToSelectedHistory
    view plan.handoff.model
  requestCoverage : EveryEnabledTargetDemandCreatesAnExactEnabledViewOccurrence
    WithNonemptyTerminalOrInfiniteBehavior view plan.handoff.model
  adequacy : EveryEnabledViewOperationHasACoherentPrefixAndAccountedFrontier
    view plan.handoff.model
  maximalExecutions : EveryMaximalViewExecutionProjectsToTerminalHistoryOrAllowedInfiniteChain
    view plan.handoff.model
  privateProductivity : EveryNonterminalPrivateViewSegmentHasFiniteDecreasingRankOrProducesHistoryExtension
    view plan.handoff.model

theorem EffectLoweringPlan.providerDemands_certified_iff :
    plan.providerDemands.CertifiedBy view <->
      (plan.handoff.requirements.CertifiedBy view /\
       EffectPlanRealizedByView plan view)

theorem EffectLoweringPlan.realizationDemands_certified_iff :
    plan.realizationDemands.CertifiedBy view <->
      EffectPlanRealizedByView plan view
```

The handoff and its `providerDemands` are transparent derived values with no
author-populated proof fields. They retain the exact
law-bearing family packages, rooted history model, observation lenses, and
their nominal identities. Act 3 owns the nontrivial
`ProviderRealizesEffectPlan providerEnv plan` certificate tying each of those
values and every requirement origin to the selected physical dictionary;
matching a family or requirement name is insufficient. Its authoritative shape
is in [REFINEMENT.md](REFINEMENT.md#act-3-platform-realization).

The exported family is the exact compatible union of the retained and
handler-introduced requirements with the plan-realization demands; original
origin IDs survive unchanged. `providerDemands_certified_iff` is the no-loss
theorem. Act 3 may discharge provider-owned members and forward other authorities
to their later stages, but it cannot certify only the fresh realization half and
drop the inherited half.

`EffectPlanRealizedByView` is Effect-owned and mentions only the neutral binding
snapshot. Every fresh realization-demand statement is a local projection of this
structure.
Act 3 connects the selected physical environment to this predicate through
`providerEnv.bindingView`; environment-wide ABI/import/coexistence coherence
remains a separate Platform proof.

Its maximal-execution and productivity fields are universal. A favorable
response branch cannot hide a provider branch which stutters forever in private
state while projecting repeatedly to one pending abstract prefix. Every maximal
provider execution either reaches the exact terminal history or productively
extends an admitted `infiniteAllowed` chain; finite private work is justified by
a decreasing rank.

This plan may replace an abstract graphics family with a `Vulkan13` effect
family, but `Vulkan13` is still an abstract demanded API protocol family. The single
`PlatformPlan.ProviderEnv` owned by [PLATFORM_ABI.md](PLATFORM_ABI.md) later
binds every accumulated provider requirement to exact physical dictionaries,
imports, dispatch identities, ABI profiles, and runtime assumptions. That is
where whole-program provider consistency is established. Effect lowering feeds
the indexed handoff plus its requirements into that environment and cannot
create a competing provider registry.

A mid-level API may quantify over a family such as `Graphics13`; it may also
explicitly demand `Vulkan13` when that provider is product-visible. Neither use
authorizes global instance search to select a platform.

## 10. Process and serial-function connection

`EffectProgram` does not run beside `Process`. `Process.SequentialAdapter`
consumes it or an equivalent `SequentialMachine` and elaborates each request into
one exact process demand frontier. The adapter generates occurrence identities,
pending multiplicity, child bindings, channel escrow, and lifecycle plumbing.
Its reusable connection certificate characterizes the adapter in both
directions: every effect `Prefixes` derivation has the corresponding process
prefix after private-identity erasure, every normal live or returned adapter
prefix projects to an effect prefix, returned effect `Runs` correspond exactly
to terminal normal responses, and waiting frontiers correspond exactly to one live request
occurrence plus the same permitted partial context and observations. Only after
this certificate does Grass state whole-execution
refinement or equivalence; `Prefixes` alone is not a rival execution semantics.
The two normal directions preserve and reflect `EffectPrefixExtends` against
Process prefix extension, so one concrete run cannot splice abstract history
branches between observations.
Interruption, cancellation, logical fault, environment violation, and terminal
custody/disposition are Process-owned exceptional cuts, not effect frontiers. A
separate one-way `ExceptionalCutRefinesWaitingOccurrence` theorem retains the
exact partial state/observations and proves the Process-owned resource and
obligation disposition; it never projects the cut back as an ordinary wait or
result.
Both normal and exceptional connections use `PrefixObservations`; neither may
drop the waiting history's partial segment.

This requires a real pending-progress path. The adapter-owned waiting state
contains the exact rooted operation history, and a `pendingProgress` transition
extends that same history without consuming the occurrence, emitting precisely
the newly exposed `PrefixObservations`. Completion alone consumes the occurrence
and resumes the continuation. The Effect adapter generates this relation from
`EffectTheory.Extends` and proves an exact projection to the selected
`PendingInteractionModel`. For a plain `SequentialMachine`, the library accepts
a `SequentialPendingSemantics` indexed by that exact model: its automatic
`atomic` instance selects the canonical Unit-start, Unit-history, empty-
observation model and matches the currently landed adapter; a
streaming/custom instance supplies the history extension relation.
This optional certificate adds no field to a simple machine. A custom raw
`DirectRelationalProgram` may instead express pending progress as an internal
transition which preserves its exact held-occurrence bag. The general Effect
adapter may not be implemented by the atomic route, and the two routes share a
theorem only after preserving and reflecting `EffectPrefixExtends`.

The adapter constructs a `Process.CertifiedDirectProgram` whose dependent
`DirectProgramDerivation` payload retains the exact effect program,
`EffectProgramAdequate`, selected `EffectProgramMeetsProgress`, and adapter
certificate. The derivation is also indexed by the exact projected
`PendingInteractionModel`, `SequentialPendingSemantics`, and
Effect-theory-to-model projection; neither `certifiedMachine` nor the final
source constructor performs ambient model inference. Separately, the generated `CertifiedDriverBoundary` sidecar carries
the stable `plan.providerDemands`; the underlying five-field `DriverBoundary`
does not change. Its statements are indexed only by the source
and target row models, lowering plan, and handoff—not by the caller's program
body. Every generated operation occurrence points to the exact finite subfamily
it uses, which may contain zero, one, or several independent origins. The
certified wrapper's `originDemands` is extensionally fixed
to that boundary envelope, so a continuation-only edit rebuilds local adapter provenance
without changing an otherwise identical provider certificate.

The envelope is conservative: even `.pure` over a deliberately broad nonempty
row retains the plan's requirements. Unused broad rows remain a proof-economy
smell, but requirements are never dropped by runtime reachability inference.
Direct operations pay no Effect ceremony; their selected boundary still states
their actual lower requirements and each occurrence points to its exact
registered subfamily.
Decision 120 remains authoritative:

```lean
abbrev EffectDemand (boundary : DriverBoundary) := boundary.Demand
abbrev EffectResult (demand : EffectDemand boundary) := boundary.Result demand
```

An embedding from an effect row into a `DriverBoundary` proves exact demand and
dependent-result preservation plus requirement coverage. It is not a cast based
only on matching names.

A terminating, frontier-free pure or serial helper may be called inside an
effect continuation without becoming a child process. A computation which can
wait for external entropy, remain pending, be independently cancelled, or
interleave observably becomes a process frontier even if its physical provider
uses one blocking ABI call.

An interactive or infinite application loop is expressed by a `ProcessSpec` or
`SequentialMachine` whose individual decisions may construct finite effect
prefixes of well-founded effect programs. This gives strong induction inside
each global-loop turn without
pretending the whole application is a terminating free-monad value.

## 11. Memory, resources, and obligations

Effect theories state logical behavior and neutral theorem requirements. They do
not contain the canonical obligation ledger.

An effect such as `lock` may declare an obligation requirement saying that a
successful result creates an unlock duty with specified failure/cancellation
behavior. That statement is not itself a live duty. A later binding owned by
`Obligation`/`Refinement` proves that the selected provider transition creates
the exact existential obligation identity and that every continuation, transfer,
fault, cancellation, and terminal edge gives it an allowed disposition.

Similarly, an allocation effect may state logical success/failure and resource
requirements. `Memory` and `Std.Owned` prove provenance, loans, initialization,
cleanup, and physical representation. Effect code cannot mint provenance or
claim an allocation obligation discharged.

The bridge has one direction of ownership:

```text
Effect theory requirement
  -> selected process/provider operation contract
  -> canonical Memory/Obligation transition and certificate
```

There is no reverse import and no second effect-local ledger. A handler which
introduces a memory or obligation action adds the corresponding requirement to
its exact delta; whole-program closure later rejects an unbound one.

## 12. Failure, interruption, and cancellation

The result family must expose every ordinary outcome a caller is required to
handle. A helper may provide combinators for common exhaustive case analysis,
but it may not erase cases.

Process-level cancellation and interruption remain outside ordinary `bind`.
They can cut an outstanding request without invoking its normal continuation.
The process realization therefore proves the disposition of continuation state,
resources, partial effects, and obligations at that cut. An API-specific adapter
may reify cancellation as a normal result only when the portable specification
demands that behavior and a total equivalence theorem covers the race.

A handler which performs only finite internal work may be collapsed into one
logical operation by a finite-stuttering simulation. A handler which can block
must expose a real frontier. `fuel` exhaustion, timeout in a proof runner, or an
unexecuted continuation is not a program result.

Whole-process exit, abort, and thread termination are terminal Process
transitions, not effect requests faked with an uninhabited result type. Such a
fake cannot distinguish “the process terminated” from “the request is still
pending” in the complete-run relation and would lose terminal resource and
obligation dispositions.

## 13. First-class assembly route

The Effect layer is not a compiler mandate. There are two equal-status routes:

```text
portable EffectProgram/model -> lawful handlers -> process/CFG -> assembly
PortableSpecCertificate      -> authored process/CFG/assembly refinement
```

Both end at the same `SpecProcess` requirements, `DriverBoundary`, obligation
and memory models, machine semantics, artifact connection, and
`VerifiedProgram`. Both begin with the required assembly-independent proof that
a portable model satisfies the precious specification. The direct route may
then implement that model boundary with arbitrary custom assembly and prove the
local simulation directly. It bypasses `EffectProgram`, not the portable
correctness theorem.

Conversely, use of a high-level effect program cannot hide or replace authored
assembly. Generated CFG or instruction fragments become reviewed replaceable
construction input only when explicitly adopted; an assembly author may replace
them while retaining the same effect/specification theorem.

## 14. Proof construction and automation boundary

The reusable core proofs are conventional structural inductions:

1. monad laws: induction on the left program;
2. trace order: induction on program/traversed vector structure;
3. handler lifting: induction on the source program;
4. handler composition: relational composition and the lifting theorem;
5. requirement preservation: finite-set union/subset algebra; and
6. sequential adaptation: simulation on pure/request constructors plus the
   process adapter's occurrence invariant.

Automation may construct and kernel-check these certificates. It may normalize
syntax, solve finite row membership, transport dependent results through proved
equalities, and leave explicit residual goals for family laws. It may not invent
an invariant, infer a provider, decide a semantic observation filter, assume a
commutation law, or turn sampled execution into proof.

No public theorem uses `axiom`, `sorry`, `admit`, or `native_decide`. Finite
`decide`/`bv_decide` checks are acceptable only where the theorem still
quantifies over the entire finite domain. Universal effect results and contexts
are proved symbolically.

## 15. Sharding and rebuild locality

Each effect family owns a narrow signature module, theory module, law
certificate, and optional abstract lowering-handler modules. Public row and program
combinators depend on signatures and opaque certificates, not handler bodies.

A change to:

- one family operation invalidates that family and consumers of its signature;
- one family law invalidates its certificate and handlers consuming that law;
- one handler invalidates that handler and aggregate path, not sibling handlers;
- one physical provider choice invalidates its
  `ProviderRealizesEffectPlan`/platform/ABI/machine path, not the abstract
  lowering plan or portable caller proof; a changed target theory or requirement
  invalidates the affected lowering path; and
- one effect-program body invalidates its local model/process shard, not the
  effect family library.

Rows, handler plans, and requirement manifests are finite generated registries.
Clean builds may inspect them linearly; a local rebuild consumes cached `.olean`
signatures and certificates. No theorem type contains a million-instruction
whole-program source merely to state an effect law.

## 16. Required acceptance fixtures

The first implementation is incomplete until checked fixtures demonstrate:

1. `pure` has an empty trace and performs no operation.
   `pure` over a nonempty selected row still exports that row's conservative
   provider-demand envelope; lowering requirements do not disappear merely
   because this body reaches no request.
2. Two writes retain source order through `bind`, `mapM`, and `Vec.traverse`.
3. A result-dependent branch is proved for every permitted success and failure,
   including an infinite result type without enumeration; removing one
   `AllowedResult` branch violates outcome completeness.
4. An outstanding request admits a pending prefix without fabricating a result.
   The same fixture makes an unenabled request unable to construct
   `EffectProgramAdequate` or enter a DSL-capture/model junction. An enabled root
   with no terminal history must carry a real member
   `PendingFrontierRequirement` and an allowed constructive infinite chain, not
   an anonymous proposition. The same pending-only program cannot satisfy a
   terminating specification's `EffectProgramMeetsProgress`.
   Two individually valid prefixes from sibling history branches cannot form an
   `EffectPrefixExtends` chain. A two-history model with universal `Extends`
   and unequal observation prefixes is rejected by
   `PendingInteractionModel.observations_congruent`; it cannot masquerade as an
   atomic model by placing the observable change between equivalent histories.
   A custom model with `Start _ := Empty` cannot be selected by the standard
   atomic constructor, which owns its Unit start and history. A pending advance
   between distinct waiting occurrences is rejected because its history
   transport requires an equality of the dependent occurrences.
5. A project-local effect family is added from another module without editing a
   core sum type.
   Three independently authored extension-authority registries compose under
   both family-union associations after all pairwise and outer descriptor
   compatibility witnesses are supplied. Reindexing either association into
   the same canonical three-way union plan produces extensionally identical
   origin IDs, descriptors, and lookups; a fixture which omits an outer witness
   or replaces structural scope transport with an unchecked dependent cast
   fails. Reindexing `introduce scope slot descriptor` commutes with structural
   slot transport, so a scope cannot mint a different origin after embedding.
   An independently certified extension vocabulary and driver boundary survive
   two-way and three-way normalization through the standard envelope/sidecar
   reindex constructors with the identical `ProviderDemandView` and
   `origins_exact` theorem; a `Requires` predicate cannot inspect the old
   registry representation.
6. Row membership embeds dependent results exactly; a forged name-only embedding
   is unconstructible.
7. Duplicate family keys are rejected, and the lowering selection cannot carry
   two dispositions for one source key. Physical-provider duplication is
   rejected later by `PlatformPlan.ProviderEnv`.
8. Syntax weakening derives result/requirement preservation without authored
   fields; behavioral preservation requires and consumes a row-model embedding.
9. A handler discharges and introduces exactly its declared requirement delta;
   omission of one lower requirement fails, and an Effect handler cannot claim
   to discharge an obligation-, memory-, ABI-, or provider-owned key. The
   negative fixture starts from the exact owner-indexed origin and attempts to
   relabel it as `.builtin .effect`; changing only a descriptor or capability
   name cannot typecheck. An operation with two independent origins retains and
   disposes both, while an operation with an empty subfamily adds none.
   Exactness quantifies over every `ProviderDemandView`, not merely selected
   members: omitting one semantically required view makes the reverse direction
   of `origins_exact` false even when every retained origin remains registered.
10. Handler identity and two-stage composition agree with direct handling in
    both complete and pending-prefix behavior directions.
11. Graphics-only lowering leaves storage abstract, followed by storage-only
    lowering without reopening the graphics certificate.
    A provider with matching names but a different selected effect theory is
    rejected by the indexed Act 3 handoff.
12. A proposed reorder of noncommuting writes is rejected; an independent pair
    reorders only with a proved commutation certificate.
13. A lock-like effect cannot mutate the obligation ledger from this layer; its
    later binding creates and discharges the canonical duty exactly once.
14. Expected failure flows through the dependent result continuation, while an
    interruption does not silently invoke it. A completed interaction followed
    by a partially emitting wait/cut retains both segments in
    `PrefixObservations`. A streaming pending history exposes at least one
    observation before completion through `pendingProgress`; the atomic adapter
    is rejected for that theory.
15. A blocking handler exposes a process frontier and cannot claim finite silent
    execution.
16. `SequentialAdapter` generates distinct occurrence identities for two equal
    demands and preserves pending multiplicity.
17. A direct authored-assembly realization discharges the same specification
    requirement without constructing an effect-program witness.
18. Removing any family-law proof, handler simulation direction, requirement
    substitution entry, derived operation-origin demand, or provider-connection witness
    fails at the corresponding local declaration.

The implementation should begin with pure/request/bind, one two-operation test
family, row membership, relational runs, and one identity/translation handler.
Process, obligation, and platform bindings follow only after this core shape
elaborates and the negative fixtures bite.

## 17. Review questions

- Does a family expose every ordinary failure as a dependent result?
- Does every theorem quantify over all permitted responses rather than one run?
- Can a pending request be mistaken for termination or failure?
- Is a typeclass selecting only row membership, or secretly choosing a provider?
- Can two providers handle one coherent family without an explicit split?
- Does a handler prove both directions when the claim says equivalence?
- Are observation filters explicit and unable to hide safety or obligations?
- Can a lawless rewrite reorder, duplicate, eliminate, or fuse effects?
- Has an effect-local token become a counterfeit obligation or provenance ledger?
- Can a long-running or cancellable computation hide inside finite `bind`?
- Can a new family be introduced without editing a master enumeration?
- Can custom assembly refine the same requirement without a monadic witness?
- Does changing one provider leave unrelated portable and sibling proofs cached?
