# Composable specification languages

Grass specifications are precious compositions of small domain languages. No
single DSL is expected to express algorithms, binary syntax, reactive behavior,
temporal guarantees, resources, graphics, schemas, and platform boundaries
equally well. This document owns how those languages share one correctness
theory without prescribing implementation weaving.

## 1. One theorem, several authoring languages

Every specification language implements the same semantic interface:

```lean
structure ContractFragment (resources : R) where
  ports : SemanticPortFamily
  assumptions : AssumptionFamily ports
  guarantees : GuaranteeFamily ports
  observations : ObservationProjection ports
  failures : FailureProjection ports
  progress : ProgressFragment ports
  resourceUse : ResourceSemanticUse resources ports
  processDemands : FiniteProcessDemandFamily resources ports

class SpecificationLanguage {R : Type u} [ResourceModel R]
    (resources : R) (Syntax : Type) where
  wellFormed : Syntax -> Prop
  denote : (term : Syntax) -> wellFormed term -> ContractFragment resources
  sourceOwner : NormativeSemanticOwner Syntax

structure SomeSpecComponent {R : Type u} [ResourceModel R]
    (resources : R) where
  Syntax : Type
  language : SpecificationLanguage resources Syntax
  term : Syntax
  wellFormed : language.wellFormed term
  name : ComponentId
```

The language's syntax and the authored term are retained as precious source.
Its denotation is Lean-defined and kernel checked. A plugin may add a language,
but it cannot add a new meaning of refinement, safety, progress, resources, or
artifact correctness.

Initial language families include:

- relational specifications for mathematical input/output properties;
- stream and trace specifications for causal and reactive behavior;
- grammar/format specifications for text, binary, token, and instruction
  languages;
- protocol/state-machine specifications for contextual legality and failure;
- temporal specifications for progress, termination, cancellation, and
  environment premises;
- resource specifications parameterized over selected resource values;
- domain languages for graphics/scenes, database schemas/queries,
  filesystems/storage, ABIs, and other reviewed semantic domains.

This list is open. Each new language states what it denotes, how it composes,
which source is normative, and which validation fixtures can falsify its laws.

## 2. Semantic composition, not execution weaving

A specification suite connects fragments at typed semantic ports:

```lean
structure SpecJunction (left right : ContractFragment resources) where
  leftPort : left.ports.Key
  rightPort : right.ports.Key
  compatible : PortTypesAndDirectionsMatch leftPort rightPort
  relation : JunctionRelation leftPort rightPort
  totalForDemandedCases : JunctionCoversEveryDemandedValue relation
  preserves : JunctionPreservesObservationsFailuresProgressAndResources relation

structure SpecificationSuite (resources : R) where
  components : FiniteComponentFamily (SomeSpecComponent resources)
  junctions : FiniteJunctionFamily components
  closed : EveryInternalPortConnectedExactlyAsDeclared components junctions
  coherent : NoContradictoryGuaranteesOrResourceSemantics components junctions
  contract : BehaviorContract resources
  contractExact : contract = ComposeFragmentDenotations components junctions
  resourceSemantics : SelectedResourceSemantics resources
  resourceSemanticsExact :
    SuiteUsesSelectedResourceSemantics components resourceSemantics
  processDemands : FiniteKeyedProcessDemandFamily resources resourceSemantics
  processDemandsExact : processDemands =
    ComposeProcessDemands components junctions resourceSemanticsExact
```

This composition is precious only where it states meaning. Connecting an HTTP/2
frame grammar's decoded-frame port to an HTTP/2 protocol transition is semantic.
Connecting that protocol's accepted request to a route relation is semantic.
Projecting its response to observable bytes is semantic. Assigning those steps
to threads, processes, callbacks, basic blocks, buffers, registers, or APIs is
execution weaving and is not part of the suite.

Semantic composition closes and hides internal ports into one precious root
`SpecProcess`. The root retains the suite as source, the exact selected
resource-semantics snapshot, and theorem demands. Its public transition and
trace contract are derived, never separately maintained. `SEMANTICS.md` owns
the structure; this document uses its single capture constructor:

```lean
def SpecProcess.capture
    (suite : SpecificationSuite resources) : SpecProcess resources
```

`VerifiedProgram spec` is indexed directly by this one root `SpecProcess` and
targets its trace contract. There is no
parser-correctness theorem, protocol-correctness theorem, and reactive-
correctness theorem which can disagree while independently claiming success.
Local component theorems and junction theorems compose into that one demand.

The root is a semantic process, not an execution topology. A suite may contain
or connect other spec processes; `capture` existentially hides their internal
states and ports while preserving the selected public boundary. Lexer/parser,
connection/stream, graphics/storage, and other decompositions remain
replaceable presentations after that boundary theorem is established.

A DSL may also introduce an abstract process demand rather than construct a
witness:

```lean
structure RequiredProcessContract
    {R : Type u} [ResourceModel R] (resources : R) where
  boundary : AbstractProcessBoundary
  resourceView : RequiredResourceView resources
  contract : BehaviorContract resources

structure ProcessRequirement
    {R : Type u} [ResourceModel R] (resources : R) where
  required : RequiredProcessContract resources
  acceptable : (witness : SpecProcess resources) ->
    witness.boundary = required.boundary ->
    witness.resourceSemantics.restrict required.resourceView =
      required.resourceView -> Prop
  contractOnly : AcceptabilityDependsOnlyOnExportedSpecContract acceptable

structure SelectedProcessRequirementWitness
    (requirement : ProcessRequirement resources) where
  witness : SpecProcess resources
  boundaryExact : witness.boundary = requirement.required.boundary
  resourceViewExact :
    witness.resourceSemantics.restrict requirement.required.resourceView =
      requirement.required.resourceView
  acceptable : requirement.acceptable witness boundaryExact resourceViewExact

def parserRequirement (format : Format alpha) : ProcessRequirement resources :=
  { required := ParserProcess.requiredContract format
    acceptable := fun process boundaryExact resourceExact =>
      ParserProcessRealizes format process boundaryExact resourceExact
    contractOnly := ParserProcess.realization_extensional }
```

An enclosing spec may therefore say “a process implementing this parser,” use
only its typed `bytes -> done | needMore | invalid` contract, and prove its own
behavior parametrically over every acceptable witness. Weaving later supplies a
single parser process, a lexer/parser graph captured as one process, a generated
table parser, or direct assembly. The requirement is precious; the selected
witness and its internal topology are not. This is the specification-language
form of demanding lower-layer typeclass capabilities without running ambient
instance search after construction.

`ContractFragment.processDemands`, `SpecificationSuite.processDemands`, and
`SpecProcess.requirements` are the same finite keyed dependent family carried
through composition.  Refinement selects one
`SelectedProcessRequirementWitness` per key and records occurrence-exact
substitution.  A requirement cannot advertise one boundary while accepting a
witness at another boundary, and it cannot silently capture a different
resource view.

## 3. Junction examples

The HTTP/2 server suite has the semantic chain:

```text
TCP byte-stream/rechunking contract
  -> HTTP/2 frame and HPACK Format derivations
  -> HTTP/2 connection/stream protocol transitions
  -> route lookup relation
  -> response-field/body contract
  -> observable output-byte and terminal/failure trace
```

Flow-control credit, scoped errors, CONTINUATION ordering, and stream isolation
belong to the protocol fragment. Frame and HPACK accepted/rejected languages
belong to grammar fragments. Route selection belongs to a relation. Deadlines
and shutdown guarantees belong to temporal/resource fragments. The process
presentation can choose connection and stream roles because that is a useful
proof lens, but those roles are not forced by the captured root.

The sort suite combines a line-format/rechunking fragment, a stable-permutation
relation, allocation-failure silence, output framing, and progress. The gzip
suite combines gzip/DEFLATE formats, a decompression round-trip relation,
streaming prefix/failure behavior, and bounded history resources. The cube suite
combines scene geometry, input/reactive transitions, frame-observation accuracy,
temporal progress, and graphics resource demands.

## 4. Proof economy and change locality

Each component exports a small denotation theorem. Each junction exports a
small compatibility theorem. Changing a parser algorithm changes neither.
Changing grammar syntax rechecks its denotation and downstream junctions, but
not an unrelated route theorem. Changing route behavior rechecks the route and
response junction cone, but not the frame grammar. Changing a process topology
rechecks no precious component when its process presentation still denotes the
same suite contract.

Libraries generate standard junctions only from explicit types and laws. They
may not infer semantic intent from matching names, synthesize an unspecified
failure policy, silently select PEG priority, or turn a resource exhaustion
case into divergence. A novel junction remains ordinary Lean and can be proved
directly.

The corpus must include two views for each spike:

1. the complete precious DSL composition and its capture into one root
   `SpecProcess`; and
2. a non-precious realization map showing which process/model/assembly proof
   discharges each component and junction.

That map is review metadata and an invalidation guide, not a second
specification.

## 5. Extension discipline

A new specification language is accepted only with:

- a total Lean denotation into `ContractFragment`;
- an explicit account of assumptions, observations, failures, progress, and
  selected resource semantics it uses;
- composition/junction laws and conflict diagnostics;
- positive, negative, ambiguity, and mutation fixtures appropriate to the
  domain;
- a direct-proof escape hatch which does not require its preferred DSL; and
- a proof that its addition does not create a second `VerifiedProgram` route.

The family exists to make precious intent smaller and clearer. If using a DSL
requires encoding implementation topology or restating another fragment's
meaning, its boundary is wrong.
