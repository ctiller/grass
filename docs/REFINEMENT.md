# Refinement pipeline

Grass began with six conceptual acts. They are ordered proof concerns, not a
mandatory compiler pipeline or six required stored datatypes. A completed
certificate must connect high-level demands, composition, provider selection,
control/machine realization, closure, and artifact behavior in a sound order.
It may take any route whose dependent certificates compose those facts without
skipping a demand. In particular, authored assembly may refine a realized
platform contract directly instead of imitating a compiler-generated CFG.

The ordering is local, not a whole-program phase barrier. Different subgraphs
may temporarily sit at different refinement depths: graphics may already be a
Vulkan process/call graph while disk I/O remains an abstract storage protocol;
disk may later refine through a Win32 asynchronous-file protocol and then IOCP.
Each local proof preserves its exported protocol and introduces explicit lower
requirements. Whole-program closure requires every reachable abstract frontier
to be discharged, not every component to advance in lockstep.

The corpus uses three SDLC categories:

- **precious semantic source**: the transparent authored declarations that
  jointly state portable meaning and demanded theorems; these receive the
  highest intent review and contain no replaceable implementation identity;
- **reviewed replaceable construction input**: an explicit platform plan,
  authored assembly/CFG, process plan, or explicitly adopted generated-source
  snapshot selected to realize the
  spec; these are underdetermined by the spec, tuned/reviewed, and may be deleted
  and rebuilt or replaced; and
- **derived witness**: generated contracts, local certificates, proof terms,
  compiler-selected register allocation, encodings, layouts, and artifact bytes
mechanically dependent on the first two categories.

Generation history does not decide ownership. A generated snapshot becomes a
reviewed construction input only through explicit adoption as the source to tune
and preserve during that realization. Mechanically regenerable output which has
not been adopted remains a derived witness. Adoption is recorded and reviewed;
it cannot occur implicitly because a generated file happened to be inspected.

Several transparent declarations may jointly constitute one precious
specification; that composition is not a second independently maintained spec.
Register choices written literally in authored assembly are part of that
reviewed construction input, not a derived register-allocation result.

## Act 1: high-level refinement

Authors express the minimal precious specification using ordinary Lean models:
functional observations, outcome/status policy, safety, progress, liveness, and
terminal resource demands actually required. A generated-code route may also
express structure using high-level monads and prove that program satisfies the
specification. The direct authored-assembly route does not require a decorative
monadic program witness. Missing lower-layer facilities are introduced as
nominal capability requirements with laws, not assumed implementations.

The authored specification body may be relational or an abstract spec-process
network. Spec processes expose only logical roles, typed channels, linear/shared
logical state, and causal protocol laws; their derived trace denotation is not a
second maintained spec. Physical population, state partition, scheduling,
buffering, provider calls, and execution topology first appear in reviewed
replaceable realization inputs.

The portable source is a precious specification function parameterized by a
reviewed selectable resource model. The dependency points from resources into
the specification: exhaustion, admission, backpressure, and lifecycle semantics
are ordinary behavior of `spec resources`, not a later contract attached to an
already-closed behavior. Resource premises and theorem keys retain independent
dependency facets, so another resource instantiation reuses the specification
definition and every proof genuinely parametric in the model. Target
spelling—newline encoding, numeric status mapping, concrete
clock/API provider, ABI, and wire representation not explicitly promised by the
product—belongs to the Act 3 target projection rather than either portable
contract.

Resource capabilities are stratified typeclasses over an explicit resource
value. A specification declares only the bounded customization interfaces and
laws it consumes; it neither imports a universal resource schema nor chooses a
platform provider through instance search. Application- or domain-specific axes
extend the common algebra without invalidating specifications which never name
them.

Act 1 must end in a portable correctness theorem, not merely a proposition which
is left for machine code to prove directly. Its witness may be a pure function,
relational program, reactive application, process graph, or another Lean model:

```lean
structure PortableSpecCertificate {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources) where
  Model : Type
  model : Model
  satisfies : ModelSatisfiesSpecification model spec
```

`Model` is not required to appear in the precious specification source. It is a
replaceable proof witness whose theorem is independent of ISA, ABI, platform,
layout, and assembly identity. Later acts consume the theorem and prove the
selected realization refines `model`. This factors the final result as
`artifact -> assembly -> portable model -> specification`, allowing product
reasoning to be reused by every correct implementation.

Direct extensional assembly-to-specification proof remains available for truly
novel code, but it is an explicit escape hatch. It does not justify removing
the ordinary high-level theorem boundary or making assembly authors repeat
portable application proofs.

Portable code may demand an abstract effect; target-specific code may demand a
specific provider family. Requirements remain explicit data/propositions so
they can be propagated and reviewed.

## Act 2: weave

Weaving composes programs, specifications, observations, requirements, and
proofs. It includes sequencing, parallel composition, linking, shared-state
composition, adapters, and proofs of noninteraction between independently
running components.

When a process presentation has been proved exact for the precious contract,
Act 2 proves that a selected `ProcessRealization` refines that abstract network. It need not have
the same number of processes or channels: one abstract connection session may
be serialized, multiplexed through a reactor, or distributed across workers as
long as the refinement preserves its denotation, causal ordering, linear state,
and demanded resource behavior.

Local heterogeneous refinement uses an explicit lens:

```lean
structure ProcessRefinementLens
    (whole : ProcessGraph) (selected : ProcessScope whole) where
  boundary : AbstractProcessBoundary selected
  context : ProcessContext whole selected boundary
  source : ProcessSubgraph boundary

structure LocalProcessRefinement (lens : ProcessRefinementLens whole selected) where
  replacement : ProcessSubgraph lens.boundary
  simulation : replacement.Refines lens.source
  observations : PreservesProjectedObservationOrigins lens replacement
  custody : PreservesLinearStateAndObligationBoundary lens replacement
  resources : PreservesBoundaryResourceFlux lens replacement
  progress : PreservesOrStrengthensProgressWithNamedPremises lens replacement
  newRequirements : RequirementFamily

theorem refineSubgraph
    (local : LocalProcessRefinement lens) :
    ReplaceAt whole lens local.replacement
      ⊑ whole.withRequirements local.newRequirements
```

The context/frame proof keeps nonselected processes and their certificates
unchanged. A replacement may refine one abstract role into several processes or
serialize several roles into one; equality of process count or topology is not
required. Independent local refinements commute when their boundaries,
requirements, and shared-resource effects are disjoint or explicitly proved
compatible.

The author-facing staged form is indexed by an exact, replaceable process
presentation of the precious specification. No role projection is fabricated
from an arbitrary behavior contract:

```lean
structure StagedProcessPresentation
    {R : Type u} [ResourceModel R] {resources : R}
    (spec : SpecProcess resources) where
  network : AbstractSpecificationProcessNetwork resources
  resourceView : network.RoleSchema -> RequiredResourceView resources
  resourceRestrictionExact : forall schema,
    (network.protocol schema).resourceSemantics.restrict (resourceView schema) =
      spec.resourceSemantics.restrict (resourceView schema)
  resourceViewsCoverRoot : ExactUnionOfRequiredResourceViews
    resourceView spec.resourceSemantics.requiredAxes
  denotationExact : network.traceDenotation = spec.contract
  requirementsExact : TransportedProcessRequirements network denotationExact =
    spec.requirements

def StagedProcessPresentation.ofNetwork
    (spec : SpecProcess resources)
    (network : AbstractSpecificationProcessNetwork resources)
    (resourceView : network.RoleSchema -> RequiredResourceView resources)
    (resourceRestrictionExact : forall schema,
      (network.protocol schema).resourceSemantics.restrict (resourceView schema) =
        spec.resourceSemantics.restrict (resourceView schema))
    (resourceViewsCoverRoot : ExactUnionOfRequiredResourceViews
      resourceView spec.resourceSemantics.requiredAxes)
    (denotationExact : network.traceDenotation = spec.contract)
    (requirementsExact :
      TransportedProcessRequirements network denotationExact = spec.requirements) :
    StagedProcessPresentation spec :=
  { network, resourceView, resourceRestrictionExact, resourceViewsCoverRoot,
    denotationExact, requirementsExact }

def StagedProcessPresentation.ofProtocol
    (spec : SpecProcess resources)
    (protocol : ProtocolSpec resources)
    (resourceView : protocol.RoleSchema -> RequiredResourceView resources)
    (resourceRestrictionExact : forall schema,
      protocol.resourceSemanticsFor schema |>.restrict (resourceView schema) =
        spec.resourceSemantics.restrict (resourceView schema))
    (resourceViewsCoverRoot : ExactUnionOfRequiredResourceViews
      resourceView spec.resourceSemantics.requiredAxes)
    (denotationExact : protocol.denotation = spec.contract)
    (requirementsExact :
      TransportedProtocolRequirements protocol denotationExact = spec.requirements) :
    StagedProcessPresentation spec :=
  (ProtocolSpec.elaboratesToProcessNetwork protocol).presentation
    resourceView resourceRestrictionExact resourceViewsCoverRoot
    denotationExact requirementsExact

structure ProcessNormalization (spec : SpecProcess resources) where
  normalized : SpecProcess resources
  resourceSemanticsExact :
    normalized.resourceSemantics = spec.resourceSemantics
  bodyExact : normalized.contract = spec.contract
  requirementsExact : TransportRequirementsAcrossBodyEquality
    normalized.requirements bodyExact = spec.requirements
  processShape : StagedProcessPresentation normalized
  realizationTransport : ProcessRealization normalized -> ProcessRealization spec
  realizationTransportExact : forall realization,
    RealizationTransportPreservesBodyRequirementsAndResourceSnapshot
      realization (realizationTransport realization)
      bodyExact requirementsExact resourceSemanticsExact

def ProcessNormalization.shape
    (normalization : ProcessNormalization spec) :
    StagedProcessPresentation normalization.normalized :=
  normalization.processShape

structure SubsystemRealization
    (shaped : StagedProcessPresentation spec)
    (schema : shaped.network.RoleSchema) where
  implementation : PortableClosedSubgraph
    (shaped.network.protocol schema).boundary
  boundaryExact : implementation.ExportsExactly
    (shaped.network.protocol schema).boundary
  refines : forall instance : shaped.network.Instance schema,
    implementation.instantiate instance
      |>.Refines (shaped.network.instances schema instance)
  internalFrontiersClosed : forall instance frontier,
    ReachableInternalFrontier (implementation.instantiate instance) frontier ->
    FrontierRealized frontier
  requirements : RequirementDelta

inductive BlendedNode (shaped : StagedProcessPresentation spec)
    (schema : shaped.network.RoleSchema)
  | abstract
  | realized (certificate : SubsystemRealization shaped schema)

structure BlendedProcessGraph (shaped : StagedProcessPresentation spec) where
  nodes : forall schema : shaped.network.RoleSchema,
    BlendedNode shaped schema
  composition : MixedNodesComposeAtExactAbstractBoundaries nodes
  requirements : ExactUnionOfRealizedRequirementDeltas nodes

structure PartialProcessRealization
    (shaped : StagedProcessPresentation spec)
    (graph : BlendedProcessGraph shaped) where
  origin : ExactBlendedGraphOrigin shaped graph
  localRefinements : EveryRealizedNodeHasItsExactCertificate graph

def ProcessRealization.blend
    (graph : BlendedProcessGraph shaped) :
    PartialProcessRealization shaped graph

structure ClosedBlend
    (partial : PartialProcessRealization shaped graph)
    (complete : EverySchemaRealizedParametrically graph)
    (coherent : AccumulatedPortableRequirementsResourcesAndObligationsCoherent
      partial) where
  realization : ProcessRealization spec
  provenance : ClosedBlendProvenance spec realization.boundary
    realization.registry realization.plan realization.correct
  exactSource : ProvenanceNamesExactPartialGraphAndCertificates
    provenance partial
  exactClosure : ProvenanceNamesExactClosureEvidence
    provenance complete coherent
  originExact : realization.origin = .blended
    realization.registry realization.plan realization.correct provenance

def PartialProcessRealization.close
    (partial : PartialProcessRealization shaped graph)
    (complete : EverySchemaRealizedParametrically graph)
    (coherent : AccumulatedPortableRequirementsResourcesAndObligationsCoherent
      partial) :
    ClosedBlend partial complete coherent
```

`RoleSchema` is finite static syntax; its `Instance` family may be infinite.
Thus one connection-session schema has a proof polymorphic in
`ConnectionId`—closure never enumerates runtime identities. A realized node is
internally frontier-closed, so an abstract descendant cannot hide beneath an
outer `.realized` tag.

No specification has intrinsic role projections. Before `blend`, the author or
library supplies an explicit `ProcessNormalization` whose denotation and
requirements are exact. A protocol presentation and the sequential adapter are
standard constructors. The normalized `SpecProcess`, its process-shaped
presentation, equality of the retained resource snapshot, body/denotation
transport, requirement transport, and realization transport are actual fields.
No constructor calls `SpecProcess.fromBody` or re-runs
construction-time resource typeclass search; staging remains indexed by the
resource snapshot retained in the suite and root. `realizationTransport`
returns the closed realization to the original
precious `spec` with all three equalities. Failure to construct normalization
leaves direct relational realization available; it never fabricates roles or
changes the specification.

An abstract node is proof-visible but not executable. A runnable prototype uses
a proved mock/interpreter `SubsystemRealization`; unresolved abstraction is not
silently trusted. `VerifiedProgram` accepts `closed.realization` only together
with its indexed `ClosedBlend`; it never accepts a partial blend or closure
evidence belonging to another graph. The realization's `.blended` origin
retains that same dependent provenance after ordinary process APIs hide staging.

This Act-2 blend is portable. It may introduce a Vulkan, IOCP, or other provider
requirement and prove refinement to that provider's abstract API model, but it
does not claim x86, SPIR-V, ABI, encoding, or artifact identity before target
projection and a coherent platform plan exist. After selection, the same lens
supports a second, machine-indexed blend:

```lean
structure MachineSubsystemRealization
    (driver : ProjectedDriverCertificate portable projection)
    (scope : ClosedProcessOriginScope driver.plan.processOrigin) where
  source : HeterogeneousMachineSource driver.plan scope
  local : SourceRefinesExactClosedScope source scope
  boundary : MachineSourceExportsExactDriverBoundary source scope
  crossIsa : EveryCrossIsaEdgeConnected source driver.plan scope

structure MachineBlend
    (driver : ProjectedDriverCertificate portable projection) where
  origin : ProcessPlanSource spec driver.plan.boundary
  originExact : origin = driver.plan.processOrigin
  nodes : forall scope : ClosedProcessOriginScope origin,
    MachineSubsystemRealization driver (originExact ▸ scope)
  coverage : EveryReachableClosedScopeAppearsExactlyOnce nodes
  coherent : MachineSourcesAbiIsaAndProviderCoherent driver nodes
```

`MachineCertificate` consumes this exact `MachineBlend`, whose dependent
`origin` is the exact `ProcessPlanSource` value retained by the platform plan.
For a `.blended` origin that value contains the exact graph and closure
certificates; it cannot be reconstructed from a lookalike plan or replaced by
an extensionally similar source. This is where one team may finish the Vulkan
x86/SPIR-V source proof before another finishes the IOCP x86 source proof,
without losing either artifact connection at the final gate.

Weaving must preserve existing theorems and may introduce new interference,
provider-coherence, resource, progress, or obligation requirements. It must not
silently resolve conflicts through instance priority.

Global invariants are exported as independently owned, frameable families—for
example admission permits, generation freshness, race arbitration, slot
ownership, obligation custody, and resource accounting—not proved as one
inseparable conjunction. A plan-specific aggregate witness may collect those
certificates for a closing theorem, but changing one family must not reopen
proofs of the framed families. Each transition declares the families it opens;
the composition frame theorem preserves the rest. Cross-family steps supply an
explicit coupling lemma rather than depending on record-field proof order.

A single component uses the identity weave implicitly. This boundary remains
available for diagnostics and later composition but creates no author ceremony.

## Act 3: platform realization

An explicit `PlatformPlan` owns a `ProviderEnv` assigning nominal provider keys
to cited API/platform profiles and proves compatibility. Typeclasses are
projections of that explicit environment; the plan does not perform a later
ambient search. Realization proves that the exact dictionary used by upstream
definitions and proofs is the selected provider. Provider identities and
environment evidence are ghost-propagated through requirements, ABIs, blocks,
calls, and obligations.

One provider key has one realization. Intentional multi-backend programs use
distinct keys and prove their coexistence. Platform, ISA, and API set are
independent axes constrained by the plan.

The plan contains a `TargetProjection` from the tripartite product boundary. It
must prove that normalization of observations and outcomes is faithful, that
the selected capabilities discharge exactly the abstract requirements, and
that target-specific failure values do not collapse a portable failure into
success. Projection is not permission to change the specification during a
port; a change in admitted product behavior belongs in the behavior or resource
contract.

Provider realization may consume a proved high-level program or derive a
platform contract directly from a specification's abstract operations. Each
abstract operation is refined to its provider operation with a simulation or
equivalence theorem over all results the provider permits.

## Act 4: control/machine realization

There are at least two equal routes from a realized platform contract:

- generated lowering turns monadic structure into a typed CFG; or
- authored assembly supplies a typed CFG that directly refines the same
  platform contract.

Neither route is semantically privileged. Generated lowering may choose storage
and register allocation; authored assembly chooses its own, subject only to the
boundary contract. Programs may mix routes at requirement, block, or sub-CFG
granularity.

Pure provider/driver glue may prove its provider-facing extensional event
contract directly. Reusable algorithms instead bank their mathematical proof at
an explicit model boundary:

```lean
structure ImplementationCertificate
    (implementation : ImplementationModel)
    (contract : ComponentContract) where
  realizes : ImplementationRealizesContract implementation contract

structure ImplementationBinding
    (source : MachineSource plan) (requirement : ProgramRequirement) where
  sourceScope : SourceScope source
  componentContract : ComponentContract
  implementation : ImplementationModel
  representation : RepresentationPlan sourceScope
  model : ImplementationCertificate implementation componentContract
  assembly : AssemblyRefinesImplementation
    sourceScope representation implementation
  connects : ComponentContractRefinesRequirement componentContract requirement

structure ImplementationBundle
    (source : MachineSource plan) (program : ProcessRealization spec) where
  processRequirements : RequirementSubstitution spec :=
    program.requirementSubstitution
  bindings : FiniteDependentMap (ProgramRequirement program)
    (ImplementationBinding source)
  scopeCoverage : ExactClaimedSourceScopeCoverage bindings
  requirementCoverage : ExactClaimedRequirementCoverage bindings
  overlap : DisjointOrExplicitlyComposedOverlaps bindings
  substitutionCoverage :
    EverySelectedProcessRequirementWitnessConnectedToExactBindings
      processRequirements bindings

theorem assembly_model_component
    (binding : ImplementationBinding source requirement) :
    AssemblyImplementsRequirement binding.sourceScope requirement
```

Stable sorting, CRC, LZ77, Huffman, bit writing, parsers, and other data
transformations prove `ImplementationRealizesContract` once. Assembly proves its
representation, control, and complete execution refinement to that exact model.
An optimized or novel assembly body remains unrestricted: it may refine the
same model, select/prove another model, or deliberately pay for a direct
extensional proof. The framework does not force simulation of an irrelevant
library implementation, but spike/library defaults may require the reusable
model adjacency to demonstrate the intended proof economy. Whole-application
I/O, failure, terminal and progress correctness is composed outside these
component bindings; no pure sort or codec model claims to realize it alone.

The source phase accepts an explicit `PlatformPlan` and authored `AsmSource` but
does not claim refinement. The closing elaborator separately accepts `spec`, a
sequential relational proof or explicit `ProcessPlanRealizes` witness, the
selected plan source, and machine source. Sequential authoring is normalized by
`SequentialAdapter`; both modes construct one `ProcessRealization`, any selected
algorithm-model certificate/refinement, the exact platform contract, and
assembly-refinement witness as
inspectable proof objects. Naming those intermediates is optional and useful for
diagnostics, library sharing, or multiple implementations, not a ceremony
imposed on a one-component program.

Each basic block type carries an entry contract and all normal, call, pending,
fault, interruption, and terminal exit contracts. Local symbolic verification
proves the body establishes an exit. Calls and jumps prove that the source state
satisfies the callee or target entry contract. Contracts name registers, stack,
memory shape, ghost state, obligations, and progress assumptions.

Labels are Lean identifiers (`Name`) wrapped with a scope-unique nominal identity
and a no-duplicate proof. They are not unvalidated strings or final addresses.
Indirect edges require a proved finite target set or are rejected.

## Act 5: fractal lowering

A requirement description is repeatedly replaced by concrete operations or
calls/edges to further blocks. Lowering may produce zero, one, or many operations
and dependent outcomes. Mixed realized and unresolved bodies are allowed during
construction; `VerifiedProgram` requires closure.

Assembly and verified macros are first-class replacements. Local certificates
are indexed by their code, selected profiles, and boundary contracts rather than
the identity of an entire surrounding CFG. Checked plugging preserves those
proofs across unrelated graph changes. The consequence rule permits a new entry
only when it entails the proved entry and permits a new exit only when the proved
exit entails it, separately for every exit kind. Resource framing is a distinct
theorem requiring disjoint ownership, noninterference, and obligation
preservation. Progress measures/frontier laws require dedicated refinement and
are not transported by ordinary consequence.

Phase one of `asm_source` emits syntax/source identities only; it cannot claim a
semantic boundary identity before the exact process/platform contract exists.
Phase two computes stable alpha-normalized boundary facets and emits each block
certificate in a measured content-addressed proof shard plus a hierarchical
verified replay manifest, rather than declarations in one opaque `.olean`. The
leaf cache locator contains canonical source/consumed-boundary facets and a Merkle root of
the exact theorem type, transitive semantic/profile environment, verifier,
toolchain/options, and axiom-audit policy. A changed block elaborates and
kernel-checks its affected shard; an unchanged sibling subtree is imported by
its prior root and its replay theorem checks the current environment and theorem
type. Cached sub-CFG/component compositions feed final layout/link modules which
depend on the exact selected roots and block outputs.

This is an explicit build architecture, not a promise that declarations inside
one changed Lean module somehow evade elaboration. Generated call/loan binders
are existential or dependently bound and alpha-normalized; ephemeral names and
proof terms do not enter boundary hashes. The manifest and every imported
certificate remain reproducible by clean uncached construction.

The process stops only when every reachable body is a raw-erasable CFG over the
selected ISA and platform calls. A `StraightLineOp` may internally contain CFG
structure only with a proof that its only normal exit is after its final logical
operation; all other fault/interruption exits remain declared.

## Act 6: optimization

Optimization may occur at high-level structure, CFG, layout, or instruction
sequences. Each pass proves preservation of the relevant projected functional
behavior and every independent mandatory demand. Proofs should depend on
abstract block/effect theorems so instruction scheduling and layout changes do
not re-prove unrelated high-level properties.

Low-level contracts are extensional specifications. Symbolic assembly
verification should automatically establish most straight-line implementations
against them. Implementations proved equivalent to the same deterministic
contract are equivalent by composition; relational contracts use the required
directed refinements. Loops normally expose an invariant and measure/frontier
law rather than a hand-written instruction-by-instruction bisimulation.

For process-backed programs, reordering and batching proofs happen before
flattening. The graph derives independence from disjoint local state, compatible
shared access, distinct channel escrows, obligations, and exact provider/
observation footprints. Its diamond theorem generates trace congruence under
adjacent independent syscall swaps. Instruction streams which refine different
linearizations of the same process partial order therefore obtain strong
observed equivalence without a bespoke flattened-trace bisimulation.
Noncommuting handle, time, cancellation, shared-write, and obligation edges
remain ordered.

## Libraries and proof economy

Libraries package specifications, requirements, refinements, ABIs, verified
blocks, exports, serializers, and automation. Reusable theorems own routine
drudgery. Automation may construct proof terms; it may not replace kernel
checking or hide unresolved cases.

Proof economy includes incremental invalidation. Certificates depend on the
smallest reviewed interfaces that justify them: local blocks on boundary
contracts, provider realization on abstract effect laws, and artifact stages on
exact preceding outputs. Generated identities must not leak into precious
specifications or unrelated proofs. A build should explain why a changed
specification field invalidates each rebuilt certificate; whole-program proof
churn from an independent local edit is a design defect.

Every incremental build emits a pre-build invalidation plan and a separate
post-build execution report:

```lean
inductive SourceClass | preciousSemantic | reviewedConstruction | derivedWitness
inductive SemanticStatus | reusable | invalidated | new | removed
inductive BuildAction | elaborate | kernelCheck | generate | link | serialize

structure DependencyEdge where
  source : DeclarationId
  consumer : DeclarationId
  semanticFacet : FacetId
  cacheKeyContribution : CacheKeyPart

structure LocalityContract where
  fixture : MutationFixtureId
  reviewedBoundary : DeclarationId
  stableSubjects : Finset DeclarationId
  consumedFacets : DeclarationId -> Finset FacetId
  allowedImpactCone : Finset DeclarationId
  allowedActions : DeclarationId -> Finset BuildAction
  requiredActions : DeclarationId -> Finset BuildAction
  requiredReuse : Finset DeclarationId
  stableSubtreeRoots : Array MerkleRoot

structure PlannedImpact where
  subject : DeclarationId
  semanticStatus : SemanticStatus
  expectedActions : Finset BuildAction
  causalFacetPaths : Array (NonEmptyList DependencyEdge)
  expectedCacheKey : Option CacheKey

structure InvalidationPlan where
  changedInputs : Array (DeclarationId × SourceClass)
  localityContract : LocalityContract
  impacts : Array PlannedImpact

structure BuildResult where
  subject : DeclarationId
  priorIdentities : Option IdentityFacets
  currentIdentities : Option IdentityFacets
  actualActions : Finset BuildAction
  cacheEvidence : CacheEvidence

structure BuildExecutionReport where
  plan : InvalidationPlan
  results : Array BuildResult
  complete : PlannedAndActualSubjectsCovered plan results
  respectsLocality : ResultsSatisfyLocality plan results

structure SemanticEnvironmentRoot where
  theoremType : NormalizedTheoremTypeHash
  imports : MerkleRoot -- every transitive consumed semantic/API/ISA/ownership facet
  profile : CanonicalProfileFacet
  generatorVerifier : ToolVersionRoot
  leanKernelOptions : LeanKernelAndOptionRoot
  axiomAuditPolicy : AxiomAuditAllowlistRoot

structure BlockCacheLocator where
  source : CanonicalSourceFacet
  consumedBoundary : CanonicalBoundaryFacet
  environment : SemanticEnvironmentRoot

structure SourceFragmentClosure (fragment : AuthoredSourceFragment) where
  expanded : RawInstructionFragment
  expansionExact : FragmentExpansionExactly fragment expanded
  symbols : FragmentSymbolSummary fragment expanded
  imports : FragmentImportSummary fragment expanded
  boundaries : FragmentBoundarySummary fragment expanded
  resolved : EveryReferenceResolvedLocallyOrExported fragment symbols

structure FragmentBehaviorCertificate
    (closed : SourceFragmentClosure fragment) where
  expandedIdentity : ExactExpandedFragmentIdentity closed.expanded
  certificate : FragmentMachineCertificate
    closed.expanded closed.boundaries closed.imports

inductive SourceClosureNode
  | fragment (source : AuthoredSourceFragment)
      (closed : SourceFragmentClosure source)
  | shard (children : Array SourceClosureNode)
      (summary : ComposedSourceSummary children)
      (interfacesExact : ChildExportsImportsMatchExactly children summary)
      (syntacticComposition : ChildSourceSummariesCompose children summary)
  | component (children : Array SourceClosureNode)
      (summary : ComposedSourceSummary children)
      (interfacesExact : ChildExportsImportsMatchExactly children summary)
      (syntacticComposition : ChildSourceSummariesCompose children summary)

inductive BehaviorCertificateNode : SourceClosureNode -> Type
  | fragment (closed : SourceFragmentClosure source)
      (behavior : FragmentBehaviorCertificate closed)
  | shard (children : Array SourceClosureNode)
      (certificates : forall index, BehaviorCertificateNode children[index])
      (composition : ChildMachineCertificatesCompose certificates)
  | component (children : Array SourceClosureNode)
      (certificates : forall index, BehaviorCertificateNode children[index])
      (composition : ChildMachineCertificatesCompose certificates)

structure HierarchicalClosedAsmSource where
  root : SourceClosureNode
  sourceCoverage : EveryAuthoredFragmentAppearsExactlyOnce root
  macroCoverage : EveryMacroDefinitionAndExpansionIsAClosedFragment root
  staticCoverage : EveryStaticObjectAndSymbolIsOwnedByOneFragment root
  importCoverage : RootHasNoUnresolvedInternalReference root
  rawListing : HierarchicalConcatenation root
  listingExact : RawListingObtainedByRecursiveChildConcatenation root rawListing

structure HierarchicalMachineCertificate
    (source : HierarchicalClosedAsmSource) where
  behavior : BehaviorCertificateNode source.root
  rootContract : ComposedMachineContract behavior

structure BlockReplayEntry where
  locator : BlockCacheLocator
  module : ImportedKernelCheckedLeanModule
  theoremName : Name
  sourceEqual : ActualCanonicalSourceEquality module locator.source
  boundaryEqual : ActualCanonicalBoundaryEquality module locator.consumedBoundary
  theoremTypeEqual : KernelCheckedNormalizedTheoremTypeEquality
    module theoremName CurrentRequiredTheoremType
  importsEqual : ActualImportedDeclarationEnvironmentEquality
    module CurrentTransitiveSemanticEnvironment
  policyEqual : ActualToolchainOptionsAndAuditPolicyEquality module
  replay : sourceEqual -> boundaryEqual -> theoremTypeEqual -> importsEqual ->
    policyEqual ->
    ImportedCertificateApplies module theoremName

inductive ReplayNode
  | shard (policy : MeasuredShardPolicy) (entries : Array BlockReplayEntry)
      (root : MerkleRoot entries)
  | composition (kind : CompositionKind) (children : Array ReplayNode)
      (certificate : CachedCompositionCertificate children)
      (root : MerkleRoot (children.map ReplayNode.root, certificate.typeHash))

structure VerifiedReplayManifest where
  source : HierarchicalClosedAsmSource
  root : ReplayNode
  complete : EverySelectedBlockAppearsExactlyOnceInHierarchy source root
  cleanRebuild : ReconstructsIdenticalRootAndCertificatesFromSources source root
```

Source closure is proved at leaves and composed through exported summaries.
Macro definitions, their transparent expansions, static data, and ordinary raw
fragments all enter as `SourceFragmentClosure` leaves. Syntactic closure is
independent of behavior. A behavior shard consumes child certificates paired by
exact expanded-leaf identity; it does not reduce a single aggregate array of
all instructions. `listingExact` is a tree induction using child
concatenation theorems. The final writer may stream that hierarchy into one byte
artifact, but a leaf edit rechecks the changed fragment and its ancestor
composition nodes rather than rerunning whole-source `decide`.

`IdentityFacets` keeps separate canonical hashes for adopted/authored source,
semantic boundary interfaces, raw machine code, and serialized artifact bytes.
Alpha-renaming generated binders or unrelated labels cannot change a semantic
boundary identity; a relocation/layout edit may change artifact identity without
changing raw-code or process-contract identity. Proof terms and fresh nominal
implementation names never enter cache keys.

Merkle and content hashes are lookup locators and change detectors only. After a
candidate module is imported, replay checks actual canonical source/boundary
content, actual imported declaration identities, exact normalized theorem type,
and toolchain/options/audit policy through the ordinary kernel-checked
environment. Hash equality proves none of those facts. Collision, substitution,
or cache corruption causes rejection or a clean rebuild; it cannot manufacture a
certificate. No cryptographic collision-resistance assumption enters the logical
theorem or TCB. Clean reconstruction compares canonical content and exported
types in addition to reproducing locator roots.

Semantic status is independent of work performed: one subject may be invalidated,
elaborated, kernel-checked, generated, and serialized in a single build, while a
reusable subject may be checked through an independent cache-validation action.
The pre-build plan never claims identities produced only after execution.
Reusing a local certificate requires unchanged canonical code/boundary and the
complete transitive semantic-environment root. Replay also checks the exact
current normalized theorem type; matching source under changed instruction/API,
ownership, verifier, toolchain, option, or axiom-audit semantics is a miss.
Regenerating PE bytes after an instruction change is expected. Any
action without a semantic-facet path is failure, as is an invalidation outside
the allowed cone or failure to reuse a `requiredReuse` subject.

Every reviewed module/boundary publishes a machine-readable `LocalityContract`.
It records stable subjects, consumed semantic facets/interface hashes, allowed
and required actions, and the negative required-reuse set—not wall-clock
promises. Every dependency edge names the facet and cache-key contribution which
justifies it. CI validates reuse with clean uncached/differential reconstruction,
not solely with the incremental graph that proposed the plan. Mutation fixtures
establish that changing a leaf block cannot re-elaborate or re-prove an unrelated
provider, specification, or sibling block even when final layout and artifact
must regenerate. Semantic-owner, verifier/toolchain/options, and audit-policy
mutation fixtures prove their roots invalidate every dependent certificate.

Replay aggregation is hierarchical: appropriate-sized proof shards feed cached
sub-CFG, component, and artifact composition nodes. A leaf edit recomputes work
proportional to its semantic impact cone and hierarchy depth. Sibling-subtree
roots locate candidate replay certificates; actual kernel-visible source,
boundary, theorem-type, import-environment, option, and audit-policy equalities
justify reuse. Roots alone prove neither applicability nor negative reuse.
Source discovery may read and hash the complete tree even when proof replay is
local, and its byte count is reported separately. Grass does not mandate one
Lean module per basic block. The shard
policy is selected from measured elaboration/import/kernel-check tradeoffs and
is itself recorded in the manifest. Scale fixtures publish selected-block,
source-byte-scan, equality-construction, shard-import, elaboration, kernel-check,
diagnostic, composition-node, aggregation, artifact-scan, and artifact-write
counts for the mandatory 1M- and 10M+-instruction fixtures. A flat
whole-program proof-certificate reconstruction on a leaf edit fails the locality
gate; a full source hash scan or final artifact write does not, but must not be
misreported as local proof work.

Each shard is an ordinary generated Lean module imported and kernel-checked by
the ordinary Lean environment. The build layer may content-address, reuse, and
compose those modules; it does not intercept sub-declaration elaboration,
deserialize unchecked proof objects, or modify the kernel. If measured Lean
module/import overhead makes a proposed shard size uneconomic, the policy must
coarsen the shard rather than assume a custom kernel frontend.

The 1M/10M+ corpus and locality reports are future acceptance evidence, not
facts established by the current five design spikes. Until reproducible source
generators, retained `LocalityContract`, `InvalidationPlan`, and
`BuildExecutionReport` artifacts, and clean/incremental measurements exist in
the repository, the hierarchical scheme is a proposed architecture with an
unpassed scale gate. No document or certificate may infer target-scale proof
economics from the small fixtures or from asymptotic prose alone.

The pipeline is complete only with a composed connection chain from the original
specification to the final loaded artifact. Pairwise theorems that are never
composed are insufficient.
