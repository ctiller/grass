# VerifiedProgram contract

This document owns the certificate accepted by `emitProgram`. Exact Lean fields
may evolve, but no implementation may merge independent demands in a way that
makes a weaker theorem appear to discharge a stronger one.

There is exactly one precious semantic index: the root `SpecProcess`. Other
specification DSLs and semantic subprocesses have already been composed and
captured into that value; implementation process graphs merely realize it.

## 1. Conceptual interface

```lean
structure VerifiedProgram {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources) where
  process               : ProcessRealization spec
  portableCorrectness   : ProcessModelSatisfiesSpecification
                             process.model spec
  realization           : PlatformPlan process.boundary.requirements
  machineSource         : MachineSource realization
  implementationModels  : ImplementationBundle machineSource process
  modelCorrectness      : EveryBindingRealizesItsComponentContract
                             implementationModels
  modelCoverage         : ExactSourceScopeAndRequirementCoverage
                             implementationModels machineSource process
  sourceModelRefinement : SourceRefinesImplementationBundle
                             machineSource implementationModels
  ghostProgram          : GhostProgram process.boundary realization
  sourceElaboration     : SourceElaboratesExactlyTo
                             machineSource ghostProgram
  driver                : ProcessDriver spec process.plan process.correct
                             realization ghostProgram
  platformContract      : PlatformContract
                             spec process realization driver
  assemblyCorrectness   : AssemblyImplements
                             platformContract machineSource
  rawProgram            : RawProgram realization
  sourceErasure         : ErasesExactSource ghostProgram rawProgram
  sourceEncoding        : EncodesExactlyTheInstructions
                             machineSource rawProgram
  linkedArtifact        : Artifact realization
  requirementClosure    : AllRequirementsDischarged ghostProgram realization
  stepApplicability     : AllReachableStepsApplicable ghostProgram realization
  prefixSafety          : EveryPermittedPrefixSafe ghostProgram realization
  progress              : MeetsProgressContract ghostProgram spec.progress
  concreteLivenessInhabited : Nonempty (ConcreteResponsiveStrategy realization)
  livenessProjection    : ConcreteResponsiveStrategy realization ->
                             AbstractEnvironmentStrategy spec
  livenessCoupling      : ∀ s, StrategyRefines realization spec s.strategy
                             (livenessProjection s)
  livenessAdequacy      : ∀ s, StrategyAdequate (livenessProjection s)
  livenessScheduleComplete : ∀ s,
                             SchedulingComplete spec (livenessProjection s)
  livenessResultComplete : ∀ s, FrontierComplete spec (livenessProjection s)
  livenessResponsive    : ∀ s, EnvironmentResponsive spec
                             (livenessProjection s)
  functionalRefinement  : Refines ghostProgram spec
  abiCorrectness        : EveryBoundarySatisfiesABI ghostProgram realization
  obligationCorrectness : ObligationsMatchSpecification ghostProgram spec realization
  terminalProtocols     : TerminalProtocolsFor
                             ghostProgram rawProgram spec realization
  containmentCorrectness : EverySelectedContainmentCovered
                             ghostProgram rawProgram realization
  erasureCorrectness    : ErasurePreservesSemantics ghostProgram rawProgram
  artifactCorrectness   : ArtifactRepresents rawProgram linkedArtifact
  artifactContainment   : SelectedContainmentsRepresented
                             rawProgram linkedArtifact
  writerReady           : WellFormed linkedArtifact
  profileAdequacy       : AdequateExecutionAndResponseDomains realization
  contextInhabited      : InhabitedAdmissibleExecutionContexts realization
  baseInhabited         : InhabitedAdmissibleLoadBases linkedArtifact
  importsInhabited      : InhabitedAdmissibleImportEnvironments
                             realization linkedArtifact
  loadDomainsIndependent : IndependentLoadDomains realization linkedArtifact
  loadable              : EveryAdmissibleEnvironmentLoads
                             (write linkedArtifact) realization
  endToEnd               : LoadedBytesBehaviorIncluded
                             (write linkedArtifact) ghostProgram spec realization
```

The listing above is the **audit inventory of independent demands**, not a
mandate for one 44-field elaboration telescope. The implementation groups it
behind stratified exported certificates:

```lean
structure PortableProgramCertificate {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources) where
  model : PortableProcessModel spec.driverBoundary
  correctness : ModelSatisfiesSpecification model spec
  boundary : ProcessBoundary
  exportsBoundary : ModelExportsBoundary model boundary
  demands : DemandCertificateFamily spec.requirements model

structure ProjectedDriverCertificate {R : Type u} [ResourceModel R]
    {resources : R} {spec : SpecProcess resources}
    (portable : PortableProgramCertificate spec)
    (projection : TargetProjection spec profile) where
  plan : PlatformPlan projection portable.boundary.requirements
  driverSummary : DriverBoundarySummary portable.boundary plan
  blendRequirementsExact :
    plan.requirements = portable.model.processOrigin.accumulatedRequirements
  providerCoherence : OneGloballyCoherentProviderAbiIsaEnvironment
    plan portable.model.processOrigin
  projectionCorrect : ProjectionAndDriverRefine portable projection driverSummary

structure MachineCertificate {R : Type u} [ResourceModel R]
    {resources : R} {spec : SpecProcess resources}
    (driver : ProjectedDriverCertificate portable projection) where
  blend : MachineBlend driver
  source : MachineSource driver.plan
  sourceExact : source = blend.exactSource
  summary : MachineBoundarySummary driver.driverSummary
  implementationModels : ImplementationBundle source portable.model
  localCertificates : MachineDemandCertificateFamily source summary
  closedBlendCoverage : SourceCoversExactlyEveryClosedBlendScope
    source driver.plan.processOrigin blend
  sourceAndMachineCorrect : SourceRefinesDriverExactly source summary driver

structure ArtifactCertificate {R : Type u} [ResourceModel R]
    {resources : R} {spec : SpecProcess resources}
    (machine : MachineCertificate driver) where
  raw : RawProgram driver.plan
  linked : Artifact driver.plan
  exactSourceChain : ExactSourceErasureEncodingAndLink machine.source raw linked
  writerParserLoader : ArtifactDemandCertificateFamily linked machine.summary

structure VerifiedProgram {R : Type u} [ResourceModel R]
    {resources : R} (spec : SpecProcess resources) where
  portable : PortableProgramCertificate spec
  projection : TargetProjection spec profile
  driver : ProjectedDriverCertificate portable projection
  machine : MachineCertificate driver
  artifact : ArtifactCertificate machine
  endToEnd : LoadedBytesSatisfySpecification
    (write artifact.linked) spec portable projection driver machine artifact
```

Each tier is compiled/exported through its small summary. Private process state
changes reopen the portable proof but not a consumer whose boundary is
unchanged; an instruction edit rechecks affected machine shards and regenerates
artifact identity but reuses portable and projection proofs; a layout-only edit
reuses machine behavior. Exact witnesses remain inside the tiers and the final
theorem consumes all of them, so stratification does not weaken adjacency or
permit an extensionally similar source to replace the authored one.

`DemandCertificateFamily` retains the separately keyed functional, safety,
memory, concurrency, progress, termination, resource, obligation,
applicability, diagnostic, and artifact theorems. Grouping them by dependency
tier does not conflate their statements or make one theorem discharge another.

`VerifiedProgram` remains indexed only by the precious `spec`. `portable.model.origin`
records whether the plan was synthesized from a sequential relational program
or explicitly authored; both have already elaborated to the same universal
process algebra. The exact registry, population, local/shared state partition,
channels, supervision, and process proof are carried inside the certificate. They are
reviewed replaceable construction inputs and cannot leak into the stable public
type. The exact value `v` still indexes all downstream proofs, so replaceability
does not mean ambiguity.

`portableCorrectness` is the independently reusable high-level theorem. It is
proved over the portable process/model semantics before platform selection or
machine realization. `functionalRefinement` is not a duplicate of it: it shows
that the selected ghost-bearing machine behavior refines that proved process
model. `endToEnd` composes this adjacency with exact source and artifact
identity. Implementations may package these fields into stratified certificates
to keep rebuild cones narrow; the conceptual interface lists the independent
demands rather than prescribing one flat elaboration unit.

`portable.boundary` is the stable extensional interface consumed by machine-source
and local block certificates. A process-plan-only change which preserves this
boundary does not change their types. `platformContract` is nevertheless
internally indexed by the exact process realization, provider plan, and driver, and
`assemblyCorrectness` consumes that exact contract; the final adjacency is not
weakened to an unconnected `GhostProgram` claim.

`machineSource` precedes and determines the ghost/raw chain.
`sourceElaboration` connects every authored label, instruction, operand,
annotation, and expansion to `ghostProgram`; `sourceErasure` removes exactly the
ghost constructs from that elaboration; `sourceEncoding` connects the remaining
ordered instruction/CFG identities to `rawProgram`. `artifactCorrectness` then
consumes that exact raw value. Contract equivalence cannot substitute a
different implementation: arbitrary register choices, literal instruction
sequences, layout decisions, and containment tails in the selected source are
the ones decoded from the emitted artifact.

`implementationModels` is a finite dependent map from exact source/CFG scopes
and exact process/platform requirement occurrences to component contracts,
representations, and Lean model values. `modelCorrectness` proves each model
realizes only its component contract; `modelCoverage` proves scopes cover exactly
the requirements claimed, with disjointness or an explicit overlap/composition
law. `sourceModelRefinement` connects each exact source scope to its binding. The
remaining driver/assembly proof composes those component results with I/O,
failure, terminal, progress, and platform behavior into the whole spec. An empty
bundle means “no algorithm bindings,” never a vacuous whole-spec theorem.

The fields remain separately named even if reusable library theorems construct
several together. `endToEnd` composes them and is the public assurance theorem:
every permitted execution obtained by parsing, mapping, relocating, resolving,
and starting the exact bytes returned by `write linkedArtifact` is matched by a
permitted ghost-program execution and therefore satisfies the independently
proved mandatory demands.

`concreteLivenessInhabited` proves the selected providers' assumptions are
jointly satisfiable. `livenessProjection` names the abstract branching strategy
of that same concrete strategy, `livenessCoupling` relates their complete
generated-history sets, choices, events, frontiers, and eventual settlement, and
`livenessAdequacy` rules out an empty strategy tree while
`livenessScheduleComplete` prevents selection of one favorable schedule among
those satisfying the named timing/fairness premise,
`livenessResultComplete` prevents the premise from pruning any allowed result
value or dependent response branch, and
`livenessResponsive` proves responsiveness of every compatible maximal
continuation. A constant unrelated abstract strategy cannot discharge the
coupling. Abstract inhabitance is a derived theorem, not an independent field:

```lean
theorem VerifiedProgram.abstractLivenessInhabited (v : VerifiedProgram spec) :
    Nonempty (ResponsiveStrategyWitness spec) := by
  rcases v.concreteLivenessInhabited with ⟨s⟩
  exact ⟨{ strategy := v.livenessProjection s
           adequate := v.livenessAdequacy s
           scheduleComplete := v.livenessScheduleComplete s
           resultComplete := v.livenessResultComplete s
           responsive := v.livenessResponsive s }⟩
```

The fields remain separate theorem demands, but ordinary sequential providers
use one library constructor which produces them from “every external call
settles” plus the program's between-frontier measure. The public application
theorem is explicit and execution-indexed:

```lean
theorem VerifiedProgram.liveness_for_every_compatible_execution
    (v : VerifiedProgram spec)
    (strategy : ConcreteResponsiveStrategy v.realization)
    (execution : CompatibleExecution v strategy) :
    SatisfiesLiveness spec execution :=
  apply_responsive_strategy
    (v.livenessCoupling strategy)
    (v.livenessAdequacy strategy)
    (v.livenessScheduleComplete strategy)
    (v.livenessResultComplete strategy)
    (v.livenessResponsive strategy)
    execution
```

Strategy construction lives below this theorem and cannot consume
`SatisfiesLiveness`. Timing/scheduling permissions and dependent result choices
are separate namespaces; the strategy may restrict only profile-named timing or
scheduling dimensions, while every permitted result at every
strategy-compatible frontier remains represented.

None may be derived from an execution whose existence
already assumes the liveness conclusion. `terminalProtocols` contains
preservation, reflection, distinguishability, and pending/resource-fidelity
laws for every demanded terminal observable. These do not collapse into
functional refinement or generic response adequacy.

`endToEnd` additionally classifies every modeled execution: conforming executions
receive the complete guarantee above; environment-violation executions receive
only the maximal matched safe-prefix result defined below.

Behavioral inclusion is from loaded bytes to the proved program; the raw or
loaded machine may not acquire extra behavior. The matching relation covers
admissible initial states and load bases, coupled environment/oracle choices,
finite and infinite executions, divergence, terminal results, faults,
interruptions, complete audit events, projected observations, ABI state, and
terminal obligation dispositions. Pairwise simulations are supporting lemmas,
not substitutes for this composed theorem.

Functional equivalence never substitutes for safety, and testing never
substitutes for any field.

## 2. Fundamental theorem

The public theorem has this shape, with profile-specific details hidden behind
named definitions rather than omitted:

```lean
theorem emitted_sound
    (v : VerifiedProgram spec)
    (context : AdmissibleExecutionContext v.realization)
    (base : AdmissibleLoadBase v.linkedArtifact)
    (imports : AdmissibleImportEnvironment
      v.realization v.linkedArtifact) :
  (∃ machine,
     Loads v.realization (emitProgram v) context base imports machine) ∧
  ∀ machine,
    (load : Loads v.realization (emitProgram v) context base imports machine) ->
    ValidInitialState
      v.realization context v.linkedArtifact machine ∧
    SatisfiesEntryContract v.rawProgram.entry machine ∧
    ∀ trace,
      (exec : ModeledExecution machine trace) ->
      AssuranceResult v context base imports machine load trace exec
```

Validity and the raw entry contract are consequences of the exact `Loads`
witness, never hypotheses supplied by the caller. Otherwise an invalid loader
result could fall outside the public theorem while still satisfying `Loads`.
The separate existential conjunct and the independently inhabited load domains
prevent the universal clause from becoming vacuous.

`AssuranceResult` is a reviewed dependent sum indexed by the exact certificate,
context, base, imports, loaded machine, trace, and modeled-execution occurrence;
it is not an opaque escape hatch:

- `conforming` supplies a matching ghost execution, coinductive trace/observation
  refinement, universal prefix safety, applicable progress/liveness, ABI
  correctness, and matching obligation behavior. If and only if the trace has a
  finite specified terminal result, it additionally supplies terminal
  specification acceptance; or
- `environmentViolation` identifies the first contract-violating event and
  supplies a matching safe maximal prefix through the state immediately before
  it. Assurance explicitly ends there; it makes no functional, liveness, ABI,
  cleanup, or post-state claim about later physical behavior.

Both constructors are indexed by and retain the exact `load`/`exec` occurrences. `conforming`
existentially returns the coupled ghost initial state and namespaced choices;
`environmentViolation` returns those values for the maximal pre-violation
prefix plus the exact first violating step. Neither may switch to a different
loaded machine, oracle history, or occurrence with extensionally similar data.

For an infinite conforming `trace`, no completed result or terminal observation
is fabricated. It carries coinductive trace refinement and the applicable
progress fact. A conditional-liveness theorem excludes that trace only when its
universally quantified responsive-strategy premise holds. The trace-matching relation is not
arbitrary: its owner proves preservation/reflection of mandatory audit events,
faults, termination/divergence, environment coupling, ABI states, and
observations.
`Loads` consumes the exact `emitProgram v` bytes and models the selected loader;
it cannot be replaced by a second hand-constructed artifact.

The existential loadability conjunct prevents vacuity: every admissible
execution-context/base/import triple produces at least one loaded machine.
Behavioral inclusion then ranges over every machine the loader relation permits.

The three named inhabitance fields separately exhibit at least one admissible
execution context, artifact-indexed base, and artifact-indexed import
environment. Module dependencies define all three below `Loads` and execution
and prevent one domain from manufacturing witnesses from another;
`loadDomainsIndependent` records the resulting composition theorem rather than
serving as an unconstrained substitute for that stratification. Context admissibility means
that the explicit initial platform requirements exported by provider selection
are satisfied; it is not inferred from a later successful execution. Base and
import admissibility is indexed by `v.linkedArtifact` and defined from its exact
image size, address/relocation arithmetic, format alignment/range rules, and
declared import set. None is defined
from `Loads` or execution existence. Artifact connection also
proves `Loads ... machine -> ValidInitialState ... machine`, so a loader result
cannot escape the execution-adequacy package.

This is a theorem about the cited formal CPU/platform/loader model. The claim
that physical implementations conform to that model remains explicit TCB
correspondence challenged by validation campaigns.

## 3. Emission

```lean
emitProgram : VerifiedProgram spec -> ByteArray
```

For authored assembly, the economical closing surfaces are:

```lean
def standardSequentialVerified : VerifiedProgram spec := by
  verify_assembly plan with source

def sequentialVerified : VerifiedProgram spec := by
  verify_assembly plan using sequential_process directRealizes with source

def processVerified : VerifiedProgram spec := by
  verify_assembly plan using explicit_process processPlanRealizes with source
```

The shortest form requires an exact unique lookup for `spec` in the named closed
`Grass.Std.Realizers.registry` and normalizes the selected
`StandardSequentialRealization` through `SequentialAdapter`; absence or
ambiguity is a hard elaboration error, never priority-based ambient choice. The
selected registry key is retained in the certificate and build manifest. The explicit sequential form selects a novel
relational implementation proof. Here `source : MachineSource plan` contains syntax, labels, literal
instructions, and layout intent. The selected authoring proof either feeds the
standard sequential adapter or supplies an explicit process composition. Both
produce the same `ProcessRealization`. The elaborator constructs the exact
process-indexed `PlatformContract` and proves the source
realizes its driver. Source alone cannot
claim functional, terminal, frontier, or process refinement. These remain named,
inspectable proof objects in diagnostics. The generated-code peer consumes the
same process-plan witness before lowering its high-level source.

Every certificate exposes its fundamental theorem as `v.sound`; authors do not
write a wrapper around `emitted_sound`. A named specialization may still improve
an API or document a particular context, base, or import profile.

Emission is total over a completed certificate. Requirements that could make it
fail must be resolved while constructing the certificate. Platform realization,
layout, import selection, relocation production, and writer well-formedness are
therefore certificate inputs or proved consequences.

`emitProgram` writes the certificate's connected, well-formed artifact. Its
construction calls proved erasure, layout, and linking before certification.
Raw emission remains
available as `Grass.Unsafe.emitRaw : RawProgram -> Except EmitError ByteArray`
for fuzzing and unverified work. It is not an alternate verified route.

The implementation theorem states `emitProgram v = write v.linkedArtifact`, so
the end-to-end theorem refers to the actual returned byte array rather than an
abstract artifact with the same metadata.

## 4. Results and exit status

The specification defines outcomes and any abstract terminal observations or
statuses it needs. A process exit code is one provider realization, not the
universal model. For the initial Win32 profile, successful completion exposes
status zero and specified failure exposes nonzero statuses through
`ExitProcess`. Every error branch is modeled; noncontinuable failure is allowed
when its terminal postcondition and obligation dispositions are explicit.

Interactive fuel exhaustion is an interpreter result carrying a safe-prefix
proof. It is neither success nor program failure and is not emitted as a process
exit code unless a separate host tool chooses such a policy.

## 5. Callable programs and libraries

A verified artifact may export named callables. Each export declares:

- a nominal ABI profile and complete entry/exit contract;
- registers, stack shape, memory shape, hidden arguments, and thread context;
- allowed inputs and all dependent outputs;
- functional observation and refinement theorem;
- ghost state and obligations consumed, produced, or transferred;
- fault, interruption, cancellation, and concurrency behavior;
- progress/termination conditions.

The library certificate proves that the export table serialized in the artifact
matches these declarations. Importers receive requirements, not implementation
access. Exports may be mutually recursive only through a typed CFG with a
reviewed progress argument.

## 6. Rejection

A value cannot become `VerifiedProgram` if any reachable path has an unresolved
requirement, applicability condition, indirect target, memory access, provider
choice, ABI edge, external response, obligation disposition, or artifact link.
Over-approximating clobbers and resource usage is allowed; under-approximation is
not.

A `PartialProcessRealization` produced by staged `blend` is deliberately not an
input to this gate. Every abstract node must be replaced by a proved subsystem
realization, including a proved mock where appropriate; all requirement deltas
must be closed by one coherent provider environment; and cross-subsystem
resource/obligation boundaries must compose before `VerifiedProgram` can be
constructed.

Portable blending and machine blending are separate dependent stages. Portable
subsystem certificates may introduce provider requirements but contain no
pre-projection machine artifact. After one coherent projection and platform plan
is selected, `MachineBlend driver` owns the per-scope heterogeneous x86/SPIR-V
sources, ABI/ISA/provider compatibility, and exact cross-ISA edges.
`MachineCertificate` consumes that exact blend and proves complete source
coverage; it cannot discard a locally proved artifact and substitute an
extensionally equivalent twin.

It is also rejected if the selected profiles cannot prove a nonempty admissible
initial execution domain, nonempty response-or-pending behavior for every
reachable request, or loadability for every environment satisfying the declared
artifact requirements.

The verified dependency closure must be free of `sorry`, `admit`, `sorryAx`,
dependency- or project-defined axioms, unsound declarations, and
native-evaluation proof shortcuts. A transitive audit permits only the exact
reviewed Lean logical-foundation constants. External CPU/platform correspondence
is represented by explicit profile parameters and recorded meta-level trust,
never by manufacturing a Lean theorem with an axiom.
