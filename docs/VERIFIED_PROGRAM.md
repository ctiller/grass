# VerifiedProgram contract

This document owns the certificate accepted by `emitProgram`. Exact Lean fields
may evolve, but no implementation may merge independent demands in a way that
makes a weaker theorem appear to discharge a stronger one.

## 1. Conceptual interface

```lean
structure VerifiedProgram (spec : Specification) where
  ghostProgram          : GhostProgram
  realization           : PlatformPlan
  rawProgram            : RawProgram realization
  linkedArtifact        : Artifact realization
  requirementClosure    : AllRequirementsDischarged ghostProgram realization
  stepApplicability     : AllReachableStepsApplicable ghostProgram realization
  prefixSafety          : EveryPermittedPrefixSafe ghostProgram realization
  progress              : MeetsProgressContract ghostProgram spec.progress
  functionalRefinement  : Refines ghostProgram spec
  abiCorrectness        : EveryBoundarySatisfiesABI ghostProgram realization
  obligationCorrectness : ObligationsMatchSpecification ghostProgram spec realization
  erasureCorrectness    : ErasurePreservesSemantics ghostProgram rawProgram
  artifactCorrectness   : ArtifactRepresents rawProgram linkedArtifact
  writerReady           : WellFormed linkedArtifact
  profileAdequacy       : AdequateExecutionAndResponseDomains realization
  loadDomainAdequacy    : InhabitedIndependentLoadDomains realization
  loadable              : EveryAdmissibleEnvironmentLoads
                             (write linkedArtifact) realization
  endToEnd               : LoadedBytesBehaviorIncluded
                             (write linkedArtifact) ghostProgram spec realization
```

The fields remain separately named even if reusable library theorems construct
several together. `endToEnd` composes them and is the public assurance theorem:
every permitted execution obtained by parsing, mapping, relocating, resolving,
and starting the exact bytes returned by `write linkedArtifact` is matched by a
permitted ghost-program execution and therefore satisfies the independently
proved mandatory demands.

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
    (base : AdmissibleLoadBase v.realization)
    (imports : AdmissibleImportEnvironment v.realization) :
  (∃ machine,
     Loads v.realization (emitProgram v) base imports machine ∧
     ValidInitialState v.realization machine) ∧
  ∀ machine trace,
    Loads v.realization (emitProgram v) base imports machine ->
    ValidInitialState v.realization machine ->
    ModeledExecution machine trace ->
    AssuranceResult spec v.ghostProgram trace
```

`AssuranceResult` is a reviewed sum, not an opaque escape hatch:

- `conforming` supplies a matching ghost execution, universal prefix safety,
  specification acceptance, progress/liveness, ABI correctness, and matching
  obligation behavior; or
- `environmentViolation` identifies the first contract-violating event and
  supplies a matching safe maximal prefix through the state immediately before
  it. Assurance explicitly ends there; it makes no functional, liveness, ABI,
  cleanup, or post-state claim about later physical behavior.

For an infinite conforming `trace`, terminal conclusions are interpreted by the
progress contract rather than fabricated. The trace-matching relation is not
arbitrary: its owner proves preservation/reflection of mandatory audit events,
faults, termination/divergence, environment coupling, ABI states, and
observations.
`Loads` consumes the exact `emitProgram v` bytes and models the selected loader;
it cannot be replaced by a second hand-constructed artifact.

The existential loadability conjunct prevents vacuity: every admissible base and
import environment produces at least one loaded machine. Behavioral inclusion
then ranges over every machine the loader relation permits.

`InhabitedIndependentLoadDomains` separately exhibits at least one admissible
base and import environment. Their admissibility is defined from format
alignment/range rules and satisfaction of the program's declared import
requirements, not from `Loads` or execution existence. Artifact connection also
proves `Loads ... machine -> ValidInitialState ... machine`, so a loader result
cannot escape the execution-adequacy package.

This is a theorem about the cited formal CPU/platform/loader model. The claim
that physical implementations conform to that model remains explicit TCB
correspondence challenged by validation campaigns.

## 3. Emission

```lean
emitProgram : VerifiedProgram spec -> ByteArray
```

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

The specification defines a result type and maps it to process observations.
For the initial Win32 profile, successful completion exits with code zero and
specified failure exits nonzero. Every error branch is modeled; noncontinuable
failure is allowed when its terminal postcondition and obligation dispositions
are explicit.

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
