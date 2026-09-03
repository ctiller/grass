import Grass.Op.Step
import Tests.Memory.Spike1Block

/-!
# The Spike 1 reference set, stepped

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §3's M2 exit criterion is that "the M1
reference instruction set steps end to end over a hand-built `MemState`". Nothing
did. `Tests/Memory/Spike1Block.lean` runs `runBlock`, the `applyAccess`-level
executor, and says so in its own comment; no `StepPolicy`, `MemoryProfile` or
`AdmittedVocabulary` existed anywhere under `Tests/Memory/`, and five of the eight
reference cases were executed by nothing at all. What stepped end to end was
`Tests/Op/FakeIsa.lean`, which is explicitly a fake. Review found the gap while
checking the plan's exit criteria against the tree, and wrote the missing policy in
about forty lines to prove the point — so this is an absent fixture rather than an
inexpressible one.

This is that policy, and the reference cases through `Grass.Op.step`.

## What it shows, and what it cannot

Every reference case that is a program-thread operation steps and records what it
should. That is the criterion, for the program's own instructions.

**Spike 1's point does not step.** `WriteFile` is a second execution context, and
`Grass/Op/Step.lean`'s `ConflictsWithHistory` refuses any cross-context access whose
event conflicts with an earlier one — `StepPolicy.compatible` defaults to refusing
every pair, which the comment there names as the conservative direction pending M8's
happens-before. So the agent's write to the slot the program lent it is refused and
recorded, and `docs/MEMORY_MODEL.md` §8 requires the ledger to be empty for a
`VerifiedProgram`.

The conservative direction is right. What was not recorded until review found it is
that its consequence lands on the *first* acceptance program rather than the fourth:
M8 is a prerequisite for M2's exit criterion, not an additive milestone for Spike 4.
`the_agent_write_is_refused` below is that fact, stepped, so it is a theorem rather
than a claim in a plan.
-/

namespace Grass.Tests.Spike1Policy

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Tests.Spike1
open Tests.Memory.Spike1Block

/-! ## The profile -/

/-- The vocabulary Spike 1's instructions actually use.

Every registry is populated from the reference set rather than from what would make
the fixture pass: the two fault classes the descriptors admit, the one allocation
source each provenance names, the provenance step kinds the frame and image paths
use, and the violation classes the transition can emit. The three justification
registries and the two ordering registries are empty, and that is a fact about
Spike 1: it declares no profile-specific ordering, cites no initialization rule, and
claims no cross-substep atomicity. -/
def vocabulary : AdmittedVocabulary :=
  { addressSpaces := .cpuOnly
    faultClasses := ⟨[.pageFault, .generalProtection, invalidOpcode, divideError]⟩
    allocationSources := ⟨[.stack, .imageMapping]⟩
    provenanceStepKinds := ⟨[.frame, .slot, .imageSection, .symbol]⟩
    auditViolationClasses := ⟨AuditViolationClass.emittedByTransition⟩
    obligationKinds := ⟨[]⟩
    orderingModes := ⟨[]⟩
    orderingScopes := ⟨[]⟩
    initializationJustifications := ⟨[]⟩
    atomicityJustifications := ⟨[]⟩
    faultVisibilityRules := ⟨[⟨"x86.splitPageStore"⟩]⟩
    -- §6's call lends the frame slot it passes, so `loan` is Spike 1's; `frame` is
    -- M4's and this reference set does not model a frame grant yet.
    grantKinds := ⟨[.loan]⟩ }

/-- The profile. Its §10 package is explicitly unproved, like the seam fixture's:
`RequiredProofPackage.Holds` is what nothing here establishes, and a fixture that
supplied evidence it does not have would be the defect this layer keeps finding. -/
def profile : MemoryProfile :=
  { id := ⟨"spike1.win64"⟩, vocabularyVersion := 1, vocabulary := vocabulary
    package :=
      { accessDescriptorSoundness := True
        rangeProvenanceInitializationPreservation := True
        permissionEnforcementAndFaultFidelity := True
        loanMapLaws := True, consistencyGraphWellFormedness := True
        raceFreedomConsequences := True, synchronizationAndObligationTransfer := True
        allocatorFreshnessTeardownEpoch := True, callStackFrameLifetime := True
        erasurePreservation := True, validationMetadata := True } }

/-- What a store writes: a pattern distinct from what the state starts with, so
observing it is evidence the load read the store's bytes. -/
def storedBytes : MachineState → AccessDescriptor → ByteSeq :=
  fun _ d => List.replicate d.range.size 0xAB

/-- What an indeterminate read observes. Supplied because `Oracle.ofMemory` requires
it; the stack reservation starts uninitialized, so unlike the seam fixture this one
can reach it. -/
def indeterminateByte : MachineState → (d : AccessDescriptor) → Nat → Byte :=
  fun _ _ _ => 0x00

/-- The policy. It adopts the standard loan rule rather than writing one, which is
what `Grass/Op/Step.lean`'s `refusalOf` does for every profile. -/
def policy : StepPolicy :=
  { profile := profile
    requiredFacets := [.memoryEffects, .faults, .restartability, .ordering]
    oracle := .ofMemory storedBytes indeterminateByte
    authorities := []
    violationClassesDeclared := by decide
    vocabularyWellFormed := by decide }

/-! ## The operations

One constructor per reference case, and the facets read straight off
`Tests/Memory/Spike1Reference.lean` — the point is that the *reference* set steps,
not that a fresh set does. -/

/-- Spike 1's memory-touching instruction forms. -/
inductive Op where
  /-- `push r12`. -/
  | pushR12
  /-- `mov ecx, STD_OUTPUT_HANDLE`. -/
  | movEcxImm
  /-- `lea r13, [rip + payload]`. -/
  | leaPayload
  /-- `mov transferred, 0`. -/
  | movTransferredZero
  /-- `lea r9, transferred.addr`. -/
  | leaTransferred
  /-- `call [rip + __imp_WriteFile]`. -/
  | callImportWriteFile
  /-- `mov eax, transferred`. -/
  | movEaxTransferred
  /-- `ud2` in the containment tail. -/
  | ud2Containment
  /-- The API agent's write to the slot the program lent it. Not one of the
  program's instructions: `WriteFile` is a second execution context and this is what
  it does to memory. -/
  | agentWrite
deriving DecidableEq, Repr

instance : HasOperationFacets Op where
  facets
    | .pushR12 =>
        { memoryEffects := some pushR12, faults := some [.pageFault, .generalProtection]
          restartability := some .notRestartable, ordering := some .plain }
    | .movEcxImm =>
        { memoryEffects := some movEcxImm, faults := some []
          restartability := some .notRestartable, ordering := some .plain }
    | .leaPayload =>
        { memoryEffects := some leaPayload, faults := some []
          restartability := some .notRestartable, ordering := some .plain }
    | .movTransferredZero =>
        { memoryEffects := some movTransferredZero
          faults := some [.pageFault, .generalProtection]
          restartability := some .notRestartable, ordering := some .plain }
    | .leaTransferred =>
        { memoryEffects := some leaTransferred, faults := some []
          restartability := some .notRestartable, ordering := some .plain }
    | .callImportWriteFile =>
        { memoryEffects := some callImportWriteFile
          faults := some [.pageFault, .generalProtection]
          restartability := some .notRestartable, ordering := some .plain }
    | .movEaxTransferred =>
        { memoryEffects := some movEaxTransferred
          faults := some [.pageFault, .generalProtection]
          restartability := some .notRestartable, ordering := some .plain }
    | .ud2Containment =>
        { memoryEffects := some ud2Containment, faults := some [invalidOpcode]
          restartability := some .notRestartable, ordering := some .plain }
    | .agentWrite =>
        { memoryEffects := some (.single Tests.Memory.Spike1Block.agentWrite)
          faults := some [.pageFault, .generalProtection]
          restartability := some .notRestartable, ordering := some .plain }

/-- The starting machine state: the block fixture's memory, no authority held. -/
def machine₀ : MachineState := .initial state₀

/-- Step one operation as the program thread. -/
def stepThread (state : MachineState) (op : Op) : StepOutcome :=
  Grass.Op.step policy state (SomeOperation.of op) mainThread .thread ⟨⟨"spike1"⟩⟩

/-! ## The criterion: the reference set steps -/

/-- **`mov transferred, 0` steps and records one event with no violation.** -/
theorem the_store_steps :
    ∀ s, (stepThread machine₀ .movTransferredZero).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- **`push r12` steps.** The implicit stack write §9 risk 1 names. -/
theorem the_push_steps :
    ∀ s, (stepThread machine₀ .pushR12).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- **The `call` steps, and records both of its accesses.** Two events from one
instruction, which is the thing a one-descriptor-per-instruction model could not
say. -/
theorem the_call_steps :
    ∀ s, (stepThread machine₀ .callImportWriteFile).state? = some s →
      s.events.length = 2 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- **The three operations with no memory effect step and record nothing.**
`SubstepSequence.none_` is a declaration, and these are the cases that show it is a
real one rather than an absence. -/
theorem the_effectless_operations_step :
    (∀ s, (stepThread machine₀ .movEcxImm).state? = some s → s.events = []) ∧
    (∀ s, (stepThread machine₀ .leaPayload).state? = some s → s.events = []) ∧
    (∀ s, (stepThread machine₀ .leaTransferred).state? = some s → s.events = []) := by
  refine ⟨?_, ?_, ?_⟩ <;> (intro s hs; cases hs; decide)

/-- **The reload before the store is refused as an uninitialized read**, and the
violation is recorded rather than the step failing. §4's demand, through the
transition rather than through `denialOf` alone. -/
theorem the_reload_before_the_store_is_refused :
    ∀ s, (stepThread machine₀ .movEaxTransferred).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- And after the store it is not, so the theorem above is the initialization check
running rather than the reload being unreachable. -/
theorem the_reload_after_the_store_steps :
    ∀ afterStore, (stepThread machine₀ .movTransferredZero).state? = some afterStore →
      ∀ s, (stepThread afterStore .movEaxTransferred).state? = some s →
        s.events.length = 2 ∧ s.violations.IsEmpty := by
  intro afterStore hstore s hs
  cases hstore
  cases hs
  exact ⟨by decide, by decide⟩

/-! ## What does not step, and why

The rest of the criterion, and the reason it cannot be met here. -/

/-- The API agent's write, packaged. -/
def agentOperation : SomeOperation := SomeOperation.of Op.agentWrite

/--
**The agent's write is refused, and the ledger is not empty.**

`Grass/Op/Step.lean`'s `ConflictsWithHistory` refuses any cross-context access whose
event conflicts with an earlier one, and `StepPolicy.compatible` defaults to refusing
every pair. The program stores to the slot; the agent then writes the same bytes from
a different `ContextId`; distinct contexts, overlapping committed ranges, one writes,
and no happens-before exists in this layer. So the write is refused with
`authorityUnavailable` and recorded — and `docs/MEMORY_MODEL.md` §8 requires the
ledger to be empty for a `VerifiedProgram`.

This is the conservative direction working exactly as its comment says, and the
consequence is that M8 is a prerequisite for **M2's** exit criterion. Recorded in
§4.2; this is it as a theorem.

The event count is one and not two: the store's event is still there and the agent's
access minted none, which is what a refusal does.
-/
theorem the_agent_write_is_refused :
    ∀ afterStore, (stepThread machine₀ .movTransferredZero).state? = some afterStore →
      ∀ s, (Grass.Op.step policy afterStore agentOperation apiAgent .externalAgent
          ⟨⟨"win64"⟩⟩).state? = some s →
        s.violations.recordCount = 1 ∧ s.events.length = 1 := by
  intro afterStore hstore s hs
  cases hstore
  cases hs
  exact ⟨by decide, by decide⟩

/-- **And the step is not merely rejected**, which would make the theorem above
vacuous: it runs, and records a violation. A first version of this fixture stepped
the *program's* store as the agent, which `contextMismatch` rejects outright, so
`state? = some s` was unsatisfiable and `cases` closed the goal with nothing shown.
The build caught it; the shape is worth naming. -/
theorem the_agent_step_runs :
    ∀ afterStore, (stepThread machine₀ .movTransferredZero).state? = some afterStore →
      (Grass.Op.step policy afterStore agentOperation apiAgent .externalAgent
        ⟨⟨"win64"⟩⟩).state?.isSome := by
  intro afterStore hstore
  cases hstore
  decide

end Grass.Tests.Spike1Policy
