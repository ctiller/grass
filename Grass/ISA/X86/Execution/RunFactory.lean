import Grass.ISA.X86.Execution.AccessFree
import Grass.Op.AccessFactory

/-!
# Checked operation-run factories

These factories construct the operation whose facets are checked by `step`.
Callers provide descriptors and execution context, but cannot substitute an
unrelated `SomeOperation` or fault plan into the returned receipt.
-/

namespace Grass.ISA.X86.Execution.RunFactory

open Grass.Core Grass.Memory Grass.Op

/-- Compatibility aliases for the generic singleton-access factory. `access`
retains the generic execution implementation; this x86 layer keeps only
state-shaped failure views and access-free execution below. -/
abbrev singletonOperation := Grass.Op.AccessFactory.singletonOperation
abbrev noFaultPlan := Grass.Op.AccessFactory.noFaultPlan
abbrev AccessFailure := Grass.Op.AccessFactory.AccessFailure
abbrev AccessSuccess := Grass.Op.AccessFactory.AccessSuccess
abbrev access := Grass.Op.AccessFactory.access

namespace AccessFailure

export Grass.Op.AccessFactory.AccessFailure
  (rejected violations preparationUnavailable answerUnavailable)

end AccessFailure

/-- Recover the CPU prefix at an access failure. `AccessFailure.reached_rejected` retains the
supplied state; the other constructor equations retain its CPU fields and use
the failure's actual machine state. -/
def AccessFailure.reached (before : State) {descriptor : AccessDescriptor} :
    AccessFailure descriptor → State
  | .rejected _ => before
  | .violations after | .preparationUnavailable after _ | .answerUnavailable after =>
      { before with machine := after }

@[simp] theorem AccessFailure.reached_rejected (before : State)
    (descriptor : AccessDescriptor) (reason : StepRejection) :
    reached before (AccessFailure.rejected (descriptor := descriptor) reason) = before := rfl

@[simp] theorem AccessFailure.reached_violations (before : State)
    (descriptor : AccessDescriptor) (after : MachineState) :
    reached before (AccessFailure.violations (descriptor := descriptor) after) =
      { before with machine := after } := rfl

@[simp] theorem AccessFailure.reached_preparationUnavailable (before : State)
    (descriptor : AccessDescriptor) (after : MachineState) (reason : AuditViolationClass) :
    reached before (AccessFailure.preparationUnavailable (descriptor := descriptor) after reason) =
      { before with machine := after } := rfl

@[simp] theorem AccessFailure.reached_answerUnavailable (before : State)
    (descriptor : AccessDescriptor) (after : MachineState) :
    reached before (AccessFailure.answerUnavailable (descriptor := descriptor) after) =
      { before with machine := after } := rfl

private inductive FixedAccessFreeOperation where | run

private instance : HasOperationFacets FixedAccessFreeOperation where
  facets
    | .run =>
      { memoryEffects := some .none_
        faults := some []
        restartability := some .restartable
        ordering := some .plain }

def accessFreeOperation : SomeOperation := SomeOperation.of FixedAccessFreeOperation.run

structure AccessFreeRun (policy : StepPolicy) (before after : MachineState)
    (context : ContextId) (contextKind : ContextKind) (cause : EventCause) : Type where
  ran : step policy before accessFreeOperation context contextKind cause noFaultPlan = .ran after
  state_eq : after = before.noteContext context contextKind

/-- Execute the fixed empty-substep operation, retaining either its rejection or
the actual state and the derived context-only state equality. -/
def accessFree (policy : StepPolicy) (before : MachineState) (context : ContextId)
    (contextKind : ContextKind) (cause : EventCause) :
    Except StepRejection
      (Σ after, AccessFreeRun policy before after context contextKind cause) :=
  match ran : step policy before accessFreeOperation context contextKind cause noFaultPlan with
  | .rejected reason => .error reason
  | .ran after =>
      .ok ⟨after,
        { ran := ran
          state_eq := ran_accessFree_noFault_eq_noteContext policy before accessFreeOperation
            context contextKind cause noFaultPlan .none_ after rfl
            (by simp [SubstepSequence.accesses, SubstepSequence.none_])
            rfl ran }⟩

end Grass.ISA.X86.Execution.RunFactory
