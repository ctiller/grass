import Grass.ISA.X86.Execution.AccessFree

/-!
# Checked operation-run factories

These factories construct the operation whose facets are checked by `step`.
Callers provide descriptors and execution context, but cannot substitute an
unrelated `SomeOperation` or fault plan into the returned receipt.
-/

namespace Grass.ISA.X86.Execution.RunFactory

open Grass.Core Grass.Memory Grass.Op

private inductive SingletonAccessOperation (descriptor : AccessDescriptor) where
  | run

private instance (descriptor : AccessDescriptor) :
    HasOperationFacets (SingletonAccessOperation descriptor) where
  facets
    | .run =>
      { memoryEffects := some (.single descriptor)
        faults := some descriptor.admittedFaults
        restartability := some descriptor.restartability
        ordering := some descriptor.ordering }

def singletonOperation (descriptor : AccessDescriptor) : SomeOperation :=
  SomeOperation.of (SingletonAccessOperation.run (descriptor := descriptor))

def noFaultPlan : (sequence : SubstepSequence) → FaultPlan sequence := fun _ => .none

inductive AccessFailure (descriptor : AccessDescriptor) where
  | rejected (reason : StepRejection)
  | violations (after : MachineState)
  | preparationUnavailable (after : MachineState) (reason : AuditViolationClass)
  | answerUnavailable (after : MachineState)

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

structure AccessSuccess (policy : StepPolicy) (before : MachineState)
    (descriptor : AccessDescriptor) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) where
  after : MachineState
  run : AccessRun before after descriptor
  policy_exact : run.policy = policy
  context_exact : run.context = context
  contextKind_exact : run.contextKind = contextKind
  cause_exact : run.cause = cause
  operation_exact : run.operation = singletonOperation descriptor
  faultAt_exact : run.faultAt = noFaultPlan

/-- Execute the fixed singleton operation and, only for a clean completed run,
return the actual post-state together with its `AccessRun` proof. -/
def access (policy : StepPolicy) (before : MachineState) (descriptor : AccessDescriptor)
    (context : ContextId) (contextKind : ContextKind) (cause : EventCause) :
    Except (AccessFailure descriptor)
      (AccessSuccess policy before descriptor context contextKind cause) :=
  let operation := singletonOperation descriptor
  let sequence := SubstepSequence.single descriptor
  match ran : step policy before operation context contextKind cause noFaultPlan with
  | .rejected reason => .error (.rejected reason)
  | .ran after =>
      if clean : after.violations.IsEmpty then
        match prepared : prepareAccess (before.noteContext context contextKind).memory descriptor with
        | .error reason => .error (.preparationUnavailable after reason)
        | .ok resolved =>
            match answered : policy.oracle.answerResolved
                (before.noteContext context contextKind) descriptor resolved with
            | none => .error (.answerUnavailable after)
            | some complete =>
                .ok
                  { after := after
                    run :=
                      { policy := policy
                        operation := operation
                        context := context
                        contextKind := contextKind
                        cause := cause
                        faultAt := noFaultPlan
                        sequence := sequence
                        selected := rfl
                        substeps_exact := rfl
                        noFault := rfl
                        ran := ran
                        resolved := resolved
                        prepared := prepared
                        complete := complete
                        answerResolved := answered
                        clean := clean }
                    policy_exact := rfl
                    context_exact := rfl
                    contextKind_exact := rfl
                    cause_exact := rfl
                    operation_exact := rfl
                    faultAt_exact := rfl }
      else .error (.violations after)

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
