import Grass.Op.AccessRun

/-!
# Generic singleton-access factory

This factory constructs one exact singleton operation and retains a clean
`AccessRun` only when the generic stepper actually completed it. It supplies no
ISA transfer semantics and does not choose a descriptor for any caller.
-/

namespace Grass.Op.AccessFactory

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

/-- `singletonOperation` is the only operation this factory can run for a descriptor. -/
def singletonOperation (descriptor : AccessDescriptor) : SomeOperation :=
  SomeOperation.of (SingletonAccessOperation.run (descriptor := descriptor))

/-- `noFaultPlan` makes this factory represent only a no-fault completed singleton run. -/
def noFaultPlan : (sequence : SubstepSequence) → FaultPlan sequence := fun _ => .none

inductive AccessFailure (descriptor : AccessDescriptor) where
  | rejected (reason : StepRejection)
  | violations (after : MachineState)
  | preparationUnavailable (after : MachineState) (reason : AuditViolationClass)
  | answerUnavailable (after : MachineState)

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

/-- `access` executes the fixed singleton operation and, only for a clean completed
run, returns the actual post-state together with its `AccessRun` proof. -/
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

end Grass.Op.AccessFactory
