import Grass.ISA.X86.Execution.State
import Grass.Op.Completion

/-!
# Actual execute-fetch attempts

This receipt describes the operation step before deciding whether it completed
an observable fetch. It carries the exact `StepOutcome`; it does not rename a
rejection or a running fault into an ISA-level result.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

/-- An exact selected singleton execute-fetch attempt, indexed by the actual
generic step outcome. -/
structure FetchAttempt (before : State) (outcome : StepOutcome) where
  policy : StepPolicy
  operation : SomeOperation
  context : ContextId
  contextKind : ContextKind
  cause : EventCause
  faultAt : (sequence : SubstepSequence) → FaultPlan sequence
  descriptor : AccessDescriptor
  sequence : SubstepSequence
  selected : operation.facets.substeps? = some sequence
  substeps_exact : sequence.substeps = [.access descriptor]
  contextExact : descriptor.context = context
  intent : descriptor.intent = .execute
  initialization : descriptor.initialization = .allBytesInitialized
  ledgerEffect : descriptor.ledgerEffect = []
  authorityEffect : descriptor.authorityEffect = []
  address : descriptor.address = .numeric before.rip
  actual : step policy before.machine operation context contextKind cause faultAt = outcome

namespace FetchAttempt

/-- A rejected attempt is tied to the generic rejection it actually received. -/
theorem rejected {before : State} {reason : StepRejection}
    (attempt : FetchAttempt before (.rejected reason)) :
    step attempt.policy before.machine attempt.operation attempt.context attempt.contextKind
      attempt.cause attempt.faultAt = .rejected reason := attempt.actual

/-- A running attempt passed the generic selected-sequence well-formedness gate. -/
theorem selected_wellFormed {before : State} {after : MachineState}
    (attempt : FetchAttempt before (.ran after)) :
    attempt.sequence.WellFormedIn attempt.policy.profile.vocabulary.addressSpaces :=
  ran_selected_wellFormed attempt.policy before.machine attempt.operation attempt.context
    attempt.contextKind attempt.cause attempt.faultAt attempt.sequence after attempt.selected
    attempt.actual

/-- The descriptor of a running attempt is admitted in an exact declared address
space. This says nothing about oracle completion or a decoded instruction. -/
theorem wellFormed {before : State} {after : MachineState}
    (attempt : FetchAttempt before (.ran after)) :
    ∃ space, attempt.policy.profile.vocabulary.addressSpaces.find? attempt.descriptor.space = some space ∧
      attempt.descriptor.WellFormedIn space := by
  apply ran_selected_access_wellFormed attempt.policy before.machine attempt.operation
    attempt.context attempt.contextKind attempt.cause attempt.faultAt attempt.sequence after
    attempt.descriptor attempt.selected attempt.actual
  simp [SubstepSequence.accesses, attempt.substeps_exact]

end FetchAttempt
end Grass.ISA.X86.Execution
