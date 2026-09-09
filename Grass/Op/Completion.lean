import Grass.Op.Step

/-!
# Completion receipts for selected operations

These theorems expose the concrete memory-transition shape of an operation that
the generic stepper actually returned as `.ran`. They do not supply admission,
oracle, or clean-event facts, and they contain no ISA transfer semantics.
-/

namespace Grass.Op

open Grass.Core Grass.Memory

/-- A ran step with the selected sequence and its actual no-fault plan is the
corresponding `runStep` from the context-noted machine state. -/
theorem ran_noFault_eq_runStep (policy : StepPolicy) (before : MachineState)
    (operation : SomeOperation) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (faultAt : (sequence : SubstepSequence) → FaultPlan sequence)
    (sequence : SubstepSequence) (after : MachineState)
    (selected : operation.facets.substeps? = some sequence)
    (noFault : faultAt sequence = .none)
    (ran : step policy before operation context contextKind cause faultAt = .ran after) :
    after = runStep policy (before.noteContext context contextKind) sequence context
      contextKind cause .none := by
  unfold step at ran
  rw [selected] at ran
  dsimp only at ran
  rw [noFault] at ran
  repeat' split at ran
  all_goals first | contradiction | (cases ran; rfl)

/-- A selected sequence of a step that actually ran passed the generic
well-formedness gate. This exposes admission evidence without treating `.ran`
as a clean access result. -/
theorem ran_selected_wellFormed (policy : StepPolicy) (before : MachineState)
    (operation : SomeOperation) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (faultAt : (sequence : SubstepSequence) → FaultPlan sequence)
    (sequence : SubstepSequence) (after : MachineState)
    (selected : operation.facets.substeps? = some sequence)
    (ran : step policy before operation context contextKind cause faultAt = .ran after) :
    sequence.WellFormedIn policy.profile.vocabulary.addressSpaces := by
  unfold step at ran
  rw [selected] at ran
  dsimp only at ran
  repeat' split at ran <;> simp_all

/-- Every descriptor listed by a selected sequence that ran has a declared
address space and is well formed in that exact declaration. -/
theorem ran_selected_access_wellFormed (policy : StepPolicy) (before : MachineState)
    (operation : SomeOperation) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (faultAt : (sequence : SubstepSequence) → FaultPlan sequence)
    (sequence : SubstepSequence) (after : MachineState) (descriptor : AccessDescriptor)
    (selected : operation.facets.substeps? = some sequence)
    (ran : step policy before operation context contextKind cause faultAt = .ran after)
    (member : descriptor ∈ sequence.accesses) :
    ∃ space, policy.profile.vocabulary.addressSpaces.find? descriptor.space = some space ∧
      descriptor.WellFormedIn space := by
  have wellFormed := ran_selected_wellFormed policy before operation context contextKind cause
    faultAt sequence after selected ran
  obtain ⟨substep, hsubstep, hdescriptor⟩ := List.mem_filterMap.mp member
  cases substep with
  | compute faults => simp at hdescriptor
  | access actual =>
    simp only [Substep.descriptor?_access, Option.some.injEq] at hdescriptor
    subst actual
    have accessWellFormed := wellFormed (.access descriptor) hsubstep
    unfold Substep.WellFormedIn at accessWellFormed
    cases found : policy.profile.vocabulary.addressSpaces.find? descriptor.space with
    | none => simp [found] at accessWellFormed
    | some space =>
      change (match policy.profile.vocabulary.addressSpaces.find? descriptor.space with
        | some foundSpace => descriptor.WellFormedIn foundSpace
        | none => False) at accessWellFormed
      rw [found] at accessWellFormed
      exact ⟨space, rfl, accessWellFormed⟩

/-- A ran, selected access-free no-fault step has no generic memory transition;
only the context-kind association may change. This does not execute compute
substeps, whose ISA meaning belongs to a later layer. -/
theorem ran_accessFree_noFault_eq_noteContext (policy : StepPolicy) (before : MachineState)
    (operation : SomeOperation) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (faultAt : (sequence : SubstepSequence) → FaultPlan sequence)
    (sequence : SubstepSequence) (after : MachineState)
    (selected : operation.facets.substeps? = some sequence)
    (accessFree : sequence.accesses = [])
    (noFault : faultAt sequence = .none)
    (ran : step policy before operation context contextKind cause faultAt = .ran after) :
    after = before.noteContext context contextKind := by
  rw [ran_noFault_eq_runStep policy before operation context contextKind cause faultAt
    sequence after selected noFault ran]
  simp [runStep, runAccesses, accessFree]

/-- A ran no-fault step whose selected sequence has exactly one access reduces
to the prepared access transition at the reached context-noted state. The
premises intentionally retain the exact prepared access and resolved oracle
answer; they do not claim the transition produced a clean event. -/
theorem ran_singleton_prepared_eq_performPreparedAccess (policy : StepPolicy)
    (before : MachineState) (operation : SomeOperation) (context : ContextId)
    (contextKind : ContextKind) (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence)
    (sequence : SubstepSequence) (descriptor : AccessDescriptor) (after : MachineState)
    (selected : operation.facets.substeps? = some sequence)
    (singleton : sequence.accesses = [descriptor])
    (noFault : faultAt sequence = .none)
    (ran : step policy before operation context contextKind cause faultAt = .ran after)
    (resolved : (before.noteContext context contextKind).memory.ResolvedAccess
      descriptor.provenance descriptor.range)
    (prepared : prepareAccess (before.noteContext context contextKind).memory descriptor = .ok resolved)
    (complete : CompleteCommitted descriptor)
    (answerResolved : policy.oracle.answerResolved (before.noteContext context contextKind)
      descriptor resolved = some complete) :
    after = performPreparedAccess policy (before.noteContext context contextKind) descriptor
      resolved prepared (.completed complete) contextKind cause := by
  rw [ran_noFault_eq_runStep policy before operation context contextKind cause faultAt
    sequence after selected noFault ran]
  simp only [runStep, singleton]
  rw [runAccesses_of_prepared policy (before.noteContext context contextKind) descriptor []
    contextKind cause resolved prepared, answerResolved]
  simp [runAccesses]

end Grass.Op
