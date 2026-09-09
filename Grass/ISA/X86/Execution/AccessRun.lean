import Grass.Op.CompletedAccess

/-!
# Exact singleton-access execution receipts

`AccessRun` packages evidence already checked by the generic operation stepper.
It does not describe instruction decoding, register transfer, or x86 memory
address computation. An ISA adapter supplies the descriptor and this receipt;
the generic completion theorem derives the completed event from the actual run.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

/-- Evidence that one exactly selected singleton access actually ran to a clean
completion under a concrete operation policy. -/
structure AccessRun (before after : MachineState) (descriptor : AccessDescriptor) where
  policy : StepPolicy
  operation : SomeOperation
  context : ContextId
  contextKind : ContextKind
  cause : EventCause
  faultAt : (sequence : SubstepSequence) → FaultPlan sequence
  sequence : SubstepSequence
  selected : operation.facets.substeps? = some sequence
  /-- The selected sequence contains this access substep and no other substep. -/
  substeps_exact : sequence.substeps = [.access descriptor]
  noFault : faultAt sequence = .none
  ran : step policy before operation context contextKind cause faultAt = .ran after
  resolved : (before.noteContext context contextKind).memory.ResolvedAccess
    descriptor.provenance descriptor.range
  prepared : prepareAccess (before.noteContext context contextKind).memory descriptor = .ok resolved
  complete : CompleteCommitted descriptor
  answerResolved : policy.oracle.answerResolved (before.noteContext context contextKind)
    descriptor resolved = some complete
  clean : after.violations.IsEmpty

namespace AccessRun

/-- The exact substep singleton projects to the singleton access list required
by the generic completion theorem. -/
theorem accesses_exact {before after : MachineState} {descriptor : AccessDescriptor}
    (run : AccessRun before after descriptor) : run.sequence.accesses = [descriptor] := by
  simp [SubstepSequence.accesses, run.substeps_exact]

/-- The fresh completed event is derived from the actual selected run and clean
ledger, not supplied by the caller as an output assertion. -/
theorem completed_event {before after : MachineState} {descriptor : AccessDescriptor}
    (run : AccessRun before after descriptor) :
    ∃ space valid,
      run.policy.profile.vocabulary.addressSpaces.find? descriptor.space = some space ∧
      MemoryEvent.ofOutcome before.eventSupply.fresh.1 run.contextKind run.cause space descriptor
        (.completed run.complete) run.resolved.allocation.mapping = some valid ∧
      after.events = before.events ++ [valid] ∧
      after.eventSupply = before.eventSupply.fresh.2 ∧
      after.faults = before.faults ∧ after.violations = before.violations := by
  exact ran_clean_singleton_event run.policy before run.operation run.context run.contextKind
    run.cause run.faultAt run.sequence descriptor after run.selected run.accesses_exact run.noFault
    run.ran run.resolved run.prepared run.complete run.answerResolved run.clean

end AccessRun
end Grass.ISA.X86.Execution
