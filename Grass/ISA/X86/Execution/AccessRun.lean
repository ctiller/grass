import Grass.Op.AccessRun

/-!
# x86 compatibility name for generic singleton-access receipts

The receipt is generic `Grass.Op.AccessFactory.AccessRun`; this alias keeps existing x86
consumers and qualified theorem names stable while platform and other ISA
adapters use the source-independent API.
-/

namespace Grass.ISA.X86.Execution

abbrev AccessRun := Grass.Op.AccessFactory.AccessRun

namespace AccessRun

/-- Compatibility wrapper preserving method-style use by existing x86 consumers. -/
theorem accesses_exact {before after : Grass.Memory.MachineState}
    {descriptor : Grass.Memory.AccessDescriptor} (run : AccessRun before after descriptor) :
    run.sequence.accesses = [descriptor] :=
  Grass.Op.AccessFactory.AccessRun.accesses_exact run

/-- Compatibility wrapper preserving x86-qualified admission projection. -/
theorem wellFormed {before after : Grass.Memory.MachineState}
    {descriptor : Grass.Memory.AccessDescriptor} (run : AccessRun before after descriptor) :
    ∃ space, run.policy.profile.vocabulary.addressSpaces.find? descriptor.space = some space ∧
      descriptor.WellFormedIn space :=
  Grass.Op.AccessFactory.AccessRun.wellFormed run

/-- Compatibility wrapper preserving x86-qualified prepared-result projection. -/
theorem prepared_result {before after : Grass.Memory.MachineState}
    {descriptor : Grass.Memory.AccessDescriptor} (run : AccessRun before after descriptor) :
    after = Grass.Op.performPreparedAccess run.policy
      (before.noteContext run.context run.contextKind) descriptor run.resolved run.prepared
      (.completed run.complete) run.contextKind run.cause :=
  Grass.Op.AccessFactory.AccessRun.prepared_result run

/-- Compatibility wrapper preserving x86-qualified completed-event projection. -/
theorem completed_event {before after : Grass.Memory.MachineState}
    {descriptor : Grass.Memory.AccessDescriptor} (run : AccessRun before after descriptor) :
    ∃ space valid,
      run.policy.profile.vocabulary.addressSpaces.find? descriptor.space = some space ∧
      Grass.Memory.MemoryEvent.ofOutcome before.eventSupply.fresh.1 run.contextKind run.cause
        space descriptor (.completed run.complete) run.resolved.allocation.mapping = some valid ∧
      after.events = before.events ++ [valid] ∧
      after.eventSupply = before.eventSupply.fresh.2 ∧
      after.faults = before.faults ∧ after.violations = before.violations :=
  Grass.Op.AccessFactory.AccessRun.completed_event run

end AccessRun
end Grass.ISA.X86.Execution
