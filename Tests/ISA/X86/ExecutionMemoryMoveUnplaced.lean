import Grass.ISA.X86.Execution.MemoryMoveNormal

/-! A numeric access can prepare against a base-less allocation, but such a
resolution cannot satisfy the placement requirement of a normal x86 memory MOV. -/

namespace Grass.Tests.ISA.X86.ExecutionMemoryMoveUnplaced

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution Grass.ISA.X86.Execution.MemoryMoveNormal

private def alloc : AllocId := (FreshSupply.initial : FreshSupply AllocTag).fresh.1
private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def epoch : EpochId := (FreshSupply.initial : FreshSupply EpochTag).fresh.1
private def context : ContextId := (FreshSupply.initial : FreshSupply ContextTag).fresh.1

private def record : AllocationRecord :=
  { extent := ⟨0, 16⟩, epoch := epoch, space := .cpuVirtual, source := .stack
    owners := [context], permission := .readWrite, live := true
    backing := backing, origin := 0, base := none }

private def memory? : Option MemoryState := do
  let state ← MemoryState.empty.installBacking? backing ⟨16, .empty⟩
  state.allocate? alloc record

private def memory : MemoryState := memory?.get (by decide)

private def provenance : Provenance :=
  { space := .cpuVirtual, root := alloc, epoch := epoch, source := .stack
    rootExtent := ⟨0, 16⟩, path := [] }

private def descriptor : AccessDescriptor :=
  { context := context, address := .numeric 0x9000, space := .cpuVirtual
    provenance := provenance, range := ⟨0, 4⟩, intent := .write
    requiredPermission := .readWrite, alignment := 4
    initialization := .readsNothing, producesInitialized := true
    admittedFaults := [.pageFault, .generalProtection] }

private def resolved : memory.ResolvedAccess descriptor.provenance descriptor.range :=
  (prepareAccess memory descriptor).toOption.get (by decide)

example : prepareAccess memory descriptor = .ok resolved := by rfl
example : resolved.allocation.base = none := by rfl

/-- Any purported normal store using the successfully prepared but unplaced
allocation contradicts the generic receipt's mandatory placement witness. -/
example {instruction : MemoryMoveNormal.Instruction}
    {encoded : MemoryMoveNormal.Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : MemoryMoveNormal.StoreNormal instruction encoded before afterFetch afterData)
    (sameAllocation : receipt.access.run.resolved.allocation = resolved.allocation) : False := by
  apply receipt.unplaced_impossible
  rw [sameAllocation]
  exact rfl

/-- `LoadNormal.unplaced_impossible` enforces the same requirement for reads. -/
example {instruction : MemoryMoveNormal.Instruction}
    {encoded : MemoryMoveNormal.Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : MemoryMoveNormal.LoadNormal instruction encoded before afterFetch afterData)
    (sameAllocation : receipt.access.run.resolved.allocation = resolved.allocation) : False := by
  apply receipt.unplaced_impossible
  rw [sameAllocation]
  exact rfl

end Grass.Tests.ISA.X86.ExecutionMemoryMoveUnplaced
