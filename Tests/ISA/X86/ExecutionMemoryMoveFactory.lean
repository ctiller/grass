import Grass.ISA.X86.Execution.MemoryMoveFactory
import Tests.Op.FakeIsa

namespace Grass.Tests.MemoryMoveFactory

open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.ISA.X86.Execution.MemoryMoveNormal
open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Tests.FakeIsa

private def s32 := (movMem32Imm32 (.base .rsp 0x20) 0xAABBCCDD).get (by decide)
private def s64 := (movMem64Imm32 (.base .rsp 0x24) 0xFFFFFFFF).get (by decide)
private def l32 := (BasicInstructions.movReg32Mem .rcx (.base .rsp 0x28)).get (by decide)

example : (MemoryMoveSelection.select s32).map (·.instruction) =
    some (.store32Imm 0x20 0xAABBCCDD) := by decide
example : (MemoryMoveSelection.select s64).map (·.instruction) =
    some (.store64SignedImm32 0x24 0xFFFFFFFF) := by decide
example : (MemoryMoveSelection.select l32).map (·.instruction) =
    some (.load32 0x28 .rcx) := by decide
example : MemoryMoveSelection.select (BasicInstructions.movRegReg .w64 .rax .rcx) = none :=
  by decide

private def stores : FreshSupply StorageTag := .initial
private def codeBacking := stores.fresh.1
private def stackBacking := stores.fresh.2.fresh.1
private def rec (backing : StorageId) (source : AllocationSourceId)
    (permission : Permission) (base : Nat) : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual, source := source
    owners := [thread₀], permission := permission, live := true, backing := backing
    origin := 0, base := some base }
private def memory (encoding : InsnEncoding) : MemoryState :=
  let code := ByteStore.empty.write 0 encoding.toBytes true
  let stack := (ByteStore.empty.write 0 (List.replicate 64 0) true).write 40
    (le32 0x89ABCDEF) true
  let m0 := (MemoryState.empty.installBacking? codeBacking ⟨64, code⟩).getD .empty
  let m1 := (m0.installBacking? stackBacking ⟨64, stack⟩).getD .empty
  (m1.allocateAll? [(bufferAlloc, rec codeBacking .virtualAlloc .readExecute 0x1000),
    (chainedAlloc, rec stackBacking .mappedFile .readWrite 0x4000)]).getD .empty
private def before (encoding : InsnEncoding) : State :=
  { machine := .initial (memory encoding)
    gpr := fun r => if r = .rsp then 0x4000 else if r = .rcx then 0xFEDCBA9876543210 else 0
    rip := 0x1000, rflags := 0x202 }
private def cpu : CpuAccessPolicy :=
  { operationPolicy := policy, context := thread₀, contextKind := .thread
    cause := ⟨⟨"memory-move"⟩⟩, code := bufferProv, stack := chainedProv
    faults := fun _ => [.pageFault] }
private def ranStore := MemoryMoveFactory.memoryMove cpu (before s32)
private def stored := ranStore.toOption.get (by decide)

private def storeCommitted : Bool := match stored.execution with
  | .store _ receipt _ => receipt.access.run.complete.committed.written == some (le32 0xAABBCCDD)
  | .load _ _ _ => false
example : storeCommitted = true := by decide
example : stored.execution.result.machine.events.length = 2 := by decide

private def stored64 := (MemoryMoveFactory.memoryMove cpu (before s64)).toOption.get (by decide)
private def store64Committed : Bool := match stored64.execution with
  | .store _ receipt _ => receipt.access.run.complete.committed.written ==
      some (le64 (BitVec.signExtend 64 (0xFFFFFFFF : BitVec 32)))
  | .load _ _ _ => false
example : store64Committed = true := by decide
example : stored64.execution.result.machine.events.length = 2 := by decide

private def loaded32 := (MemoryMoveFactory.memoryMove cpu (before l32)).toOption.get (by decide)
private def load32Result : BitVec 64 := match loaded32.execution with
  | .load _ receipt _ => receipt.result.gpr .rcx
  | .store _ _ _ => 0
example : load32Result = 0x89ABCDEF := by decide
example : BitVec.extractLsb' 32 32 load32Result = 0 := by decide
example : loaded32.execution.result.machine.events.length = 2 := by decide

private def unplacedRecord : AllocationRecord :=
  { rec stackBacking .mappedFile .readWrite 0x4000 with base := none }
private def unplacedMemory : MemoryState :=
  let code := ByteStore.empty.write 0 s32.toBytes true
  let stack := ByteStore.empty.write 0 (List.replicate 64 0) true
  let m0 := (MemoryState.empty.installBacking? codeBacking ⟨64, code⟩).getD .empty
  let m1 := (m0.installBacking? stackBacking ⟨64, stack⟩).getD .empty
  (m1.allocateAll? [(bufferAlloc, rec codeBacking .virtualAlloc .readExecute 0x1000),
    (chainedAlloc, unplacedRecord)]).getD .empty
private def beforeUnplaced : State :=
  { before s32 with machine := .initial unplacedMemory }
private def unplacedRejected : Bool :=
  match MemoryMoveFactory.memoryMove cpu beforeUnplaced with
  | .error (.address reached .unplacedAllocation) => reached.machine.events.length = 1
  | _ => false
example : unplacedRejected = true := by decide

private def beforeOutOfBounds : State :=
  { before s32 with gpr := fun r => if r = .rsp then 0x4040 else 0 }
private def outOfBoundsRetainsFetch : Bool :=
  match MemoryMoveFactory.memoryMove cpu beforeOutOfBounds with
  | .error (.access reached _ (.rejected _)) =>
      reached.machine.events.length = 1
  | _ => false
example : outOfBoundsRetainsFetch = true := by decide

end Grass.Tests.MemoryMoveFactory
