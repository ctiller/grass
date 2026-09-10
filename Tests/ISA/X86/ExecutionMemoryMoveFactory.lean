import Grass.ISA.X86.Execution.MemoryMoveFactory
import Tests.Op.FakeIsa

namespace Grass.Tests.MemoryMoveFactory

open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.ISA.X86.Execution.MemoryMoveNormal
open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Tests.FakeIsa

private def s32 := (movMem32Imm32 (.base .rsp 0x20) 0xAABBCCDD).get (by decide)
private def s64 := (movMem64Imm32 (.base .rsp 0x24) 0xFFFFFFFF).get (by decide)
private def l32 := (BasicInstructions.movReg32Mem .rcx (.base .rsp 0x28)).get (by decide)
private def sr64 := (MemoryMoveNormal.Instruction.store64Reg (.base .rsp 0x30) .rcx).encode?.get
  (by decide)
private def dataStore64 :=
  (MemoryMoveNormal.Instruction.store64Reg (.base .rdx 0x30) .rcx).encode?.get (by decide)
private def rspIndexStore64 :=
  (MemoryMoveNormal.Instruction.store64Reg (.baseIndex .rsp .rax .s1 0x30) .rcx).encode?.get
    (by decide)
private def ripStore64 :=
  (MemoryMoveNormal.Instruction.store64Reg (.ripRelative 0x2FF9) .r9).encode?.get (by decide)
private def l64 := (MemoryMoveNormal.Instruction.load64 (.base .rsp 0x28) .rax).encode?.get
  (by decide)

example : (MemoryMoveSelection.select s32).map (·.instruction) =
    some (.store32Imm 0x20 0xAABBCCDD) := by decide
example : (MemoryMoveSelection.select s64).map (·.instruction) =
    some (.store64SignedImm32 0x24 0xFFFFFFFF) := by decide
example : (MemoryMoveSelection.select l32).map (·.instruction) =
    some (.load32 0x28 .rcx) := by decide
example : (MemoryMoveSelection.select sr64).map (·.instruction) =
    some (.store64Reg (.base .rsp 0x30) .rcx) := by decide
example : (MemoryMoveSelection.select l64).map (·.instruction) =
    some (.load64 (.base .rsp 0x28) .rax) := by decide
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
private def dataCpu : CpuAccessPolicy :=
  { cpu with data := fun address width =>
      if address = (0x4030 : MachineAddress) ∧ width = 8 then some chainedProv else none }
private def ranStore := MemoryMoveFactory.memoryMove cpu (before s32)
private def stored := ranStore.toOption.get (by decide)

private def storeCommitted : Bool := match stored.execution with
  | .store _ receipt _ => receipt.access.run.complete.committed.written == some (le32 0xAABBCCDD)
  | .load _ _ _ => false
  | .storeRegister64 _ _ _ | .load64 _ _ _ => false
example : storeCommitted = true := by decide
example : stored.execution.result.machine.events.length = 2 := by decide

private def stored64 := (MemoryMoveFactory.memoryMove cpu (before s64)).toOption.get (by decide)
private def store64Committed : Bool := match stored64.execution with
  | .store _ receipt _ => receipt.access.run.complete.committed.written ==
      some (le64 (BitVec.signExtend 64 (0xFFFFFFFF : BitVec 32)))
  | .load _ _ _ => false
  | .storeRegister64 _ _ _ | .load64 _ _ _ => false
example : store64Committed = true := by decide
example : stored64.execution.result.machine.events.length = 2 := by decide

private def loaded32 := (MemoryMoveFactory.memoryMove cpu (before l32)).toOption.get (by decide)
private def load32Result : BitVec 64 := match loaded32.execution with
  | .load _ receipt _ => receipt.result.gpr .rcx
  | .store _ _ _ => 0
  | .storeRegister64 _ _ _ | .load64 _ _ _ => 0
example : load32Result = 0x89ABCDEF := by decide
example : BitVec.extractLsb' 32 32 load32Result = 0 := by decide

example : loaded32.execution.provenance = cpu.stack :=
  MemoryMoveFactory.memoryMove_load_stack (by rfl)
example : loaded32.execution.result.machine.events.length = 2 := by decide

private def storedRegister64 :=
  (MemoryMoveFactory.memoryMove cpu (before sr64)).toOption.get (by decide)
private def storeRegister64Committed : Bool := match storedRegister64.execution with
  | .storeRegister64 _ receipt _ =>
      receipt.access.run.complete.committed.written == some (le64 0xFEDCBA9876543210)
  | _ => false
example : storeRegister64Committed = true := by decide

private def storedDataRegister64 :=
  (MemoryMoveFactory.memoryMove dataCpu
    { before dataStore64 with gpr := fun r =>
        if r = .rsp then 0x4000 else if r = .rdx then 0x4000
        else if r = .rcx then 0xFEDCBA9876543210 else 0 }).toOption.get (by decide)
private def dataStorePurpose : Bool := match storedDataRegister64.execution with
  | .storeRegister64 _ receipt _ =>
      receipt.access.descriptor.intent == .write ∧
        receipt.access.descriptor.provenance == chainedProv
  | _ => false
example : dataStorePurpose = true := by decide

private def storedRspIndex64 :=
  (MemoryMoveFactory.memoryMove cpu (before rspIndexStore64)).toOption.get (by decide)
example : storedRspIndex64.execution.provenance = cpu.stack := by decide

private def missingDataIsDistinct : Bool :=
  match MemoryMoveFactory.memoryMove cpu
      { before dataStore64 with gpr := fun r =>
          if r = .rsp then 0x4000 else if r = .rdx then 0x4000 else 0 } with
  | .error (.missingData reached address) =>
      reached.machine.events.length = 1 ∧ address = (0x4030 : MachineAddress)
  | _ => false
example : missingDataIsDistinct = true := by decide

private def ripCpu : CpuAccessPolicy :=
  { cpu with data := fun address width =>
      if address = (0x4000 : MachineAddress) ∧ width = 8 then some chainedProv else none }
private def storedRip64 :=
  (MemoryMoveFactory.memoryMove ripCpu
    { before ripStore64 with gpr := fun r =>
        if r = .rsp then 0x4000 else if r = .r9 then 0x1122334455667788 else 0 }).toOption.get
      (by decide)
private def ripStoreExact : Bool := match storedRip64.execution with
  | .storeRegister64 _ receipt _ =>
      receipt.access.descriptor.address == .numeric 0x4000 ∧
        receipt.access.run.complete.committed.written == some (le64 0x1122334455667788)
  | _ => false
example : ripStoreExact = true := by decide

private def loaded64 := (MemoryMoveFactory.memoryMove cpu (before l64)).toOption.get (by decide)
private def load64Result : BitVec 64 := match loaded64.execution with
  | .load64 _ receipt _ => receipt.result.gpr .rax
  | _ => 0
example : load64Result = 0x89ABCDEF := by decide
example : loaded64.execution.provenance = cpu.stack := by decide

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
