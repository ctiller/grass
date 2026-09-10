import Grass.ISA.X86.Execution.ReturnSlotFactory
import Grass.ISA.X86.Execution.CallFactory
import Tests.Op.FakeIsa

namespace Grass.Tests.ExecutionReturnSlot

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def stores : FreshSupply StorageTag := .initial
private def codeBacking := stores.fresh.1
private def iatBacking := stores.fresh.2.fresh.1
private def stackBacking := stores.fresh.2.fresh.2.fresh.1

private def record (backing : StorageId) (source : AllocationSourceId)
    (permission : Permission) (base : Nat) : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual, source := source
    owners := [thread₀], permission := permission, live := true, backing := backing
    origin := 0, base := some base }

private def memoryWithSlot (slot : ByteSeq) : MemoryState :=
  let code := ByteStore.empty.write 0 [0xFF, 0x15, 0xFA, 0x1F, 0, 0] true
  let iat := ByteStore.empty.write 0 (le64 0x5000) true
  let stack := (ByteStore.empty.write 0 (List.replicate 64 0) true).write 56 slot true
  let m0 := (MemoryState.empty.installBacking? codeBacking ⟨64, code⟩).getD .empty
  let m1 := (m0.installBacking? iatBacking ⟨64, iat⟩).getD .empty
  let m2 := (m1.installBacking? stackBacking ⟨64, stack⟩).getD .empty
  (m2.allocateAll?
    [(bufferAlloc, record codeBacking .virtualAlloc .readExecute 0x1000),
     (viewAlloc, record iatBacking .mappedFile .readOnly 0x3000),
     (chainedAlloc, record stackBacking .mappedFile .readWrite 0x4000)]).getD .empty

private def before : State :=
  { machine := .initial (memoryWithSlot (List.replicate 8 0))
    gpr := fun register => if register = .rsp then 0x4040 else 0xCAFE
    rip := 0x1000, rflags := 0x10602 }

private def cpu : CpuAccessPolicy :=
  { operationPolicy := policy, context := thread₀, contextKind := .thread
    cause := ⟨⟨"return-slot"⟩⟩, code := bufferProv, stack := chainedProv
    data := fun address size =>
      if address = (0x3000 : MachineAddress) ∧ size = 8 then some viewProv else none
    faults := fun _ => [.pageFault] }

private def call := (CallFactory.call cpu before).toOption.get (by decide)
private def returned := ReturnSlotFactory.read cpu call.receipt call.result
private def success := returned.toOption.get (by decide)

example : success.receipt.read.value = (0x1006 : BitVec 64) := by decide
example : call.result.gpr .rsp + 8 = before.gpr .rsp := success.receipt.restoredRsp
example : success.afterRead.events.length = 4 := by decide
example : success.afterRead.memory = call.afterStore.memory ∧
    success.afterRead.obligations = call.afterStore.obligations := success.receipt.state_frame
example : success.receipt.descriptor.range = call.receipt.storeDescriptor.range :=
  success.receipt.slotRange
example : ∃ base, success.receipt.run.resolved.allocation.base = some base ∧
    base.toNat + call.receipt.storeDescriptor.range.stop = (before.gpr .rsp).toNat :=
  success.receipt.slot_origin

/-- A provider may replace the slot before this read; the actual read is retained on mismatch. -/
private def corrupted : State :=
  { machine := .initial (memoryWithSlot (le64 0xDEAD))
    gpr := fun register => if register = .rsp then 0x4038 else 0xBEEF
    rip := 0x7777, rflags := 0x202 }
private def corruptedResult := ReturnSlotFactory.read cpu call.receipt corrupted
private def mismatchRetainsRead : Bool := match corruptedResult with
  | .error (.targetMismatch reached actual expected) =>
      reached.machine.events.length = 1 && reached.rip == corrupted.rip &&
        actual == (0xDEAD : BitVec 64) &&
        expected == (0x1006 : BitVec 64)
  | _ => false
example : mismatchRetainsRead = true := by decide

end Grass.Tests.ExecutionReturnSlot
