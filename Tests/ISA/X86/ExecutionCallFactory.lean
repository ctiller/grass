import Grass.ISA.X86.Execution.CallFactory
import Tests.Op.FakeIsa

namespace Grass.Tests.ExecutionCallFactory

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

private def memory : MemoryState :=
  let code := ByteStore.empty.write 0 [0xFF, 0x15, 0xFA, 0x1F, 0, 0] true
  let iat := ByteStore.empty.write 0 (le64 0x5000) true
  let stack := ByteStore.empty.write 0 (List.replicate 64 0) true
  let m0 := (MemoryState.empty.installBacking? codeBacking ⟨64, code⟩).getD .empty
  let m1 := (m0.installBacking? iatBacking ⟨64, iat⟩).getD .empty
  let m2 := (m1.installBacking? stackBacking ⟨64, stack⟩).getD .empty
  (m2.allocateAll?
    [(bufferAlloc, record codeBacking .virtualAlloc .readExecute 0x1000),
     (viewAlloc, record iatBacking .mappedFile .readOnly 0x3000),
     (chainedAlloc, record stackBacking .mappedFile .readWrite 0x4000)]).getD .empty

private def before : State :=
  { machine := .initial memory
    gpr := fun register => if register = .rsp then 0x4040 else 0xCAFE
    rip := 0x1000
    rflags := 0x10602 }

private def cpu : CpuAccessPolicy :=
  { operationPolicy := policy
    context := thread₀
    contextKind := .thread
    cause := ⟨⟨"call.factory"⟩⟩
    code := bufferProv
    stack := chainedProv
    data := fun address size =>
      if address = (0x3000 : MachineAddress) ∧ size = 8 then some viewProv else none
    faults := fun _ => [.pageFault] }

private def result := CallFactory.call cpu before
private def success := result.toOption.get (by decide)

example : success.displacement = 0x1FFA := by decide
example : success.result.rip = 0x5000 := by decide
example : success.result.gpr .rsp = 0x4038 := by decide
example : success.result.rflags = 0x602 := by decide
example : success.afterStore.events.length = 3 := by decide
example : success.afterStore.memory.byteAt? chainedAlloc 56 = some 0x06 := by decide
example : success.receipt.storeRun.complete.committed.written =
    some (le64 (BitVec.ofNat 64 0x1006)) := success.receipt.written_exact

private def missingCpu : CpuAccessPolicy := { cpu with data := fun _ _ => none }
private def missingResult := CallFactory.call missingCpu before
private def missingRetainsFetch : Bool := match missingResult with
  | .error (.missingData reached address) =>
      reached.machine.events.length = 1 && address == (0x3000 : MachineAddress)
  | _ => false
example : missingRetainsFetch = true := by decide

private def underflow : State := { before with gpr := fun _ => 0 }
private def underflowResult := CallFactory.call cpu underflow
private def underflowRetainsRead : Bool := match underflowResult with
  | .error (.stackUnderflow reached) => reached.machine.events.length = 2
  | _ => false
example : underflowRetainsRead = true := by decide

/-- This fault name is deliberately absent from the fixture vocabulary. -/
private def rejectedStoreFault : FaultClassId := ⟨⟨"call.factory.rejectedStore"⟩⟩

/-- Fetch and target reads retain their admitted page-fault declaration; only
the return-address store names the absent fault class. -/
private def storeRejectedCpu : CpuAccessPolicy :=
  { cpu with faults := fun purpose =>
      if purpose = .stackWrite then [rejectedStoreFault] else cpu.faults purpose }

/-- The inadmissible store is rejected before it can run.  The completed fetch
and indirect-target read remain the exact visible prefix, while CALL's CPU
register state remains the original one. -/
private def storeRejectionRetainsReadAndCpu : Bool :=
  match CallFactory.call storeRejectedCpu before with
  | .error (.store reached descriptor
      (.rejected (.accessNotAdmitted (.faultClassNotRecognized fault)))) =>
      fault == rejectedStoreFault &&
      reached.machine.events.length == 2 &&
      reached.rip == before.rip &&
      Gpr.all.all (fun register => decide (reached.gpr register = before.gpr register)) &&
      reached.rflags == before.rflags &&
      descriptor.provenance == chainedProv &&
      descriptor.range == (⟨56, 8⟩ : ByteRange) &&
      reached.machine.violations.records? == []
  | _ => false

example : storeRejectionRetainsReadAndCpu = true := by decide

end Grass.Tests.ExecutionCallFactory
