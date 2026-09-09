import Grass.ISA.X86.Execution.PushFactory
import Tests.Op.FakeIsa

namespace Grass.Tests.ExecutionPushFactory

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def codeBacking : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def stackBacking : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.2.fresh.1
private def codeRecord : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual, source := .virtualAlloc
    owners := [thread₀], permission := .readExecute, live := true, backing := codeBacking
    origin := 0, base := some 0x1000 }
private def stackRecord : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual, source := .mappedFile
    owners := [thread₀], permission := .readWrite, live := true, backing := stackBacking
    origin := 0, base := some 0x2000 }
private def memory : MemoryState :=
  let code := ByteStore.empty.write 0 [0x41, 0x54] true
  let withCode := (MemoryState.empty.installBacking? codeBacking ⟨64, code⟩).getD .empty
  let withStack := (withCode.installBacking? stackBacking ⟨64, ByteStore.empty⟩).getD .empty
  (withStack.allocateAll? [(bufferAlloc, codeRecord), (viewAlloc, stackRecord)]).getD .empty
private def before : State :=
  { machine := .initial memory
    gpr := fun register => if register = .rsp then 0x2040
      else if register = .r12 then 0x0123456789ABCDEF else 0
    rip := 0x1000
    rflags := 0x10000 }
private def cpu : CpuAccessPolicy :=
  { operationPolicy := policy, context := thread₀, contextKind := .thread
    cause := ⟨⟨"push.factory"⟩⟩, code := bufferProv, stack := viewProv
    faults := fun _ => [.pageFault] }
private def result := PushFactory.push cpu before
private def success := result.toOption.get (by decide)

example : success.register = .r12 := by decide
example : success.receipt.result.gpr .rsp = 0x2038 := by decide
example : success.receipt.result.rip = 0x1002 := by decide
example : success.afterStore.events.length = 2 := by decide
example : success.receipt.store.complete.committed.written =
    some (le64 (before.gpr .r12)) := success.receipt.written_exact
example : success.afterStore.memory.byteAt? viewAlloc 56 = some 0xEF := by decide

private def underflow : State := { before with gpr := fun _ => 0 }
private def underflowResult := PushFactory.push cpu underflow
private def underflowRetainsFetch : Bool := match underflowResult with
  | .error (.stackUnderflow reached) => reached.machine.events.length = 1
  | _ => false
example : underflowRetainsFetch = true := by decide

end Grass.Tests.ExecutionPushFactory
