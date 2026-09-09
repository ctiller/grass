import Grass.ISA.X86.Execution.ComputationFactory
import Tests.Op.FakeIsa

namespace Grass.Tests.ExecutionComputationFactory

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def makeMemory (bytes : ByteSeq) : MemoryState :=
  let store := ByteStore.empty.write 0 bytes true
  let record : AllocationRecord :=
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
      source := .virtualAlloc, owners := [thread₀], permission := .readExecute
      live := true, backing := backing, origin := 0, base := some 0x1000 }
  let backed := (MemoryState.empty.installBacking? backing ⟨64, store⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty
private def makeState (bytes : ByteSeq) : State :=
  { machine := .initial (makeMemory bytes)
    gpr := fun register => if register = .rax then 0x123456789ABCDEF0 else 0
    rip := 0x1000
    rflags := 0x10000 }
private def cpu : CpuAccessPolicy :=
  { operationPolicy := policy
    context := thread₀
    contextKind := .thread
    cause := ⟨⟨"computation.factory"⟩⟩
    code := bufferProv
    stack := bufferProv
    faults := fun _ => [.pageFault] }

private def movState := makeState [0x48, 0x89, 0xC3]
private def movResult := ComputationFactory.move cpu movState
private def movSuccess := movResult.toOption.get (by decide)
example : movSuccess.result.gpr .rbx = 0x123456789ABCDEF0 := by decide
example : movSuccess.result.rip = 0x1003 := by decide
example : movSuccess.result.rflags = 0 := by decide
example : movSuccess.afterFetch.events.length = 1 := by decide
example : movSuccess.afterCompute.events.length = 1 := by decide

private def addState := makeState [0x48, 0x01, 0xC3]
private def addResult := ComputationFactory.move cpu addState
private def isUnsupported : Bool := match addResult with
  | .error (.unsupported reached (.arithmetic _)) => reached.machine.events.length = 1
  | _ => false
example : isUnsupported = true := by decide

private def rejectedState : State :=
  { movState with machine := movState.machine.noteContext thread₀ .dmaEngine }
private def rejectedResult := ComputationFactory.move cpu rejectedState
private def isFetchRejected : Bool := match rejectedResult with
  | .error (.fetch (.access reached _ (.rejected _))) => reached.machine.events.isEmpty
  | _ => false
example : isFetchRejected = true := by decide

end Grass.Tests.ExecutionComputationFactory
