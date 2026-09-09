import Grass.ISA.X86.Execution.FetchFactory
import Tests.Op.FakeIsa

namespace Grass.Tests.ExecutionFetchFactory

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def bytes : ByteSeq := [0x48, 0x89, 0xC3]
private def store := ByteStore.empty.write 0 bytes true
private def record : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
    source := .virtualAlloc, owners := [thread₀], permission := .readExecute
    live := true, backing := backing, origin := 0, base := some 0x1000 }
private def memory : MemoryState :=
  let backed := (MemoryState.empty.installBacking? backing ⟨64, store⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty
private def state : State :=
  { machine := .initial memory, gpr := fun _ => 0, rip := 0x1000, rflags := 0 }
private def cpu : CpuAccessPolicy :=
  { operationPolicy := policy, context := thread₀, contextKind := .thread
    cause := ⟨⟨"factory.fetch"⟩⟩, code := bufferProv, stack := bufferProv
    faults := fun _ => [.pageFault] }
private def result := FetchFactory.fetch cpu state
private def resultKind : Nat := match result with
  | .ok _ => 0
  | .error (.address _ _) => 1
  | .error (.access _ _ (.rejected _)) => 2
  | .error (.access _ _ (.violations _)) => 3
  | .error (.access _ _ (.preparationUnavailable _ _)) => 4
  | .error (.access _ _ (.answerUnavailable _)) => 5
  | .error (.applicability _ _) => 6

example : resultKind = 0 := by decide
private def success := result.toOption.get (by decide)
example : success.dispatched.fetch.site.encoding.toBytes = bytes := by decide
example : success.observed.bytes = bytes := by decide
example : success.after.events.length = 1 := by decide
example : success.observed.run.policy = FetchFactory.fetchPolicy cpu := success.policy_exact

private def unsupportedStore := ByteStore.empty.write 0 [0x90] true
private def unsupportedMemory : MemoryState :=
  let backed := (MemoryState.empty.installBacking? backing ⟨64, unsupportedStore⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty
private def unsupportedState : State := { state with machine := .initial unsupportedMemory }
private def unsupportedResult := FetchFactory.fetch cpu unsupportedState
private def unsupportedKind : Bool := match unsupportedResult with
  | .error (.applicability reached _) => reached.machine.events.length = 1
  | _ => false
example : unsupportedKind = true := by decide

private def disagreeingState : State :=
  { state with machine := state.machine.noteContext thread₀ .dmaEngine }
private def rejectedResult := FetchFactory.fetch cpu disagreeingState
private def rejectedKind : Bool := match rejectedResult with
  | .error (.access reached _ (.rejected _)) => reached.machine.events.isEmpty
  | _ => false
example : rejectedKind = true := by decide

private def invalidState : State := { state with machine := .initial MemoryState.empty }
private def invalidResult := FetchFactory.fetch cpu invalidState
example : (match invalidResult with | .error (.address reached _) => reached = invalidState | _ => False) := by
  rfl

end Grass.Tests.ExecutionFetchFactory
