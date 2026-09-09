import Grass.ISA.X86.Execution.RunFactory
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionRunFactory

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def store := ByteStore.empty.write 0 [0x90] true
private def record : AllocationRecord :=
  { extent := ⟨0, 16⟩, epoch := epoch₀, space := .cpuVirtual, source := .virtualAlloc
    owners := [thread₀], permission := .readExecute, live := true, backing := backing
    origin := 0, base := some 0x1000 }
private def memory : MemoryState :=
  let backed := (MemoryState.empty.installBacking? backing ⟨16, store⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty
private def before := MachineState.initial memory
private def descriptor : AccessDescriptor :=
  { acc bufferProv ⟨0, 1⟩ 0x1000 .execute .readExecute true false with
    restartability := .restartable }
private def cause : EventCause := ⟨⟨"factory.fetch"⟩⟩

private def built := RunFactory.access policy before descriptor thread₀ .thread cause
example : (RunFactory.singletonOperation descriptor).facets.memoryEffects =
    some (.single descriptor) := rfl
example : (RunFactory.singletonOperation descriptor).facets.faults =
    some descriptor.admittedFaults := rfl
example : (RunFactory.singletonOperation descriptor).facets.restartability =
    some descriptor.restartability := rfl
example : (RunFactory.singletonOperation descriptor).facets.ordering =
    some descriptor.ordering := rfl

/-- This policy reports a violation for the descriptor's exact requested
facets. The factory retains the actual ran state instead of producing a normal receipt. -/
private def retainedRanState : Bool := match built with
  | .error (.violations _) => true
  | _ => false
example : retainedRanState = true := by decide

private def freeBuilt := RunFactory.accessFree policy before thread₀ .thread cause
private def freeSuccess := freeBuilt.toOption.get (by decide)
example : freeSuccess.1 = before.noteContext thread₀ .thread := freeSuccess.2.state_eq
example : freeSuccess.1.events = before.events := by rw [freeSuccess.2.state_eq]; rfl

/-- A descriptor outside the allocation is rejected; the factory does not mint
a successful receipt for it. -/
private def badDescriptor : AccessDescriptor :=
  { acc bufferProv ⟨32, 1⟩ 0x1020 .execute .readExecute true false with
    restartability := .restartable }
private def failed := RunFactory.access policy before badDescriptor thread₀ .thread cause
private def retainedViolation : Bool := match failed with
  | .error (.violations _) => true
  | _ => false
example : retainedViolation = true := by decide

end Grass.Tests.ISA.X86.ExecutionRunFactory
