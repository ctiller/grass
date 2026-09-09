import Grass.ISA.X86.Execution.ObservedFetch
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionObservedFetch

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def bytes : ByteStore := ByteStore.empty.write 0 [0x0F, 0x0C] true
private def record : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual, source := .virtualAlloc
    owners := [thread₀], permission := .readExecute, live := true, backing := backing
    origin := 0, base := some 0x1000 }
private def memory : MemoryState :=
  let backed := (MemoryState.empty.installBacking? backing ⟨64, bytes⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty
private def machine : MachineState := .initial memory
private def descriptor : AccessDescriptor :=
  acc bufferProv ⟨0, 2⟩ 0x1000 .execute .readExecute true false
private inductive Operation where | fetch
private instance : HasOperationFacets Operation where
  facets
    | .fetch =>
      { memoryEffects := some (.single descriptor), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }
private def before : State :=
  { machine := machine, gpr := fun _ => 0, rip := 0x1000, rflags := 0 }
private def reached : MachineState := machine.noteContext thread₀ .thread
private def resolved : reached.memory.ResolvedAccess descriptor.provenance descriptor.range :=
  (prepareAccess reached.memory descriptor).toOption.get (by decide)
private theorem prepared : prepareAccess reached.memory descriptor = .ok resolved := by rfl
private def complete : CompleteCommitted descriptor :=
  (policy.oracle.answerResolved reached descriptor resolved).get (by decide)
private def stepResult : StepOutcome :=
  step policy machine (SomeOperation.of Operation.fetch) thread₀ .thread ⟨⟨"raw-fetch"⟩⟩
private def after : MachineState :=
  match stepResult with | .ran state => state | .rejected _ => machine

example : ∃ (fetch : ObservedFetch before after),
    fetch.bytes = [0x0F, 0x0C] ∧ (DecodedSite.check before.rip fetch.bytes).toOption = none := by
  have ran : stepResult = .ran after := by rfl
  have clean : after.violations.IsEmpty := by decide
  let run : AccessRun machine after descriptor :=
    { policy := policy, operation := SomeOperation.of Operation.fetch
      context := thread₀, contextKind := .thread, cause := ⟨⟨"raw-fetch"⟩⟩
      faultAt := fun _ => .none, sequence := .single descriptor
      selected := by rfl, substeps_exact := by rfl, noFault := by rfl, ran := ran
      resolved := resolved, prepared := by
        change prepareAccess reached.memory descriptor = .ok resolved
        exact prepared
      complete := complete, answerResolved := by simp [complete, reached]
      clean := clean }
  let fetch : ObservedFetch before after :=
    { descriptor := descriptor, run := run, writeData := storedBytes
      indeterminate := indeterminateByte, memoryOracle := by rfl
      intent := by rfl, initialization := by rfl, ledgerEffect := by rfl
      authorityEffect := by rfl, address := by rfl, placed := ⟨0x1000, by rfl⟩ }
  have bytesExact : fetch.bytes = [0x0F, 0x0C] := by rfl
  have undecoded : (DecodedSite.check before.rip fetch.bytes).toOption = none := by
    rw [bytesExact]
    decide
  exact ⟨fetch, bytesExact, undecoded⟩

end Grass.Tests.ISA.X86.ExecutionObservedFetch
