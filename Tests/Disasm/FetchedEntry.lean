import Grass.Disasm.FetchedEntry
import Tests.Artifact.PE.Imported
import Tests.Op.FakeIsa

/-! Conditional original-entry fetch receipt only; no store-execution claim. -/
namespace Grass.Tests.Disasm.FetchedEntry
open Grass.Core Grass.Artifact.PE Grass.Disasm.Entry Grass.Disasm.FetchedEntry Grass.Memory
  Grass.Op Grass.Std.Logical Grass.ISA.X86 Grass.ISA.X86.Execution
open Tests.Artifact.PE.Imported Grass.Tests.FakeIsa
set_option maxRecDepth 10000

private def input : Grass.Std.Logical.ByteArray := (externalFixture.set 512 0x41).set 513 0x54
private def checked? : Option (CheckedImportedImage input) :=
  match checkImportedImage input with | .done x _ => some x | _ => none
theorem checked_ok : checked?.isSome := by decide
private def checked := checked?.get checked_ok
private def entry? : Option (Entry input) := match selectEntry checked 0x1000 with | .ok x => some x | _ => none
theorem entry_ok : entry?.isSome := by decide
private def entry := entry?.get entry_ok
example : entry.bytes = [0x41, 0x54] := by decide

private def fetchBacking : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def fetchBytes : ByteStore := ByteStore.empty.write 0 [0x41, 0x54] true
private def fetchRecord : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual, source := .virtualAlloc
    owners := [thread₀], permission := .readExecute, live := true, backing := fetchBacking
    origin := 0, base := some 0x50001000 }
private def fetchMemory? : Option MemoryState := do
  let backed ← MemoryState.empty.installBacking? fetchBacking ⟨64, fetchBytes⟩
  backed.allocateAll? [(bufferAlloc, fetchRecord)]
theorem fetch_memory_ok : fetchMemory?.isSome := by decide
private def fetchMachine : MachineState := .initial (fetchMemory?.get fetch_memory_ok)
private def descriptor : AccessDescriptor := acc bufferProv ⟨0, 2⟩ 0x50001000 .execute .readExecute true false
private inductive FetchOperation where | fetch
private instance : HasOperationFacets FetchOperation where
  facets
    | .fetch =>
      { memoryEffects := some (.single descriptor), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }
private def before : State := { machine := fetchMachine, gpr := fun _ => 0, rip := 0x50001000, rflags := 0 }
private def fetchStep : StepOutcome := step policy fetchMachine (SomeOperation.of FetchOperation.fetch) thread₀ .thread ⟨⟨"fetch"⟩⟩
private def after? : Option MachineState := match fetchStep with | .ran state => some state | _ => none
theorem after_ok : after?.isSome := by decide
private def after : MachineState := after?.get after_ok
private theorem ran : fetchStep = .ran after := by rfl
private def reached : MachineState := fetchMachine.noteContext thread₀ .thread
private def resolved : reached.memory.ResolvedAccess descriptor.provenance descriptor.range :=
  (prepareAccess reached.memory descriptor).toOption.get (by decide)
private def complete : CompleteCommitted descriptor :=
  (policy.oracle.answerResolved reached descriptor resolved).get (by decide)
private def observed : ByteSeq := observedBytes resolved (indeterminateByte reached descriptor)
private def site : DecodedSite before.rip observed := (DecodedSite.check before.rip observed).toOption.get (by decide)
private theorem site_noTrailing : site.rest = [] := by decide
private def fetch : FetchedSite before after :=
  { descriptor := descriptor
    run :=
      { policy := policy, operation := SomeOperation.of FetchOperation.fetch
        context := thread₀, contextKind := .thread, cause := ⟨⟨"fetch"⟩⟩
        faultAt := fun _ => .none, sequence := .single descriptor
        selected := by rfl, substeps_exact := by rfl, noFault := by rfl, ran := ran
        resolved := resolved, prepared := by rfl, complete := complete
        answerResolved := by simp [complete, reached, before], clean := by decide }
    writeData := storedBytes, indeterminate := indeterminateByte, memoryOracle := by rfl
    intent := by rfl, initialization := by rfl, ledgerEffect := by rfl, authorityEffect := by rfl
    address := by rfl, placed := ⟨0x50001000, by rfl⟩, site := site, noTrailing := site_noTrailing }
private def binding? : Option (Binding entry 0x50000000 fetch) := match check entry 0x50000000 fetch with | .ok x => some x | _ => none
theorem binding_ok : binding?.isSome := by decide
private def binding := binding?.get binding_ok
example := original_instruction binding
example := original_event binding
example : (match check entry 0x50000001 fetch with | .error .wrongRip => true | _ => false) = true := by decide
private def otherInput : Grass.Std.Logical.ByteArray := (input.set 512 0x53).set 513 0x90
private def otherChecked? : Option (CheckedImportedImage otherInput) := match checkImportedImage otherInput with | .done x _ => some x | _ => none
theorem other_checked_ok : otherChecked?.isSome := by decide
private def otherEntry? : Option (Entry otherInput) := match selectEntry (otherChecked?.get other_checked_ok) 0x1000 with | .ok x => some x | _ => none
theorem other_entry_ok : otherEntry?.isSome := by decide
private def otherEntry := otherEntry?.get other_entry_ok
example : (match check otherEntry 0x50000000 fetch with | .error .differentInstruction => true | _ => false) = true := by decide
end Grass.Tests.Disasm.FetchedEntry
