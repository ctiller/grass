import Grass.Platform.BareMetal.X86BootFetch
import Grass.Platform.BareMetal.AArch64BootFetch
import Grass.ISA.X86.BasicInstructions

/-!
# Operational bare-metal boot fetch controls

This fixture admits one supplied fresh machine snapshot, performs real checked
execute reads through the shared memory oracle, and passes the resulting bytes
to the bounded x86 and AArch64 adapters.  The physical map is fixture input; the
examples make no hardware-safety, firmware-provenance, or native-execution claim.
-/

namespace Tests.Platform.BareMetal.BootFetch

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.BareMetal
open Grass.Platform.BareMetal.BootMemory

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def allocs : FreshSupply AllocTag := .initial
private def stores : FreshSupply StorageTag := .initial
private def epochs : FreshSupply EpochTag := .initial
private def contexts : FreshSupply ContextTag := .initial

private def code : AllocId := allocs.fresh.1
private def codeStore : StorageId := stores.fresh.1
private def epoch : EpochId := epochs.fresh.1
private def core : ContextId := contexts.fresh.1

private def x86Bytes : ByteSeq := [0x48, 0x89, 0xC0]
private def aarch64Bytes : ByteSeq := [0x1F, 0x20, 0x03, 0xD5]

private def codeBytes : ByteStore :=
  ((ByteStore.empty.write 0 (List.replicate 16 0) true).write 0 x86Bytes true).write
    8 aarch64Bytes true

private def codeBacking : BackingRecord :=
  { capacity := 16, bytes := codeBytes }

private def codeRecord : AllocationRecord :=
  { extent := ⟨0, 16⟩
    epoch := epoch
    space := .cpuPhysical
    source := .imageMapping
    owners := [core]
    permission := .readExecute
    live := true
    backing := codeStore
    origin := 0
    base := some 0x1000 }

private def physicalMap : PhysicalMap :=
  { ram := [⟨0x1000, 0x100⟩]
    devices := [⟨0x2000, 0x100⟩] }

private def memoryOf? (record : AllocationRecord) (backing : BackingRecord) :
    Option MemoryState := do
  let installed ← MemoryState.empty.installBacking? codeStore backing
  installed.allocate? code record

private def memoryOf (record : AllocationRecord) (backing : BackingRecord) : MemoryState :=
  (memoryOf? record backing).getD .empty

private def memory : MemoryState := memoryOf codeRecord codeBacking
private def before : MachineState := MachineState.initial memory

theorem memory_uses_public_doors : (memoryOf? codeRecord codeBacking).isSome := by decide

theorem snapshot_is_admitted : (admit? physicalMap core before).isSome := by decide

private def admission : Admission physicalMap core before :=
  (admit? physicalMap core before).get snapshot_is_admitted

/-! ## Operational profile -/

private def vocabulary : AdmittedVocabulary :=
  { addressSpaces := ⟨[Grass.Platform.BareMetal.BootFetch.ramSpace]⟩
    faultClasses := ⟨[]⟩
    allocationSources := ⟨[.imageMapping]⟩
    provenanceStepKinds := ⟨[]⟩
    auditViolationClasses := ⟨AuditViolationClass.emittedByTransition⟩
    obligationKinds := ⟨[]⟩
    orderingModes := ⟨[]⟩
    orderingScopes := ⟨[]⟩
    contextKinds := ⟨[.thread]⟩
    initializationJustifications := ⟨[]⟩
    atomicityJustifications := ⟨[]⟩
    faultVisibilityRules := ⟨[]⟩
    grantKinds := ⟨[]⟩
    protocols := ⟨[]⟩ }

private def operationProfile : OperationalProfile :=
  { id := ⟨"baremetal.boot.fetch.fixture"⟩
    vocabularyVersion := 1
    vocabulary := vocabulary }

private def operationPolicy : StepPolicy :=
  { profile := operationProfile
    requiredFacets := [.memoryEffects, .faults, .restartability, .ordering]
    oracle := .ofMemory (fun _ _ => []) (fun _ _ _ => 0)
    authorities := []
    violationClassesDeclared := by decide
    vocabularyWellFormed := by decide }

private def policy : Grass.Platform.BareMetal.BootFetch.Policy :=
  { operation := operationPolicy
    ramDeclared := rfl
    faults := []
    cause := ⟨⟨"baremetal-boot-fetch"⟩⟩ }

/-! ## Successful x86 fetch and decode -/

private def x86Range : ByteRange := ⟨0, x86Bytes.length⟩
private theorem x86_entry_exists : (entry? admission code x86Range).isSome := by decide
private def x86Entry : Entry admission code x86Range :=
  (entry? admission code x86Range).get x86_entry_exists

private theorem x86_fetch_succeeds :
    (Grass.Platform.BareMetal.BootFetch.fetch policy x86Entry).toOption.isSome := by decide

private def x86Read : Grass.Platform.BareMetal.BootFetch.Success policy x86Entry :=
  (Grass.Platform.BareMetal.BootFetch.fetch policy x86Entry).toOption.get x86_fetch_succeeds

theorem x86_observes_exact_backing_bytes : x86Read.bytes = x86Bytes := by decide

theorem x86_read_appends_one_completed_event : x86Read.after.events.length = 1 := by
  obtain ⟨_, valid, _, _, appended, _, _, _⟩ := x86Read.run.completed_event
  rw [appended]
  simp [Admission.machine, before, MachineState.initial, MachineState.noteContext]

theorem x86_execute_read_preserves_memory : x86Read.after.memory = before.memory :=
  x86Read.storage_frame.1

theorem x86_completed_event_records_exact_read :
    ∃ valid, x86Read.after.events = [valid] ∧
      valid.event.valueRead = some x86Bytes ∧
      valid.event.status = .completed 3 0 := by
  obtain ⟨_, valid, _, event, appended, _, _, _⟩ := x86Read.run.completed_event
  rcases completedEvent_fields event with
    ⟨_, _, _, _, _, _, status, valueRead, _⟩
  have readCount := x86Read.run.complete.readsFull (by rfl)
  have writtenAbsent := x86Read.run.complete.committed.writtenAbsent (by rfl)
  refine ⟨valid, ?_, ?_, ?_⟩
  · simpa [Admission.machine, before, MachineState.initial, MachineState.noteContext]
      using appended
  · calc
      valid.event.valueRead = x86Read.run.complete.committed.observed := valueRead
      _ = some x86Read.bytes := x86Read.observed_exact
      _ = some x86Bytes := congrArg some x86_observes_exact_backing_bytes
  · calc
      valid.event.status = .completed x86Read.run.complete.committed.readCount
          x86Read.run.complete.committed.writeCount := status
      _ = .completed 3 0 := by
        rw [readCount]
        simp [Grass.Platform.BareMetal.BootFetch.descriptor, x86Range, x86Bytes,
          Committed.writeCount, writtenAbsent]

private theorem x86_decodes :
    (Grass.Platform.BareMetal.X86BootFetch.decode x86Read).toOption.isSome := by decide

private def x86Site : Grass.ISA.X86.Execution.DecodedSite x86Entry.pc x86Read.bytes :=
  (Grass.Platform.BareMetal.X86BootFetch.decode x86Read).toOption.get x86_decodes

theorem x86_decoder_selects_the_existing_mov :
    x86Site.encoding = Grass.ISA.X86.BasicInstructions.movRegReg .w64 .rax .rax ∧
      x86Site.rest = [] := by decide

/-! ## Successful aligned AArch64-width read -/

private def aarch64Range : ByteRange := ⟨8, 4⟩
private theorem aarch64_entry_exists :
    (entry? admission code aarch64Range).isSome := by decide
private def aarch64Entry : Entry admission code aarch64Range :=
  (entry? admission code aarch64Range).get aarch64_entry_exists

private theorem aarch64_fetch_succeeds :
    (Grass.Platform.BareMetal.AArch64BootFetch.fetchWord policy aarch64Entry).toOption.isSome :=
  by decide

private def aarch64Word :
    Grass.Platform.BareMetal.AArch64BootFetch.Word policy aarch64Entry :=
  (Grass.Platform.BareMetal.AArch64BootFetch.fetchWord policy aarch64Entry).toOption.get
    aarch64_fetch_succeeds

theorem aarch64_observes_exact_four_backing_bytes :
    aarch64Word.read.bytes = aarch64Bytes := by decide

theorem aarch64_read_appends_one_completed_event :
    aarch64Word.read.after.events.length = 1 := by
  obtain ⟨_, valid, _, _, appended, _, _, _⟩ := aarch64Word.read.run.completed_event
  rw [appended]
  simp [Admission.machine, before, MachineState.initial, MachineState.noteContext]

theorem aarch64_execute_read_preserves_memory :
    aarch64Word.read.after.memory = before.memory :=
  aarch64Word.read.storage_frame.1

theorem aarch64_completed_event_records_exact_read :
    ∃ valid, aarch64Word.read.after.events = [valid] ∧
      valid.event.valueRead = some aarch64Bytes ∧
      valid.event.status = .completed 4 0 := by
  obtain ⟨_, valid, _, event, appended, _, _, _⟩ :=
    aarch64Word.read.run.completed_event
  rcases completedEvent_fields event with
    ⟨_, _, _, _, _, _, status, valueRead, _⟩
  have readCount := aarch64Word.read.run.complete.readsFull (by rfl)
  have writtenAbsent := aarch64Word.read.run.complete.committed.writtenAbsent (by rfl)
  refine ⟨valid, ?_, ?_, ?_⟩
  · simpa [Admission.machine, before, MachineState.initial, MachineState.noteContext]
      using appended
  · calc
      valid.event.valueRead = aarch64Word.read.run.complete.committed.observed := valueRead
      _ = some aarch64Word.read.bytes := aarch64Word.read.observed_exact
      _ = some aarch64Bytes := congrArg some aarch64_observes_exact_four_backing_bytes
  · calc
      valid.event.status = .completed aarch64Word.read.run.complete.committed.readCount
          aarch64Word.read.run.complete.committed.writeCount := status
      _ = .completed 4 0 := by
        rw [readCount]
        simp [Grass.Platform.BareMetal.BootFetch.descriptor, aarch64Range,
          Committed.writeCount, writtenAbsent]

/-! ## Entry and AArch64 shape refusals -/

private def nonExecutableRecord : AllocationRecord :=
  { codeRecord with permission := .readOnly }
private def nonExecutableMemory : MemoryState := memoryOf nonExecutableRecord codeBacking
private def nonExecutableBefore : MachineState := MachineState.initial nonExecutableMemory
private theorem nonExecutable_admitted :
    (admit? physicalMap core nonExecutableBefore).isSome := by decide
private def nonExecutableAdmission : Admission physicalMap core nonExecutableBefore :=
  (admit? physicalMap core nonExecutableBefore).get nonExecutable_admitted

private def uninitializedBacking : BackingRecord := { capacity := 16, bytes := .empty }
private def uninitializedMemory : MemoryState := memoryOf codeRecord uninitializedBacking
private def uninitializedBefore : MachineState := MachineState.initial uninitializedMemory
private theorem uninitialized_admitted :
    (admit? physicalMap core uninitializedBefore).isSome := by decide
private def uninitializedAdmission : Admission physicalMap core uninitializedBefore :=
  (admit? physicalMap core uninitializedBefore).get uninitialized_admitted

theorem nonexecutable_and_uninitialized_entries_are_rejected :
    entry? nonExecutableAdmission code x86Range = none ∧
      entry? uninitializedAdmission code x86Range = none := by decide

private def misalignedRange : ByteRange := ⟨1, 4⟩
private theorem misaligned_entry_exists :
    (entry? admission code misalignedRange).isSome := by decide
private def misalignedEntry : Entry admission code misalignedRange :=
  (entry? admission code misalignedRange).get misaligned_entry_exists

theorem aarch64_rejects_wrong_width :
    Grass.Platform.BareMetal.AArch64BootFetch.fetchWord policy x86Entry =
      .error .width := by
  rfl

theorem aarch64_rejects_misaligned_pc :
    Grass.Platform.BareMetal.AArch64BootFetch.fetchWord policy misalignedEntry =
      .error .alignment := by
  rfl

end Tests.Platform.BareMetal.BootFetch
