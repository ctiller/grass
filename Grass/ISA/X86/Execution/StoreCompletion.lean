import Grass.ISA.X86.Execution.Fetch
import Grass.ISA.X86.Execution.StoreCandidate
import Grass.Op.WriteCompletion

/-!
# Completed bounded immediate stores after checked fetch

This adapter joins an actual completed singleton `AccessRun` to the decoded
candidate obtained from the bytes of a `FetchedSite`. It does not define a new
x86 transition, prove reachability, cover faulting attempts, or turn a denied
ghost access into successful execution. Caller-object association remains above
the ISA layer. `descriptor.admittedFaults` and the operation facet's
restartability remain caller-selected policy data on this normal completed
branch; this adapter does not pin them as a total model of x86 store faults or
restart behavior.
-/
namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86

/-- A fetched bounded `MOV m32, imm32` candidate whose exact singleton write
subsequently completed through the generic operation stepper. -/
structure StoreCompletion (before : State) (fetched after : MachineState)
    (fetch : FetchedSite before fetched) where
  candidate : StoreCandidate.Evidence before.rip fetch.site.encoding.toBytes fetch.afterState
  candidateChecked :
    StoreCandidate.check before.rip fetch.site.encoding.toBytes fetch.afterState = .ok candidate
  descriptor : AccessDescriptor
  run : AccessRun fetched after descriptor
  writeData : MachineState → AccessDescriptor → ByteSeq
  indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte
  memoryOracle : run.policy.oracle = Oracle.ofMemory writeData indeterminate
  sameContext : run.context = fetch.run.context
  sameContextKind : run.contextKind = fetch.run.contextKind
  sameCause : run.cause = fetch.run.cause
  sameProfile : run.policy.profile = fetch.run.policy.profile
  sameRequiredFacets : run.policy.requiredFacets = fetch.run.policy.requiredFacets
  sameAuthorities : run.policy.authorities = fetch.run.policy.authorities
  sameCompatibility : run.policy.compatible = fetch.run.policy.compatible
  descriptorContext : descriptor.context = run.context
  descriptorAddress : descriptor.address = .numeric candidate.address
  space : descriptor.space = .cpuVirtual
  descriptorWidth : descriptor.range.size = candidate.width
  intent : descriptor.intent = .write
  requiredPermission : descriptor.requiredPermission = .readWrite
  alignment : descriptor.alignment = 1
  ordering : descriptor.ordering.IsPlain
  initialization : descriptor.initialization = .readsNothing
  producesInitialized : descriptor.producesInitialized = true
  observations : descriptor.observations = []
  ledgerEffect : descriptor.ledgerEffect = []
  authorityEffect : descriptor.authorityEffect = []
  placed : ∃ base, run.resolved.allocation.base = some base
  written : run.complete.committed.written = some (le32 candidate.immediate)

namespace StoreCompletion

/-- Re-decoding the fetched encoding bytes recovers exactly the encoding that
the execute-access receipt observed, with no suffix. -/
theorem candidate_encoding_exact {before fetched after fetch}
    (completion : StoreCompletion before fetched after fetch) :
    completion.candidate.site.encoding = fetch.site.encoding ∧
      completion.candidate.site.rest = [] := by
  have bytesExact :
      observedBytes fetch.run.resolved
          (fetch.indeterminate (before.machine.noteContext fetch.run.context fetch.run.contextKind)
            fetch.descriptor) = fetch.site.encoding.toBytes := by
    simpa [fetch.noTrailing] using fetch.site.bytesExact
  have decodedFetch : decodeInsn fetch.site.encoding.toBytes =
      .ok (fetch.site.encoding, []) := by
    rw [← bytesExact]
    simpa [fetch.noTrailing] using fetch.site.decoded
  have equalResults := completion.candidate.site.decoded.symm.trans decodedFetch
  have pair := Except.ok.inj equalResults
  exact ⟨congrArg Prod.fst pair, congrArg Prod.snd pair⟩

/-- The candidate encoding is the byte sequence observed by the actual fetch
run, not an independently supplied byte array. -/
theorem candidate_observed_exact {before fetched after fetch}
    (completion : StoreCompletion before fetched after fetch) :
    fetch.run.complete.committed.observed =
      some completion.candidate.site.encoding.toBytes := by
  rw [completion.candidate_encoding_exact.1]
  exact fetch.observed_exact

/-- Successful preparation and present placement connect the numeric descriptor
address to the actual allocation-relative range used by the completed run. -/
theorem placement {before fetched after fetch}
    (completion : StoreCompletion before fetched after fetch) :
    ∃ base, completion.run.resolved.allocation.base = some base ∧
      FitsAllocation base completion.run.resolved.allocation.extent.stop ∧
      addressOf base completion.descriptor.range.start = completion.candidate.address := by
  obtain ⟨base, placed⟩ := completion.placed
  obtain ⟨fits, address⟩ :=
    prepared_base_fits_and_address completion.run.prepared placed
  refine ⟨base, placed, fits, ?_⟩
  exact Address.numeric.inj (address.symm.trans completion.descriptorAddress)

@[simp] theorem descriptor_width_four {before fetched after fetch}
    (completion : StoreCompletion before fetched after fetch) :
    completion.descriptor.range.size = 4 := by
  rw [completion.descriptorWidth, StoreCandidate.Evidence.width_eq]

/-- The actual clean prepared completion commits the checked immediate bytes to
the resolved backing. This instantiates the generic write-completion law; it
does not add an x86-specific transition rule. -/
theorem memory_written {before fetched after fetch}
    (completion : StoreCompletion before fetched after fetch) :
    after.memory =
      (fetched.noteContext completion.run.context completion.run.contextKind).memory.writeResolved
        completion.run.resolved (le32 completion.candidate.immediate) true
        (completion.run.complete.committed.writtenFits _ completion.written) := by
  obtain ⟨space, found, wellFormed⟩ := completion.run.wellFormed
  have written := clean_prepared_complete_memory_eq_commitResolved completion.run.policy
    (fetched.noteContext completion.run.context completion.run.contextKind) after
    completion.descriptor completion.run.resolved completion.run.prepared
    completion.run.complete completion.run.contextKind completion.run.cause space found wellFormed
    completion.run.prepared_result completion.run.clean completion.ledgerEffect
    completion.authorityEffect
  have committed := Grass.Memory.commitResolved_of_eq_some
    (fetched.noteContext completion.run.context completion.run.contextKind).memory
    completion.descriptor completion.run.resolved completion.run.complete.committed.written
    completion.run.complete.committed.writtenFits (le32 completion.candidate.immediate)
    completion.written
  exact written.trans (by simpa only [completion.producesInitialized] using committed)

/-- The completed event follows from the actual `AccessRun`; it is not supplied
as a guessed post-state fact. -/
theorem completed_event {before fetched after fetch}
    (completion : StoreCompletion before fetched after fetch) :
    ∃ space valid,
      completion.run.policy.profile.vocabulary.addressSpaces.find?
          completion.descriptor.space = some space ∧
      MemoryEvent.ofOutcome fetched.eventSupply.fresh.1 completion.run.contextKind
          completion.run.cause space completion.descriptor
          (.completed completion.run.complete) completion.run.resolved.allocation.mapping =
        some valid ∧
      after.events = fetched.events ++ [valid] ∧
      after.eventSupply = fetched.eventSupply.fresh.2 ∧
      after.faults = fetched.faults ∧ after.violations = fetched.violations :=
  completion.run.completed_event

/-- The event derived from the actual run records the decoded immediate's four
little-endian bytes. -/
theorem completed_written_event {before fetched after fetch}
    (completion : StoreCompletion before fetched after fetch) :
    ∃ valid, after.events = fetched.events ++ [valid] ∧
      valid.event.valueWritten = some (le32 completion.candidate.immediate) ∧
      valid.event.status = .completed 0 4 := by
  obtain ⟨_space, valid, _, event, appended, _, _, _⟩ := completion.completed_event
  have fields := completedEvent_fields event
  have reads : completion.descriptor.intent.reads = false := by
    rw [completion.intent]
    rfl
  have writes : completion.descriptor.intent.writes = true := by
    rw [completion.intent]
    rfl
  have readCount : completion.run.complete.committed.readCount = 0 := by
    simp [Committed.readCount, completion.run.complete.committed.observedAbsent reads]
  have writeCount : completion.run.complete.committed.writeCount = 4 := by
    rw [completion.run.complete.writesFull writes, completion.descriptor_width_four]
  refine ⟨valid, appended, fields.2.2.2.2.2.2.2.2.trans completion.written, ?_⟩
  simpa [readCount, writeCount] using fields.2.2.2.2.2.2.1

/-- The same actual completed event exposes its range, backing mapping, and
placed first address for downstream object-boundary reasoning. -/
theorem completed_write_location {before fetched after fetch}
    (completion : StoreCompletion before fetched after fetch) :
    ∃ base valid,
      completion.run.resolved.allocation.base = some base ∧
      FitsAllocation base completion.run.resolved.allocation.extent.stop ∧
      addressOf base completion.descriptor.range.start = completion.candidate.address ∧
      after.events = fetched.events ++ [valid] ∧
      valid.event.context.id = completion.descriptor.context ∧
      valid.event.provenance = completion.descriptor.provenance ∧
      valid.event.range = completion.descriptor.range ∧
      valid.event.mapping = completion.run.resolved.allocation.mapping ∧
      valid.event.valueWritten = some (le32 completion.candidate.immediate) ∧
      valid.event.status = .completed 0 4 := by
  obtain ⟨base, placed, fits, address⟩ := completion.placement
  obtain ⟨space, valid, _, event, appended, _, _, _⟩ := completion.completed_event
  have fields := completedEvent_fields event
  have reads : completion.descriptor.intent.reads = false := by
    rw [completion.intent]
    rfl
  have writes : completion.descriptor.intent.writes = true := by
    rw [completion.intent]
    rfl
  have readCount : completion.run.complete.committed.readCount = 0 := by
    simp [Committed.readCount, completion.run.complete.committed.observedAbsent reads]
  have writeCount : completion.run.complete.committed.writeCount = 4 := by
    rw [completion.run.complete.writesFull writes, completion.descriptor_width_four]
  refine ⟨base, valid, placed, fits, address, appended, fields.2.1, fields.2.2.2.1,
    fields.2.2.2.2.1,
    fields.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.2.trans completion.written, ?_⟩
  simpa [readCount, writeCount] using fields.2.2.2.2.2.2.1

end StoreCompletion
end Grass.ISA.X86.Execution
