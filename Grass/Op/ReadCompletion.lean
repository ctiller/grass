import Grass.Op.Step

/-!
# Read-only completion facts

These lemmas expose two consequences of the generic checked transition.  A
read-only prepared access cannot change the allocation or backing tables, and
the memory-backed oracle reports the bytes observed through the exact resolved
access it was given.
-/

namespace Grass.Op

open Grass.Core Grass.Memory Grass.Std.Logical

/-- A complete read-only answer carries a full-width observed byte sequence and
no committed write bytes. -/
theorem CompleteCommitted.readOnly_bytes {d : AccessDescriptor}
    (complete : CompleteCommitted d) (reads : d.intent.reads = true)
    (writes : d.intent.writes = false) :
    ∃ bytes, complete.committed.observed = some bytes ∧
      bytes.length = d.range.size ∧ complete.committed.writeCount = 0 := by
  obtain ⟨bytes, observed⟩ := Option.isSome_iff_exists.mp
    (complete.committed.observedPresent reads)
  refine ⟨bytes, observed, ?_, ?_⟩
  · have full := complete.readsFull reads
    simpa [Committed.readCount, observed] using full
  · simp [Committed.writeCount, complete.committed.writtenAbsent writes]

/-- Preparation of an access that demands initialized bytes certifies that the
exact resolved backing span is initialized. -/
theorem rangeInitialized_of_prepareAccess_allBytesInitialized
    {state : MemoryState} {d : AccessDescriptor}
    {resolved : state.ResolvedAccess d.provenance d.range}
    (prepared : prepareAccess state d = .ok resolved)
    (demand : d.initialization = .allBytesInitialized) :
    resolved.RangeInitialized := by
  unfold prepareAccess at prepared
  repeat' split at prepared
  all_goals try contradiction
  rename_i initializationAllowed
  cases Except.ok.inj prepared
  by_cases initialized : resolved.RangeInitialized
  · exact initialized
  · exact (initializationAllowed ⟨demand, initialized⟩).elim

/-- Once the resolved range is initialized, `observedBytes` is independent of
the fallback supplied for missing backing cells. A present cell whose
initialization bit is false still supplies its stored byte. -/
theorem observedBytes_eq_of_rangeInitialized
    {state : MemoryState} {d : AccessDescriptor}
    (resolved : state.ResolvedAccess d.provenance d.range)
    (initialized : resolved.RangeInitialized) (left right : Nat → Byte) :
    observedBytes resolved left = observedBytes resolved right := by
  unfold observedBytes
  apply List.map_congr_left
  intro i member
  have indexLt : i < d.range.size := List.mem_range.mp member
  have covered : d.range.Covers (d.range.start + i) := by
    simp [ByteRange.covers_def, indexLt]
  have backingCovered : resolved.span.range.Covers
      (resolved.allocation.origin + (d.range.start + i)) :=
    (Coordinates.Mapping.span_covers resolved.allocation.mapping d.range
      (d.range.start + i)).2 covered
  have initializedAt := initialized _ backingCovered
  unfold MemoryState.ResolvedAccess.byteAt? MemoryState.ResolvedAccess.cellAt?
  rw [if_pos covered]
  unfold ByteStore.InitializedAt at initializedAt
  cases cell : resolved.backing.cellAt?
      (resolved.allocation.origin + (d.range.start + i)) with
  | none =>
      unfold BackingRecord.cellAt? at cell
      simp [cell] at initializedAt
  | some value => simp

private theorem outcome_written_none_of_readOnly {d : AccessDescriptor}
    (outcome : AccessOutcome d) (readOnly : d.intent.writes = false) :
    outcome.committed?.bind Committed.written = Option.none := by
  cases outcome with
  | completed complete =>
      simp only [AccessOutcome.committed?, Option.bind_some]
      exact complete.committed.writtenAbsent readOnly
  | faulted fault committed =>
      simp only [AccessOutcome.committed?, Option.bind_some]
      exact committed.writtenAbsent readOnly
  | denied violation => rfl

/-- A read-only prepared access preserves both storage tables on every branch,
including refusal branches. -/
theorem performPreparedAccess_readOnly_storage
    (policy : StepPolicy) (state : MachineState) (d : AccessDescriptor)
    (resolved : state.memory.ResolvedAccess d.provenance d.range)
    (prepared : prepareAccess state.memory d = .ok resolved)
    (outcome : AccessOutcome d) (contextKind : ContextKind) (cause : EventCause)
    (readOnly : d.intent.writes = false) :
    (performPreparedAccess policy state d resolved prepared outcome contextKind cause).memory.allocations =
      state.memory.allocations ∧
    (performPreparedAccess policy state d resolved prepared outcome contextKind cause).memory.backings =
      state.memory.backings := by
  unfold performPreparedAccess
  repeat' split
  all_goals first
    | exact ⟨rfl, rfl⟩
    | (rename_i lent authorityApplied
       have writtenAbsent := outcome_written_none_of_readOnly outcome readOnly
       rw [Grass.Memory.commitResolved_of_eq_none _ _ _ _ _ writtenAbsent]
       exact ⟨MemoryState.allocations_applyAuthorityEffect? authorityApplied,
         MemoryState.backings_applyAuthorityEffect? authorityApplied⟩)

/-- A read-only prepared access preserves the complete allocation table on
every branch, including refusal branches. -/
theorem performPreparedAccess_readOnly_allocations
    (policy : StepPolicy) (state : MachineState) (d : AccessDescriptor)
    (resolved : state.memory.ResolvedAccess d.provenance d.range)
    (prepared : prepareAccess state.memory d = .ok resolved)
    (outcome : AccessOutcome d) (contextKind : ContextKind) (cause : EventCause)
    (readOnly : d.intent.writes = false) :
    (performPreparedAccess policy state d resolved prepared outcome contextKind cause).memory.allocations =
      state.memory.allocations :=
  (performPreparedAccess_readOnly_storage policy state d resolved prepared outcome
    contextKind cause readOnly).1

/-- A read-only prepared access preserves the complete backing table on every
branch, including refusal branches. -/
theorem performPreparedAccess_readOnly_backings
    (policy : StepPolicy) (state : MachineState) (d : AccessDescriptor)
    (resolved : state.memory.ResolvedAccess d.provenance d.range)
    (prepared : prepareAccess state.memory d = .ok resolved)
    (outcome : AccessOutcome d) (contextKind : ContextKind) (cause : EventCause)
    (readOnly : d.intent.writes = false) :
    (performPreparedAccess policy state d resolved prepared outcome contextKind cause).memory.backings =
      state.memory.backings := by
  exact (performPreparedAccess_readOnly_storage policy state d resolved prepared outcome
    contextKind cause readOnly).2

/-- A successful answer from `Oracle.ofMemory` records exactly the bytes read
through the supplied resolved access. -/
theorem Oracle.ofMemory_observed_of_answerResolved
    (writeData : MachineState → AccessDescriptor → ByteSeq)
    (indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte)
    (state : MachineState) (d : AccessDescriptor)
    (resolved : state.memory.ResolvedAccess d.provenance d.range)
    (complete : CompleteCommitted d)
    (answer : (Oracle.ofMemory writeData indeterminate).answerResolved state d resolved =
      some complete)
    (reads : d.intent.reads = true) :
    complete.committed.observed =
      some (observedBytes resolved (indeterminate state d)) := by
  simp only [Oracle.ofMemory] at answer
  split at answer
  · injection answer with same
    subst complete
    simp
  · contradiction

end Grass.Op
