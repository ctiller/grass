import Grass.Memory.Apply

/-!
# Backing resolution boundaries

These controls use only public construction doors for executable states. They
verify that missing and undersized backings are rejected before such a state can
be constructed; the sealed-state malformed branches remain covered by the
resolver's definition and proofs rather than by an unconstructible fixture.
-/

namespace Tests.Memory.BackingResolution

open Grass.Core Grass.Memory Grass.Std.Logical

private def allocs : FreshSupply AllocTag := .initial
private def backings : FreshSupply StorageTag := .initial
private def contexts : FreshSupply ContextTag := .initial

private def primaryAlloc : AllocId := allocs.fresh.1
private def secondAlloc : AllocId := allocs.fresh.2.fresh.1
private def thirdAlloc : AllocId := allocs.fresh.2.fresh.2.fresh.1
private def primaryBacking : StorageId := backings.fresh.1
private def alternateBacking : StorageId := backings.fresh.2.fresh.1
private def owner : ContextId := contexts.fresh.1
private def epoch : EpochId := (FreshSupply.initial (Tag := EpochTag)).fresh.1
private def nextEpoch : EpochId := (FreshSupply.initial (Tag := EpochTag)).fresh.2.fresh.1

/-- A nonzero local extent and a nonzero backing origin make both coordinate
translations observable. Its shifted view is `[216, 266)`. -/
private def primaryRecord : AllocationRecord :=
  { extent := ⟨200, 50⟩, epoch := epoch, space := .cpuVirtual
    source := .virtualAlloc, owners := [owner], permission := .readWrite, live := true
    backing := primaryBacking, origin := 16, base := none }

private def backingRecord : BackingRecord := { capacity := 266, bytes := .empty }

private def provenance : Provenance :=
  { space := .cpuVirtual, root := primaryAlloc, epoch := epoch
    source := .virtualAlloc, rootExtent := ⟨200, 50⟩, path := [] }

private def state? : Option MemoryState := do
  let state ← MemoryState.empty.installBacking? primaryBacking backingRecord
  let state ← state.installBacking? alternateBacking backingRecord
  state.allocate? primaryAlloc primaryRecord

private def state : MemoryState := state?.getD .empty

/-- The supported one-view state is built through both checked doors. -/
theorem supported_setup_succeeds : state?.isSome := by decide

/-- The stored origin, rather than a caller-supplied translation, determines the
resolved backing span. -/
theorem shifted_nonzero_view_resolves_to_its_backing_span :
    (state.resolveAccess? provenance ⟨220, 8⟩).map MemoryState.ResolvedAccess.span =
      .ok ⟨primaryBacking, ⟨236, 8⟩⟩ := by rfl

/-- Resolve the exact local request before writing it. There is no fallback state
on a failed resolution. -/
private def writeAt220? : Except MemoryState.ResolveFailure MemoryState := do
  let access ← state.resolveAccess? provenance ⟨220, 8⟩
  pure (state.writeResolved access [0xA5] true (by
    change 1 ≤ 8
    decide))

/-- The one-byte write lands at backing offset `220 + 16 = 236`; checked local
observation uses the same translation. Treating 220 as a backing offset, or 236
as a local offset, observes no byte. -/
private def writeAt220Observations : Except MemoryState.ResolveFailure
    (Option (Byte × Bool) × Option (Byte × Bool) × Option (Byte × Bool) × Option (Byte × Bool)) :=
  writeAt220?.map fun next =>
    (next.cellAtBacking? ⟨primaryBacking, ⟨236, 1⟩⟩ 236,
     next.cellAt? primaryAlloc 220,
     next.cellAtBacking? ⟨primaryBacking, ⟨220, 1⟩⟩ 220,
     next.cellAt? primaryAlloc 236)

theorem checked_write_uses_the_captured_nonzero_origin :
    writeAt220Observations = .ok (some (0xA5, true), some (0xA5, true), none, none) := by rfl

private def staleProvenance : Provenance := { provenance with epoch := nextEpoch }
private def wrongSourceProvenance : Provenance :=
  { provenance with source := .processHeap }

private def resolutionFailure {α : Type} : Except MemoryState.ResolveFailure α →
    Option MemoryState.ResolveFailure
  | .error failure => some failure
  | .ok _ => none

theorem stale_epoch_is_a_precise_resolution_failure :
    resolutionFailure (state.resolveAccess? staleProvenance ⟨220, 8⟩) = some .staleEpoch := by
  decide

theorem source_mismatch_is_a_precise_resolution_failure :
    resolutionFailure (state.resolveAccess? wrongSourceProvenance ⟨220, 8⟩) =
      some .provenanceSourceMismatch := by decide

theorem out_of_view_range_is_a_precise_resolution_failure :
    resolutionFailure (state.resolveAccess? provenance ⟨249, 2⟩) =
      some .rangeOutsideProvenance := by decide

/-- Tearing down a view retains the backing record but makes checked local reads
and resolver access fail closed. -/
private def deadState? : Option MemoryState :=
  state.allocate? primaryAlloc { primaryRecord with live := false }

private def deadState : MemoryState := deadState?.getD state

theorem dead_view_setup_succeeds : deadState?.isSome := by decide

theorem dead_view_cannot_be_read_through_its_retained_backing :
    deadState.backingCapacity? primaryBacking = some 266 ∧
    deadState.cellAt? primaryAlloc 220 = none ∧
    resolutionFailure (deadState.resolveAccess? provenance ⟨220, 8⟩) =
      some .deadProvenance := by decide

/-- Existing backing identities are immutable through the installation door. -/
theorem installation_cannot_overwrite_an_existing_identity :
    (MemoryState.empty.installBacking? primaryBacking backingRecord).bind
      (fun state => state.installBacking? primaryBacking
        { capacity := 999, bytes := ByteStore.empty.write 0 [0xFF] true }) = none := by
  decide

/-- A live allocation cannot be remapped even when the candidate also changes its
epoch. Reuse first requires teardown. -/
theorem live_mapping_cannot_change_with_a_new_epoch :
    state.allocate? primaryAlloc
      { primaryRecord with epoch := nextEpoch, backing := alternateBacking, origin := 0 } = none := by
  decide

/-! A missing backing cannot enter a public state: `allocate?` refuses the record
before it becomes observable. -/
theorem missing_backing_is_rejected_by_allocation :
    MemoryState.empty.allocate? primaryAlloc primaryRecord = none := by
  decide

/-! The same checked door rejects a view whose nonzero shifted extent cannot fit
the installed backing capacity. -/
theorem shifted_view_must_fit_its_backing_capacity :
    (MemoryState.empty.installBacking? primaryBacking
      { capacity := 265, bytes := .empty }).bind
        (fun state => state.allocate? primaryAlloc primaryRecord) = none := by
  decide

/-- A translated second live view over the first view's backing is rejected before
it can become an executable dedicated state. The shifted origin still fits this
backing independently, so rejection is about sharing rather than bounds. -/
private def sharedRecord : AllocationRecord :=
  { primaryRecord with backing := primaryBacking, origin := 8 }

theorem shared_live_layout_is_rejected_by_allocation :
    state.allocate? secondAlloc sharedRecord = none := by
  decide

/-- The same shifted view is accepted when it names the independently installed
backing. This is the dedicated-layout control for the preceding refusal. -/
private def independentShiftedRecord : AllocationRecord :=
  { primaryRecord with backing := alternateBacking, origin := 8 }

theorem independently_backed_shifted_view_is_admitted :
    (state.allocate? thirdAlloc independentShiftedRecord).isSome := by
  decide

end Tests.Memory.BackingResolution
