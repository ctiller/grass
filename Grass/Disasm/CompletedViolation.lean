import Grass.Disasm.FetchedEntry
import Grass.Disasm.Spatial
import Grass.ISA.X86.Execution.StoreCompletion

/-! A completed model write outside a separately declared caller object.
The imported instruction, fetch, and write retain one continuous state history.
The object interpretation is supplied by the caller contract; numeric equality
does not recover source-language provenance. Root-allocation completion does not
discharge the narrower object's bounds. No OS-loader or model-adequacy claim is
made by this composition. -/
namespace Grass.Disasm.CompletedViolation

open Grass.Std.Logical Grass.Memory Grass.Memory.SpatialAccess Grass.ISA.X86.Execution

private def transportObject {first second : MemoryState} (same : first = second) {provenance}
    (object : PlacedObject first provenance) : PlacedObject second provenance := same ▸ object

private theorem transportObject_base {first second : MemoryState} (same : first = second) {provenance}
    (object : PlacedObject first provenance) : (transportObject same object).base = object.base := by
  cases same
  rfl

def fetchedObject {before fetched} (fetch : FetchedSite before fetched) {provenance}
    (object : PlacedObject before.machine.memory provenance) :
    PlacedObject fetched.memory provenance := transportObject fetch.state_frame.1.symm object

/-- The chosen object's interpretation is a declared input. This witness checks
its pointer placement and exhibits an excluded byte of an actual completed write. -/
structure Witness {before fetched after fetch}
    (completion : StoreCompletion before fetched after fetch) {provenance}
    (object : PlacedObject before.machine.memory provenance) where
  pointerAtStart : before.gpr completion.candidate.base =
    addressOf object.base provenance.extent.start
  index : Nat
  outside : OutsideByte (fetchedObject fetch object) (Spatial.footprint completion.candidate) index

inductive Error where | pointerDoesNotStartAtObject
deriving DecidableEq, Repr

/-- Search only the spatial witness after the actual completion and caller
object have been supplied. `none` states no excluded byte, not binary safety. -/
def check {before fetched after fetch}
    (completion : StoreCompletion before fetched after fetch) {provenance}
    (object : PlacedObject before.machine.memory provenance) :
    Except Error (Option (Witness completion object)) :=
  if pointer : before.gpr completion.candidate.base = addressOf object.base provenance.extent.start then
    match excluded : outsideIndex? (fetchedObject fetch object) (Spatial.footprint completion.candidate) with
    | none => .ok none
    | some index => .ok (some ⟨pointer, index,
        outsideIndex?_sound (fetchedObject fetch object) (Spatial.footprint completion.candidate) excluded⟩)
  else .error .pointerDoesNotStartAtObject

/-- The same event sequence contains the original imported fetch and a fully
completed write whose placed byte is outside the declared caller object. -/
theorem original_fetch_and_outside_write {input entry imageBase before fetched after fetch}
    (binding : @FetchedEntry.Binding input entry imageBase before fetched fetch)
    (completion : StoreCompletion before fetched after fetch) {provenance}
    (object : PlacedObject before.machine.memory provenance) (witness : Witness completion object) :
    ∃ base fetchEvent writeEvent,
      after.events = before.machine.events ++ [fetchEvent, writeEvent] ∧
      fetchEvent.event.valueRead = some (entry.bytes.take binding.decoded.encoding.size) ∧
      writeEvent.event.range = completion.descriptor.range ∧
      writeEvent.event.mapping = completion.run.resolved.allocation.mapping ∧
      writeEvent.event.valueWritten = some (Grass.ISA.X86.le32 completion.candidate.immediate) ∧
      writeEvent.event.status = .completed 0 4 ∧
      witness.index < writeEvent.event.range.size ∧
      completion.run.resolved.allocation.base = some base ∧
      ∀ offset, provenance.extent.Covers offset →
        addressOf base (writeEvent.event.range.start + witness.index) ≠
          addressOf object.base offset := by
  obtain ⟨fetchEvent, fetchAppend, fetchRead, _⟩ := FetchedEntry.original_event binding
  obtain ⟨base, writeEvent, placed, _, firstAddress, writeAppend, _, _, rangeEq,
    mappingEq, payloadEq, statusEq⟩ := completion.completed_write_location
  have addressEq : addressOf base (writeEvent.event.range.start + witness.index) =
      addressOf completion.candidate.address witness.index := by
    rw [rangeEq, ← firstAddress]
    simp [addressOf, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨base, fetchEvent, writeEvent, ?_, fetchRead, rangeEq, mappingEq, payloadEq,
    statusEq, ?_, placed, ?_⟩
  · rw [writeAppend, fetchAppend]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · rw [rangeEq, completion.descriptorWidth]
    exact witness.outside.touched
  · intro offset covered
    rw [addressEq]
    have excluded := witness.outside.outside offset covered
    simpa only [fetchedObject, transportObject_base, Spatial.footprint,
      StoreAttempt.Evidence.address] using excluded

end Grass.Disasm.CompletedViolation
