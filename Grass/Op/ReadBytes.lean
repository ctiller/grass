import Grass.Op.ReadCompletion

/-! Pointwise backing observations assembled into an exact byte sequence. -/

namespace Grass.Op

open Grass.Core Grass.Memory Grass.Std.Logical

/-- `observedBytes_eq_of_resolved_bytes` assembles the exact resolved byte observations. -/
theorem observedBytes_eq_of_resolved_bytes {state : MemoryState} {d : AccessDescriptor}
    (resolved : state.ResolvedAccess d.provenance d.range) (bytes : ByteSeq)
    (width : bytes.length = d.range.size)
    (pointwise : ∀ i, (hi : i < bytes.length) →
      resolved.byteAt? (d.range.start + i) = some bytes[i])
    (indeterminate : Nat → Byte) : observedBytes resolved indeterminate = bytes := by
  apply List.ext_getElem
  · simp [observedBytes, width]
  · intro i leftBound rightBound
    simp only [observedBytes, List.getElem_map, List.getElem_range]
    rw [pointwise i rightBound]

/-- `observedBytes_eq_of_state_cells` obtains resolved observations from initialized state cells. -/
theorem observedBytes_eq_of_state_cells {state : MemoryState} {d : AccessDescriptor}
    (resolved : state.ResolvedAccess d.provenance d.range) (bytes : ByteSeq)
    (width : bytes.length = d.range.size)
    (cells : ∀ offset, d.range.Covers offset →
      state.cellAt? d.provenance.root offset =
        (bytes[offset - d.range.start]?).map (·, true))
    (indeterminate : Nat → Byte) : observedBytes resolved indeterminate = bytes := by
  apply observedBytes_eq_of_resolved_bytes resolved bytes width _ indeterminate
  intro i bound
  have covered : d.range.Covers (d.range.start + i) := by
    simp only [ByteRange.covers_def]
    omega
  unfold MemoryState.ResolvedAccess.byteAt?
  rw [resolved.cellAt?_eq_state covered, cells _ covered]
  simp [bound]

end Grass.Op
