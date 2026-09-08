import Grass.Artifact.Binary.Realization
import Grass.Std.Logical.Order

/-!
# Overflow-free byte spans

Binary container validation needs offsets and extents in an unbounded arithmetic
domain even when both originated in fixed-width on-disk fields. This module
provides the generic span algebra; individual formats decide which spans exist.
-/

namespace Grass.Artifact.Binary

/-- A half-open byte interval `[offset, offset + length)`. -/
structure ByteSpan where
  offset : Nat
  length : Nat
deriving DecidableEq, Repr

/-- The exclusive upper bound, computed in unbounded `Nat` arithmetic. -/
def ByteSpan.endExclusive (span : ByteSpan) : Nat :=
  span.offset + span.length

/-- Whether all bytes of `span` lie inside a container of `containerLength`. -/
def ByteSpan.Fits (span : ByteSpan) (containerLength : Nat) : Prop :=
  span.endExclusive ≤ containerLength

/-- Whether empty and nonempty spans use zero and nonzero pointers respectively. -/
def ByteSpan.PointerCoherent (span : ByteSpan) : Prop :=
  span.offset = 0 ↔ span.length = 0

/-- Half-open spans are disjoint when either ends no later than the other begins. -/
def ByteSpan.Disjoint (left right : ByteSpan) : Prop :=
  left.endExclusive ≤ right.offset ∨ right.endExclusive ≤ left.offset

instance (span : ByteSpan) (containerLength : Nat) :
    Decidable (span.Fits containerLength) := by
  unfold ByteSpan.Fits
  infer_instance

instance (span : ByteSpan) : Decidable span.PointerCoherent := by
  unfold ByteSpan.PointerCoherent
  infer_instance

instance (left right : ByteSpan) : Decidable (left.Disjoint right) := by
  unfold ByteSpan.Disjoint
  infer_instance

/-- `ByteSpan.disjoint_comm` makes disjointness independent of argument order. -/
theorem ByteSpan.disjoint_comm (left right : ByteSpan) :
    left.Disjoint right ↔ right.Disjoint left := by
  simp only [ByteSpan.Disjoint, or_comm]

/-- `ByteSpan.offset_le_endExclusive` records the lower-bound half of a span. -/
theorem ByteSpan.offset_le_endExclusive (span : ByteSpan) :
    span.offset ≤ span.endExclusive := by
  simp [ByteSpan.endExclusive]

/-- `ByteSpan.Fits.offset_le` exposes the checked starting-offset bound. -/
theorem ByteSpan.Fits.offset_le {span : ByteSpan} {containerLength : Nat}
    (fits : span.Fits containerLength) : span.offset ≤ containerLength := by
  exact Nat.le_trans span.offset_le_endExclusive fits

/-- `ByteSpan.Fits.length_le` exposes the checked extent bound. -/
theorem ByteSpan.Fits.length_le {span : ByteSpan} {containerLength : Nat}
    (fits : span.Fits containerLength) : span.length ≤ containerLength := by
  unfold ByteSpan.Fits ByteSpan.endExclusive at fits
  omega

end Grass.Artifact.Binary
