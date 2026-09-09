import Grass.Memory.Range

/-!
# Spatial range witnesses

This module computes the first byte of a requested range that lies outside an
extent. The result is an index relative to the request, so it can be carried to
later layers without introducing allocation or machine-address assumptions.

An empty request has no byte to witness and therefore returns `none` at every
position. Consequently, the containment characterization below requires a
positive request size: `Contains` also checks the position of an empty range.
-/

namespace Grass.Memory.ByteRange

/-- The first request-relative byte index outside `extent`, if one exists.

The start byte is checked before the upper endpoint so a request wholly before
the extent reports index zero. Empty requests contain no candidate byte. -/
def firstOutsideIndex? (extent request : ByteRange) : Option Nat :=
  if request.size = 0 then none
  else if ¬ extent.Covers request.start then some 0
  else if extent.stop < request.stop then some (extent.stop - request.start)
  else none

/-- `firstOutsideIndex?_some_sound` states both obligations carried by a returned
witness: it indexes a byte of the request, and that byte is outside `extent`. -/
theorem firstOutsideIndex?_some_sound {extent request : ByteRange} {index : Nat}
    (h : firstOutsideIndex? extent request = some index) :
    index < request.size ∧ ¬ extent.Covers (request.start + index) := by
  unfold firstOutsideIndex? at h
  split at h
  · simp at h
  split at h
  · simp only [Option.some.injEq] at h
    subst index
    constructor
    · omega
    · simpa using ‹¬ extent.Covers request.start›
  split at h
  · simp only [Option.some.injEq] at h
    subst index
    have hstart : extent.Covers request.start := by simp_all
    constructor
    · rw [covers_def] at hstart
      unfold stop at *
      omega
    · rw [covers_def] at hstart ⊢
      unfold stop at *
      omega
  · simp at h

/-- `firstOutsideIndex?` returns no witness exactly when every byte indexed by the
request is covered by `extent`. This remains true for empty requests. -/
theorem firstOutsideIndex?_eq_none_iff (extent request : ByteRange) :
    firstOutsideIndex? extent request = none ↔
      ∀ index, index < request.size → extent.Covers (request.start + index) := by
  constructor
  · intro hnone index hindex
    unfold firstOutsideIndex? at hnone
    split at hnone
    · omega
    split at hnone
    · simp at hnone
    split at hnone
    · simp at hnone
    · have hstart : extent.Covers request.start := by simp_all
      rw [covers_def] at hstart ⊢
      unfold stop at *
      omega
  · intro hall
    cases hresult : firstOutsideIndex? extent request with
    | none => rfl
    | some index =>
        exfalso
        exact absurd (hall index (firstOutsideIndex?_some_sound hresult).1)
          (firstOutsideIndex?_some_sound hresult).2

/-- For a positive-size request, absence of an outside-byte witness is equivalent
to extent containment. The positivity premise is necessary because an empty
request has no witness even when its position lies outside `extent`. -/
theorem firstOutsideIndex?_eq_none_iff_contains {extent request : ByteRange}
    (hpositive : 0 < request.size) :
    firstOutsideIndex? extent request = none ↔ extent.Contains request := by
  rw [firstOutsideIndex?_eq_none_iff]
  constructor
  · intro hall
    constructor
    · exact (hall 0 hpositive).1
    · have hlast := hall (request.size - 1) (by omega)
      rw [covers_def] at hlast
      change request.start + request.size ≤ extent.start + extent.size
      omega
  · intro hcontains index hindex
    apply hcontains.covers
    rw [covers_def]
    constructor <;> omega

end Grass.Memory.ByteRange
