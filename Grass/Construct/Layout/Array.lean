import Grass.Construct.Layout.Core

/-!
# Ordinary array layouts

An array layout selects one element representation, a positive element count,
and an explicit stride. The stride may contain tail padding but is checked to
fit and align every element. Flexible tails and zero-length format extensions
use separate profile-specific constructors.
-/

namespace Grass.Construct.Layout

open Grass.Memory

/-- Selected layout of one ordinary fixed-length array. -/
structure ArrayLayout (profile : LayoutProfile) where
  element : ObjectRepr profile
  count : Nat
  stride : Nat
deriving Repr, DecidableEq

namespace ArrayLayout

variable {profile : LayoutProfile}

/-- Total byte extent, including any tail padding in the final stride. -/
def size (layout : ArrayLayout profile) : Nat := layout.count * layout.stride

/-- Alignment of the aggregate is the selected element alignment. -/
def alignment (layout : ArrayLayout profile) : Nat := layout.element.alignment

/-- Checked byte range for one element occurrence. -/
def elementRange? (layout : ArrayLayout profile) (index : Nat) : Option ByteRange :=
  if index < layout.count then
    some ⟨index * layout.stride, layout.element.size⟩
  else
    none

/-- Executable checker for an ordinary fixed-length array. -/
def wellFormed (layout : ArrayLayout profile) : Bool :=
  layout.element.wellFormed &&
  decide (0 < layout.element.size) &&
  decide (0 < layout.count) &&
  decide (layout.element.size ≤ layout.stride) &&
  decide (IsAligned layout.stride layout.element.alignment)

def WellFormed (layout : ArrayLayout profile) : Prop := layout.wellFormed = true

instance (layout : ArrayLayout profile) : Decidable layout.WellFormed :=
  inferInstanceAs (Decidable (layout.wellFormed = true))

@[simp] theorem wellFormed_iff (layout : ArrayLayout profile) :
    layout.WellFormed ↔
      ((((layout.element.WellFormed ∧ 0 < layout.element.size) ∧
          0 < layout.count) ∧
          layout.element.size ≤ layout.stride) ∧
        IsAligned layout.stride layout.element.alignment) := by
  simp [WellFormed, wellFormed, ObjectRepr.WellFormed]

theorem elementWellFormed_of_wellFormed (layout : ArrayLayout profile)
    (h : layout.WellFormed) : layout.element.WellFormed :=
  (wellFormed_iff layout).mp h |>.1.1.1.1

theorem elementSizePositive_of_wellFormed (layout : ArrayLayout profile)
    (h : layout.WellFormed) : 0 < layout.element.size :=
  (wellFormed_iff layout).mp h |>.1.1.1.2

theorem countPositive_of_wellFormed (layout : ArrayLayout profile)
    (h : layout.WellFormed) : 0 < layout.count :=
  (wellFormed_iff layout).mp h |>.1.1.2

theorem elementFitsStride_of_wellFormed (layout : ArrayLayout profile)
    (h : layout.WellFormed) : layout.element.size ≤ layout.stride :=
  (wellFormed_iff layout).mp h |>.1.2

theorem strideAligned_of_wellFormed (layout : ArrayLayout profile)
    (h : layout.WellFormed) :
    IsAligned layout.stride layout.element.alignment :=
  (wellFormed_iff layout).mp h |>.2

@[simp] theorem elementRange?_isSome_iff (layout : ArrayLayout profile)
    (index : Nat) :
    (layout.elementRange? index).isSome = true ↔ index < layout.count := by
  simp [elementRange?]

/-- Every in-bounds array index has one concrete selected byte range. -/
theorem rangeForIndex (layout : ArrayLayout profile) (index : Nat)
    (inBounds : index < layout.count) :
    ∃ range, layout.elementRange? index = some range := by
  apply Option.isSome_iff_exists.mp
  exact (layout.elementRange?_isSome_iff index).2 inBounds

@[simp] theorem elementRange?_eq_none_of_not_lt (layout : ArrayLayout profile)
    {index : Nat} (h : ¬ index < layout.count) :
    layout.elementRange? index = none := by
  simp [elementRange?, h]

@[simp] theorem elementRange?_eq_some (layout : ArrayLayout profile)
    {index : Nat} (h : index < layout.count) :
    layout.elementRange? index =
      some ⟨index * layout.stride, layout.element.size⟩ := by
  simp [elementRange?, h]

/-- Every checked element range stays within the array's total extent. -/
theorem elementRange?_withinBound {layout : ArrayLayout profile}
    (valid : layout.WellFormed) {index : Nat} {range : ByteRange}
    (selected : layout.elementRange? index = some range) :
    range.WithinBound layout.size := by
  simp only [elementRange?] at selected
  split at selected
  · rename_i inBounds
    cases selected
    simp only [ByteRange.WithinBound, ByteRange.stop, size]
    have fits : layout.element.size ≤ layout.stride :=
      layout.elementFitsStride_of_wellFormed valid
    calc
      index * layout.stride + layout.element.size ≤
          index * layout.stride + layout.stride := Nat.add_le_add_left fits _
      _ = (index + 1) * layout.stride := by simp [Nat.add_mul]
      _ ≤ layout.count * layout.stride :=
        Nat.mul_le_mul_right layout.stride (Nat.succ_le_iff.mpr inBounds)
  · contradiction

/-- Distinct ordered indices in a valid array select disjoint byte ranges. -/
theorem elementRange?_disjoint {layout : ArrayLayout profile}
    (valid : layout.WellFormed) {leftIndex rightIndex : Nat}
    {leftRange rightRange : ByteRange}
    (ordered : leftIndex < rightIndex)
    (leftSelected : layout.elementRange? leftIndex = some leftRange)
    (rightSelected : layout.elementRange? rightIndex = some rightRange) :
    leftRange.Disjoint rightRange := by
  have leftInBounds : leftIndex < layout.count :=
    (layout.elementRange?_isSome_iff leftIndex).mp (by simp [leftSelected])
  have rightInBounds : rightIndex < layout.count :=
    (layout.elementRange?_isSome_iff rightIndex).mp (by simp [rightSelected])
  rw [elementRange?_eq_some layout leftInBounds] at leftSelected
  rw [elementRange?_eq_some layout rightInBounds] at rightSelected
  cases leftSelected
  cases rightSelected
  apply Or.inr
  apply Or.inr
  apply Or.inl
  simp only [ByteRange.stop]
  have fits : layout.element.size ≤ layout.stride :=
    layout.elementFitsStride_of_wellFormed valid
  calc
    leftIndex * layout.stride + layout.element.size ≤
        leftIndex * layout.stride + layout.stride := Nat.add_le_add_left fits _
    _ = (leftIndex + 1) * layout.stride := by simp [Nat.add_mul]
    _ ≤ rightIndex * layout.stride :=
      Nat.mul_le_mul_right layout.stride (Nat.succ_le_iff.mpr ordered)

end ArrayLayout

end Grass.Construct.Layout
