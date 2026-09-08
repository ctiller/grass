import Grass.Construct.Layout.Core

/-!
# Bounded flexible-tail layouts

`FlexibleTailLayout` keeps an ordinary checked prefix and a separately bounded
trailing element family.  `FlexibleTailLayout.wellFormed` checks the declared
maximum extent, while `FlexibleTailLayout.selectedRange` exposes the currently
selected prefix of that capacity without changing the ordinary struct rules.
-/

namespace Grass.Construct.Layout

open Grass.Memory

/-- An ordinary prefix followed by zero or more elements up to a fixed bound. -/
structure FlexibleTailLayout (profile : LayoutProfile) where
  head : StructLayout profile
  element : ObjectRepr profile
  tailOffset : Nat
  maxCount : Nat
  selectedCount : Nat
  size : Nat
  alignment : Nat
deriving Repr, DecidableEq

namespace FlexibleTailLayout

variable {profile : LayoutProfile}

/-- Complete capacity range reserved for the flexible tail. -/
def reservedRange (layout : FlexibleTailLayout profile) : ByteRange :=
  ⟨layout.tailOffset, layout.maxCount * layout.element.size⟩

/-- Range occupied by the currently selected tail elements. -/
def selectedRange (layout : FlexibleTailLayout profile) : ByteRange :=
  ⟨layout.tailOffset, layout.selectedCount * layout.element.size⟩

/-- Exact range of a selected tail element, rejecting out-of-selection indices. -/
def elementRange? (layout : FlexibleTailLayout profile) (index : Nat) :
    Option ByteRange :=
  if index < layout.selectedCount then
    some ⟨layout.tailOffset + index * layout.element.size, layout.element.size⟩
  else
    none

/-- Select another element count without changing the capacity reservation. -/
def selectCount? (layout : FlexibleTailLayout profile) (count : Nat) :
    Option (FlexibleTailLayout profile) :=
  if count ≤ layout.maxCount then some { layout with selectedCount := count }
  else none

@[simp] theorem elementRange?_isSome_iff
    (layout : FlexibleTailLayout profile) (index : Nat) :
    (layout.elementRange? index).isSome = true ↔
      index < layout.selectedCount := by
  simp [elementRange?]

@[simp] theorem selectCount?_eq_some_iff
    (layout selected : FlexibleTailLayout profile) (count : Nat) :
    layout.selectCount? count = some selected ↔
      count ≤ layout.maxCount ∧
      selected = { layout with selectedCount := count } := by
  simp [selectCount?, eq_comm]

/-- Executable checker for a bounded flexible-tail representation. -/
def wellFormed (layout : FlexibleTailLayout profile) : Bool :=
  layout.head.wellFormed &&
  decide (0 < layout.element.size) &&
  layout.element.wellFormed &&
  decide (layout.head.size ≤ layout.tailOffset) &&
  decide (IsAligned layout.tailOffset layout.element.alignment) &&
  decide (layout.selectedCount ≤ layout.maxCount) &&
  decide (0 < layout.alignment) &&
  profile.acceptsAlignment layout.alignment &&
  decide (layout.alignment % layout.head.alignment = 0) &&
  decide (layout.alignment % layout.element.alignment = 0) &&
  decide (layout.size = layout.reservedRange.stop) &&
  decide (IsAligned layout.size layout.alignment)

/-- Certificate-facing statement for `FlexibleTailLayout.wellFormed`. -/
def WellFormed (layout : FlexibleTailLayout profile) : Prop :=
  layout.wellFormed = true

instance (layout : FlexibleTailLayout profile) : Decidable layout.WellFormed :=
  inferInstanceAs (Decidable (layout.wellFormed = true))

/-- Public decomposition of bounded flexible-tail closure. -/
@[simp] theorem wellFormed_iff (layout : FlexibleTailLayout profile) :
    layout.WellFormed ↔
      ((((((((((layout.head.WellFormed ∧ 0 < layout.element.size) ∧
        layout.element.WellFormed) ∧
        layout.head.size ≤ layout.tailOffset) ∧
        IsAligned layout.tailOffset layout.element.alignment) ∧
        layout.selectedCount ≤ layout.maxCount) ∧
        0 < layout.alignment) ∧
        profile.acceptsAlignment layout.alignment = true) ∧
        layout.alignment % layout.head.alignment = 0) ∧
        layout.alignment % layout.element.alignment = 0) ∧
        layout.size = layout.reservedRange.stop) ∧
        IsAligned layout.size layout.alignment := by
  simp [WellFormed, wellFormed, StructLayout.WellFormed, ObjectRepr.WellFormed]

theorem selectedCountWithinCapacity_of_wellFormed
    (layout : FlexibleTailLayout profile) (h : layout.WellFormed) :
    layout.selectedCount ≤ layout.maxCount := by
  exact (wellFormed_iff layout).mp h |>.1.1.1.1.1.1.2

theorem extentExact_of_wellFormed
    (layout : FlexibleTailLayout profile) (h : layout.WellFormed) :
    layout.size = layout.reservedRange.stop := by
  exact (wellFormed_iff layout).mp h |>.1.2

/-- `FlexibleTailLayout.selectedRange_within_reservedRange` proves that the
selected tail is contained in the reserved capacity range. -/
theorem selectedRange_within_reservedRange
    (layout : FlexibleTailLayout profile) (h : layout.WellFormed) :
    layout.reservedRange.Contains layout.selectedRange := by
  constructor
  · simp [reservedRange, selectedRange]
  · simp only [reservedRange, selectedRange, ByteRange.stop]
    apply Nat.add_le_add_left
    exact Nat.mul_le_mul_right layout.element.size
      (layout.selectedCountWithinCapacity_of_wellFormed h)

/-- `FlexibleTailLayout.selectedRange_withinBound` places the selected tail
within the complete aggregate extent. -/
theorem selectedRange_withinBound
    (layout : FlexibleTailLayout profile) (h : layout.WellFormed) :
    layout.selectedRange.WithinBound layout.size := by
  rw [layout.extentExact_of_wellFormed h]
  exact (layout.selectedRange_within_reservedRange h).2

/-- `FlexibleTailLayout.elementRange?_within_selectedRange` places every
successfully selected element range inside the selected tail. -/
theorem elementRange?_within_selectedRange
    (layout : FlexibleTailLayout profile) {index : Nat} {range : ByteRange}
    (selected : layout.elementRange? index = some range) :
    layout.selectedRange.Contains range := by
  have inBounds : index < layout.selectedCount :=
    (layout.elementRange?_isSome_iff index).mp (by simp [selected])
  simp only [elementRange?] at selected
  split at selected
  · cases selected
    constructor
    · simp [selectedRange]
    · simp only [selectedRange, ByteRange.stop]
      rw [Nat.add_assoc]
      apply Nat.add_le_add_left
      calc
        index * layout.element.size + layout.element.size =
            (index + 1) * layout.element.size := by simp [Nat.add_mul]
        _ ≤ layout.selectedCount * layout.element.size :=
          Nat.mul_le_mul_right layout.element.size (Nat.succ_le_iff.mpr inBounds)
  · contradiction

/-- `FlexibleTailLayout.selectCount?_wellFormed` proves that successful count
selection preserves well-formedness and capacity. -/
theorem selectCount?_wellFormed
    (layout selected : FlexibleTailLayout profile) (h : layout.WellFormed)
    (count : Nat) (chosen : layout.selectCount? count = some selected) :
    selected.WellFormed := by
  rcases (layout.selectCount?_eq_some_iff selected count).mp chosen with
    ⟨withinCapacity, rfl⟩
  rcases (wellFormed_iff layout).mp h with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨headValid, elementPositive⟩, elementValid⟩,
      headBeforeTail⟩, tailAligned⟩, _oldSelectedWithin⟩,
      aggregateAlignmentPositive⟩, profileAcceptsAlignment⟩,
      aggregateAlignsHead⟩, aggregateAlignsElement⟩, extentExact⟩,
      aggregateSizeAligned⟩
  apply (wellFormed_iff _).2
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨headValid, elementPositive⟩, elementValid⟩,
      headBeforeTail⟩, tailAligned⟩, withinCapacity⟩,
      aggregateAlignmentPositive⟩, profileAcceptsAlignment⟩,
      aggregateAlignsHead⟩, aggregateAlignsElement⟩, extentExact⟩,
      aggregateSizeAligned⟩

end FlexibleTailLayout

end Grass.Construct.Layout
