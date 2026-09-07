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

end FlexibleTailLayout

end Grass.Construct.Layout
