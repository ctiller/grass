import Grass.Construct.Layout.Stack

/-!
# Bounded dynamic stack reservations

`BoundedStackLayout` extends one checked ordinary `StackLayout` with named
reservations whose selected extents may vary up to explicit capacities.
`BoundedStackLayout.dynamicDisjoint` and
`BoundedStackLayout.fixedDynamicDisjoint` check the complete capacity ranges;
`DynamicStackObject.reservedRange_contains_selectedRange` keeps every admitted
selected extent inside the checked reservation.
-/

namespace Grass.Construct.Layout

open Grass.Core Grass.Memory

/-- One lexically scoped stack reservation with a bounded selected extent. -/
structure DynamicStackObject (profile : LayoutProfile) where
  name : Name
  offset : Nat
  capacity : Nat
  selectedSize : Nat
  alignment : Nat
  scope : ScopeId
deriving Repr, DecidableEq

namespace DynamicStackObject

variable {profile : LayoutProfile}

/-- The whole byte range reserved for every permitted selected extent. -/
def reservedRange (object : DynamicStackObject profile) : ByteRange :=
  ⟨object.offset, object.capacity⟩

/-- The currently selected prefix of `DynamicStackObject.reservedRange`. -/
def selectedRange (object : DynamicStackObject profile) : ByteRange :=
  ⟨object.offset, object.selectedSize⟩

/-- Select another extent without changing reservation identity or placement. -/
def selectSize? (object : DynamicStackObject profile) (size : Nat) :
    Option (DynamicStackObject profile) :=
  if size ≤ object.capacity then some { object with selectedSize := size }
  else none

/-- An admitted selected extent is contained by its capacity reservation. -/
theorem reservedRange_contains_selectedRange (object : DynamicStackObject profile)
    (h : object.selectedSize ≤ object.capacity) :
    object.reservedRange.Contains object.selectedRange := by
  simp only [reservedRange, selectedRange, ByteRange.contains_def]
  omega

end DynamicStackObject

/-- Fixed stack objects plus separately checked bounded dynamic reservations. -/
structure BoundedStackLayout (profile : LayoutProfile) where
  fixed : StackLayout profile
  dynamic : List (DynamicStackObject profile)
deriving Repr, DecidableEq

namespace BoundedStackLayout

variable {profile : LayoutProfile}

/-- Names across both the fixed and dynamic parts of the frame. -/
def objectNames (layout : BoundedStackLayout profile) : List Name :=
  layout.fixed.objectNames ++ layout.dynamic.map DynamicStackObject.name

/-- Local capacity, selection, alignment, containment, and scope check. -/
def dynamicWellFormed (layout : BoundedStackLayout profile)
    (object : DynamicStackObject profile) : Bool :=
  decide (0 < object.capacity) &&
  decide (object.selectedSize ≤ object.capacity) &&
  decide (0 < object.alignment) &&
  profile.acceptsAlignment object.alignment &&
  decide (IsAligned object.offset object.alignment) &&
  decide (layout.fixed.alignment % object.alignment = 0) &&
  decide (object.reservedRange.WithinBound layout.fixed.size) &&
  layout.fixed.scopeIds.contains object.scope

/-- Whether dynamic capacity reservations are pairwise disjoint. -/
def dynamicDisjoint (layout : BoundedStackLayout profile) : Bool :=
  decide (layout.dynamic.Pairwise fun left right =>
    left.reservedRange.Disjoint right.reservedRange)

/-- Whether every fixed object is disjoint from every dynamic capacity range. -/
def fixedDynamicDisjoint (layout : BoundedStackLayout profile) : Bool :=
  layout.fixed.objects.all fun fixed =>
    layout.dynamic.all fun dynamic =>
      decide (fixed.byteRange.Disjoint dynamic.reservedRange)

/-- Executable checker for a frame with bounded dynamic reservations. -/
def wellFormed (layout : BoundedStackLayout profile) : Bool :=
  layout.fixed.wellFormed &&
  decide layout.objectNames.Nodup &&
  layout.dynamic.all layout.dynamicWellFormed &&
  layout.dynamicDisjoint &&
  layout.fixedDynamicDisjoint

/-- Certificate-facing statement for `BoundedStackLayout.wellFormed`. -/
def WellFormed (layout : BoundedStackLayout profile) : Prop :=
  layout.wellFormed = true

instance (layout : BoundedStackLayout profile) : Decidable layout.WellFormed :=
  inferInstanceAs (Decidable (layout.wellFormed = true))

/-- Public decomposition of bounded dynamic stack-layout closure. -/
@[simp] theorem wellFormed_iff (layout : BoundedStackLayout profile) :
    layout.WellFormed ↔
      ((((layout.fixed.WellFormed ∧ layout.objectNames.Nodup) ∧
        layout.dynamic.all layout.dynamicWellFormed = true) ∧
        layout.dynamicDisjoint = true) ∧
        layout.fixedDynamicDisjoint = true) := by
  simp [WellFormed, wellFormed, StackLayout.WellFormed]

end BoundedStackLayout

end Grass.Construct.Layout
