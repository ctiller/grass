import Grass.Construct.Layout.Core

/-!
# Nested layout composition

Nested field offsets are relative to their immediate aggregate. This module
connects those local offsets to an outer `StructLayout` without flattening the
inner layout or duplicating its checker. A `NestedPlacement` records exact size
and alignment agreement between the parent's selected representation and the
inner aggregate, then exports absolute range, containment, alignment, and
framing theorems.
-/

namespace Grass.Construct.Layout

open Grass.Memory

/-- Translate a relative byte range by an enclosing base offset. -/
def translateRange (base : Nat) (range : ByteRange) : ByteRange :=
  ⟨base + range.start, range.size⟩

namespace translateRange

@[simp] theorem start (base : Nat) (range : ByteRange) :
    (translateRange base range).start = base + range.start := rfl

@[simp] theorem size (base : Nat) (range : ByteRange) :
    (translateRange base range).size = range.size := rfl

@[simp] theorem stop (base : Nat) (range : ByteRange) :
    (translateRange base range).stop = base + range.stop := by
  simp [translateRange, ByteRange.stop, Nat.add_assoc]

/-- Repeated nesting is exactly one translation by the summed parent offsets. -/
theorem compose (outerBase innerBase : Nat) (range : ByteRange) :
    translateRange outerBase (translateRange innerBase range) =
      translateRange (outerBase + innerBase) range := by
  cases range
  simp [translateRange, Nat.add_assoc]

/-- Translating a range within a parent extent keeps it inside that parent range. -/
theorem contained (base parentSize : Nat) (range : ByteRange)
    (h : range.WithinBound parentSize) :
    (ByteRange.mk base parentSize).Contains (translateRange base range) := by
  rw [ByteRange.withinBound_def] at h
  constructor
  · simp [translateRange]
  · simp [translateRange, ByteRange.stop] at h ⊢
    omega

/-- Translation by a common base preserves containment exactly. -/
theorem contains (base : Nat) {outer inner : ByteRange}
    (h : outer.Contains inner) :
    (translateRange base outer).Contains (translateRange base inner) := by
  constructor
  · exact Nat.add_le_add_left h.1 base
  · simpa only [stop] using Nat.add_le_add_left h.2 base

/-- Translation by a common base preserves separation of sibling ranges. -/
theorem disjoint (base : Nat) {left right : ByteRange}
    (h : left.Disjoint right) :
    (translateRange base left).Disjoint (translateRange base right) := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (by
      simpa only [stop, start] using Nat.add_le_add_left h base)))
  · exact Or.inr (Or.inr (Or.inr (by
      simpa only [stop, start] using Nat.add_le_add_left h base)))

/-- `translateRange.aligned` preserves local alignment when the base is aligned too. -/
theorem aligned {base : Nat} {range : ByteRange} {alignment : Nat}
    (baseAligned : IsAligned base alignment)
    (localAligned : IsAligned range.start alignment) :
    IsAligned (translateRange base range).start alignment := by
  have baseDivides : alignment ∣ base := Nat.dvd_of_mod_eq_zero baseAligned
  have localDivides : alignment ∣ range.start :=
    Nat.dvd_of_mod_eq_zero localAligned
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add baseDivides localDivides)

end translateRange

/-- One inner field composed through a selected outer field representation. -/
structure NestedPlacement {profile : LayoutProfile}
    (outer inner : StructLayout profile) where
  parent : PlacedField profile
  parentMember : parent ∈ outer.fields
  child : PlacedField profile
  childMember : child ∈ inner.fields
  sizeExact : parent.field.repr.size = inner.size
  alignmentExact : parent.field.repr.alignment = inner.alignment

namespace NestedPlacement

variable {profile : LayoutProfile} {outer inner : StructLayout profile}

/-- Absolute byte range of the child relative to the outer aggregate. -/
def byteRange (nested : NestedPlacement outer inner) : ByteRange :=
  translateRange nested.parent.offset nested.child.byteRange

@[simp] theorem byteRange_start (nested : NestedPlacement outer inner) :
    nested.byteRange.start = nested.parent.offset + nested.child.offset := rfl

@[simp] theorem byteRange_size (nested : NestedPlacement outer inner) :
    nested.byteRange.size = nested.child.field.repr.size := rfl

@[simp] theorem byteRange_stop (nested : NestedPlacement outer inner) :
    nested.byteRange.stop = nested.parent.offset + nested.child.byteRange.stop :=
  translateRange.stop nested.parent.offset nested.child.byteRange

/-- Inner well-formedness places the translated child inside its selected parent. -/
theorem containedInParent (nested : NestedPlacement outer inner)
    (innerWellFormed : inner.WellFormed) :
    nested.parent.byteRange.Contains nested.byteRange := by
  have childValid := inner.fieldsWellFormed_of_wellFormed innerWellFormed
  unfold StructLayout.FieldsWellFormed at childValid
  have selectedChild := childValid.2 nested.child nested.childMember
  have childBound : nested.child.byteRange.WithinBound inner.size :=
    selectedChild.2.2.2.1
  rw [← nested.sizeExact] at childBound
  exact translateRange.contained nested.parent.offset
    nested.parent.field.repr.size nested.child.byteRange childBound

/-- Outer and inner well-formedness transport the child's bound to the outer storage. -/
theorem withinOuter (nested : NestedPlacement outer inner)
    (outerWellFormed : outer.WellFormed)
    (innerWellFormed : inner.WellFormed) :
    nested.byteRange.WithinBound outer.size := by
  have parentValid := outer.fieldsWellFormed_of_wellFormed outerWellFormed
  unfold StructLayout.FieldsWellFormed at parentValid
  have selectedParent := parentValid.2 nested.parent nested.parentMember
  exact selectedParent.2.2.2.1.of_contains
    (nested.containedInParent innerWellFormed)

/-- A range disjoint from the parent is disjoint from every translated child. -/
theorem disjointOfParentDisjoint (nested : NestedPlacement outer inner)
    (innerWellFormed : inner.WellFormed) {other : ByteRange}
    (h : other.Disjoint nested.parent.byteRange) :
    other.Disjoint nested.byteRange :=
  h.of_contains (nested.containedInParent innerWellFormed)

/-- Two children translated through the same parent remain disjoint whenever
their inner byte ranges are disjoint. -/
theorem disjointOfChildDisjoint
    (left right : NestedPlacement outer inner)
    (sameParent : left.parent = right.parent)
    (h : left.child.byteRange.Disjoint right.child.byteRange) :
    left.byteRange.Disjoint right.byteRange := by
  unfold byteRange
  rw [sameParent]
  exact translateRange.disjoint right.parent.offset h

/-- Exact representation agreement composes the child's local alignment into an absolute one. -/
theorem aligned (nested : NestedPlacement outer inner)
    (outerWellFormed : outer.WellFormed)
    (innerWellFormed : inner.WellFormed) :
    IsAligned nested.byteRange.start nested.child.field.repr.alignment := by
  have parentValid := outer.fieldsWellFormed_of_wellFormed outerWellFormed
  unfold StructLayout.FieldsWellFormed at parentValid
  have selectedParent := parentValid.2 nested.parent nested.parentMember
  have childValid := inner.fieldsWellFormed_of_wellFormed innerWellFormed
  unfold StructLayout.FieldsWellFormed at childValid
  have selectedChild := childValid.2 nested.child nested.childMember
  have parentAligned :
      IsAligned nested.parent.offset nested.parent.field.repr.alignment :=
    selectedParent.2.2.1
  have childAlignmentDividesInner :
      nested.child.field.repr.alignment ∣ inner.alignment :=
    Nat.dvd_of_mod_eq_zero selectedChild.2.2.2.2
  have childAlignmentDividesParent :
      nested.child.field.repr.alignment ∣ nested.parent.field.repr.alignment := by
    simpa [nested.alignmentExact] using childAlignmentDividesInner
  have childAlignmentDividesOffset :
      nested.child.field.repr.alignment ∣ nested.parent.offset :=
    Nat.dvd_trans childAlignmentDividesParent
      (Nat.dvd_of_mod_eq_zero parentAligned)
  have baseAligned :
      IsAligned nested.parent.offset nested.child.field.repr.alignment :=
    Nat.mod_eq_zero_of_dvd childAlignmentDividesOffset
  exact translateRange.aligned baseAligned selectedChild.2.2.1

end NestedPlacement

end Grass.Construct.Layout
