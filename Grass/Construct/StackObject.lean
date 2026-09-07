import Grass.Construct.Layout.Stack

/-!
# Checked stack-object references and slices

`CheckedStackLayout` turns the existing executable layout predicate into a
stable proof-bearing input. `StackObjectRef` binds an object to that exact
layout, and `CheckedStackSlice` bounds a nonempty relative byte range within the
object. Absolute ranges are derived rather than authored independently.
-/

namespace Grass.Construct

open Grass.Core Grass.Memory Grass.Construct.Layout

/-- One ordinary stack layout paired with its structural certificate. -/
structure CheckedStackLayout (profile : LayoutProfile) where
  layout : StackLayout profile
  valid : layout.WellFormed

/-- Why a raw stack layout or object slice was rejected. -/
inductive StackObjectError where
  | invalidLayout
  | missingObject (name : Name)
  | zeroSize
  | outOfBounds (offset size objectSize : Nat)
deriving Repr, DecidableEq

/-- Check one raw ordinary stack layout. -/
def checkStackLayout {profile : LayoutProfile} (layout : StackLayout profile) :
    Except StackObjectError (CheckedStackLayout profile) :=
  if valid : layout.WellFormed then .ok ⟨layout, valid⟩
  else .error .invalidLayout

/-- One stack object with evidence that it belongs to an exact checked layout. -/
structure StackObjectRef {profile : LayoutProfile}
    (checked : CheckedStackLayout profile) where
  object : Layout.StackObject profile
  member : object ∈ checked.layout.objects

namespace StackObjectRef

variable {profile : LayoutProfile} {checked : CheckedStackLayout profile}

/-- The referenced object's existing layout checker result is true. -/
theorem objectWellFormed (slot : StackObjectRef checked) :
    checked.layout.objectWellFormed slot.object = true := by
  have allObjects := (StackLayout.wellFormed_iff checked.layout).mp checked.valid |>.1.2
  exact List.all_eq_true.mp allObjects slot.object slot.member

/-- The referenced object's whole range lies within its checked layout. -/
theorem withinLayout (slot : StackObjectRef checked) :
    slot.object.byteRange.WithinBound checked.layout.size := by
  have valid := slot.objectWellFormed
  simp [StackLayout.objectWellFormed] at valid
  exact valid.1.1.2

end StackObjectRef

namespace CheckedStackLayout

variable {profile : LayoutProfile}

/-- One checked stack-object reference whose nominal lookup is exact. -/
structure NamedStackObjectRef (checked : CheckedStackLayout profile) (name : Name) where
  slot : StackObjectRef checked
  nameExact : slot.object.name = name

/-- Find an object by name while retaining membership and exact-name evidence. -/
def findObject? (checked : CheckedStackLayout profile) (name : Name) :
    Option (NamedStackObjectRef checked name) :=
  match found : checked.layout.objects.find? fun object => object.name == name with
  | none => none
  | some object =>
      have nameExact : object.name = name := by
        have matched : (object.name == name) = true :=
          List.find?_some (p := fun candidate : Layout.StackObject profile =>
            candidate.name == name) found
        exact LawfulBEq.eq_of_beq matched
      some ⟨⟨object, List.mem_of_find?_eq_some found⟩, nameExact⟩

end CheckedStackLayout

/-- Nonempty object-relative byte slice before its bounds are checked. -/
structure StackSlice {profile : LayoutProfile} {checked : CheckedStackLayout profile}
    (slot : StackObjectRef checked) where
  offset : Nat
  size : Nat
deriving Repr, DecidableEq

namespace StackSlice

variable {profile : LayoutProfile} {checked : CheckedStackLayout profile}
  {slot : StackObjectRef checked}

/-- Object-relative half-open range. -/
def relativeRange (slice : StackSlice slot) : ByteRange := ⟨slice.offset, slice.size⟩

/-- Frame-relative range derived from the object's selected offset. -/
def absoluteRange (slice : StackSlice slot) : ByteRange :=
  ⟨slot.object.offset + slice.offset, slice.size⟩

/-- Executable nonempty object-containment check. -/
def wellFormed (slice : StackSlice slot) : Bool :=
  decide (0 < slice.size) &&
    decide (slice.relativeRange.WithinBound slot.object.repr.size)

/-- Certificate-facing statement for `StackSlice.wellFormed`. -/
def WellFormed (slice : StackSlice slot) : Prop := slice.wellFormed = true

instance (slice : StackSlice slot) : Decidable slice.WellFormed :=
  inferInstanceAs (Decidable (slice.wellFormed = true))

@[simp] theorem wellFormed_iff (slice : StackSlice slot) :
    slice.WellFormed ↔
      0 < slice.size ∧ slice.relativeRange.WithinBound slot.object.repr.size := by
  simp [WellFormed, wellFormed]

end StackSlice

/-- One object-relative slice paired with its nonempty containment proof. -/
structure CheckedStackSlice {profile : LayoutProfile}
    {checked : CheckedStackLayout profile} (slot : StackObjectRef checked) where
  slice : StackSlice slot
  valid : slice.WellFormed

namespace CheckedStackSlice

variable {profile : LayoutProfile} {checked : CheckedStackLayout profile}
  {slot : StackObjectRef checked}

/-- Frame-relative range of a checked object slice. -/
def absoluteRange (slice : CheckedStackSlice slot) : ByteRange :=
  slice.slice.absoluteRange

/-- A checked slice's derived absolute range lies within the checked layout. -/
theorem withinLayout (slice : CheckedStackSlice slot) :
    slice.absoluteRange.WithinBound checked.layout.size := by
  have relative := (StackSlice.wellFormed_iff slice.slice).mp slice.valid |>.2
  have object := slot.withinLayout
  simp [absoluteRange, StackSlice.absoluteRange, StackSlice.relativeRange,
    ByteRange.withinBound_def, Layout.StackObject.byteRange] at relative object ⊢
  omega

end CheckedStackSlice

/-- Checked slice returned by one exact nominal object lookup. -/
structure NamedCheckedStackSlice {profile : LayoutProfile}
    (checked : CheckedStackLayout profile) (name : Name) where
  objectRef : CheckedStackLayout.NamedStackObjectRef checked name
  checkedSlice : CheckedStackSlice objectRef.slot

/-- Find an object and check a nonempty relative slice within it. -/
def checkStackSlice {profile : LayoutProfile} (checked : CheckedStackLayout profile)
    (name : Name) (offset size : Nat) :
    Except StackObjectError (NamedCheckedStackSlice checked name) :=
  match checked.findObject? name with
  | none => .error (.missingObject name)
  | some objectRef =>
      if _positive : 0 < size then
        let slice : StackSlice objectRef.slot := ⟨offset, size⟩
        if valid : slice.WellFormed then .ok ⟨objectRef, ⟨slice, valid⟩⟩
        else .error (.outOfBounds offset size objectRef.slot.object.repr.size)
      else .error .zeroSize

end Grass.Construct
