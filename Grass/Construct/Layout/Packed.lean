import Grass.Construct.Layout.Core

/-!
# Explicit packed layouts

`PackedLayout.wellFormed` checks containment and disjointness without requiring
each field offset to satisfy its representation alignment.  This is a distinct
constructor because `StructLayout.fieldWellFormed` deliberately retains that
alignment requirement; whether an unaligned field can be accessed is a later
machine/profile proof, not granted here.
-/

namespace Grass.Construct.Layout

open Grass.Core Grass.Memory

/-- A selected packed aggregate with explicit byte offsets. -/
structure PackedLayout (profile : LayoutProfile) where
  fields : List (PlacedField profile)
  size : Nat
  alignment : Nat
deriving Repr, DecidableEq

namespace PackedLayout

variable {profile : LayoutProfile}

def fieldNames (layout : PackedLayout profile) : List Name :=
  layout.fields.map (fun placed => placed.field.name)

def lookup? (layout : PackedLayout profile) (name : Name) :
    Option (PlacedField profile) :=
  layout.fields.find? (fun placed => placed.field.name == name)

/-- Packed fields remain positive, represented, and within the aggregate. -/
def fieldWellFormed (layout : PackedLayout profile)
    (placed : PlacedField profile) : Bool :=
  decide (0 < placed.field.repr.size) &&
  placed.field.repr.wellFormed &&
  decide (placed.byteRange.WithinBound layout.size)

def fieldsDisjoint (layout : PackedLayout profile) : Bool :=
  decide (layout.fields.Pairwise fun left right =>
    left.byteRange.Disjoint right.byteRange)

/-- Whether a packed placement violates its representation alignment. -/
def requiresUnalignedAccess (placed : PlacedField profile) : Bool :=
  !decide (IsAligned placed.offset placed.field.repr.alignment)

/-- Executable structural checker for an explicitly packed aggregate. -/
def wellFormed (layout : PackedLayout profile) : Bool :=
  decide (layout.fields ≠ []) &&
  decide layout.fieldNames.Nodup &&
  decide (0 < layout.alignment) &&
  profile.acceptsAlignment layout.alignment &&
  decide (IsAligned layout.size layout.alignment) &&
  layout.fields.all layout.fieldWellFormed &&
  layout.fieldsDisjoint

def WellFormed (layout : PackedLayout profile) : Prop := layout.wellFormed = true

instance (layout : PackedLayout profile) : Decidable layout.WellFormed :=
  inferInstanceAs (Decidable (layout.wellFormed = true))

@[simp] theorem wellFormed_iff (layout : PackedLayout profile) :
    layout.WellFormed ↔
      (((((layout.fields ≠ [] ∧ layout.fieldNames.Nodup) ∧
        0 < layout.alignment) ∧
        profile.acceptsAlignment layout.alignment = true) ∧
        IsAligned layout.size layout.alignment) ∧
        layout.fields.all layout.fieldWellFormed = true) ∧
        layout.fieldsDisjoint = true := by
  simp [WellFormed, wellFormed]

end PackedLayout

end Grass.Construct.Layout
