import Grass.Construct.Layout.Core

/-!
# Explicit bitfield layouts

`BitfieldLayout.wellFormed` checks named logical bit ranges inside a declared
byte-sized storage unit.  Physical bit numbering remains a profile concern;
this constructor records offsets without weakening `StructLayout`.
-/

namespace Grass.Construct.Layout

open Grass.Core Grass.Memory

/-- A half-open logical bit range. -/
structure BitRange where
  start : Nat
  width : Nat
deriving Repr, DecidableEq

namespace BitRange

def stop (range : BitRange) : Nat := range.start + range.width

def Disjoint (left right : BitRange) : Prop :=
  left.width = 0 ∨ right.width = 0 ∨ left.stop ≤ right.start ∨ right.stop ≤ left.start

instance (left right : BitRange) : Decidable (left.Disjoint right) :=
  inferInstanceAs (Decidable
    (left.width = 0 ∨ right.width = 0 ∨
      left.stop ≤ right.start ∨ right.stop ≤ left.start))

end BitRange

/-- One named field occupying an explicit logical bit range. -/
structure BitField where
  name : Name
  range : BitRange
deriving Repr, DecidableEq

/-- Selected non-overlapping bitfields within one storage representation. -/
structure BitfieldLayout (profile : LayoutProfile) where
  fields : List BitField
  storageSize : Nat
  alignment : Nat
deriving Repr, DecidableEq

namespace BitfieldLayout

variable {profile : LayoutProfile}

def fieldNames (layout : BitfieldLayout profile) : List Name :=
  layout.fields.map BitField.name

def lookup? (layout : BitfieldLayout profile) (name : Name) : Option BitField :=
  layout.fields.find? (fun field => field.name == name)

def fieldWellFormed (layout : BitfieldLayout profile) (field : BitField) : Bool :=
  decide (0 < field.range.width) &&
  decide (field.range.stop ≤ layout.storageSize * 8)

def fieldsDisjoint (layout : BitfieldLayout profile) : Bool :=
  decide (layout.fields.Pairwise fun left right => left.range.Disjoint right.range)

/-- Executable checker for an explicit bitfield layout. -/
def wellFormed (layout : BitfieldLayout profile) : Bool :=
  decide (layout.fields ≠ []) &&
  decide layout.fieldNames.Nodup &&
  decide (0 < layout.storageSize) &&
  decide (0 < layout.alignment) &&
  profile.acceptsAlignment layout.alignment &&
  decide (IsAligned layout.storageSize layout.alignment) &&
  layout.fields.all layout.fieldWellFormed &&
  layout.fieldsDisjoint

def WellFormed (layout : BitfieldLayout profile) : Prop := layout.wellFormed = true

instance (layout : BitfieldLayout profile) : Decidable layout.WellFormed :=
  inferInstanceAs (Decidable (layout.wellFormed = true))

@[simp] theorem wellFormed_iff (layout : BitfieldLayout profile) :
    layout.WellFormed ↔
      ((((((layout.fields ≠ [] ∧ layout.fieldNames.Nodup) ∧
        0 < layout.storageSize) ∧ 0 < layout.alignment) ∧
        profile.acceptsAlignment layout.alignment = true) ∧
        IsAligned layout.storageSize layout.alignment) ∧
        layout.fields.all layout.fieldWellFormed = true) ∧
        layout.fieldsDisjoint = true := by
  simp [WellFormed, wellFormed]

end BitfieldLayout

end Grass.Construct.Layout
