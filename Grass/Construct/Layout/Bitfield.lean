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

theorem Disjoint.symm {left right : BitRange} (h : left.Disjoint right) :
    right.Disjoint left := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

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

theorem lookup?_sound (layout : BitfieldLayout profile) (name : Name)
    (field : BitField) (h : layout.lookup? name = some field) :
    field ∈ layout.fields ∧ field.name = name := by
  constructor
  · exact List.mem_of_find?_eq_some (by simpa [lookup?] using h)
  · have matched : field.name == name := List.find?_some
      (p := fun candidate : BitField => candidate.name == name) (by
        simpa [lookup?] using h)
    exact LawfulBEq.eq_of_beq matched

@[simp] theorem lookup?_isSome_iff_mem_fieldNames
    (layout : BitfieldLayout profile) (name : Name) :
    (layout.lookup? name).isSome = true ↔ name ∈ layout.fieldNames := by
  simp [lookup?, fieldNames]

/-- Every declared bitfield name has a concrete range lookup result. -/
theorem fieldForName (layout : BitfieldLayout profile) (name : Name)
    (member : name ∈ layout.fieldNames) :
    ∃ field, layout.lookup? name = some field := by
  apply Option.isSome_iff_exists.mp
  exact (layout.lookup?_isSome_iff_mem_fieldNames name).2 member

def fieldWellFormed (layout : BitfieldLayout profile) (field : BitField) : Bool :=
  decide (0 < field.range.width) &&
  decide (field.range.stop ≤ layout.storageSize * 8)

/-- Proposition-level positivity and storage containment for one bitfield. -/
def FieldWellFormed (layout : BitfieldLayout profile) (field : BitField) : Prop :=
  0 < field.range.width ∧ field.range.stop ≤ layout.storageSize * 8

@[simp] theorem fieldWellFormed_eq_true_iff
    (layout : BitfieldLayout profile) (field : BitField) :
    layout.fieldWellFormed field = true ↔ layout.FieldWellFormed field := by
  simp [fieldWellFormed, FieldWellFormed]

/-- Proposition-level validity of every declared bitfield. -/
def FieldsWellFormed (layout : BitfieldLayout profile) : Prop :=
  ∀ field ∈ layout.fields, layout.FieldWellFormed field

@[simp] theorem fieldsAll_eq_true_iff (layout : BitfieldLayout profile) :
    layout.fields.all layout.fieldWellFormed = true ↔
      layout.FieldsWellFormed := by
  simp [FieldsWellFormed]

def fieldsDisjoint (layout : BitfieldLayout profile) : Bool :=
  decide (layout.fields.Pairwise fun left right => left.range.Disjoint right.range)

/-- Proposition-level pairwise separation of declared logical bit ranges. -/
def FieldsDisjoint (layout : BitfieldLayout profile) : Prop :=
  layout.fields.Pairwise fun left right => left.range.Disjoint right.range

@[simp] theorem fieldsDisjoint_eq_true_iff (layout : BitfieldLayout profile) :
    layout.fieldsDisjoint = true ↔ layout.FieldsDisjoint := by
  simp [fieldsDisjoint, FieldsDisjoint]

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
        layout.FieldsWellFormed) ∧
        layout.FieldsDisjoint := by
  simp [WellFormed, wellFormed, FieldsWellFormed]

theorem fieldNamesNodup_of_wellFormed (layout : BitfieldLayout profile)
    (h : layout.WellFormed) : layout.fieldNames.Nodup :=
  (wellFormed_iff layout).mp h |>.1.1.1.1.1.1.2

theorem fieldsWellFormed_of_wellFormed (layout : BitfieldLayout profile)
    (h : layout.WellFormed) : layout.FieldsWellFormed :=
  (wellFormed_iff layout).mp h |>.1.2

theorem fieldsDisjoint_of_wellFormed (layout : BitfieldLayout profile)
    (h : layout.WellFormed) : layout.FieldsDisjoint :=
  (wellFormed_iff layout).mp h |>.2

theorem fieldWithinStorage_of_wellFormed (layout : BitfieldLayout profile)
    (h : layout.WellFormed) (field : BitField)
    (member : field ∈ layout.fields) :
    field.range.stop ≤ layout.storageSize * 8 :=
  (layout.fieldsWellFormed_of_wellFormed h field member).2

end BitfieldLayout

end Grass.Construct.Layout
