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

universe u₁ u₂

variable {profile : LayoutProfile}

def fieldNames (layout : PackedLayout profile) : List Name :=
  layout.fields.map (fun placed => placed.field.name)

def lookup? (layout : PackedLayout profile) (name : Name) :
    Option (PlacedField profile) :=
  layout.fields.find? (fun placed => placed.field.name == name)

/-- A successful packed-field lookup returns a declared field with the requested name. -/
theorem lookup?_sound (layout : PackedLayout profile) (name : Name)
    (placed : PlacedField profile) (h : layout.lookup? name = some placed) :
    placed ∈ layout.fields ∧ placed.field.name = name := by
  constructor
  · exact List.mem_of_find?_eq_some (by simpa [lookup?] using h)
  · have matched : placed.field.name == name := List.find?_some
      (p := fun candidate : PlacedField profile => candidate.field.name == name) (by
        simpa [lookup?] using h)
    exact LawfulBEq.eq_of_beq matched

@[simp] theorem lookup?_isSome_iff_mem_fieldNames
    (layout : PackedLayout profile) (name : Name) :
    (layout.lookup? name).isSome = true ↔ name ∈ layout.fieldNames := by
  simp [lookup?, fieldNames]

/-- Every declared packed-field name has a concrete placement result. -/
theorem fieldForName (layout : PackedLayout profile) (name : Name)
    (member : name ∈ layout.fieldNames) :
    ∃ placed, layout.lookup? name = some placed := by
  apply Option.isSome_iff_exists.mp
  exact (layout.lookup?_isSome_iff_mem_fieldNames name).2 member

/-- Packed fields remain positive, represented, and within the aggregate. -/
def fieldWellFormed (layout : PackedLayout profile)
    (placed : PlacedField profile) : Bool :=
  decide (0 < placed.field.repr.size) &&
  placed.field.repr.wellFormed &&
  decide (placed.byteRange.WithinBound layout.size)

/-- Proposition-level representation validity and containment for a packed field. -/
def FieldWellFormed (layout : PackedLayout profile)
    (placed : PlacedField profile) : Prop :=
  0 < placed.field.repr.size ∧
  placed.field.repr.WellFormed ∧
  placed.byteRange.WithinBound layout.size

@[simp] theorem fieldWellFormed_eq_true_iff
    (layout : PackedLayout profile) (placed : PlacedField profile) :
    layout.fieldWellFormed placed = true ↔ layout.FieldWellFormed placed := by
  simp [fieldWellFormed, FieldWellFormed, ObjectRepr.WellFormed, and_assoc]

/-- Proposition-level validity of every declared packed field. -/
def FieldsWellFormed (layout : PackedLayout profile) : Prop :=
  ∀ placed ∈ layout.fields, layout.FieldWellFormed placed

@[simp] theorem fieldsAll_eq_true_iff (layout : PackedLayout profile) :
    layout.fields.all layout.fieldWellFormed = true ↔
      layout.FieldsWellFormed := by
  simp [FieldsWellFormed]

def fieldsDisjoint (layout : PackedLayout profile) : Bool :=
  decide (layout.fields.Pairwise fun left right =>
    left.byteRange.Disjoint right.byteRange)

/-- Proposition-level pairwise separation of packed field ranges. -/
def FieldsDisjoint (layout : PackedLayout profile) : Prop :=
  layout.fields.Pairwise fun left right =>
    left.byteRange.Disjoint right.byteRange

@[simp] theorem fieldsDisjoint_eq_true_iff (layout : PackedLayout profile) :
    layout.fieldsDisjoint = true ↔ layout.FieldsDisjoint := by
  simp [fieldsDisjoint, FieldsDisjoint]

/-- Whether a packed placement violates its representation alignment. -/
def requiresUnalignedAccess (placed : PlacedField profile) : Bool :=
  !decide (IsAligned placed.offset placed.field.repr.alignment)

/-- The executable marker is exact: it holds precisely for a misaligned field offset. -/
@[simp] theorem requiresUnalignedAccess_eq_true_iff
    (placed : PlacedField profile) :
    requiresUnalignedAccess placed = true ↔
      ¬IsAligned placed.offset placed.field.repr.alignment := by
  simp [requiresUnalignedAccess]

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
        layout.FieldsWellFormed) ∧
        layout.FieldsDisjoint := by
  simp [WellFormed, wellFormed, FieldsWellFormed]

/-- A valid packed layout has no duplicate nominal fields. -/
theorem fieldNamesNodup_of_wellFormed (layout : PackedLayout profile)
    (h : layout.WellFormed) : layout.fieldNames.Nodup :=
  (wellFormed_iff layout).mp h |>.1.1.1.1.1.2

/-- A valid packed aggregate has a positive declared alignment. -/
theorem aggregateAlignmentPositive_of_wellFormed
    (layout : PackedLayout profile) (h : layout.WellFormed) :
    0 < layout.alignment :=
  (wellFormed_iff layout).mp h |>.1.1.1.1.2

/-- A valid packed aggregate uses an alignment admitted by its profile. -/
theorem profileAcceptsAlignment_of_wellFormed
    (layout : PackedLayout profile) (h : layout.WellFormed) :
    profile.acceptsAlignment layout.alignment = true :=
  (wellFormed_iff layout).mp h |>.1.1.1.2

/-- A valid packed aggregate's storage size respects its declared alignment. -/
theorem sizeAligned_of_wellFormed (layout : PackedLayout profile)
    (h : layout.WellFormed) : IsAligned layout.size layout.alignment :=
  (wellFormed_iff layout).mp h |>.1.1.2

/-- A valid packed layout makes every declared representation valid and contained. -/
theorem fieldsWellFormed_of_wellFormed (layout : PackedLayout profile)
    (h : layout.WellFormed) : layout.FieldsWellFormed :=
  (wellFormed_iff layout).mp h |>.1.2

/-- A valid packed layout keeps all declared byte ranges pairwise separate. -/
theorem fieldsDisjoint_of_wellFormed (layout : PackedLayout profile)
    (h : layout.WellFormed) : layout.FieldsDisjoint :=
  (wellFormed_iff layout).mp h |>.2

/-- Every field in a valid packed layout remains inside its aggregate storage. -/
theorem fieldWithinStorage_of_wellFormed (layout : PackedLayout profile)
    (h : layout.WellFormed) (placed : PlacedField profile)
    (member : placed ∈ layout.fields) :
    placed.byteRange.WithinBound layout.size :=
  (layout.fieldsWellFormed_of_wellFormed h placed member).2.2

private theorem eq_of_mem_of_mem_of_map_nodup
    {α : Type u₁} {β : Type u₂} (key : α → β)
    {items : List α} {left right : α}
    (unique : (items.map key).Nodup)
    (leftMem : left ∈ items) (rightMem : right ∈ items)
    (sameKey : key left = key right) : left = right := by
  induction items with
  | nil => simp at leftMem
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at unique
      rw [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · exfalso
          apply unique.1
          rw [sameKey]
          exact List.mem_map.mpr ⟨right, rightMem, rfl⟩
      · rcases rightMem with rfl | rightMem
        · exfalso
          apply unique.1
          rw [← sameKey]
          exact List.mem_map.mpr ⟨left, leftMem, rfl⟩
        · exact ih unique.2 leftMem rightMem

/-- Two declared fields of a valid packed aggregate with the same name are the
same authored placement. -/
theorem field_eq_of_mem_of_mem_of_name_eq
    (layout : PackedLayout profile) (left right : PlacedField profile)
    (closed : layout.WellFormed)
    (leftMem : left ∈ layout.fields) (rightMem : right ∈ layout.fields)
    (sameName : left.field.name = right.field.name) : left = right := by
  exact eq_of_mem_of_mem_of_map_nodup
    (fun placed : PlacedField profile => placed.field.name)
    (by simpa [fieldNames] using layout.fieldNamesNodup_of_wellFormed closed)
    leftMem rightMem sameName

/-- Under `PackedLayout.WellFormed`, nominal lookup returns the exact authored
placement already held by the caller. -/
theorem lookup?_eq_some_of_mem
    (layout : PackedLayout profile) (name : Name)
    (placed : PlacedField profile) (closed : layout.WellFormed)
    (member : placed ∈ layout.fields) (hasName : placed.field.name = name) :
    layout.lookup? name = some placed := by
  have nameMember : name ∈ layout.fieldNames := by
    simp [fieldNames]
    exact ⟨placed, member, hasName⟩
  obtain ⟨found, foundLookup⟩ := layout.fieldForName name nameMember
  have foundFacts := layout.lookup?_sound name found foundLookup
  have foundEq : found = placed :=
    layout.field_eq_of_mem_of_mem_of_name_eq found placed closed
      foundFacts.1 member (foundFacts.2.trans hasName.symm)
  simpa [foundEq] using foundLookup

end PackedLayout

end Grass.Construct.Layout
