import Grass.Core.Name
import Grass.Memory.Range

/-!
# Physical layout core

Profile-indexed representation demands and explicitly placed aggregate fields.
This module checks a selected layout; automatic placement is a separate layer
that must return one of these values together with `StructLayout.WellFormed`.

Keeping selection and checking separate leaves the literal-offset escape hatch
available: an author may choose every offset, while `StructLayout.wellFormed`
checks
alignment, containment, non-overlap, and aggregate compatibility.
-/

namespace Grass.Construct.Layout

open Grass.Core Grass.Memory

/-- Target or format policy for admissible field alignments.

The predicate is executable because layout checking is a construction phase.
Named ABI, device, packed, and wire profiles supply different policies rather
than inheriting an ambient C layout rule.
-/
structure LayoutProfile where
  acceptsAlignment : Nat → Bool

/-- Size and alignment demanded by the selected representation of one value. -/
structure ObjectRepr (profile : LayoutProfile) where
  size : Nat
  alignment : Nat
deriving Repr, DecidableEq

namespace ObjectRepr

variable {profile : LayoutProfile}

/-- A representation has a positive alignment admitted by its explicit
profile. Zero-sized representations remain expressible; constructors for them
belong to the profile that permits their semantics. -/
def wellFormed (repr : ObjectRepr profile) : Bool :=
  decide (0 < repr.alignment) && profile.acceptsAlignment repr.alignment

def WellFormed (repr : ObjectRepr profile) : Prop := repr.wellFormed = true

instance (repr : ObjectRepr profile) : Decidable repr.WellFormed :=
  inferInstanceAs (Decidable (repr.wellFormed = true))

@[simp] theorem wellFormed_iff (repr : ObjectRepr profile) :
    repr.WellFormed ↔
      0 < repr.alignment ∧ profile.acceptsAlignment repr.alignment = true := by
  simp [WellFormed, wellFormed]

end ObjectRepr

/-- One logical field and its selected physical representation. -/
structure FieldSpec (profile : LayoutProfile) where
  name : Name
  repr : ObjectRepr profile
deriving Repr, DecidableEq

/-- One field placed at an explicit byte offset. -/
structure PlacedField (profile : LayoutProfile) where
  field : FieldSpec profile
  offset : Nat
deriving Repr, DecidableEq

namespace PlacedField

variable {profile : LayoutProfile}

/-- Exact half-open byte range occupied by this field. -/
def byteRange (placed : PlacedField profile) : ByteRange :=
  ⟨placed.offset, placed.field.repr.size⟩

end PlacedField

/-- A selected ordinary aggregate layout.

Special representations such as unions, overlays, packed aggregates,
bitfields, and flexible tails use separate constructors; weakening the
ordinary pairwise-disjoint check is not their extension mechanism.
-/
structure StructLayout (profile : LayoutProfile) where
  fields : List (PlacedField profile)
  size : Nat
  alignment : Nat
deriving Repr, DecidableEq

namespace StructLayout

variable {profile : LayoutProfile}

def fieldNames (layout : StructLayout profile) : List Name :=
  layout.fields.map (fun placed => placed.field.name)

/-- Find a field placement by its nominal field name. -/
def lookup? (layout : StructLayout profile) (name : Name) :
    Option (PlacedField profile) :=
  layout.fields.find? (fun placed => placed.field.name == name)

/-- A successful lookup returns the requested nominal field. -/
theorem name_of_lookup? {layout : StructLayout profile} {name : Name}
    {placed : PlacedField profile} (h : layout.lookup? name = some placed) :
    placed.field.name = name := by
  have hmatch : (placed.field.name == name) = true := by
    exact List.find?_some (p := fun candidate : PlacedField profile =>
      candidate.field.name == name) (by simpa [lookup?] using h)
  exact LawfulBEq.eq_of_beq hmatch

/-- A successful lookup returns a placement from the selected field list. -/
theorem mem_of_lookup? {layout : StructLayout profile} {name : Name}
    {placed : PlacedField profile} (h : layout.lookup? name = some placed) :
    placed ∈ layout.fields :=
  List.mem_of_find?_eq_some h

/-- Local validity of one placement within an aggregate. -/
def fieldWellFormed (layout : StructLayout profile)
    (placed : PlacedField profile) : Bool :=
  decide (0 < placed.field.repr.size) &&
  placed.field.repr.wellFormed &&
  decide (IsAligned placed.offset placed.field.repr.alignment) &&
  decide (placed.byteRange.WithinBound layout.size) &&
  decide (layout.alignment % placed.field.repr.alignment = 0)

/-- Ordinary structs are nonempty and every field passes its local placement
check. Empty aggregates and zero-sized fields use their profile-specific
constructors instead of weakening this predicate. -/
def fieldsWellFormed (layout : StructLayout profile) : Bool :=
  decide (layout.fields ≠ []) && layout.fields.all (fieldWellFormed layout)

@[simp] theorem fieldsWellFormed_iff (layout : StructLayout profile) :
    layout.fieldsWellFormed = true ↔
      layout.fields ≠ [] ∧
      layout.fields.all (fieldWellFormed layout) = true := by
  simp [fieldsWellFormed]

/-- Pairwise spatial separation for the ordinary struct constructor. -/
def fieldsDisjoint (layout : StructLayout profile) : Bool :=
  decide (layout.fields.Pairwise fun left right =>
    left.byteRange.Disjoint right.byteRange)

/-- Executable checker for a selected ordinary aggregate layout. -/
def wellFormed (layout : StructLayout profile) : Bool :=
  decide layout.fieldNames.Nodup &&
  decide (0 < layout.alignment) &&
  profile.acceptsAlignment layout.alignment &&
  decide (IsAligned layout.size layout.alignment) &&
  layout.fieldsWellFormed &&
  layout.fieldsDisjoint

/-- Certificate-facing statement for a selected ordinary layout. -/
def WellFormed (layout : StructLayout profile) : Prop := layout.wellFormed = true

instance (layout : StructLayout profile) : Decidable layout.WellFormed :=
  inferInstanceAs (Decidable (layout.wellFormed = true))

/-- Public checker decomposition. Consumers recover the named structural facts
without unfolding `StructLayout.wellFormed`. -/
@[simp] theorem wellFormed_iff (layout : StructLayout profile) :
    layout.WellFormed ↔
      ((((layout.fieldNames.Nodup ∧ 0 < layout.alignment) ∧
        profile.acceptsAlignment layout.alignment = true) ∧
        IsAligned layout.size layout.alignment) ∧
        layout.fieldsWellFormed = true) ∧
        layout.fieldsDisjoint = true := by
  simp [WellFormed, wellFormed]

end StructLayout

end Grass.Construct.Layout
