import Grass.Construct.Layout.Core

/-!
# Explicit untagged union layouts

An untagged union deliberately overlays every alternative at byte offset zero.
`UnionLayout.wellFormed` therefore checks each representation against the same
storage range instead of weakening `StructLayout.FieldsDisjoint`. Selecting and
tracking a live alternative is a separate typed-value obligation; this module
only certifies the physical storage choice.
-/

namespace Grass.Construct.Layout

open Grass.Core Grass.Memory

/-- Explicit shared storage for a nonempty family of named alternatives. -/
structure UnionLayout (profile : LayoutProfile) where
  variants : List (FieldSpec profile)
  size : Nat
  alignment : Nat
deriving Repr, DecidableEq

namespace UnionLayout

variable {profile : LayoutProfile}

/-- Nominal alternatives in declaration order. -/
def variantNames (layout : UnionLayout profile) : List Name :=
  layout.variants.map (fun variant => variant.name)

/-- Find a union alternative by its nominal name. -/
def lookup? (layout : UnionLayout profile) (name : Name) :
    Option (FieldSpec profile) :=
  layout.variants.find? (fun variant => variant.name == name)

/-- A successful lookup returns a declared alternative with the requested name. -/
theorem lookup?_sound (layout : UnionLayout profile) (name : Name)
    (variant : FieldSpec profile) (h : layout.lookup? name = some variant) :
    variant ∈ layout.variants ∧ variant.name = name := by
  constructor
  · exact List.mem_of_find?_eq_some (by simpa [lookup?] using h)
  · have matched : variant.name == name := List.find?_some
      (p := fun candidate : FieldSpec profile => candidate.name == name) (by
        simpa [lookup?] using h)
    exact LawfulBEq.eq_of_beq matched

@[simp] theorem lookup?_isSome_iff_mem_variantNames
    (layout : UnionLayout profile) (name : Name) :
    (layout.lookup? name).isSome = true ↔ name ∈ layout.variantNames := by
  simp [lookup?, variantNames]

/-- Every declared union name has a concrete alternative lookup result. -/
theorem variantForName (layout : UnionLayout profile) (name : Name)
    (member : name ∈ layout.variantNames) :
    ∃ variant, layout.lookup? name = some variant := by
  apply Option.isSome_iff_exists.mp
  exact (layout.lookup?_isSome_iff_mem_variantNames name).2 member

/-- Exact byte range occupied when this alternative is live. -/
def variantRange (variant : FieldSpec profile) : ByteRange :=
  ⟨0, variant.repr.size⟩

/-- Executable validity check for one alternative against the shared storage. -/
def variantWellFormed (layout : UnionLayout profile)
    (variant : FieldSpec profile) : Bool :=
  decide (0 < variant.repr.size) &&
  variant.repr.wellFormed &&
  decide ((variantRange variant).WithinBound layout.size) &&
  decide (layout.alignment % variant.repr.alignment = 0)

/-- Proposition-level representation, capacity, and alignment obligations for one alternative. -/
def VariantWellFormed (layout : UnionLayout profile)
    (variant : FieldSpec profile) : Prop :=
  0 < variant.repr.size ∧
  variant.repr.WellFormed ∧
  (variantRange variant).WithinBound layout.size ∧
  layout.alignment % variant.repr.alignment = 0

@[simp] theorem variantWellFormed_eq_true_iff
    (layout : UnionLayout profile) (variant : FieldSpec profile) :
    layout.variantWellFormed variant = true ↔
      layout.VariantWellFormed variant := by
  simp [variantWellFormed, VariantWellFormed, ObjectRepr.WellFormed, and_assoc]

/-- Proposition-level validity of every declared union alternative. -/
def VariantsWellFormed (layout : UnionLayout profile) : Prop :=
  ∀ variant ∈ layout.variants, layout.VariantWellFormed variant

@[simp] theorem variantsAll_eq_true_iff (layout : UnionLayout profile) :
    layout.variants.all layout.variantWellFormed = true ↔
      layout.VariantsWellFormed := by
  simp [VariantsWellFormed]

/-- Executable checker for an explicit untagged union storage choice. -/
def wellFormed (layout : UnionLayout profile) : Bool :=
  decide (layout.variants ≠ []) &&
  decide layout.variantNames.Nodup &&
  decide (0 < layout.alignment) &&
  profile.acceptsAlignment layout.alignment &&
  decide (IsAligned layout.size layout.alignment) &&
  layout.variants.all layout.variantWellFormed

/-- Certificate-facing statement for an explicit untagged union layout. -/
def WellFormed (layout : UnionLayout profile) : Prop :=
  layout.wellFormed = true

instance (layout : UnionLayout profile) : Decidable layout.WellFormed :=
  inferInstanceAs (Decidable (layout.wellFormed = true))

/-- Public decomposition of every storage obligation checked for an untagged union. -/
@[simp] theorem wellFormed_iff (layout : UnionLayout profile) :
    layout.WellFormed ↔
      (((((layout.variants ≠ [] ∧ layout.variantNames.Nodup) ∧
        0 < layout.alignment) ∧
        profile.acceptsAlignment layout.alignment = true) ∧
        IsAligned layout.size layout.alignment) ∧
        layout.VariantsWellFormed) := by
  simp [WellFormed, wellFormed, VariantsWellFormed]

/-- A valid union has no duplicate nominal alternatives. -/
theorem variantNamesNodup_of_wellFormed (layout : UnionLayout profile)
    (h : layout.WellFormed) : layout.variantNames.Nodup := by
  rcases (wellFormed_iff layout).mp h with
    ⟨⟨⟨⟨⟨_, names⟩, _⟩, _⟩, _⟩, _⟩
  exact names

/-- Every alternative in a valid union satisfies its representation and storage obligations. -/
theorem variantsWellFormed_of_wellFormed (layout : UnionLayout profile)
    (h : layout.WellFormed) : layout.VariantsWellFormed :=
  (wellFormed_iff layout).mp h |>.2

/-- Every alternative in a valid union fits inside the selected shared storage. -/
theorem variantWithinStorage_of_wellFormed (layout : UnionLayout profile)
    (h : layout.WellFormed) (variant : FieldSpec profile)
    (member : variant ∈ layout.variants) :
    (variantRange variant).WithinBound layout.size :=
  (layout.variantsWellFormed_of_wellFormed h variant member).2.2.1

/-- The selected union alignment is compatible with every declared alternative. -/
theorem alignmentSupportsVariant_of_wellFormed (layout : UnionLayout profile)
    (h : layout.WellFormed) (variant : FieldSpec profile)
    (member : variant ∈ layout.variants) :
    layout.alignment % variant.repr.alignment = 0 :=
  (layout.variantsWellFormed_of_wellFormed h variant member).2.2.2

end UnionLayout

end Grass.Construct.Layout
