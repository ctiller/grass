import Grass.Construct.Placement

/-!
# Logical-field placement fixtures

The fixtures map a padded logical layout to abstract physical locations and
reject missing, duplicate, extra, reordered, and representation-incompatible
assignments.
-/

namespace Grass.Tests.Construct.Placement

open Grass.Core Grass.Construct Grass.Construct.Layout

def profile : LayoutProfile where
  acceptsAlignment := fun alignment => [1, 2, 4, 8].contains alignment

def byte : ObjectRepr profile := ⟨1, 1⟩
def word : ObjectRepr profile := ⟨4, 4⟩

def field (name : String) (repr : ObjectRepr profile) (offset : Nat) :
    PlacedField profile :=
  ⟨⟨⟨name⟩, repr⟩, offset⟩

def layout : StructLayout profile where
  fields := [field "tag" byte 0, field "value" word 4]
  size := 8
  alignment := 4

structure Location where
  slot : Nat
  capacity : Nat
  alignment : Nat
deriving Repr, DecidableEq

def policy : LocationPolicy profile Location where
  accepts := fun repr location =>
    repr.size ≤ location.capacity &&
    location.alignment % repr.alignment == 0

def selected : Placement layout policy where
  fields := [
    ⟨⟨"tag"⟩, ⟨0, 1, 1⟩⟩,
    ⟨⟨"value"⟩, ⟨1, 8, 8⟩⟩
  ]

example : selected.WellFormed := by decide
example : selected.lookup? ⟨"value"⟩ = some ⟨⟨"value"⟩, ⟨1, 8, 8⟩⟩ := by decide
example : (selected.lookup? ⟨"value"⟩).isSome = true ↔
    (⟨"value"⟩ : Name) ∈ selected.fieldNames :=
  selected.lookup?_isSome_iff_mem_fieldNames ⟨"value"⟩
example : ∃ field, selected.lookup? ⟨"value"⟩ = some field :=
  selected.locationForName ⟨"value"⟩ (by decide)
example : layout.WellFormed := selected.layoutWellFormed_of_wellFormed (by decide)
example : selected.fieldNames = layout.fieldNames :=
  selected.fieldNamesExact_of_wellFormed (by decide)
example : selected.FieldsCompatible :=
  selected.fieldsCompatible_of_wellFormed (by decide)
example : ∃ field, selected.lookup? ⟨"tag"⟩ = some field :=
  selected.locationForLayoutField (by decide) ⟨"tag"⟩ (by decide)

def missing : Placement layout policy := {
  selected with fields := [⟨⟨"tag"⟩, ⟨0, 1, 1⟩⟩]
}
example : ¬ missing.WellFormed := by decide

def duplicate : Placement layout policy := {
  selected with fields := [
    ⟨⟨"tag"⟩, ⟨0, 1, 1⟩⟩,
    ⟨⟨"tag"⟩, ⟨1, 8, 8⟩⟩
  ]
}
example : ¬ duplicate.WellFormed := by decide

def extra : Placement layout policy := {
  selected with fields := selected.fields ++ [⟨⟨"other"⟩, ⟨2, 8, 8⟩⟩]
}
example : ¬ extra.WellFormed := by decide

def reordered : Placement layout policy := {
  selected with fields := selected.fields.reverse
}
example : ¬ reordered.WellFormed := by decide

def tooSmall : Placement layout policy := {
  selected with fields := [
    ⟨⟨"tag"⟩, ⟨0, 1, 1⟩⟩,
    ⟨⟨"value"⟩, ⟨1, 2, 8⟩⟩
  ]
}
example : ¬ tooSmall.WellFormed := by decide

def misaligned : Placement layout policy := {
  selected with fields := [
    ⟨⟨"tag"⟩, ⟨0, 1, 1⟩⟩,
    ⟨⟨"value"⟩, ⟨1, 8, 2⟩⟩
  ]
}
example : ¬ misaligned.WellFormed := by decide

end Grass.Tests.Construct.Placement
