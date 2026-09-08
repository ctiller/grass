import Grass.Construct.Layout.Bitfield

namespace Grass.Tests.Construct.LayoutBitfield

open Grass Grass.Core Grass.Construct.Layout

private def profile : LayoutProfile := ⟨fun alignment => alignment = 1 || alignment = 4⟩
private def field (name : String) (start width : Nat) : BitField :=
  ⟨⟨name⟩, ⟨start, width⟩⟩

private def valid : BitfieldLayout profile :=
  ⟨[field "tag" 0 3, field "mode" 3 5, field "payload" 8 24], 4, 4⟩

example : valid.WellFormed := by native_decide
example : valid.lookup? ⟨"mode"⟩ = some (field "mode" 3 5) := by native_decide
example : (valid.lookup? ⟨"mode"⟩).isSome = true ↔
    (⟨"mode"⟩ : Name) ∈ valid.fieldNames :=
  valid.lookup?_isSome_iff_mem_fieldNames ⟨"mode"⟩
example : ∃ selected, valid.lookup? ⟨"payload"⟩ = some selected :=
  valid.fieldForName ⟨"payload"⟩ (by native_decide)
example : valid.FieldsWellFormed := valid.fieldsWellFormed_of_wellFormed (by native_decide)
example : valid.FieldsDisjoint := valid.fieldsDisjoint_of_wellFormed (by native_decide)
example : valid.fields ≠ [] := valid.fieldsNonempty_of_wellFormed (by native_decide)
example : 0 < valid.storageSize := valid.storageSizePositive_of_wellFormed (by native_decide)
example : 0 < valid.alignment :=
  valid.aggregateAlignmentPositive_of_wellFormed (by native_decide)
example : profile.acceptsAlignment valid.alignment = true :=
  valid.profileAcceptsAlignment_of_wellFormed (by native_decide)
example : Grass.Memory.IsAligned valid.storageSize valid.alignment :=
  valid.storageSizeAligned_of_wellFormed (by native_decide)
example : (field "payload" 8 24).range.stop ≤ valid.storageSize * 8 :=
  valid.fieldWithinStorage_of_wellFormed (by native_decide)
    (field "payload" 8 24) (by native_decide)
example : 0 < (field "payload" 8 24).range.width :=
  valid.fieldWidthPositive_of_wellFormed (by native_decide)
    (field "payload" 8 24) (by native_decide)
example : valid.lookup? (field "payload" 8 24).name = some (field "payload" 8 24) :=
  valid.lookup?_eq_some_of_mem (field "payload" 8 24).name
    (field "payload" 8 24) (by native_decide) (by native_decide) rfl
example (left right : BitField)
    (leftMem : left ∈ valid.fields) (rightMem : right ∈ valid.fields)
    (sameName : left.name = right.name) : left = right :=
  valid.field_eq_of_mem_of_mem_of_name_eq left right
    (by native_decide) leftMem rightMem sameName
example : (field "mode" 3 5).range.Disjoint (field "tag" 0 3).range :=
  BitRange.Disjoint.symm (by native_decide)

private def overlap : BitfieldLayout profile :=
  ⟨[field "a" 0 5, field "b" 4 4], 4, 4⟩
example : ¬ overlap.WellFormed := by native_decide

private def outside : BitfieldLayout profile :=
  ⟨[field "a" 31 2], 4, 4⟩
example : ¬ outside.WellFormed := by native_decide

private def zeroWidth : BitfieldLayout profile :=
  ⟨[field "a" 0 0], 4, 4⟩
example : ¬ zeroWidth.WellFormed := by native_decide

private def duplicate : BitfieldLayout profile :=
  ⟨[field "a" 0 4, field "a" 4 4], 4, 4⟩
example : ¬ duplicate.WellFormed := by native_decide

private def empty : BitfieldLayout profile :=
  ⟨[], 4, 4⟩
example : ¬ empty.WellFormed := by native_decide

private def rejectedAlignment : BitfieldLayout profile :=
  ⟨[field "a" 0 8], 4, 2⟩
example : ¬ rejectedAlignment.WellFormed := by native_decide

private def badStorageAlignment : BitfieldLayout profile :=
  ⟨[field "a" 0 8], 3, 4⟩
example : ¬ badStorageAlignment.WellFormed := by native_decide

end Grass.Tests.Construct.LayoutBitfield
