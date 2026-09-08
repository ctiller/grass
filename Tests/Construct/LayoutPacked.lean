import Grass.Construct.Layout.Packed

namespace Grass.Tests.Construct.LayoutPacked

open Grass Grass.Core Grass.Memory Grass.Construct.Layout

private def profile : LayoutProfile :=
  ⟨fun alignment => alignment = 1 || alignment = 4⟩

private def field (name : String) (size alignment offset : Nat) :
    PlacedField profile :=
  ⟨⟨⟨name⟩, ⟨size, alignment⟩⟩, offset⟩

private def tag := field "tag" 1 1 0
private def payload := field "payload" 4 4 1

private def valid : PackedLayout profile :=
  ⟨[tag, payload], 5, 1⟩

example : valid.WellFormed := by native_decide
example : PackedLayout.requiresUnalignedAccess payload = true := by native_decide
example : valid.lookup? ⟨"payload"⟩ = some payload := by native_decide
example : (valid.lookup? ⟨"payload"⟩).isSome = true ↔
    (⟨"payload"⟩ : Name) ∈ valid.fieldNames :=
  valid.lookup?_isSome_iff_mem_fieldNames ⟨"payload"⟩
example : ∃ placed, valid.lookup? ⟨"tag"⟩ = some placed :=
  valid.fieldForName ⟨"tag"⟩ (by native_decide)
example : valid.FieldsWellFormed := valid.fieldsWellFormed_of_wellFormed (by native_decide)
example : valid.FieldsDisjoint := valid.fieldsDisjoint_of_wellFormed (by native_decide)
example : payload.byteRange.WithinBound valid.size :=
  valid.fieldWithinStorage_of_wellFormed (by native_decide) payload (by native_decide)
example : ¬IsAligned payload.offset payload.field.repr.alignment :=
  (PackedLayout.requiresUnalignedAccess_eq_true_iff payload).mp (by native_decide)

private def overlap : PackedLayout profile :=
  ⟨[field "a" 2 1 0, field "b" 2 1 1], 4, 1⟩
example : ¬ overlap.WellFormed := by native_decide

private def outside : PackedLayout profile :=
  ⟨[field "a" 4 4 2], 5, 1⟩
example : ¬ outside.WellFormed := by native_decide

private def duplicate : PackedLayout profile :=
  ⟨[field "a" 1 1 0, field "a" 1 1 1], 2, 1⟩
example : ¬ duplicate.WellFormed := by native_decide

private def invalidRepr : PackedLayout profile :=
  ⟨[field "a" 1 2 0], 1, 1⟩
example : ¬ invalidRepr.WellFormed := by native_decide

private def empty : PackedLayout profile :=
  ⟨[], 1, 1⟩
example : ¬ empty.WellFormed := by native_decide

private def zeroSize : PackedLayout profile :=
  ⟨[field "a" 0 1 0], 1, 1⟩
example : ¬ zeroSize.WellFormed := by native_decide

private def rejectedAlignment : PackedLayout profile :=
  ⟨[field "a" 1 1 0], 2, 2⟩
example : ¬ rejectedAlignment.WellFormed := by native_decide

private def badAggregateAlignment : PackedLayout profile :=
  ⟨[field "a" 1 1 0], 3, 4⟩
example : ¬ badAggregateAlignment.WellFormed := by native_decide

end Grass.Tests.Construct.LayoutPacked
