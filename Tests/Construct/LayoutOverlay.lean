import Grass.Construct.Layout.Overlay

namespace Grass.Tests.Construct.LayoutOverlay

open Grass Grass.Core Grass.Construct.Layout

private def profile : LayoutProfile :=
  ⟨fun alignment => alignment = 1 || alignment = 4 || alignment = 8⟩

private def member (name : String) (size alignment : Nat) : FieldSpec profile :=
  ⟨⟨name⟩, ⟨size, alignment⟩⟩

private def tag := member "tag" 4 4
private def payload := member "payload" 8 8

private def valid : OverlayLayout profile :=
  ⟨[tag, payload], 8, 8⟩

example : valid.WellFormed := by native_decide
example : valid.lookup? ⟨"payload"⟩ = some payload := by native_decide
example : valid.lookup? ⟨"missing"⟩ = none := by native_decide
example : OverlayLayout.memberRange tag = ⟨0, 4⟩ := by native_decide
example : OverlayLayout.memberRange payload = ⟨0, 8⟩ := by native_decide
example : (valid.lookup? ⟨"payload"⟩).isSome = true ↔
    (⟨"payload"⟩ : Name) ∈ valid.memberNames :=
  valid.lookup?_isSome_iff_mem_memberNames ⟨"payload"⟩
example : ∃ field, valid.lookup? ⟨"payload"⟩ = some field :=
  valid.memberForName ⟨"payload"⟩ (by native_decide)
example : valid.memberNames.Nodup := valid.memberNamesNodup_of_wellFormed (by native_decide)
example : valid.MembersWellFormed := valid.membersWellFormed_of_wellFormed (by native_decide)
example : valid.MemberWellFormed payload :=
  valid.memberWellFormed_of_wellFormed (by native_decide) payload (by native_decide)
example : 0 < payload.repr.size :=
  valid.memberSizePositive_of_wellFormed (by native_decide) payload (by native_decide)
example : payload.repr.WellFormed :=
  valid.memberReprWellFormed_of_wellFormed (by native_decide) payload (by native_decide)
example : (OverlayLayout.memberRange payload).WithinBound valid.size :=
  valid.memberRangeWithinStorage_of_wellFormed
    (by native_decide) payload (by native_decide)
example : valid.lookup? payload.name = some payload :=
  valid.lookup?_eq_some_of_mem payload.name payload
    (by native_decide) (by native_decide) rfl
example (left right : FieldSpec profile)
    (leftMem : left ∈ valid.members) (rightMem : right ∈ valid.members)
    (sameName : left.name = right.name) : left = right :=
  valid.member_eq_of_mem_of_mem_of_name_eq left right
    (by native_decide) leftMem rightMem sameName
example : Grass.Memory.IsAligned valid.size valid.alignment :=
  valid.sizeAligned_of_wellFormed (by native_decide)

private def empty : OverlayLayout profile := ⟨[], 8, 8⟩
example : ¬ empty.WellFormed := by native_decide

private def duplicate : OverlayLayout profile :=
  ⟨[tag, { payload with name := tag.name }], 8, 8⟩
example : ¬ duplicate.WellFormed := by native_decide

private def tooSmall : OverlayLayout profile :=
  ⟨[tag, payload], 4, 4⟩
example : ¬ tooSmall.WellFormed := by native_decide

private def weakAlignment : OverlayLayout profile :=
  ⟨[tag, payload], 8, 4⟩
example : ¬ weakAlignment.WellFormed := by native_decide

private def invalidMember : OverlayLayout profile :=
  ⟨[tag, member "bad" 8 2], 8, 8⟩
example : ¬ invalidMember.WellFormed := by native_decide

private def misalignedTail : OverlayLayout profile :=
  ⟨[tag], 6, 4⟩
example : ¬ misalignedTail.WellFormed := by native_decide

end Grass.Tests.Construct.LayoutOverlay
