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

example : valid.WellFormed := by decide
example : valid.lookup? ⟨"payload"⟩ = some payload := by decide
example : valid.lookup? ⟨"missing"⟩ = none := by decide
example : OverlayLayout.memberRange tag = ⟨0, 4⟩ := by decide
example : OverlayLayout.memberRange payload = ⟨0, 8⟩ := by decide

private def empty : OverlayLayout profile := ⟨[], 8, 8⟩
example : ¬ empty.WellFormed := by decide

private def duplicate : OverlayLayout profile :=
  ⟨[tag, { payload with name := tag.name }], 8, 8⟩
example : ¬ duplicate.WellFormed := by decide

private def tooSmall : OverlayLayout profile :=
  ⟨[tag, payload], 4, 4⟩
example : ¬ tooSmall.WellFormed := by decide

private def weakAlignment : OverlayLayout profile :=
  ⟨[tag, payload], 8, 4⟩
example : ¬ weakAlignment.WellFormed := by decide

private def invalidMember : OverlayLayout profile :=
  ⟨[tag, member "bad" 8 2], 8, 8⟩
example : ¬ invalidMember.WellFormed := by decide

private def misalignedTail : OverlayLayout profile :=
  ⟨[tag], 6, 4⟩
example : ¬ misalignedTail.WellFormed := by decide

end Grass.Tests.Construct.LayoutOverlay
