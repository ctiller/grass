import Grass.Construct.Layout.Packed

namespace Grass.Tests.Construct.LayoutPacked

open Grass Grass.Core Grass.Construct.Layout

private def profile : LayoutProfile :=
  ⟨fun alignment => alignment = 1 || alignment = 4⟩

private def field (name : String) (size alignment offset : Nat) :
    PlacedField profile :=
  ⟨⟨⟨name⟩, ⟨size, alignment⟩⟩, offset⟩

private def tag := field "tag" 1 1 0
private def payload := field "payload" 4 4 1

private def valid : PackedLayout profile :=
  ⟨[tag, payload], 5, 1⟩

example : valid.WellFormed := by decide
example : PackedLayout.requiresUnalignedAccess payload = true := by decide
example : valid.lookup? ⟨"payload"⟩ = some payload := by decide

private def overlap : PackedLayout profile :=
  ⟨[field "a" 2 1 0, field "b" 2 1 1], 4, 1⟩
example : ¬ overlap.WellFormed := by decide

private def outside : PackedLayout profile :=
  ⟨[field "a" 4 4 2], 5, 1⟩
example : ¬ outside.WellFormed := by decide

private def duplicate : PackedLayout profile :=
  ⟨[field "a" 1 1 0, field "a" 1 1 1], 2, 1⟩
example : ¬ duplicate.WellFormed := by decide

private def invalidRepr : PackedLayout profile :=
  ⟨[field "a" 1 2 0], 1, 1⟩
example : ¬ invalidRepr.WellFormed := by decide

end Grass.Tests.Construct.LayoutPacked
