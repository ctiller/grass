import Grass.Construct.Layout.DynamicStack

namespace Grass.Tests.Construct.LayoutDynamicStack

open Grass Grass.Core Grass.Construct.Layout

private def profile : LayoutProfile :=
  ⟨fun alignment => alignment = 1 || alignment = 4 || alignment = 8⟩

private def root : ScopeId := ⟨⟨"root"⟩⟩

private def fixedRepr : ObjectRepr profile := ⟨8, 8⟩

private def fixedObject : StackObject profile :=
  ⟨⟨"fixed"⟩, fixedRepr, 0, root⟩

private def fixed : StackLayout profile :=
  ⟨[⟨root, none⟩], [fixedObject], 32, 8, 64⟩

private def dynamicObject : DynamicStackObject profile :=
  ⟨⟨"dynamic"⟩, 8, 16, 5, 8, root⟩

private def valid : BoundedStackLayout profile :=
  ⟨fixed, [dynamicObject]⟩

example : valid.WellFormed := by native_decide

example : dynamicObject.reservedRange.Contains dynamicObject.selectedRange := by
  exact dynamicObject.reservedRange_contains_selectedRange (by decide)

example : (dynamicObject.selectSize? 16).isSome = true := by native_decide

example : dynamicObject.selectSize? 17 = none := by native_decide

example : dynamicObject.selectSize? 0 =
    some { dynamicObject with selectedSize := 0 } := by native_decide

private def overCapacity : BoundedStackLayout profile :=
  ⟨fixed, [{ dynamicObject with selectedSize := 17 }]⟩

example : ¬ overCapacity.WellFormed := by native_decide

private def overlapsFixed : BoundedStackLayout profile :=
  ⟨fixed, [{ dynamicObject with offset := 4 }]⟩

example : ¬ overlapsFixed.WellFormed := by native_decide

private def overlapsDynamic : BoundedStackLayout profile :=
  ⟨fixed, [dynamicObject, { dynamicObject with name := ⟨"second"⟩, offset := 16 }]⟩

example : ¬ overlapsDynamic.WellFormed := by native_decide

private def duplicateFixedName : BoundedStackLayout profile :=
  ⟨fixed, [{ dynamicObject with name := fixedObject.name }]⟩

example : ¬ duplicateFixedName.WellFormed := by native_decide

private def outsideFrame : BoundedStackLayout profile :=
  ⟨fixed, [{ dynamicObject with offset := 24 }]⟩

example : ¬ outsideFrame.WellFormed := by native_decide

private def unknownScope : BoundedStackLayout profile :=
  ⟨fixed, [{ dynamicObject with scope := ⟨⟨"missing"⟩⟩ }]⟩

example : ¬ unknownScope.WellFormed := by native_decide

end Grass.Tests.Construct.LayoutDynamicStack
