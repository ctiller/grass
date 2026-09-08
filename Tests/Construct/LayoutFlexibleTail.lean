import Grass.Construct.Layout.FlexibleTail

namespace Grass.Tests.Construct.LayoutFlexibleTail

open Grass Grass.Core Grass.Construct.Layout

private def profile : LayoutProfile :=
  ⟨fun alignment => alignment = 1 || alignment = 4 || alignment = 8⟩

private def prefixField : FieldSpec profile :=
  ⟨⟨"length"⟩, ⟨8, 8⟩⟩

private def head : StructLayout profile :=
  ⟨[⟨prefixField, 0⟩], 8, 8⟩

private def valid : FlexibleTailLayout profile :=
  ⟨head, ⟨4, 4⟩, 8, 4, 3, 24, 8⟩

example : valid.WellFormed := by native_decide
example : valid.reservedRange = ⟨8, 16⟩ := by native_decide
example : valid.selectedRange = ⟨8, 12⟩ := by native_decide
example : valid.elementRange? 0 = some ⟨8, 4⟩ := by native_decide
example : valid.elementRange? 2 = some ⟨16, 4⟩ := by native_decide
example : valid.elementRange? 3 = none := by native_decide
example : (valid.selectCount? 4).isSome = true := by native_decide
example : valid.selectCount? 5 = none := by native_decide
example : valid.reservedRange.Contains valid.selectedRange :=
  valid.selectedRange_within_reservedRange (by native_decide)
example : valid.selectedRange.WithinBound valid.size :=
  valid.selectedRange_withinBound (by native_decide)
example : valid.selectedRange.Contains ⟨16, 4⟩ :=
  valid.elementRange?_within_selectedRange (index := 2) (by native_decide)
example : ({ valid with selectedCount := 4 }).WellFormed :=
  valid.selectCount?_wellFormed { valid with selectedCount := 4 }
    (by native_decide) 4 (by native_decide)

private def overCapacity : FlexibleTailLayout profile :=
  { valid with selectedCount := 5 }
example : ¬ overCapacity.WellFormed := by native_decide

private def overlapsPrefix : FlexibleTailLayout profile :=
  { valid with tailOffset := 4, size := 24 }
example : ¬ overlapsPrefix.WellFormed := by native_decide

private def wrongExtent : FlexibleTailLayout profile :=
  { valid with size := 32 }
example : ¬ wrongExtent.WellFormed := by native_decide

private def weakAlignment : FlexibleTailLayout profile :=
  { valid with alignment := 4 }
example : ¬ weakAlignment.WellFormed := by native_decide

private def misalignedTail : FlexibleTailLayout profile :=
  { valid with tailOffset := 10, size := 24 }
example : ¬ misalignedTail.WellFormed := by native_decide

private def invalidElement : FlexibleTailLayout profile :=
  { valid with element := ⟨4, 2⟩ }
example : ¬ invalidElement.WellFormed := by native_decide

end Grass.Tests.Construct.LayoutFlexibleTail
