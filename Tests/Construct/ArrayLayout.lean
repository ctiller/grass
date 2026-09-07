import Grass.Construct.Layout.Array

/-! # Ordinary array-layout fixtures -/

namespace Grass.Tests.Construct.ArrayLayout

open Grass.Construct.Layout Grass.Memory

def profile : LayoutProfile where
  acceptsAlignment := fun alignment => [1, 2, 4, 8, 16].contains alignment

def u32 : ObjectRepr profile := ⟨4, 4⟩

def packed : ArrayLayout profile := ⟨u32, 3, 4⟩
def padded : ArrayLayout profile := ⟨u32, 3, 8⟩

example : packed.WellFormed := by decide
example : packed.size = 12 := rfl
example : padded.WellFormed := by decide
example : padded.size = 24 := rfl
example : padded.elementRange? 2 = some ⟨16, 4⟩ := by decide
example : padded.elementRange? 3 = none := by decide

example : (ByteRange.mk 16 4).WithinBound padded.size :=
  padded.elementRange?_withinBound (index := 2) (range := ⟨16, 4⟩)
    (by decide) (by decide)

example : (ByteRange.mk 0 4).Disjoint ⟨8, 4⟩ :=
  padded.elementRange?_disjoint
    (leftIndex := 0) (rightIndex := 1)
    (leftRange := ⟨0, 4⟩) (rightRange := ⟨8, 4⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def zeroCount : ArrayLayout profile := ⟨u32, 0, 4⟩
example : ¬ zeroCount.WellFormed := by decide

def zeroSizedElement : ArrayLayout profile := ⟨⟨0, 1⟩, 3, 1⟩
example : ¬ zeroSizedElement.WellFormed := by decide

def shortStride : ArrayLayout profile := ⟨u32, 3, 2⟩
example : ¬ shortStride.WellFormed := by decide

def misalignedStride : ArrayLayout profile := ⟨u32, 3, 6⟩
example : ¬ misalignedStride.WellFormed := by decide

end Grass.Tests.Construct.ArrayLayout
