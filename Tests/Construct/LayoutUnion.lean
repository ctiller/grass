import Grass.Construct.Layout.Union

namespace Grass.Tests.Construct.LayoutUnion

open Grass Grass.Core Grass.Memory Grass.Construct.Layout

private def profile : LayoutProfile :=
  ⟨fun alignment => alignment = 1 || alignment = 4 || alignment = 8⟩

private def variant (name : String) (size alignment : Nat) : FieldSpec profile :=
  ⟨⟨name⟩, ⟨size, alignment⟩⟩

private def word := variant "word" 4 4
private def wide := variant "wide" 8 8
private def bytes := variant "bytes" 3 1

private def valid : UnionLayout profile :=
  ⟨[word, wide, bytes], 8, 8⟩

example : valid.WellFormed := by native_decide
example : valid.lookup? ⟨"wide"⟩ = some wide := by native_decide
example : (valid.lookup? ⟨"bytes"⟩).isSome = true ↔
    (⟨"bytes"⟩ : Name) ∈ valid.variantNames :=
  valid.lookup?_isSome_iff_mem_variantNames ⟨"bytes"⟩
example : ∃ selected, valid.lookup? ⟨"word"⟩ = some selected :=
  valid.variantForName ⟨"word"⟩ (by native_decide)
example : valid.VariantsWellFormed :=
  valid.variantsWellFormed_of_wellFormed (by native_decide)
example : valid.variantNames.Nodup :=
  valid.variantNamesNodup_of_wellFormed (by native_decide)
example : (UnionLayout.variantRange word).start = 0 := rfl
example : (UnionLayout.variantRange wide).WithinBound valid.size :=
  valid.variantWithinStorage_of_wellFormed (by native_decide) wide (by native_decide)
example : valid.alignment % word.repr.alignment = 0 :=
  valid.alignmentSupportsVariant_of_wellFormed (by native_decide) word (by native_decide)

private def empty : UnionLayout profile :=
  ⟨[], 8, 8⟩
example : ¬ empty.WellFormed := by native_decide

private def duplicate : UnionLayout profile :=
  ⟨[variant "same" 4 4, variant "same" 8 8], 8, 8⟩
example : ¬ duplicate.WellFormed := by native_decide

private def zeroSize : UnionLayout profile :=
  ⟨[variant "zero" 0 1], 1, 1⟩
example : ¬ zeroSize.WellFormed := by native_decide

private def invalidRepresentation : UnionLayout profile :=
  ⟨[variant "bad" 4 2], 8, 8⟩
example : ¬ invalidRepresentation.WellFormed := by native_decide

private def tooSmall : UnionLayout profile :=
  ⟨[wide], 4, 4⟩
example : ¬ tooSmall.WellFormed := by native_decide

private def weakAlignment : UnionLayout profile :=
  ⟨[wide], 8, 4⟩
example : ¬ weakAlignment.WellFormed := by native_decide

private def rejectedAlignment : UnionLayout profile :=
  ⟨[word], 4, 2⟩
example : ¬ rejectedAlignment.WellFormed := by native_decide

private def badStorageAlignment : UnionLayout profile :=
  ⟨[word], 6, 4⟩
example : ¬ badStorageAlignment.WellFormed := by native_decide

end Grass.Tests.Construct.LayoutUnion
