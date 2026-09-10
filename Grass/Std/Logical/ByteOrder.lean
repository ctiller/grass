import Grass.Std.Logical.Vec
import Init.Data.List.Lex

/-!
# Unsigned lexicographic byte order

This module orders logical byte arrays by their byte values. Comparison is
lexicographic, an exhausted prefix comes first, and equal arrays compare less
than or equal. Bytes are converted to naturals explicitly, so this order has no
text encoding or locale interpretation.
-/

namespace Grass.Std.Logical.ByteArray

/-- Unsigned lexicographic less-than-or-equal on logical byte arrays. -/
def lexicographicLE (left right : ByteArray) : Bool :=
  decide (left.toList.map BitVec.toNat ≤ right.toList.map BitVec.toNat)

@[simp] theorem lexicographicLE_refl (bytes : ByteArray) :
    lexicographicLE bytes bytes = true := by
  simp [lexicographicLE]

theorem lexicographicLE_trans {left middle right : ByteArray}
    (hlm : lexicographicLE left middle = true)
    (hmr : lexicographicLE middle right = true) :
    lexicographicLE left right = true := by
  simp only [lexicographicLE, decide_eq_true_eq] at hlm hmr ⊢
  exact List.le_trans hlm hmr

theorem lexicographicLE_total (left right : ByteArray) :
    lexicographicLE left right = true ∨ lexicographicLE right left = true := by
  simp only [lexicographicLE, decide_eq_true_eq]
  exact Std.le_total

@[simp] theorem lexicographicLE_empty_left (right : ByteArray) :
    lexicographicLE Vec.empty right = true := by
  simp [lexicographicLE]

@[simp] theorem lexicographicLE_empty_right {left : ByteArray} :
    lexicographicLE left Vec.empty = true ↔ left = Vec.empty := by
  cases left with
  | fromList bytes => cases bytes <;> simp [lexicographicLE, Vec.empty]

/-- Adding the same prefix to both inputs does not affect their comparison. -/
theorem lexicographicLE_common_prefix (pre left right : List Byte) :
    lexicographicLE (Vec.fromList (pre ++ left)) (Vec.fromList (pre ++ right)) =
      lexicographicLE (Vec.fromList left) (Vec.fromList right) := by
  induction pre with
  | nil => rfl
  | cons byte rest ih =>
    simp only [List.cons_append, lexicographicLE, List.map_append,
      List.map_cons, decide_eq_decide] at ih ⊢
    rw [List.cons_le_cons_iff]
    simp only [Nat.lt_irrefl, false_or, true_and]
    exact ih

/-- At the first differing byte, unsigned numeric byte order decides the result. -/
theorem lexicographicLE_first_difference (pre leftTail rightTail : List Byte)
    {leftByte rightByte : Byte} (hne : leftByte ≠ rightByte) :
    lexicographicLE
        (Vec.fromList (pre ++ leftByte :: leftTail))
        (Vec.fromList (pre ++ rightByte :: rightTail)) =
      decide (leftByte.toNat < rightByte.toNat) := by
  rw [lexicographicLE_common_prefix]
  simp only [lexicographicLE, List.map_cons, decide_eq_decide]
  rw [List.cons_le_cons_iff]
  constructor
  · intro h
    rcases h with h | ⟨h, -⟩
    · exact h
    · exact (hne (BitVec.eq_of_toNat_eq h)).elim
  · exact Or.inl

end Grass.Std.Logical.ByteArray
