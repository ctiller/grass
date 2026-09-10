import Grass.Std.Logical.Order
import Init.Data.List.Sort

/-! Stable logical sorting for `Vec`.

This module deliberately delegates the algorithm to Lean's proved `List.mergeSort`.
It transports that list algorithm through the logical `Vec` boundary; it does
not model or prove an authored bottom-up runtime loop. -/
namespace Grass.Std.Logical

universe u v

namespace Vec

variable {α : Type u} {β : Type v}

/-- Sort a logical vector with Lean's stable merge sort. -/
def stableSort (le : α → α → Bool) (input : Vec α) : Vec α :=
  Vec.fromList (input.toList.mergeSort le)

/-- The wrapper's list representation is exactly Lean's merge-sort result. -/
@[simp] theorem toList_stableSort (le : α → α → Bool) (input : Vec α) :
    (stableSort le input).toList = input.toList.mergeSort le := rfl

/-- `length_stableSort` computes the unchanged logical length. -/
@[simp] theorem length_stableSort (le : α → α → Bool) (input : Vec α) :
    (stableSort le input).length = input.length :=
  List.length_mergeSort input.toList

/-- Every checked read of the sorted vector is the corresponding checked read
of Lean's merge-sort result, covering both in-range and out-of-range indices. -/
@[simp] theorem get?_stableSort (le : α → α → Bool) (input : Vec α) (index : Nat) :
    (stableSort le input).get? index = (input.toList.mergeSort le)[index]? := rfl

/-- Sorting rearranges but neither loses nor invents logical elements. -/
theorem permutation_stableSort (le : α → α → Bool) (input : Vec α) :
    (stableSort le input).Permutation input :=
  List.mergeSort_perm input.toList le

/-- A transitive, total Boolean comparator orders the result pairwise. -/
theorem pairwise_stableSort (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) (input : Vec α) :
    (stableSort le input).Pairwise (fun a b => le a b = true) :=
  List.pairwise_mergeSort trans total input.toList

/-- An already pairwise-sorted sublist of the input remains a sublist of the
sorted result. -/
theorem sublist_stableSort (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) {input sorted : List α}
    (ordered : sorted.Pairwise (fun a b => le a b = true))
    (contained : sorted.Sublist input) :
    sorted.Sublist (stableSort le (Vec.fromList input)).toList :=
  List.sublist_mergeSort trans total ordered contained

/-- A comparator-ordered input pair remains ordered in the merge-sort output,
which is the local stability fact consumers use for equal-key occurrences. -/
theorem pair_sublist_stableSort (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) {a b : α} {input : Vec α}
    (ordered : le a b = true) (contained : [a, b].Sublist input.toList) :
    [a, b].Sublist (stableSort le input).toList :=
  List.pair_sublist_mergeSort trans total ordered contained

private theorem list_pair_sublist_idxOf?_lt [BEq α] [LawfulBEq α] {output : List α}
    {a b : α} {p q : Nat} (unique : output.Nodup)
    (ordered : [a, b].Sublist output)
    (aPosition : output.idxOf? a = some p) (bPosition : output.idxOf? b = some q) :
    p < q := by
  have pairUnique : [a, b].Nodup := ordered.nodup unique
  have different : a ≠ b := by simpa using pairUnique
  induction output generalizing a b p q with
  | nil => cases ordered
  | cons head tail ih =>
      have tailUnique : tail.Nodup := (List.nodup_cons.mp unique).2
      cases ordered with
      | cons _ pairInTail =>
          have aInTail : a ∈ tail := pairInTail.subset (by simp)
          have bInTail : b ∈ tail := pairInTail.subset (by simp)
          have headNotA : head ≠ a := by
            intro same
            subst head
            exact (List.nodup_cons.mp unique).1 aInTail
          have headNotB : head ≠ b := by
            intro same
            subst head
            exact (List.nodup_cons.mp unique).1 bInTail
          cases aTail : tail.idxOf? a with
          | none => simp [List.idxOf?_cons, aTail,
              beq_eq_false_iff_ne.mpr headNotA] at aPosition
          | some pTail =>
            cases bTail : tail.idxOf? b with
            | none => simp [List.idxOf?_cons, bTail,
                beq_eq_false_iff_ne.mpr headNotB] at bPosition
            | some qTail =>
              simp [List.idxOf?_cons, aTail, bTail,
                beq_eq_false_iff_ne.mpr headNotA,
                beq_eq_false_iff_ne.mpr headNotB] at aPosition bPosition
              subst p
              subst q
              exact Nat.succ_lt_succ (ih tailUnique pairInTail aTail bTail
                (pairInTail.nodup tailUnique) (by simpa using pairInTail.nodup tailUnique))
      | cons_cons _ bInTail =>
          have pZero : p = 0 := by
            simpa [List.idxOf?_cons] using aPosition.symm
          cases bTail : tail.idxOf? b with
          | none =>
              simp [List.idxOf?_cons, bTail,
                beq_eq_false_iff_ne.mpr different] at bPosition
          | some qTail =>
              simp [List.idxOf?_cons, bTail,
                beq_eq_false_iff_ne.mpr different] at bPosition
              subst p
              subst q
              exact Nat.zero_lt_succ _

/-- In a duplicate-free vector, an explicitly ordered pair sublist fixes the
two elements' first-occurrence positions. -/
theorem pair_sublist_idxOf?_lt [BEq α] [LawfulBEq α] {output : Vec α}
    {a b : α} {p q : Nat} (unique : output.toList.Nodup)
    (ordered : [a, b].Sublist output.toList)
    (aPosition : output.idxOf? a = some p) (bPosition : output.idxOf? b = some q) :
    p < q :=
  list_pair_sublist_idxOf?_lt unique ordered aPosition bPosition

/-- `stableSort_idxOf?_lt` retains the first-occurrence order of a comparator-
ordered input pair when the input has no duplicate elements. -/
theorem stableSort_idxOf?_lt [BEq α] [LawfulBEq α] (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) {input : Vec α} {a b : α} {p q : Nat}
    (unique : input.toList.Nodup) (ordered : le a b = true)
    (contained : [a, b].Sublist input.toList)
    (aPosition : (stableSort le input).idxOf? a = some p)
    (bPosition : (stableSort le input).idxOf? b = some q) : p < q := by
  exact pair_sublist_idxOf?_lt
    (output := stableSort le input)
    ((List.mergeSort_perm input.toList le).nodup_iff.mpr unique)
    (pair_sublist_stableSort le trans total ordered contained) aPosition bPosition

/-- Sorting indexed elements and erasing their indices gives the same value
sequence as sorting the values directly. -/
theorem stableSort_zipIdx (le : α → α → Bool) (input : Vec α) :
    (stableSort (List.zipIdxLE le) (Vec.fromList input.toList.zipIdx)).toList.map Prod.fst =
      (stableSort le input).toList :=
  List.mergeSort_zipIdx

/-- Mapping commutes with stable sorting when the two comparators agree for
pairs that actually occur in this input. No global comparator equivalence is
required. -/
theorem map_stableSort (r : α → α → Bool) (s : β → β → Bool) (f : α → β)
    (input : Vec α)
    (agreement : ∀ a ∈ input.toList, ∀ b ∈ input.toList, r a b = s (f a) (f b)) :
    map f (stableSort r input) = stableSort s (map f input) :=
  Vec.toList_injective (List.map_mergeSort agreement)

end Vec
end Grass.Std.Logical
