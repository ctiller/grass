import Grass.Std.Logical.Vec

/-!
# Permutation, pairwise order, and search by position

`Spikes/2_Sort/Spec.lean` is the only place in the corpus where a milestone's
*specification* is written directly over `Vec`, which makes it the sharpest
statement of what this library owes an application author. It reads:

```text
def stableSorted (input output : Vec Occurrence) : Prop :=
  output.Permutation input ∧
  output.Pairwise Occurrence.le ∧
  ∀ i j, i < j -> input[i].value = input[j].value ->
    (output.findIdx? input[i]).get! < (output.findIdx? input[j]).get!
```

Three `Vec` operations appear there and none of them existed: `Permutation`,
`Pairwise`, and a search returning a position. This module supplies them.

## Why these belong here rather than to the sort

`docs/SPIKE_PROOF_BURDEN.md` classifies `stableSortModelCorrect` as
`authority-model` — the algorithm's own theorem — and `stable_merge_pass` as
`authored-proof/library-instance`. Neither is this library's. But the *vocabulary
the specification is written in* is, and it is worth separating: an application
author states what stable sorting means using `Permutation` and `Pairwise`, and
only then does an algorithm have something to be correct against. A sort that
shipped its own private notion of "same elements rearranged" would be proving a
theorem about itself.

`docs/STDLIB.md` §5 names the same vocabulary from the other direction, requiring
whole-element transfers to "derive occurrence, permutation, and initialization
transport from the proved physical copy".

## What `stableSorted` reveals about the authored surface

Two things in that specification do not typecheck against this library, and both
are recorded in `docs/STDLIB_IMPLEMENTATION_PLAN.md` rather than accommodated.

`input[i]` carries no proof that `i` is in range, and the surrounding binder
offers none — `∀ i j, i < j → …` bounds `i` below `j` and nothing above.
`Vec.get` demands the bound and `Vec.get?` returns an `Option`, deliberately, so
that an out-of-range read is not expressible. The specification wants a total
indexing it can write without a proof.

`output.findIdx? input[i]` passes an *element* where `findIdx?` takes a
predicate. The operation it names is `Vec.idxOf?`. Both are supplied below under
their accurate names rather than one being bent to fit the call.
-/

namespace Grass.Std.Logical

namespace Vec

universe u v

variable {α : Type u}

/-!
## Permutation
-/

/--
`v.Permutation w` holds when `v` and `w` contain the same elements with the same
multiplicities, in any order.

Spelled out rather than `Perm`, because `Spikes/2_Sort/Spec.lean` writes
`output.Permutation input` and a specification's vocabulary is the surface this
library exists to serve.
-/
def Permutation (v w : Vec α) : Prop := v.toList.Perm w.toList

@[refl] theorem Permutation.refl (v : Vec α) : v.Permutation v := List.Perm.refl _

theorem Permutation.symm {v w : Vec α} (h : v.Permutation w) : w.Permutation v :=
  List.Perm.symm h

theorem Permutation.trans {u v w : Vec α} (h₁ : u.Permutation v) (h₂ : v.Permutation w) :
    u.Permutation w := List.Perm.trans h₁ h₂

/-- A rearrangement keeps the length. This is the law a sort's caller uses to know
its output buffer is the right size. -/
theorem Permutation.length_eq {v w : Vec α} (h : v.Permutation w) : v.length = w.length :=
  List.Perm.length_eq h

/-- A rearrangement loses and invents nothing. -/
theorem Permutation.mem_iff {v w : Vec α} (h : v.Permutation w) {a : α} :
    a ∈ v ↔ a ∈ w := by
  rw [mem_iff_mem_toList, mem_iff_mem_toList]
  exact List.Perm.mem_iff h

/--
How many times `a` occurs.

Added because `Vec.Permutation`'s docstring promised "the same multiplicities"
and no law mentioned multiplicity at all. Adversarial review showed the gap was
real: a relation defined as "same length and same members" satisfies every one of
`Permutation`'s other laws and accepts `[1,1,2] ↦ [1,2,2]`, which `Permutation`
rejects. Without `Vec.Permutation.count_eq` a caller reasoning only from the
published laws could not rule out a sort that duplicated one line and dropped
another.
-/
def count [BEq α] (v : Vec α) (a : α) : Nat := v.toList.count a

/--
`Vec.Permutation.count_eq`: rearrangement preserves multiplicity.

This is the law that makes `Vec.Permutation` mean what its name says, and the
one that distinguishes it from same-length-same-members.
-/
theorem Permutation.count_eq [BEq α] {v w : Vec α} (h : v.Permutation w) (a : α) :
    v.count a = w.count a :=
  List.Perm.count_eq h a

/-- Equal sequences are trivially rearrangements of each other. -/
theorem Permutation.of_eq {v w : Vec α} (h : v = w) : v.Permutation w := h ▸ Permutation.refl v

/--
Rearrangement is decidable, so a specification that uses it can be checked.

`Tests/Std/StableSort.lean` is why this is here rather than left for later. It
restates `Spikes/2_Sort/Spec.lean`'s `stableSorted` and then discharges it
against a concrete input and output, which needs `decide`. A specification
predicate that no program can evaluate is one no fixture can exercise and no
implementation can test itself against.
-/
instance [DecidableEq α] (v w : Vec α) : Decidable (v.Permutation w) :=
  inferInstanceAs (Decidable (v.toList.Perm w.toList))

/-- Appending on the right respects rearrangement of the left. -/
theorem Permutation.append_right {v w : Vec α} (h : v.Permutation w) (rest : Vec α) :
    (v ++ rest).Permutation (w ++ rest) := by
  simpa [Permutation] using List.Perm.append_right rest.toList h

/-!
## Pairwise order

`docs/STDLIB.md` §3 lists lexicographic comparison among the predicates and this
library still does not have an ordering vocabulary, so `Pairwise` takes the
relation as a parameter rather than assuming one. That is also what
`Spikes/2_Sort/Spec.lean` needs: its order is `ByteStringOrder.lexicographicUnsigned`
lifted through `Occurrence.le`, not a `LE` instance on the element type.
-/

/-- `v.Pairwise R` holds when `R` relates every element to every later one. -/
def Pairwise (R : α → α → Prop) (v : Vec α) : Prop := v.toList.Pairwise R

@[simp] theorem pairwise_empty (R : α → α → Prop) : Pairwise R (empty : Vec α) :=
  List.Pairwise.nil

@[simp] theorem pairwise_singleton (R : α → α → Prop) (a : α) : Pairwise R (singleton a) :=
  List.pairwise_singleton ..

/-- Pairwise order is decidable when its relation is, for the reason given on the
`Vec.Permutation` instance. -/
instance (R : α → α → Prop) [DecidableRel R] (v : Vec α) : Decidable (Pairwise R v) :=
  inferInstanceAs (Decidable (v.toList.Pairwise R))

/--
Pairwise order, by index.

This is the form a sort proof and a sort specification both want, and the reason
it is worth stating separately from `Vec.Pairwise`: the definition is by
structural recursion on the representation, while the obligation a caller
discharges is about positions.
-/
theorem pairwise_iff_get {R : α → α → Prop} (v : Vec α) :
    Pairwise R v ↔
      ∀ (i j : Nat) (hi : i < v.length) (hj : j < v.length), i < j → R (v.get i hi) (v.get j hj) :=
  List.pairwise_iff_getElem

/-- A pairwise-ordered sequence stays ordered when its tail is dropped. -/
theorem Pairwise.take {R : α → α → Prop} {v : Vec α} (h : Pairwise R v) (n : Nat) :
    Pairwise R (v.take n) :=
  List.Pairwise.sublist (List.take_sublist n v.toList) h

/-- And when its head is dropped. -/
theorem Pairwise.drop {R : α → α → Prop} {v : Vec α} (h : Pairwise R v) (n : Nat) :
    Pairwise R (v.drop n) :=
  List.Pairwise.sublist (List.drop_sublist n v.toList) h

/-!
## Search by position

One operation, not two. `Spikes/2_Sort/Spec.lean` writes `output.findIdx? input[i]`
and passes an *element* where a predicate would go, so the operation its
specification means is `idxOf?`. An earlier version of this module supplied a
predicate-taking `findIdx?` alongside it "under accurate names rather than one
being bent to fit the call" -- but nothing demands the predicate version, and
`docs/STDLIB_IMPLEMENTATION_PLAN.md` §1 band 3 is explicit that an undemanded
structure "gets nothing -- not a stub, not a signature, not a placeholder". It was
removed rather than kept for symmetry.
-/

/-- The position of the first occurrence of `a`. -/
def idxOf? [BEq α] (v : Vec α) (a : α) : Option Nat := v.toList.idxOf? a

@[simp] theorem idxOf?_empty [BEq α] (a : α) : idxOf? (empty : Vec α) a = none := rfl

/--
A found position is in range, holds the element searched for, and is the *first*
such position.

The third conjunct is the whole content of the name and was missing: adversarial
review pointed out that a last-occurrence implementation satisfied every law this
operation carried. It is load-bearing rather than tidy -- stability in
`Spikes/2_Sort/Spec.lean`'s `stableSorted` is a claim about where the first
occurrence of a value lands, so a search without it cannot express the
specification it exists for.
-/
theorem idxOf?_eq_some [BEq α] [LawfulBEq α] {v : Vec α} {a : α} {i : Nat}
    (h : idxOf? v a = some i) :
    ∃ hi : i < v.length, v.get i hi = a ∧ ∀ j, j < i → v.get? j ≠ some a := by
  rw [idxOf?, List.idxOf?_eq_some_iff] at h
  obtain ⟨hi, hget, hfirst⟩ := h
  refine ⟨hi, hget, fun j hj hcontra => ?_⟩
  have hjlt : j < v.toList.length := Nat.lt_trans hj hi
  rw [get?, List.getElem?_eq_getElem hjlt] at hcontra
  exact hfirst j hj (Option.some.inj hcontra)


theorem idxOf?_isSome_of_mem [BEq α] [LawfulBEq α] {v : Vec α} {a : α} (h : a ∈ v) :
    (idxOf? v a).isSome := by
  have hmem : a ∈ v.toList := mem_iff_mem_toList.mp h
  have hex : ∃ x, x ∈ v.toList ∧ (x == a) = true := ⟨a, hmem, beq_self_eq_true a⟩
  rw [idxOf?, List.idxOf?, List.findIdx?_eq_some_of_exists hex]
  rfl

end Vec

end Grass.Std.Logical
