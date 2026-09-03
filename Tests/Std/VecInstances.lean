import Grass.Std.Logical.Vec

/-!
# `Vec` behaves like a container at the use site

`Grass/Std/Logical/Vec.lean` proves that a `Vec` has extensional equality. That
is a proof rule. This fixture checks the other thing a consumer needs, which no
theorem states: that the notation and the instances a Lean author reaches for
without thinking actually work on one.

The reason to check it rather than assume it is the module comment's own
argument. `Vec` is a private structure precisely so that consumers write `Vec`'s
API instead of `List`'s. That trade is only worth making if `Vec`'s API is
complete enough to write against; a container that cannot be compared, indexed
with `v[i]`, or printed pushes its users back to `Vec.toList`, which is the leak
the structure was chosen to prevent.
-/

namespace Grass.Tests.Std.Instances

open Grass.Std.Logical

/-! ## Indexing notation

`docs/STDLIB.md` §3 asks for a checked accessor and a bounded one. Lean's `v[i]?`
and `v[i]` are exactly that pair, and `Vec.getElem?_eq_get?` and
`Vec.getElem_eq_get` pin that the notation means those accessors.
-/

def digits : Vec Nat := Vec.fromList [10, 20, 30]

example : digits[1]? = some 20 := rfl
example : digits[5]? = none := rfl
example : digits[1] = 20 := rfl

/-- The bounded form still carries its proof; there is no default element. -/
example (v : Vec Nat) (h : 0 < v.length) : v[0] = v.get 0 h := rfl

/-- And the notation is the accessor, not a parallel implementation. -/
example (v : Vec Nat) (i : Nat) : v[i]? = v.get? i := Vec.getElem?_eq_get? v i

/-! ## Iteration

`docs/STDLIB.md` §3 lists iteration among the observations. `Vec` had no `ForIn`
until adversarial review found the gap — which this fixture had missed while
claiming to check "the notation and instances a Lean author reaches for without
thinking", and `for` is the archetype. Pinned here so the gap cannot reopen.
-/

example : Id.run (do
    let mut total := 0
    for x in digits do
      total := total + x
    return total) = 60 := rfl

/-- Iteration is in index order, not some other order. A sum would not detect a
permutation, so this accumulates asymmetrically. -/
example : Id.run (do
    let mut acc : List Nat := []
    for x in digits do
      acc := x :: acc
    return acc) = [30, 20, 10] := rfl

/-! ## Decidable equality -/

example : digits = Vec.fromList [10, 20, 30] := by decide
example : digits ≠ Vec.fromList [10, 20] := by decide
example : (Vec.empty : Vec Nat) ≠ digits := by decide

/-- Equality is agreement at every index. This says nothing about the `Decidable`
instance — an earlier version of this docstring claimed it did, and the library
declaration it names was renamed precisely to stop making that claim. The `BEq`
section below is what actually reaches the instances. -/
example (v w : Vec Nat) : v = w ↔ ∀ i, v.get? i = w.get? i :=
  Vec.eq_iff_get?_eq v w

/-! ## Boolean equality, and that it is lawful

An unlawful `BEq` is worse than none: it lets a program branch on an equality
test whose result no proof can use. `LawfulBEq` is what connects the two, and
these two examples are its directions.
-/

example : (digits == Vec.fromList [10, 20, 30]) = true := by decide
example : (digits == Vec.fromList [30, 20, 10]) = false := by decide

example (v w : Vec Nat) (h : (v == w) = true) : v = w := eq_of_beq h
example (v : Vec Nat) : (v == v) = true := beq_self_eq_true v

/-! ## Order is part of the value

The three sections above would all pass for a container that forgot order, so
this is the case that separates a sequence from a set. `docs/STDLIB.md` §1 makes
order observable through indexed elements, and equality has to respect it.
-/

example : Vec.fromList [1, 2] ≠ Vec.fromList [2, 1] := by decide

/-- Multiplicity too: a sequence is not a set. -/
example : Vec.fromList [1, 1] ≠ Vec.fromList [1] := by decide

/-! ## Representation

A `Vec` prints as its elements in order. An earlier version of this comment said
that this keeps a `Vec` and a `List` apart in a debugging session; it does the
opposite — the output is byte-identical to a `List Nat`, which adversarial review
pointed out is the one place the type distinction is invisible. That is a
deliberate readability choice, not a property of the representation.
-/

/-- info: [10, 20, 30] -/
#guard_msgs in
#eval digits

/-! ## The instances agree with each other

Three ways to ask the same question, which had better give the same answer.
-/

example (v w : Vec Nat) : (v == w) = true ↔ v = w :=
  ⟨eq_of_beq, fun h => h ▸ beq_self_eq_true v⟩

example (v w : Vec Nat) : decide (v = w) = (v == w) := by
  by_cases h : v = w
  · simp [h]
  · simp [h, beq_eq_false_iff_ne.mpr h]

end Grass.Tests.Std.Instances
