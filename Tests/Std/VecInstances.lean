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

/-! ## The instances rewrite, not just typecheck

Every section above checks that a notation or an instance *elaborates* on a
`Vec`. That is not the same as checking that a proof about one can *proceed*,
and the gap between the two is what `Grass/Std/Logical/Vec.lean`'s bridge lemmas
close: `simp` does not see through an instance projection, so a goal written with
`∅`, `default`, `v[i]` or `for` loses the laws stated about `Vec.empty`,
`Vec.get?` and `Vec.toList` — the laws a consumer reaches for immediately after
writing the notation.

That failure is silent in the worst way. The notation typechecks, so nothing
looks wrong until a proof stops with `unsolved goals` on a step that reads as
trivial, and the author has no reason to suspect the notation rather than the
law.

Each bridge gets two examples here. The first is a bare `simp`, so that removing
the corresponding `@[simp]` from the library breaks this fixture — which is the
only way it can tell a load-bearing lemma from a decorative one. The second pins
the hazard itself: the underlying law, named explicitly and applied on its own,
makes no progress against the notation.

Run that way round to check it: strip one `@[simp]` from the library and rebuild
this module. All five fail, each at the example written for it —
`Vec.emptyCollection_eq_empty` and `Vec.forIn_eq_forIn_toList` at two examples
apiece, the other three at one. A bridge that could be removed without breaking
anything here would be a bridge this fixture is not actually testing.
-/

example (v : Vec Nat) : (∅ : Vec Nat) ++ v = v := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example (v : Vec Nat) : (∅ : Vec Nat) ++ v = v := by simp only [Vec.empty_append]

/-! `Vec.emptyCollection_eq_empty` is the lemma that separates those two, and the
shape above is not invented for the fixture: it is what two conservation
obligations in a `Grass/Process/ByteFlow/Ingress.lean` port reduce to once the
sequence type is `Vec`, reported to `c-process` at `c-stdlib:49`. -/

example : (default : Vec Nat) ++ (default : Vec Nat) = default := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example : (default : Vec Nat) ++ (default : Vec Nat) = default := by
  simp only [Vec.append_empty]

/-! ### Indexing

This pair is the sharpest of the four, because the positive example is not
`rfl` — it genuinely needs the rewrite, where the `∅` and `default` goals happen
to also hold definitionally. `Vec.get_eq_iff_get?_eq` is what turns the total
read into the checked one, at which point `Vec.get?_push_self` applies; without
it the goal is stated in terms of `Vec.get`, about which this module proves
nothing at all. -/

example (v : Vec Nat) (a : Nat) : (v.push a).get v.length (by simp) = a := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example (v : Vec Nat) (a : Nat) : (v.push a).get v.length (by simp) = a := by
  simp only [Vec.get?_push_self]

/-! ### Iteration

`Vec.forIn_eq_forIn_toList` routes a loop to `List`'s iteration laws, and
`Vec.toList_empty` is what lets the empty case finish there. The residual `rfl`
below is `Id`'s `pure`, not a `Vec` obligation: `simp` discharges every step that
is this module's to discharge and stops at `pure n = n`. -/

example (v : Vec Nat) : (Id.run do
    let mut n : Nat := 0
    for _ in v do
      n := n + 1
    return n) = v.toList.length := by
  simp [Id.run]
  rfl

example : (Id.run do
    let mut n : Nat := 0
    for _ in (∅ : Vec Nat) do
      n := n + 1
    return n) = 0 := by simp

/-! ## Reading back a sequence you built

The section above checks a single `push` read at its top, which is the only
read-after-push shape `simp` could close before `Vec.get?_push` existed. A
consumer that builds a sequence pushes more than once, and every other shape
reported "no progress": the interaction of `Vec.length_push` normalising
`(v.push a).length` to `v.length + 1` with `Vec.get?_push_self` wanting the
unnormalised form meant the law could not fire on anything twice-pushed.

These are the six goals that measurement used. Five of them failed before, and
the one that passed is kept so the pair reads as a set rather than as a list of
repairs.
-/

example (v : Vec Nat) (a : Nat) : (v.push a).get? v.length = some a := by simp

example (v : Vec Nat) (a b : Nat) :
    ((v.push a).push b).get? (v.length + 1) = some b := by simp

example (v : Vec Nat) (a b : Nat) :
    ((v.push a).push b).get? v.length = some a := by simp

example (a b : Nat) : ((Vec.empty.push a).push b).get? 1 = some b := by simp

example (a b : Nat) : ((Vec.empty.push a).push b).get? 0 = some a := by simp

/-- Reading past the end, which the case split also has to get right. -/
example (a b : Nat) : ((Vec.empty.push a).push b).get? 2 = none := by simp

/-- And below the top of a variable sequence, which previously needed the
conditional `Vec.get?_push_lt` supplied by hand. -/
example (v : Vec Nat) (a : Nat) (i : Nat) (h : i < v.length) :
    (v.push a).get? i = v.get? i := by simp [h]

/-! ## Reading with a bound, in the shapes a migrating consumer writes

`c-mem:51` measured what it would cost to retype the memory layer's byte
sequences from `List Byte` to `Vec Byte` and reported twenty-five errors, all in
the proof layer rather than in the declarations: `Grass/Memory/ByteStore.lean`
and `Event.lean` discharge goals with `List.getElem?_eq_none`,
`List.getElem?_eq_some_iff`, `List.getElem?_eq_getElem` and `List.length_take`
directly rather than through any interface. After a migration each of those is a
goal about a `Vec`, and the question this section asks is whether `simp` closes
it without the consumer reaching back for `Vec.toList`.

That is a *named* consumer with a *named* use, which is band 2 in
`docs/STDLIB_IMPLEMENTATION_PLAN.md` §1 — the case the band rule exists to
serve, and the reason these goals were written before the migration rather than
after it.

Three of the nine below did not close when they were first written. Two were
laws that already existed and were not in the `simp` set — `Vec.get?_replicate`
and `Vec.get?_eq_none_iff` — and one, `Vec.get?_isSome_iff`, did not exist.
-/

section ReadingWithABound

variable {α : Type}

/-! ### Out of range reads nothing

`Vec.get?_eq_none_iff` states this and was not `@[simp]`, so the goal a consumer
writes stopped on a law the module already had. -/

example (v : Vec α) (i : Nat) (h : v.length ≤ i) : v.get? i = none := by simp [h]

/-- The same through the bracket notation, which is how a field read spells it.
This one closed before the attribute changed, through
`Vec.getElem?_eq_get?`. -/
example (v : Vec α) (i : Nat) (h : v.length ≤ i) : v[i]? = none := by simp [h]

/-! ### In range reads something

`Vec.get?_isSome_iff` is the half `Vec.get?_eq_none_iff` leaves behind: with the
`none` case normalising to arithmetic and the `isSome` case not, the asymmetry is
in the predicate rather than in the sequence. -/

example (v : Vec α) (i : Nat) (h : i < v.length) : (v.get? i).isSome := by simp [h]

/-! ### Bounds arithmetic over a prefix, which is where `c-mem`'s `omega` calls sit -/

example (v : Vec α) (n : Nat) : (v.take n).length = min n v.length := by simp

example (v : Vec α) (n i : Nat) (h : i < n) (hn : n ≤ v.length) :
    i < (v.take n).length := by
  simp; omega

/-! ### Reading back what a constructor built

`Vec.ofFn` is the counterpart of `Grass/Memory/Apply.lean`'s `observedBytes`,
which builds its result as `(List.range n).map`. `Vec.replicate` is one of the
four operations `c-mem:50` reports the layer using. `Vec.get?_replicate` existed
and was not `@[simp]`, which is the same shape `Vec.get?_push` was in before it
was written: a conditional read-back stated but unreachable. -/

example (n : Nat) (f : Nat → α) (i : Nat) (h : i < n) :
    (Vec.ofFn n f).get? i = some (f i) := by simp [h]

example (n : Nat) (f : Nat → α) (i : Nat) (h : i < n) :
    (Vec.ofFn n f)[i]? = some (f i) := by simp [h]

example (n : Nat) (a : α) (i : Nat) (h : i < n) :
    (Vec.replicate n a).get? i = some a := by simp [h]

example (n : Nat) (a : α) (i : Nat) (h : n ≤ i) :
    (Vec.replicate n a).get? i = none := by simp [h]

end ReadingWithABound

end Grass.Tests.Std.Instances
