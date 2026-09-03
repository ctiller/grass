import Grass.Std.Logical.Order

/-!
# Spike 2's `stableSorted`, written against this library

`Spikes/2_Sort/Spec.lean` defines what the sort milestone means:

```text
def stableSorted (input output : Vec Occurrence) : Prop :=
  output.Permutation input ∧
  output.Pairwise Occurrence.le ∧
  ∀ i j, i < j -> input[i].value = input[j].value ->
    (output.findIdx? input[i]).get! < (output.findIdx? input[j]).get!
```

`Grass/Std/Logical/Order.lean` exists to supply that vocabulary. This fixture is
the check that it actually does: the specification is restated here over a
stand-in `Occurrence` using only `Vec.Permutation`, `Vec.Pairwise`, and
`Vec.idxOf?`, and then discharged against a concrete sort.

Restating it is also where the two problems with the authored version show, which
is why the fixture is worth more than a claim that the vocabulary is sufficient.

**`input[i]` has no bound.** The binder is `∀ i j, i < j → …`, which bounds `i`
below `j` and nothing above, so there is no proof that `i` indexes `input` at
all. `Vec.get` demands one and `Vec.get?` returns an `Option`. The version below
takes the bounds as explicit hypotheses, which is what the specification meant.

**`.get!` hides a failure.** `(output.findIdx? input[i]).get!` panics if the
element is not found — and whether it is found is exactly the substantive claim,
since a permutation contains every input element. Writing it with `get!` makes
the specification silent about a case that a wrong implementation would hit. The
version below quantifies over the positions instead, so a sort that dropped an
element fails the specification rather than the runtime.
-/

namespace Grass.Tests.Std.StableSort

open Grass.Std.Logical

/-! ## A stand-in for the spike's types

`Occurrence` pairs a source position with a value, as in the spike. The order is
a stand-in for `ByteStringOrder.lexicographicUnsigned` — the point is that
`Vec.Pairwise` takes the relation as a parameter, so any order works.
-/

structure Occurrence where
  ordinal : Nat
  value : Nat
  deriving DecidableEq, Repr

def Occurrence.le (left right : Occurrence) : Prop := left.value ≤ right.value

instance : DecidableRel Occurrence.le := fun a b => Nat.decLe a.value b.value

/-! ## The specification, restated totally -/

/--
Stable sorting, with every index accounted for.

The three conjuncts are the spike's three: the output rearranges the input, the
output is ordered, and equal-valued elements keep their input order. The third
differs from the spike only in being total — bounds are hypotheses and the found
positions are quantified rather than extracted with `get!`.
-/
def StableSorted (input output : Vec Occurrence) : Prop :=
  output.Permutation input ∧
  output.Pairwise Occurrence.le ∧
  ∀ (i j : Nat) (hi : i < input.length) (hj : j < input.length), i < j →
    (input.get i hi).value = (input.get j hj).value →
    ∀ p q, output.idxOf? (input.get i hi) = some p →
           output.idxOf? (input.get j hj) = some q →
           p < q

/-! ## A concrete sort satisfying it

Three occurrences with a duplicated value, so stability has something to say:
`b` appears at input positions 0 and 2 and must stay in that order.
-/

def input : Vec Occurrence :=
  Vec.fromList [⟨0, 2⟩, ⟨1, 1⟩, ⟨2, 2⟩]

def output : Vec Occurrence :=
  Vec.fromList [⟨1, 1⟩, ⟨0, 2⟩, ⟨2, 2⟩]

example : output.Permutation input := by decide

example : output.Pairwise Occurrence.le := by decide

/-- The duplicated value keeps its input order in the output: the occurrence from
input position 0 lands at output position 1, and the one from input position 2
lands at output position 2. -/
example : output.idxOf? ⟨0, 2⟩ = some 1 := by decide
example : output.idxOf? ⟨2, 2⟩ = some 2 := by decide

/-- An unstable sort would swap those two, and this is the value that would then
fail. Recorded so the fixture is not only positive. -/
def unstableOutput : Vec Occurrence :=
  Vec.fromList [⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 2⟩]

/-- The unstable output is still a permutation and still ordered — which is the
whole reason stability is a separate conjunct rather than a consequence. -/
example : unstableOutput.Permutation input := by decide
example : unstableOutput.Pairwise Occurrence.le := by decide

/-- But it reverses the two equal-valued occurrences. -/
example : unstableOutput.idxOf? ⟨0, 2⟩ = some 2 := by decide
example : unstableOutput.idxOf? ⟨2, 2⟩ = some 1 := by decide

/-! ## The laws a sort's caller actually uses -/

/-- A sorted output has the same length as its input, so a caller can size a
buffer for it. -/
example (i o : Vec Occurrence) (h : StableSorted i o) : o.length = i.length :=
  h.1.length_eq

/-- Nothing is lost or invented. -/
example (i o : Vec Occurrence) (h : StableSorted i o) (x : Occurrence) :
    x ∈ o ↔ x ∈ i :=
  h.1.mem_iff

/-- Every input element has a position in the output, which is what makes the
stability conjunct non-vacuous: the `idxOf?` calls in it always succeed. -/
example (i o : Vec Occurrence) (h : StableSorted i o) (x : Occurrence) (hx : x ∈ i) :
    (o.idxOf? x).isSome :=
  Vec.idxOf?_isSome_of_mem (h.1.mem_iff.mpr hx)

/-- Multiplicity is preserved, which is what stops a "sort" from duplicating one
line and dropping another. Every other Permutation law is satisfied by a relation
that allows exactly that; adversarial review exhibited one. -/
example (i o : Vec Occurrence) (h : StableSorted i o) (x : Occurrence) :
    o.count x = i.count x :=
  h.1.count_eq x

/-- A found position is the *first* one, which is what stability is a claim
about. -/
example (o : Vec Occurrence) (x : Occurrence) (k : Nat) (h : o.idxOf? x = some k) :
    ∀ j, j < k → o.get? j ≠ some x :=
  (Vec.idxOf?_eq_some h).2.2

/-- Order by index, which is the form a merge proof discharges. -/
example (i o : Vec Occurrence) (h : StableSorted i o)
    (a b : Nat) (ha : a < o.length) (hb : b < o.length) (hab : a < b) :
    Occurrence.le (o.get a ha) (o.get b hb) :=
  (Vec.pairwise_iff_get o).mp h.2.1 a b ha hb hab

end Grass.Tests.Std.StableSort
