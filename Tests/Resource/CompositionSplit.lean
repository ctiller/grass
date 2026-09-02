import Grass.Resource.Algebra

/-!
# Parallel composition and temporal aggregation are different operations

Two sockets held at the same time are two sockets. Two branches that each need one
socket, only one of which runs, need one socket. Collapsing these into a single
operator gets one of them wrong, and which one it gets wrong depends on which
operator you pick.

This fixture pins both directions, because an earlier version of the algebra got
each in turn:

- with only `combine` and no cancellation law, `max` was a lawful *parallel*
  composition, and simultaneously held sockets were undercounted;
- with cancellation added, `max` became unavailable altogether, which would have
  forced peak-bound proofs across exclusive phases to be artificially additive.

The laws now separate them by idempotence. `alternative a a = a` is what
`combine` must not satisfy, and `combineCancel` is what `alternative` must not.
-/

namespace Grass.Tests.Resource

open Grass.Resource

/-! ## `max` is a lawful temporal aggregation -/

/-- The counting algebra aggregates exclusive branches with `max`, and that is
lawful. -/
example : Counting.alternative 1 1 = 1 := rfl

/-- Two exclusive branches each needing one socket peak at one socket. -/
theorem exclusive_branches_do_not_add :
    Counting.alternative 1 1 = 1 := rfl

/-- Two subsystems each holding one socket at the same time need two. -/
theorem parallel_holdings_add :
    Counting.combine 1 1 = 2 := rfl

/-- The peak never exceeds the parallel cost. This is the law that makes an
alternative bound a sound relaxation rather than a different claim. -/
theorem peak_bounded_by_parallel (a b : Nat) :
    Counting.alternative a b ≤ Counting.combine a b :=
  Counting.laws.alternativeLeCombine a b trivial

/-! ## `max` is not a lawful parallel composition

The witness is cancellation. `max 1 3 = max 2 3` while `1 ≠ 2`, so an algebra
using `max` for `combine` cannot satisfy `combineCancel` — and `combineCancel` is
exactly what stops a composite from forgetting one of its parts. -/

/-- The counterexample, concretely. -/
theorem max_is_not_cancellative :
    max 1 3 = max 2 3 ∧ (1 : Nat) ≠ 2 := ⟨rfl, by decide⟩

/--
No resource algebra can use `max` as its parallel composition.

Stated over an arbitrary `compatible` that admits the witnesses, so it is not a
fact about one instance: any law bundle whose `combine` is `max` is
uninhabited wherever compatibility holds at `1, 3` and `2, 3`.
-/
theorem no_laws_with_max_as_combine
    {compatible : Nat → Nat → Prop} {alternative : Nat → Nat → Nat} {le : Nat → Nat → Prop}
    (h13 : compatible 1 3) (h23 : compatible 2 3)
    (laws : OrderedPartialCommutativeResourceLaws compatible (fun a b => max a b)
      alternative 0 le) : False := by
  have := laws.combineCancel 1 2 3 h13 h23 rfl
  exact absurd this (by decide)

/-! ## `+` is not a lawful temporal aggregation

The mirror-image witness is idempotence: one branch needing one socket, taken
twice, must still peak at one. -/

/-- No resource algebra can use `+` as its alternative aggregation. -/
theorem no_laws_with_add_as_alternative
    {compatible : Nat → Nat → Prop} {combine : Nat → Nat → Nat} {le : Nat → Nat → Prop}
    (laws : OrderedPartialCommutativeResourceLaws compatible combine
      (fun a b => a + b) 0 le) : False := by
  have := laws.alternativeIdem 1
  simp at this

end Grass.Tests.Resource
