import Grass.Std.Logical.Bag
import Grass.Std.Logical.FiniteMap

/-!
# `Bag` and `FiniteMap` reach their own laws through their own notation

`Tests/Std/VecInstances.lean` makes this argument for `Vec` and this file makes it
for the other two containers, because the gap it describes was not specific to
`Vec` and was found in both of these by asking rather than by review.

An `EmptyCollection`, `Zero` or `Singleton` instance makes a notation *typecheck*.
It does not make `simp` see through the instance projection, so a goal written
with the notation reaches none of the laws stated about the underlying value. The
failure is silent in the worst way: nothing looks wrong until a proof stops with
`unsolved goals` on a step that reads as trivial, and nothing points at the
notation as the cause.

## The sweep this fixture is the result of, and what it does not cover

Every instance-provided notation across all seven modules of `Grass/Std/Logical`
was probed by asking `simp` for a law through it. The complete result:

* `Vec` — `EmptyCollection`, `Inhabited` and `ForIn` were orphaned; fixed on
  `agent/c-stdlib/empty-notation` and pinned by `Tests/Std/VecInstances.lean`.
  `Append` and `Membership` reach their laws already. There is deliberately no
  bridge from `a ∈ v` to `a ∈ v.toList`: that is the representation seam, and
  dissolving it is the leak the private structure exists to prevent.
* `Bag` and `FiniteMap` — the gaps this file pins.
* `Order` — supplies only `Decidable` instances, which `decide` reaches without a
  `simp` bridge. Checked directly on `Permutation` and `Pairwise`, both
  directions.
* `Text`, `HostBytes` and `Byte` — declare no instances, so the gap is not
  expressible in them.

**What that sweep cannot see.** The gaps were found by listing every `def` per
module and probing the ones no theorem's *name* mentions. That is a name-shaped
heuristic: a law observing an operation without naming it is invisible to it, and
it produced one false positive — `Grass/Std/Logical/Order.lean` looks like it
defines `stableSorted`, but that text is inside a quoted code block, and a scan
that does not strip fenced blocks reads documentation as declarations. So this is
evidence that the gaps below are real, not that none remain.

Each bridge gets two examples. The first is a bare `simp`, so removing the
corresponding `@[simp]` from the library breaks this fixture — the only way it can
tell a load-bearing lemma from a decorative one. The second pins the hazard: the
underlying law, named explicitly and applied on its own, makes no progress against
the notation. Strip one `@[simp]` and rebuild this module to check; every bridge
below fails at the example written for it.
-/

namespace Grass.Tests.Std.Collections

open Grass.Std.Logical

variable {α : Type}

/-! ## `Bag`: three spellings of one value

`Bag` is the sharper case, because the orphaned spelling is not only the `∅`
notation but `Bag.empty`, the module's *own* name for the value. Every law about
the empty multiset is stated with `0`, so before `Bag.empty_eq_zero` a consumer
who wrote the definition rather than the numeral got "no progress" from `simp` on
a goal the module proves.
-/

example (b : Bag α) : b + 0 = b := by simp

example (b : Bag α) : b + Bag.empty = b := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example (b : Bag α) : b + Bag.empty = b := by simp only [Bag.add_zero]

example (b : Bag α) : b + (∅ : Bag α) = b := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example (b : Bag α) : b + (∅ : Bag α) = b := by simp only [Bag.add_zero]

/-- Cardinality too, which is the law a conservation argument reaches for. -/
example : (Bag.empty : Bag α).card = 0 := by simp

example : ((∅ : Bag α)).card = 0 := by simp

/-! ### The singleton had no cardinality law at all

Not a notation gap: `card_zero`, `card_cons`, `card_add`, `card_ofList` and
`card_map` were all present, and the one arity nothing reached was the singleton.
It is a `rfl`, which is why it was easy to leave out — nothing failed without it
except a goal nobody had written yet.
-/

example (a : α) : ({a} : Bag α).card = 1 := by simp

/-- Membership was already fine, and is checked so that a later change which
routes it through the same bridges cannot quietly break it. -/
example (a b : α) : a ∈ ({b} : Bag α) ↔ a = b := by simp

/-! ## `FiniteMap`: the same gap, oriented the other way

`FiniteMap`'s laws are stated about `empty` rather than about a numeral, so here
the notation is the orphan and `empty` is the target. The two modules therefore
normalise in opposite directions, which is deliberate: the direction follows where
the theorems already are.
-/

example (k : Nat) : (FiniteMap.empty : FiniteMap Nat Nat).lookup k = none := by simp

example (k : Nat) : (∅ : FiniteMap Nat Nat).lookup k = none := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example (k : Nat) : (∅ : FiniteMap Nat Nat).lookup k = none := by
  simp only [FiniteMap.lookup_empty]

example : (∅ : FiniteMap Nat Nat).IsEmpty := by simp

end Grass.Tests.Std.Collections
