import Grass.Std.Logical.Bag
import Grass.Std.Logical.Vec
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

* `Vec` — `EmptyCollection`, `Inhabited` and `ForIn` were orphaned; fixed by
  `Vec.emptyCollection_eq_empty`, `Vec.default_eq_empty` and
  `Vec.forIn_eq_forIn_toList`, and pinned by `Tests/Std/VecInstances.lean`. Named
  rather than pointed at a branch, because a branch name stops resolving the
  moment it merges and a declaration name does not.
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

/-! ## The other direction, which is deliberately *not* bridged

Everything above adds a bridge because the laws were stated about one spelling and
a consumer could reach for another. The reverse case exists too and is left alone,
so the difference is worth pinning rather than leaving to be rediscovered as a
gap.

`Bag`'s union and membership laws are stated over `+` and `∈`, and `Vec`'s
concatenation laws over `++`. A goal naming the underlying definition instead
reaches none of them. That is a naming observation rather than a missing law --
the laws cover each operation as consumers write it, no module in the tree names
these forms in code, and the observation-coverage audit exempts `Vec.append` on
exactly this ground. `Bag.append` and `Bag.Mem` are `protected` so the second
spelling stays out of reach of an `open`.

The examples below pin both halves. If someone later decides the named forms
should reach the laws, these fail, and the decision gets made deliberately
instead of by adding a lemma that looks harmless.
-/

example (x y : Bag α) : (x + y).card = x.card + y.card := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example (x y : Bag α) : (Bag.append x y).card = x.card + y.card := by simp

example (a : α) (x y : Bag α) : a ∈ x + y ↔ a ∈ x ∨ a ∈ y := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example (a : α) (x y : Bag α) : Bag.Mem (x + y) a ↔ a ∈ x ∨ a ∈ y := by simp

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

/-! ## Confluence, because the bridges rewrite towards different targets

Three bridges normalise towards `0` and one towards `empty`, and `Vec`'s three
normalise towards `Vec.empty`. Different targets in one `simp` set is where a loop
or a split normal form would come from, and the argument that neither happens --
that the reverse lemmas are deliberately not `simp` -- is reasoning, not evidence.

These are the evidence. Each writes one value two ways and asks `simp` to close
the gap, which it can only do by driving both to the same normal form. The mixed
goals stack every bridge in one term; a cycle would show up as a recursion-depth
failure rather than a wrong answer, so they are worth having even though they look
redundant.
-/

example (v : Vec α) : (∅ : Vec α) ++ v = Vec.empty ++ v := by simp

example (v : Vec α) : (default : Vec α) ++ v = (∅ : Vec α) ++ v := by simp

example (b : Bag α) : (∅ : Bag α) + b = Bag.empty + b := by simp

example (b : Bag α) : Bag.empty + b = (0 : Bag α) + b := by simp

example (k : Nat) :
    (∅ : FiniteMap Nat Nat).lookup k = FiniteMap.empty.lookup k := by simp

/-- Every `Vec` bridge in one term. -/
example (v : Vec α) :
    ((default : Vec α) ++ ((∅ : Vec α) ++ v)).toList = v.toList := by simp

/-- Every `Bag` bridge in one term. -/
example (b : Bag α) : ((∅ : Bag α) + (Bag.empty + b)).card = b.card := by simp

/-- And iteration reached through two of them at once, which is the case that
needs `Vec.toList_empty` as well as the two `empty` bridges. -/
example : (Id.run do
    let mut n : Nat := 0
    for _ in ((∅ : Vec Nat) ++ (default : Vec Nat)) do
      n := n + 1
    return n) = 0 := by simp

/-! ## `FiniteMap`: the framing laws, which are the point of the module

`Grass/Std/Logical/FiniteMap.lean`'s own module comment says the framing lemmas
are the point of it — "almost every proof in the memory layer reduces to 'this
update did not touch the key I am reading'" — and `FiniteMap` is the module with
the most product consumers in this library, six of them, all under
`Grass/Memory`.

Those goals did not close. `FiniteMap.lookup_insert_self` and
`FiniteMap.lookup_erase_self` were `@[simp]`, and `FiniteMap.lookup_insert` and
`FiniteMap.lookup_erase` — the forms covering a lookup at *any* key, which is
what framing means — were not. The same shape as `Vec.get?_set` and for the same
reason; `Tests/Std/VecInstances.lean` collects the family.
-/

section Framing

variable {K V : Type} [DecidableEq K]

example (m : FiniteMap K V) (k o : K) (v : V) (h : o ≠ k) :
    (m.insert k v).lookup o = m.lookup o := by simp [h]

example (m : FiniteMap K V) (k o : K) (h : o ≠ k) :
    (m.erase k).lookup o = m.lookup o := by simp [h]

example (m : FiniteMap K V) (k : K) (v : V) : (m.insert k v).Binds k := by
  simp [FiniteMap.Binds]

example (m : FiniteMap K V) (k : K) : ¬ (m.erase k).Binds k := by
  simp [FiniteMap.Binds]

/-! Through the notation, since that is how a consumer writes the empty map. -/

example (k : K) : ¬ (∅ : FiniteMap K V).Binds k := by simp [FiniteMap.Binds]

/-! ### Not a gap: two inserts commuting

`FiniteMap.lookup_insert` reduces this to nested `if`s and the rest is case
analysis on the key, which a consumer does. It is here because the two goals
above and this one look alike, and only the first two were about the library. -/

example (m : FiniteMap K V) (a b o : K) (x y : V) (hab : a ≠ b) :
    ((m.insert a x).insert b y).lookup o = ((m.insert b y).insert a x).lookup o := by
  simp only [FiniteMap.lookup_insert]
  by_cases ha : o = a
  · subst ha; simp [hab]
  · by_cases hb : o = b
    · subst hb; simp [ha]
    · simp [ha, hb]

end Framing

/-! ## `Bag`: unexercised and reachable, which is the distinction §3.13 draws

`docs/STDLIB_IMPLEMENTATION_PLAN.md` §3.13 measures ten of `Bag`'s twenty-three
`@[simp]` laws as load-bearing for some fixture, and the thirteen that are not
are exactly the `ofList` and `map` families. The section says an unexercised law
is a question rather than a defect. These four goals are that question answered
for `Bag`: they are consumer-shaped, they were written after the measurement, and
every one closes without anything being added.

So `Bag`'s thirteen are unexercised because nothing consumes them — the process
layer still imports its own `Grass/Process/Bag.lean` — and not because they
cannot be reached. That is the opposite finding to `FiniteMap`'s above, from the
same probe, which is why both are in this file.
-/

section BagReachable

example (l : List α) : (Bag.ofList l).card = l.length := by simp

example (l : List α) (a : α) :
    (Bag.ofList (a :: l)).card = (Bag.ofList l).card + 1 := by simp

example (x y : Bag α) {β : Type} (f : α → β) : (x + y).map f = x.map f + y.map f := by simp

example (l : List α) {β : Type} (f : α → β) :
    (Bag.ofList l).map f = Bag.ofList (l.map f) := by simp

end BagReachable

end Grass.Tests.Std.Collections
