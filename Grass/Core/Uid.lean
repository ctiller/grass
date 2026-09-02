/-!
# Nominal identities and monotone fresh supply

`docs/FOUNDATION.md` law 22: "process generations, channel epochs, child/message
occurrences, and replacements are fresh over a monotone execution history; stale
completions never regain authority after numeric reuse."

That law has two halves and they need different mechanisms.

**Grass's own identities are never reused within one supply.** A `Uid` can only be
produced by `FreshSupply.fresh`. The constructor and the index field are
`private`, so outside this module there is no `Uid.mk` and no way to read an
index back out. `never_reissued` is therefore a mechanism rather than a
convention for a given supply.

What this module does **not** deliver, and cannot: uniqueness of the supply
itself. `initial` is public, and it must be — something has to start. So a second
`FreshSupply.initial` for the same tag reissues every identity from zero, and
nothing here prevents that. Threading one supply per domain through an execution
is the execution model's obligation, not `Core`'s; `docs/FOUNDATION.md` law 22
speaks of freshness "over a monotone execution history", and only the thing that
owns the history can guarantee there is one. `Semantics` inherits this obligation
when it takes custody of the execution state.

`Uid.rec` and `Uid.casesOn` also remain public, as they do for every Lean
structure, so a proof can case on a `Uid` and reach its index. The type is opaque
to construction, not to elimination.

**Externally reused numbers are paired with a generation.** An OS handle, a slot
index, or an array position genuinely does recycle, and forbidding that is not
available to us. `Grass/Core/Generational.lean` pairs such a value with a `Uid`
so that a recycled number in a new generation is a distinct identity.

`Reachable` is the relation an execution establishes: a supply reached by some
number of mints from an earlier one. `never_reissued` is stated over it and
quantifies over every reachable future, which is the shape law 22 needs.

Being precise about its strength: because `FreshSupply` has a single `Nat` field
that only ever increments, `Reachable s t` is *equivalent* to
`s.nextIndex ≤ t.nextIndex`. It is not a stronger relation. Its value is as an
interface — it names the thing an execution produces, and it stays correct if the
supply ever gains structure that makes the two differ — not as extra proof
strength today.

The type is `Uid`, not `Id`, because Lean's `Id` is the identity monad and
`Id.run do` is ubiquitous. A `Grass.Core.Id` would make bare `Id` ambiguous in
every module that opens `Grass.Core`.

**Custody note.** `Grass.Core` is not owned by the memory agent. This module is
temporary custody under `docs/MEMORY_IMPLEMENTATION_PLAN.md` §2.
-/

namespace Grass.Core

universe u

/--
An identity in the domain named by `Tag`.

`Tag` is phantom: it appears in the type but not in any field, so an `AllocId`
cannot be passed where a `LoanId` is expected. The representation is private, so
outside this module a `Uid` is an opaque token that can be compared and nothing
else.
-/
structure Uid (Tag : Type u) where
  private mk ::
  private index : Nat

namespace Uid

variable {Tag : Type u}

instance : Repr (Uid Tag) := ⟨fun i _ => "uid#" ++ repr i.index⟩

instance : DecidableEq (Uid Tag) := fun a b =>
  if h : a.index = b.index then
    .isTrue (by cases a; cases b; simp_all)
  else
    .isFalse (by intro eq; exact h (congrArg Uid.index eq))

private theorem eq_of_index_eq {a b : Uid Tag} (h : a.index = b.index) : a = b := by
  cases a; cases b; simp_all

end Uid

/--
The mint state of one identity domain.

`nextIndex` is the least index never yet issued. Both the constructor and the
field are private, so no consumer can fabricate a supply, rewind one, or observe
how many identities have been issued.
-/
structure FreshSupply (Tag : Type u) where
  private mk ::
  private nextIndex : Nat

namespace FreshSupply

variable {Tag : Type u}

/-- The supply that has issued nothing. -/
def initial : FreshSupply Tag := ⟨0⟩

/-- `s.Issued i` holds when `s` has already minted `i`. -/
def Issued (s : FreshSupply Tag) (i : Uid Tag) : Prop := i.index < s.nextIndex

instance (s : FreshSupply Tag) (i : Uid Tag) : Decidable (s.Issued i) :=
  inferInstanceAs (Decidable (i.index < s.nextIndex))

/-- Mint one identity, returning it together with the advanced supply. -/
def fresh (s : FreshSupply Tag) : Uid Tag × FreshSupply Tag :=
  (⟨s.nextIndex⟩, ⟨s.nextIndex + 1⟩)

/--
`Reachable s t` holds when `t` is a supply some sequence of mints reaches from
`s`.

This is the relation an execution establishes, and it is the one the freshness
laws are stated over. A bare numeric comparison between two supplies would be
satisfiable by supplies no execution connects.
-/
inductive Reachable : FreshSupply Tag → FreshSupply Tag → Prop where
  /-- A supply reaches itself. -/
  | refl (s : FreshSupply Tag) : Reachable s s
  /-- If `t` is reachable from `s`, so is the supply after one more mint. -/
  | mint {s t : FreshSupply Tag} : Reachable s t → Reachable s t.fresh.2

@[simp] theorem issued_initial (i : Uid Tag) : ¬ (initial (Tag := Tag)).Issued i := by
  simp [initial, Issued]

/-- A minted identity was not already issued. -/
theorem fresh_not_issued (s : FreshSupply Tag) : ¬ s.Issued s.fresh.1 := by
  simp [Issued, fresh]

/-- Minting issues exactly the identity it returns, and nothing else. -/
theorem issued_fresh (s : FreshSupply Tag) (i : Uid Tag) :
    s.fresh.2.Issued i ↔ s.Issued i ∨ i = s.fresh.1 := by
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with lt | eq
    · exact .inl lt
    · exact .inr (Uid.eq_of_index_eq eq)
  · rintro (h | rfl)
    · exact Nat.lt_succ_of_lt h
    · exact Nat.lt_succ_self _

/-- Reachability is transitive, so histories compose. -/
theorem Reachable.trans {s t r : FreshSupply Tag}
    (h₁ : Reachable s t) (h₂ : Reachable t r) : Reachable s r := by
  induction h₂ with
  | refl => exact h₁
  | mint _ ih => exact .mint ih

/-- Reaching a supply never decreases its mint counter. -/
private theorem nextIndex_le_of_reachable {s t : FreshSupply Tag}
    (h : Reachable s t) : s.nextIndex ≤ t.nextIndex := by
  induction h with
  | refl => exact Nat.le_refl _
  | mint _ ih => exact Nat.le_trans ih (Nat.le_succ _)

/-- Issuance is monotone along a history: nothing minted is ever unminted. -/
theorem Issued.mono {s t : FreshSupply Tag} {i : Uid Tag}
    (h : Reachable s t) (issued : s.Issued i) : t.Issued i :=
  Nat.lt_of_lt_of_le issued (nextIndex_le_of_reachable h)

/--
The no-reuse law.

An identity issued at any point in a history is not returned by any later mint,
however far the history has advanced. This is stronger than "the next mint
differs from `i`": it quantifies over every reachable future.

`docs/FOUNDATION.md` law 22 for Grass's own identities. External numbers that
genuinely recycle are handled by `Grass/Core/Generational.lean` instead.
-/
theorem never_reissued {s t : FreshSupply Tag} {i : Uid Tag}
    (h : Reachable s t) (issued : s.Issued i) : t.fresh.1 ≠ i := by
  intro eq
  exact absurd (eq ▸ Issued.mono h issued) (fresh_not_issued t)

/--
The same law in live-set form: a stale identity is never live again as a *new*
identity, so authority attached to it cannot be regained by a later mint.
-/
theorem never_reissued_along_history {s : FreshSupply Tag} {i : Uid Tag}
    (issued : s.Issued i) :
    ∀ t, Reachable s t → t.fresh.1 ≠ i :=
  fun _ h => never_reissued h issued

end FreshSupply

end Grass.Core
