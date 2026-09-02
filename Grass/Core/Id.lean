/-!
# Nominal identities and monotone fresh supply

`docs/FOUNDATION.md` law 22 forbids numeric reuse from reviving stale authority:
process generations, channel epochs, and occurrences must be fresh over a
monotone execution history. This module supplies the only identity-minting
mechanism the memory, obligation, and resource layers use.

The load-bearing design choice is a negative one. `FreshSupply` has no operation
that returns an index to the pool, and no operation that lowers `nextIndex`.
There is therefore no way to mint an index twice, which is what makes
`stale_never_reissued` provable rather than merely conventional.

Identities are phantom-tagged so that an `AllocId` cannot be passed where a
`LoanId` is expected. The tag is an open type parameter rather than a closed
enumeration of kinds, so a profile may introduce its own identity domain without
editing this module.

**Custody note.** `Grass.Core` is not owned by the memory agent. This module is
temporary custody under `docs/MEMORY_IMPLEMENTATION_PLAN.md` §2: it exists so
that milestone M1 is not blocked, contains only what M1 through M3 consume, and
is expected to transfer to the `Core` owner by rename and re-export.
-/

namespace Grass.Core

universe u

/--
An identity in the domain named by `Tag`.

`Tag` is phantom: it appears in the type but not in any field, so distinct
domains are distinguishable by the elaborator at no representational cost.
-/
structure Id (Tag : Type u) where
  /-- The mint order of this identity within its domain. -/
  index : Nat

namespace Id

variable {Tag : Type u}

instance : Repr (Id Tag) := ⟨fun i _ => repr i.index⟩

instance : DecidableEq (Id Tag) := fun a b =>
  if h : a.index = b.index then
    .isTrue (by cases a; cases b; simp_all)
  else
    .isFalse (by intro eq; exact h (congrArg Id.index eq))

theorem eq_of_index_eq {a b : Id Tag} (h : a.index = b.index) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem mk_index (n : Nat) : (Id.mk (Tag := Tag) n).index = n := rfl

end Id

/--
The mint state of one identity domain.

`nextIndex` is the least index never yet issued. It only ever increases, and
there is no operation that reclaims an issued index.
-/
structure FreshSupply (Tag : Type u) where
  /-- The least index this supply has never issued. -/
  nextIndex : Nat

namespace FreshSupply

variable {Tag : Type u}

/-- The supply that has issued nothing. -/
def initial : FreshSupply Tag := ⟨0⟩

/-- `Issued s i` holds when `s` has already minted `i`. -/
def Issued (s : FreshSupply Tag) (i : Id Tag) : Prop := i.index < s.nextIndex

instance (s : FreshSupply Tag) (i : Id Tag) : Decidable (s.Issued i) :=
  inferInstanceAs (Decidable (i.index < s.nextIndex))

/-- Mint one identity, returning it together with the advanced supply. -/
def fresh (s : FreshSupply Tag) : Id Tag × FreshSupply Tag :=
  (⟨s.nextIndex⟩, ⟨s.nextIndex + 1⟩)

/-- `s.Precedes t` holds when `t` is a possible future of `s`. -/
def Precedes (s t : FreshSupply Tag) : Prop := s.nextIndex ≤ t.nextIndex

@[simp] theorem issued_initial (i : Id Tag) : ¬ (initial (Tag := Tag)).Issued i := by
  simp [initial, Issued]

/-- A minted identity was not already issued. This is the freshness guarantee. -/
theorem fresh_not_issued (s : FreshSupply Tag) : ¬ s.Issued s.fresh.1 := by
  simp [Issued, fresh]

/-- Minting issues exactly the identity it returns, and nothing else. -/
theorem issued_fresh (s : FreshSupply Tag) (i : Id Tag) :
    s.fresh.2.Issued i ↔ s.Issued i ∨ i = s.fresh.1 := by
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with lt | eq
    · exact .inl lt
    · exact .inr (Id.eq_of_index_eq eq)
  · rintro (h | rfl)
    · exact Nat.lt_succ_of_lt h
    · exact Nat.lt_succ_self _

/-- Minting advances the supply. -/
theorem precedes_fresh (s : FreshSupply Tag) : s.Precedes s.fresh.2 :=
  Nat.le_succ _

theorem Precedes.refl (s : FreshSupply Tag) : s.Precedes s := Nat.le_refl _

theorem Precedes.trans {s t r : FreshSupply Tag}
    (h₁ : s.Precedes t) (h₂ : t.Precedes r) : s.Precedes r :=
  Nat.le_trans h₁ h₂

/-- Issuance is monotone along the history: nothing minted is ever unminted. -/
theorem Issued.mono {s t : FreshSupply Tag} {i : Id Tag}
    (h : s.Precedes t) (issued : s.Issued i) : t.Issued i :=
  Nat.lt_of_lt_of_le issued h

/--
The no-reuse law. An identity that was already issued at some point in the
history is never returned by a later mint, however far the history has advanced.

This is the mechanical content of foundation law 22 for this layer: a stale
occurrence cannot regain authority by having its index handed out again.
-/
theorem stale_never_reissued {s t : FreshSupply Tag} {i : Id Tag}
    (h : s.Precedes t) (issued : s.Issued i) : t.fresh.1 ≠ i := by
  intro eq
  exact absurd (eq ▸ Issued.mono h issued) (fresh_not_issued t)

end FreshSupply

end Grass.Core
