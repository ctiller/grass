import Grass.Core.Uid

/-!
# Generational values

`docs/FOUNDATION.md` law 22 has two halves. `Grass/Core/Uid.lean` handles the
first: Grass's own identities are never reused, enforced by a private
constructor. This module handles the second, which is the harder one.

> stale completions never regain authority after numeric reuse

Numeric reuse is not something Grass can forbid. An OS handle value, a file
descriptor, a slot index in a fixed table, a Win32 `HANDLE`, a Vulkan queue
index — all of these genuinely recycle, and a model that assumed otherwise would
be assuming away exactly the hazard the law names. A stale completion arriving
for handle `0x2C` after `0x2C` has been closed and reissued must not be able to
act on the new owner's resource.

`Generational Domain α` pairs the recycled value with a domain-tagged `Uid` that
is minted from a monotone supply. Two occurrences of the same number in
different generations are then unequal, so a stale reference simply fails to
match — no comparison against a liveness table, and no reasoning about whether
the number "looks current".

The domain parameter matters. Two subsystems may each start their own supply at
zero; without a nominal domain tag their first generations would compare equal.
The constructor is private as well: `fresh` returns an occurrence and the
corresponding successor supply together, so construction cannot silently pair a
value with an arbitrary old generation. This is not linear ownership: supplies
are pure values and `initial` is public, so replaying or restarting one can still
repeat a generation. As with `Uid`, the history owner must thread exactly one
supply per domain rather than fork or restart it. The `stale_ne_fresh` theorem
makes that history premise explicit.
-/

namespace Grass.Core

universe u v

/-- Phantom tag separating independently managed generation domains. -/
inductive GenerationTag (Domain : Type u) : Type u

/--
The identity of one generation of a recycled value.

`GenerationId` carries the domain tag, so generations minted for distinct
domains cannot be compared or substituted. Within one domain, its owner threads
the corresponding `GenerationSupply` through the execution history.
-/
abbrev GenerationId (Domain : Type u) := Uid (GenerationTag Domain)

/-- The monotone mint state for one nominal generation domain. -/
abbrev GenerationSupply (Domain : Type u) := FreshSupply (GenerationTag Domain)

/--
An externally recycled value, qualified by the generation it belongs to.

Equality compares both components, so a recycled number in a new generation is a
distinct identity from the same number in an old one.
-/
structure Generational (Domain : Type u) (α : Type v) where
  private mk ::
  /-- The externally chosen value, which may be reused after this generation ends. -/
  value : α
  /-- The generation this occurrence belongs to. -/
  generation : GenerationId Domain

namespace Generational

variable {Domain : Type u} {α : Type v}

instance [DecidableEq α] : DecidableEq (Generational Domain α) := fun a b =>
  if h : a.value = b.value ∧ a.generation = b.generation then
    .isTrue (by cases a; cases b; simp_all)
  else
    .isFalse (by
      intro eq
      exact h ⟨congrArg Generational.value eq, congrArg Generational.generation eq⟩)

/--
Create one occurrence and return its domain's successor generation supply.

`Generational.fresh` is the public construction path; the structure constructor
is private, so direct arbitrary pairing is unavailable. Because Lean values are
duplicable, the caller still has to thread the returned supply exactly once;
replaying the input repeats the generation, just as replaying a `FreshSupply`
does for `Uid`.
-/
def fresh (supply : GenerationSupply Domain) (value : α) :
    Generational Domain α × GenerationSupply Domain :=
  (⟨value, supply.fresh.1⟩, supply.fresh.2)

@[simp] theorem fresh_value (supply : GenerationSupply Domain) (value : α) :
    (fresh supply value).1.value = value := rfl

/-- The occurrence returned by `fresh` was not issued by the input supply. -/
theorem fresh_not_issued (supply : GenerationSupply Domain) (value : α) :
    ¬ supply.Issued (fresh supply value).1.generation :=
  FreshSupply.fresh_not_issued supply

/-- The output supply records the occurrence returned by `fresh` as issued. -/
theorem fresh_issued (supply : GenerationSupply Domain) (value : α) :
    (fresh supply value).2.Issued (fresh supply value).1.generation := by
  exact (FreshSupply.issued_fresh supply (fresh supply value).1.generation).2
    (.inr rfl)

/--
The staleness law.

Two occurrences in different generations are different identities, whatever their
values. This is what a stale completion runs into: it carries the generation it
was issued in, which no longer matches.
-/
theorem ne_of_generation_ne {a b : Generational Domain α}
    (h : a.generation ≠ b.generation) :
    a ≠ b := fun eq => h (congrArg Generational.generation eq)

/--
Equal numbers do not make equal identities.

Stated separately from `ne_of_generation_ne` because it is the reading that
matters at a use site: matching the recycled number is never sufficient.
-/
theorem value_eq_insufficient {a b : Generational Domain α}
    (_hv : a.value = b.value) (hg : a.generation ≠ b.generation) : a ≠ b :=
  ne_of_generation_ne hg

theorem eq_iff {a b : Generational Domain α} :
    a = b ↔ a.value = b.value ∧ a.generation = b.generation := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨hv, hg⟩; cases a; cases b; simp_all

/--
`stale_ne_fresh` combines `FreshSupply.Reachable`, `FreshSupply.Issued`, and
`FreshSupply.never_reissued`: an issued occurrence differs from the next one
minted at a reachable supply, even when the external value is recycled.
-/
theorem stale_ne_fresh {earlier later : GenerationSupply Domain}
    {stale : Generational Domain α}
    (reachable : FreshSupply.Reachable earlier later)
    (issued : earlier.Issued stale.generation) (value : α) :
    stale ≠ (fresh later value).1 :=
  ne_of_generation_ne (Ne.symm (FreshSupply.never_reissued reachable issued))

end Generational

end Grass.Core
