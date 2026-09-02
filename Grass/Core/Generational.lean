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

`Generational α` pairs the recycled value with a `Uid` that is not recycled. Two
occurrences of the same number in different generations are then unequal, so a
stale reference simply fails to match — no comparison against a liveness table,
and no reasoning about whether the number "looks current".

**Custody note.** `Grass.Core` is not owned by the memory agent. This module is
temporary custody under `docs/MEMORY_IMPLEMENTATION_PLAN.md` §2.
-/

namespace Grass.Core

universe u

/-- Phantom tag for generation identities. -/
inductive GenerationTag : Type

/--
The identity of one generation of a recycled value.

Minted from a `FreshSupply` like any other `Uid`, so generations themselves never
recycle however often the value they qualify does.
-/
abbrev GenerationId := Uid GenerationTag

/--
An externally recycled value, qualified by the generation it belongs to.

Equality compares both components, so a recycled number in a new generation is a
distinct identity from the same number in an old one.
-/
structure Generational (α : Type u) where
  /-- The externally chosen value, which may be reused after this generation ends. -/
  value : α
  /-- The generation this occurrence belongs to. -/
  generation : GenerationId

namespace Generational

variable {α : Type u}

instance [DecidableEq α] : DecidableEq (Generational α) := fun a b =>
  if h : a.value = b.value ∧ a.generation = b.generation then
    .isTrue (by cases a; cases b; simp_all)
  else
    .isFalse (by
      intro eq
      exact h ⟨congrArg Generational.value eq, congrArg Generational.generation eq⟩)

/--
The staleness law.

Two occurrences in different generations are different identities, whatever their
values. This is what a stale completion runs into: it carries the generation it
was issued in, which no longer matches.
-/
theorem ne_of_generation_ne {a b : Generational α} (h : a.generation ≠ b.generation) :
    a ≠ b := fun eq => h (congrArg Generational.generation eq)

/--
Equal numbers do not make equal identities.

Stated separately from `ne_of_generation_ne` because it is the reading that
matters at a use site: matching the recycled number is never sufficient.
-/
theorem value_eq_insufficient {a b : Generational α}
    (_hv : a.value = b.value) (hg : a.generation ≠ b.generation) : a ≠ b :=
  ne_of_generation_ne hg

theorem eq_iff {a b : Generational α} :
    a = b ↔ a.value = b.value ∧ a.generation = b.generation := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨hv, hg⟩; cases a; cases b; simp_all

end Generational

end Grass.Core
