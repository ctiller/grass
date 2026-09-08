import Grass.Std.Logical.Vec

/-!
# The recursors and the fold laws have to match

`Grass/Std/Logical/Vec.lean` supplies two induction principles. `Vec.recOnPush`
takes a sequence apart from the end and `Vec.recOnCons` from the front, and the
module's own commentary explains why both are needed: a consumer that *builds* a
sequence wants the first, and a consumer that *reads* one wants the second.

An induction principle is only usable with a law shaped like the case it hands
you. `Vec.foldl_push` and `Vec.foldr_push` match `recOnPush`. `Vec.foldl_cons`
and `Vec.foldr_cons` match `recOnCons`, and until they existed the cons recursor
had no fold law to run with at all — the same shape as the gap `recOnCons` was
itself added to close, one level up.

**What that costs is not difficulty, it is the seam.** With the cons laws absent,
`induction v using Vec.recOnCons` on a `foldr` goal reduces to a raw
`List.foldr` over `[].append u.toList`, and the proof continues in `List`. That
is the leak the private structure exists to prevent, arrived at by a consumer who
did everything right. Reproduce it by deleting `Vec.foldr_cons` and rebuilding
this module.

This fixture pins both pairs, and then does the thing the pins exist for: a proof
by cons induction that only goes through because the matching law is there.
-/

namespace Grass.Tests.Std.FoldInduction

open Grass.Std.Logical

variable {α β : Type}

/-! ## The four laws fire

Two per recursor. Written as bare `simp` so that removing an `@[simp]` from the
library breaks this file.
-/

example (f : α → β → β) (init : β) (a : α) (w : Vec α) :
    Vec.foldr f init (Vec.singleton a ++ w) = f a (Vec.foldr f init w) := by simp

example (f : β → α → β) (init : β) (a : α) (w : Vec α) :
    Vec.foldl f init (Vec.singleton a ++ w) = Vec.foldl f (f init a) w := by simp

example (f : α → β → β) (init : β) (a : α) (w : Vec α) :
    Vec.foldr f init (w.push a) = Vec.foldr f (f a init) w := by simp

example (f : β → α → β) (init : β) (a : α) (w : Vec α) :
    Vec.foldl f init (w.push a) = f (Vec.foldl f init w) a := by simp

/-! ## A proof that needs the cons pair

`Vec.foldr` with an injective step and a fixed seed determines its input. This is
the shape a consumer that folds a sequence into a digest, a tree, or an encoding
needs, and `Grass/Build/Cache/Key.lean` is the module in this tree that has it:
`importedSummariesTree` is a `Vec.foldr` whose docstring claims the result
retains import order.

The proof is by `Vec.recOnCons` in both arguments and uses nothing but
`Vec.foldr_empty` and `Vec.foldr_cons`. Without the latter it does not merely
fail — it succeeds in `List`, which is worse.
-/

/-- A step function that cannot lose its element or its tail. -/
structure InjectiveStep (α β : Type) where
  step : α → β → β
  seed : β
  /-- Two applications agree only when both arguments do. -/
  injective : ∀ a b x y, step a x = step b y → a = b ∧ x = y
  /-- The seed is not in the image, so a longer fold is never a shorter one. -/
  seed_not_step : ∀ a x, step a x ≠ seed

theorem foldr_injective (s : InjectiveStep α β) :
    ∀ v w : Vec α, Vec.foldr s.step s.seed v = Vec.foldr s.step s.seed w → v = w := by
  intro v
  induction v using Vec.recOnCons with
  | empty =>
    intro w
    induction w using Vec.recOnCons with
    | empty => intro _; rfl
    | cons b u _ => intro h; exact absurd h.symm (s.seed_not_step b _)
  | cons a t ih =>
    intro w
    induction w using Vec.recOnCons with
    | empty => intro h; exact absurd h (s.seed_not_step a _)
    | cons b u _ =>
      intro h
      simp only [Vec.foldr_cons] at h
      obtain ⟨hab, htu⟩ := s.injective a b _ _ h
      subst hab
      exact congrArg (Vec.singleton a ++ ·) (ih u htu)

end Grass.Tests.Std.FoldInduction
