import Grass.Core.Uid

/-!
# Nominal identity opacity fixtures

The supported runtime interface distinguishes identities by equality while its
diagnostic representation does not expose their allocation ordinals.
-/

namespace Grass.Tests.UidOpacity

open Grass.Core

universe u

inductive Tag

def first : Uid Tag := (FreshSupply.initial (Tag := Tag)).fresh.1

def second : Uid Tag :=
  (FreshSupply.initial (Tag := Tag)).fresh.2.fresh.1

theorem first_ne_second : first ≠ second := by
  exact Ne.symm (FreshSupply.never_reissued
    (s := (FreshSupply.initial (Tag := Tag)).fresh.2)
    (t := (FreshSupply.initial (Tag := Tag)).fresh.2)
    (.refl _)
    ((FreshSupply.issued_fresh (FreshSupply.initial (Tag := Tag)) first).2
      (.inr rfl)))

/-- Every identity has the same redacted diagnostic representation, independent
of its tag and allocation ordinal. -/
theorem repr_uid_redacted {T : Type u} (identity : Uid T) :
    repr identity = "<uid>" := rfl

/-- A representative downstream structure deriving `Repr` continues to use the
redacted identity representation rather than exposing an ordinal. -/
structure IdentityEnvelope where
  identity : Uid Tag
  deriving Repr

theorem repr_identityEnvelope_redacted
    (left right : IdentityEnvelope) : repr left = repr right := by
  cases left
  cases right
  rfl

end Grass.Tests.UidOpacity
