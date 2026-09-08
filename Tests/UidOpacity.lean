import Grass.Core.Uid

/-!
# Nominal identity opacity fixtures

The supported runtime interface distinguishes identities by equality while its
diagnostic representation does not expose their allocation ordinals.
-/

namespace Grass.Tests.UidOpacity

open Grass.Core

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

example : repr first = "<uid>" := rfl

example : repr second = "<uid>" := rfl

end Grass.Tests.UidOpacity
