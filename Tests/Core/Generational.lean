import Grass.Core.Generational

/-!
# Generational identity fixtures

These fixtures pin both parts of the Core API's ABA defense: independently
managed domains cannot be mixed, and recycling an external value after a
reachable mint still produces a different identity.
-/

namespace Grass.Tests.Core.Generational

open Grass.Core

inductive HandleDomain
inductive SlotDomain

def handles0 : GenerationSupply HandleDomain := FreshSupply.initial
def handle0 : Generational HandleDomain Nat := (Generational.fresh handles0 44).1
def handles1 : GenerationSupply HandleDomain := (Generational.fresh handles0 44).2
def handle1 : Generational HandleDomain Nat := (Generational.fresh handles1 44).1

example : handle0.value = handle1.value := rfl

/-!
`GenerationSupply` is not a linear resource. Replaying the same supply repeats
the generation, so the history owner must thread the returned successor exactly
once. This fixture keeps that limitation visible rather than pretending the
private constructor can enforce supply ownership.
-/
example : (Generational.fresh handles0 44).1.generation =
    (Generational.fresh handles0 45).1.generation := rfl

example : handles1.Issued handle0.generation := by
  simpa [handles1, handle0] using Generational.fresh_issued handles0 44

example : FreshSupply.Reachable handles0 handles1 := by
  exact .mint (.refl handles0)

example : handle0 ≠ handle1 := by
  apply Generational.stale_ne_fresh (earlier := handles1) (later := handles1)
  · exact .refl handles1
  · simpa [handles1, handle0] using Generational.fresh_issued handles0 44

def slot0 : Generational SlotDomain Nat :=
  (Generational.fresh (FreshSupply.initial : GenerationSupply SlotDomain) 44).1

/--
error: Type mismatch
  slot0
has type
  Generational SlotDomain Nat
but is expected to have type
  Generational HandleDomain Nat
-/
#guard_msgs in
#check (slot0 : Generational HandleDomain Nat)

/--
error: Invalid `⟨...⟩` notation: Constructor for `Grass.Core.Generational` is marked as private
-/
#guard_msgs in
#check (⟨44, handle0.generation⟩ : Generational HandleDomain Nat)

end Grass.Tests.Core.Generational
