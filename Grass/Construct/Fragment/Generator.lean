import Grass.Construct.Fragment.Verified

/-!
# Verified fragment generators

A generator is a dependent function returning a `VerifiedFragment` for every
accepted parameter.  Running the function is construction; the returned
contract validity, exact effects, and local correctness fields are the proof
authority.
-/

namespace Grass.Construct.Fragment

open Grass.CFG

universe u v w x

/-- A parameterized family of verified finite fragments. -/
structure Generator (Param : Type x) (Instruction : Type u) (State : Type v)
    (Effect : Type w) (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  contract : Param → BlockContract State
  generate : (parameter : Param) →
    VerifiedFragment semantics effectModel (contract parameter)

namespace Generator

variable {Param : Type x} {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}

/-- Exact expanded instructions selected for one generator application. -/
def expand (generator : Generator Param Instruction State Effect semantics effectModel)
    (parameter : Param) : List Instruction :=
  (generator.generate parameter).source.expand

/-- Every generated instance exposes its effect as the derivation over its exact
expanded instruction list. -/
theorem generated_effects_exact
    (generator : Generator Param Instruction State Effect semantics effectModel)
    (parameter : Param) :
    (generator.generate parameter).effects =
      effectModel.derive (generator.expand parameter) :=
  (generator.generate parameter).effectsExact

end Generator

end Grass.Construct.Fragment
