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

/-- `Generator.generated_contract_wellFormed` exposes contract closure for
every generated parameter instance. -/
theorem generated_contract_wellFormed
    (generator : Generator Param Instruction State Effect semantics effectModel)
    (parameter : Param) :
    (generator.contract parameter).WellFormed :=
  (generator.generate parameter).contractWellFormed

/-- The generated instruction count is exactly the length of the generator's
expanded instruction list. -/
@[simp] theorem generated_instructionCount
    (generator : Generator Param Instruction State Effect semantics effectModel)
    (parameter : Param) :
    (generator.generate parameter).instructionCount =
      (generator.expand parameter).length := by
  rfl

/-- `Generator.generated_execution_classified` transports every successful
generated execution from its declared entry to an exact exit classification. -/
theorem generated_execution_classified
    (generator : Generator Param Instruction State Effect semantics effectModel)
    (parameter : Param) {before after : State}
    (entry : (generator.contract parameter).requires before)
    (executes : semantics.Executes (generator.expand parameter) before after) :
    ClassifiesExactlyOneExit (generator.contract parameter) after :=
  (generator.generate parameter).localCorrect before after entry executes

end Generator

end Grass.Construct.Fragment
