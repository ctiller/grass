import Grass.CFG.Contract
import Grass.Construct.Fragment.Source

/-!
# Verified finite instruction fragments

Instruction semantics and effect derivation are explicit parameters supplied by
the owning operation family.  Construction records exact expansion and local
all-exit correctness; it does not infer semantics from generated syntax or
grant proof authority to a generator.
-/

namespace Grass.Construct.Fragment

open Grass.CFG

universe u v w

/-- Whole-fragment execution relation supplied by an operation semantics. -/
structure Semantics (Instruction : Type u) (State : Type v) where
  Executes : List Instruction → State → State → Prop

/-- Exact effect derivation supplied by an operation/profile layer. -/
structure EffectModel (Instruction : Type u) (Effect : Type w) where
  derive : List Instruction → Effect

/-- A state satisfies exactly one declared exit, by exit identity. -/
def ClassifiesExactlyOneExit {State : Type v}
    (contract : BlockContract State) (state : State) : Prop :=
  ∃ selected ∈ contract.exits,
    selected.ensures state ∧
      ∀ candidate ∈ contract.exits,
        candidate.ensures state → candidate.tag = selected.tag

/-- A finite source with an exact derived effect and a local all-exit theorem. -/
structure VerifiedFragment {Instruction : Type u} {State : Type v} {Effect : Type w}
    (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect)
    (contract : BlockContract State) where
  source : Source Instruction
  contractWellFormed : contract.WellFormed
  effects : Effect
  effectsExact : effects = effectModel.derive source.expand
  localCorrect : ∀ before after,
    contract.requires before →
    semantics.Executes source.expand before after →
    ClassifiesExactlyOneExit contract after

namespace VerifiedFragment

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {contract : BlockContract State}

/-- The writer-visible instruction count is derived from exact source expansion. -/
def instructionCount (fragment : VerifiedFragment semantics effectModel contract) : Nat :=
  fragment.source.instructionCount

/-- `VerifiedFragment.effects_eq_derived` exposes equality between the stored
effect summary and derivation over the selected source expansion. -/
theorem effects_eq_derived
    (fragment : VerifiedFragment semantics effectModel contract) :
    fragment.effects = effectModel.derive fragment.source.expand :=
  fragment.effectsExact

end VerifiedFragment

end Grass.Construct.Fragment
