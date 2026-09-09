import Grass.Semantics.BehaviorContract

namespace Grass

/-- Author assumptions are interpreted separately from lowering certificates. -/
inductive LivenessAssumption where
  | environmentResponsive
deriving DecidableEq

/-- An authored theorem request; adding it does not filter the denotation. -/
inductive LivenessContract where
  | terminatesUnder (assumptions : List LivenessAssumption)
deriving DecidableEq

/-- The sole specification root retains the exact captured contract. -/
structure SpecProcess {R : Type} [Resource.ResourceModel R] (resources : R) where
  contract : BehaviorContract resources
  liveness : List LivenessContract

namespace SpecProcess
variable {R : Type} [Resource.ResourceModel R] {resources : R}
def ofRelational (contract : BehaviorContract resources) : SpecProcess resources :=
  ⟨contract, []⟩
def withLiveness (spec : SpecProcess resources) (fragment : LivenessContract) :
    SpecProcess resources := ⟨spec.contract, spec.liveness ++ [fragment]⟩
abbrev Input (spec : SpecProcess resources) := spec.contract.Input
abbrev Outcome (spec : SpecProcess resources) := spec.contract.Outcome
abbrev Interpretation (spec : SpecProcess resources) := spec.contract.Interpretation
def admits (spec : SpecProcess resources) := spec.contract.admits
def denotation (spec : SpecProcess resources) := spec.contract.denotation
@[simp] theorem withLiveness_contract (spec : SpecProcess resources) (fragment : LivenessContract) :
    (spec.withLiveness fragment).contract = spec.contract := rfl
@[simp] theorem withLiveness_denotation (spec : SpecProcess resources)
    (fragment : LivenessContract) :
    (spec.withLiveness fragment).denotation = spec.denotation := rfl
end SpecProcess

end Grass
