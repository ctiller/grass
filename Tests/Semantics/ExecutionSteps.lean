import Grass.Semantics.ExecutionSteps

namespace Grass.Tests.Semantics.ExecutionSteps

open Grass Grass.RelationalSystem

private inductive NoEvent
private inductive NoChoice

private def emptyOnly : RelationalSystem NoEvent where
  State := Unit
  Choice := NoChoice
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ choice _ _ _ => nomatch choice
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ choice _ => nomatch choice 0
  Extends := Eq
  extendsRefl := fun _ => rfl
  extendsTrans := Eq.trans
  stepExtends := by intro _ _ _ choice; exact nomatch choice

/-- The zero-step decomposition requires neither events nor choices to be inhabited. -/
theorem zero_without_inhabitants :
    ∃ (states : Fin 1 → emptyOnly.State) (graphs : Fin 1 → emptyOnly.Graph)
      (choices : Fin 0 → emptyOnly.Choice),
      states ⟨0, by decide⟩ = () ∧ graphs ⟨0, by decide⟩ = () ∧
      states ⟨0, by decide⟩ = () ∧ graphs ⟨0, by decide⟩ = () ∧
      ∀ index : Fin 0,
        emptyOnly.Step (graphs index.castSucc) (states index.castSucc) (choices index)
          (([] : List NoEvent).get index) (states index.succ) (graphs index.succ) :=
  (Steps.refl (system := emptyOnly) (state := ()) (graph := ())).exists_indexed_witnesses

end Grass.Tests.Semantics.ExecutionSteps
