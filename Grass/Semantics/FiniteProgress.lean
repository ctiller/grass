import Grass.Semantics.BehaviorModel

/-! Finite-stop classification over every actual initialized history. This is a
single-system enabledness obligation, not a closed-subset network deadlock or
liveness theorem. It imposes no fairness or restriction on infinite execution.
A public certificate must select its canonical model and wait boundary; callers
cannot discharge this by replacing the execution relation or classifying a
stuck state as an unrelated external wait. -/

namespace Grass

universe uSystem uRequest uResponse uOccurrence

namespace BehaviorModel

variable {Outcome : Type}
  (model : BehaviorModel.{uSystem, uRequest, uResponse, uOccurrence} Outcome)

/-- There is an actual next edge from this exact history's state and graph. -/
def HasNext (history : model.History) : Prop :=
  ∃ choice event next nextGraph,
    model.system.Step history.graph history.state choice event next nextGraph

/-- Every actual finite execution is terminal, has a next edge, or is a
permitted wait at its exact pending occurrence. -/
def FiniteProgress : Prop :=
  ∀ history : model.History,
    model.system.Terminal history.state history.graph ∨
      model.HasNext history ∨
      Nonempty (RelationalSystem.PermanentWait model.boundary history)

variable {model}

/-- Away from terminal states and permitted waits, the obligation supplies an
actual next edge rather than merely a label for the reached state. -/
theorem FiniteProgress.hasNext (progress : model.FiniteProgress)
    (history : model.History)
    (nonterminal : ¬ model.system.Terminal history.state history.graph)
    (notWaiting : ¬ Nonempty (RelationalSystem.PermanentWait model.boundary history)) :
    model.HasNext history := by
  rcases progress history with ended | enabled | waiting
  · exact False.elim (nonterminal ended)
  · exact enabled
  · exact False.elim (notWaiting waiting)

/-- A reached nonterminal stuck state without a permitted wait refutes finite
progress, even if all existing transition-safety conditions hold vacuously. -/
theorem not_finiteProgress_of_stuck (history : model.History)
    (nonterminal : ¬ model.system.Terminal history.state history.graph)
    (stuck : ¬ model.HasNext history)
    (notWaiting : ¬ Nonempty (RelationalSystem.PermanentWait model.boundary history)) :
    ¬ model.FiniteProgress :=
  fun progress => stuck (progress.hasNext history nonterminal notWaiting)

end BehaviorModel
end Grass
