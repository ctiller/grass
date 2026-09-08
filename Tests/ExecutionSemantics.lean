import Grass.Semantics.Execution

/-!
# Relational execution fixtures

These elaboration fixtures exercise the structural terminal-state contract.
-/

namespace Grass.Tests.ExecutionSemantics

def stopped : RelationalSystem Bool where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial _ _ := True
  Step _ _ _ _ _ _ := False
  Terminal _ _ := True
  InfiniteConsistent _ _ _ _ _ := False
  Extends _ _ := True
  extendsRefl _ := trivial
  extendsTrans _ _ := trivial
  stepExtends transition := False.elim transition
  terminalNoStep _ := fun {_ _ _ _} transition => transition

/-- Consumers may rule out every attempted transition at a terminal frontier. -/
theorem stopped_has_no_successor
    (terminal : stopped.Terminal () ()) :
    ¬ ∃ choice event nextState nextGraph,
      stopped.Step () () choice event nextState nextGraph := by
  rintro ⟨choice, event, nextState, nextGraph, transition⟩
  exact stopped.terminalNoStep terminal transition

end Grass.Tests.ExecutionSemantics
