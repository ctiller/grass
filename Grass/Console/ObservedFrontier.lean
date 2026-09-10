import Grass.Console.ObservedBehavior

/-! Exact terminal-or-wait classification for the observed console model. -/

namespace Grass.Console.ObservedBehavior

open Grass.Semantics Grass.RelationalSystem
open Grass.Specification

variable {Outcome : Type}

/-- Every actual history is either terminal or retains an exact occurrence on
which the model permits permanent waiting.  This is a state classification; it
does not assume that an environment supplies any reply. -/
theorem terminal_or_permitted_wait (request : LineRequest Outcome)
    (rendering : LineRendering)
    (history : (system request rendering).History) :
    (system request rendering).Terminal history.state history.graph ∨
      Nonempty (PermanentWait (boundary request rendering) history) := by
  cases stateEq : history.state with
  | writing cut =>
      exact Or.inr ⟨⟨.output cut, stateEq, trivial⟩⟩
  | reporting selection =>
      exact Or.inr ⟨⟨.observation selection, stateEq, trivial⟩⟩
  | observed selection =>
      exact Or.inl ⟨selection, rfl⟩

end Grass.Console.ObservedBehavior
