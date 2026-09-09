import Grass.Semantics.Waiting
import Grass.Semantics.Observation

/-! A complete relational domain, including its selected wait protocol and
terminal outcome observation. This is semantic data, not a certificate root. -/

namespace Grass

/-- The outcome language is fixed by the captured syntax. -/
structure BehaviorModel (Outcome : Type) where
  Event : Type
  Observation : Type
  observationProjection : ObservationProjection Event Observation
  Request : Type
  system : RelationalSystem Event
  protocol : WaitProtocol Request
  boundary : system.WaitBoundary protocol
  result : system.State → system.Graph → Option Outcome
  terminal_result : ∀ state graph,
    system.Terminal state graph ↔ ∃ outcome, result state graph = some outcome
  terminal_no_step : ∀ {state graph}, system.Terminal state graph →
    ∀ choice event next nextGraph, ¬ system.Step graph state choice event next nextGraph

namespace BehaviorModel

abbrev History {Outcome : Type} (model : BehaviorModel Outcome) := model.system.History
abbrev Complete {Outcome : Type} (model : BehaviorModel Outcome) :=
  RelationalSystem.CompleteHistory model.boundary

end BehaviorModel
end Grass
