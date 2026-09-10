import Grass.Semantics.Waiting
import Grass.Semantics.Observation

/-! A complete relational domain, including its selected wait protocol and
terminal outcome observation. This is semantic data, not a certificate root. -/

namespace Grass

universe uSystem uRequest uResponse uOccurrence

/- These four independently selected field-carrier universes necessarily occur
together in the structure's result maximum; retain them as separate parameters. -/
set_option linter.checkUnivs false
/-- The outcome language is fixed by the captured syntax. -/
structure BehaviorModel (Outcome : Type) where
  Event : Type uSystem
  Observation : Type
  observationProjection : ObservationProjection Event Observation
  Request : Type uRequest
  system : RelationalSystem Event
  protocol : WaitProtocol.{uRequest, uResponse} Request
  boundary : system.WaitBoundary.{uSystem, uRequest, uResponse, uOccurrence} protocol
  result : system.State → system.Graph → Option Outcome
  terminal_result : ∀ state graph,
    system.Terminal state graph ↔ ∃ outcome, result state graph = some outcome
  terminal_no_step : ∀ {state graph}, system.Terminal state graph →
    ∀ choice event next nextGraph, ¬ system.Step graph state choice event next nextGraph
set_option linter.checkUnivs true

namespace BehaviorModel

abbrev History {Outcome : Type} (model : BehaviorModel.{uSystem, uRequest, uResponse,
    uOccurrence} Outcome) := model.system.History
abbrev Complete {Outcome : Type} (model : BehaviorModel.{uSystem, uRequest, uResponse,
    uOccurrence} Outcome) :=
  RelationalSystem.CompleteHistory model.boundary

end BehaviorModel
end Grass
