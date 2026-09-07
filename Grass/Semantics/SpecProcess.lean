import Grass.Core.Demand
import Grass.Semantics.Observation

/-!
# Minimal captured specification boundary

This is the foundation-level root consumed by certificates. Domain DSLs and
resource libraries construct values of this type; they do not extend the
verified gate with alternate correctness routes.
-/

namespace Grass

universe u

/-- One exact portable behavior and its independently keyed demands. -/
structure SpecProcess where
  Input : Type u
  AuditEvent : Type u
  Observation : Type u
  admits : Input -> Prop
  observationProjection : ObservationProjection AuditEvent Observation
  accepts : Input -> List Observation -> Prop
  acceptsPending : Input -> List Observation -> Prop
  acceptsInfinite : Input ->
    InfiniteObservation observationProjection -> Prop
  requirements : DemandFamily.{u}

namespace SpecProcess

/-- Acceptance for one exhaustive maximal-execution disposition. Finite,
environment-pending, and infinite behavior use independently authored
specification predicates; infinite acceptance is never supplied by a default. -/
def AcceptsComplete (spec : SpecProcess) (input : spec.Input) :
    CompleteObservation spec.observationProjection -> Prop
  | .finite observations => spec.accepts input observations
  | .pending observations => spec.acceptsPending input observations
  | .infinite observations => spec.acceptsInfinite input observations

@[simp]
theorem acceptsComplete_finite (spec : SpecProcess) (input : spec.Input)
    (observations : List spec.Observation) :
    spec.AcceptsComplete input (.finite observations) =
      spec.accepts input observations := rfl

@[simp]
theorem acceptsComplete_pending (spec : SpecProcess) (input : spec.Input)
    (observations : List spec.Observation) :
    spec.AcceptsComplete input (.pending observations) =
      spec.acceptsPending input observations := rfl

@[simp]
theorem acceptsComplete_infinite (spec : SpecProcess) (input : spec.Input)
    (observations : InfiniteObservation spec.observationProjection) :
    spec.AcceptsComplete input (.infinite observations) =
      spec.acceptsInfinite input observations := rfl

end SpecProcess

end Grass
