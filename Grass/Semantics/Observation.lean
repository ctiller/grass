/-!
# Observation contracts

An observation projection operates on a whole finite audit trace.  This is
intentional: lawful normalization may hide events or coalesce several physical
events into one abstract observation.
-/

namespace Grass

universe u v w

/-- A specification-owned projection from audit traces to observations. -/
structure ObservationProjection (Event : Type u) (Observation : Type v) where
  project : List Event -> List Observation

namespace ObservationProjection

variable {Event : Type u} {Middle : Type v} {Observation : Type w}

/-- The projection which exposes every event unchanged. -/
def identity (Event : Type u) : ObservationProjection Event Event where
  project := id

/-- Compose two trace projections without exposing either implementation. -/
def comp (outer : ObservationProjection Middle Observation)
    (inner : ObservationProjection Event Middle) :
    ObservationProjection Event Observation where
  project events := outer.project (inner.project events)

@[simp] theorem identity_project (events : List Event) :
    (identity Event).project events = events := rfl

@[simp] theorem comp_project
    (outer : ObservationProjection Middle Observation)
    (inner : ObservationProjection Event Middle) (events : List Event) :
    (outer.comp inner).project events = outer.project (inner.project events) := rfl

end ObservationProjection

end Grass
