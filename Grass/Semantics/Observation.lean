/-!
# Observation contracts

An observation projection operates on a whole finite audit trace.  This is
intentional: lawful normalization may hide events or coalesce several physical
events into one abstract observation.
-/

namespace Grass

universe u v w x

/-- A specification-owned projection from audit traces to observations. -/
structure ObservationProjection (Event : Type u) (Observation : Type v) where
  project : List Event -> List Observation

namespace ObservationProjection

variable {Event : Type u} {Middle : Type v} {Observation : Type w}
  {Upper : Type x}

/-- Two observation projections are equal when they agree on every complete
finite audit trace. -/
@[ext] theorem ext {left right : ObservationProjection Event Observation}
    (project : forall events, left.project events = right.project events) :
    left = right := by
  cases left with
  | mk leftProject =>
      cases right with
      | mk rightProject =>
          congr
          funext events
          exact project events

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

/-- Exposing every intermediate observation leaves a projection unchanged. -/
@[simp] theorem identity_comp
    (projection : ObservationProjection Event Observation) :
    (identity Observation).comp projection = projection := by
  ext events
  rfl

/-- Feeding every event unchanged into a projection leaves it unchanged. -/
@[simp] theorem comp_identity
    (projection : ObservationProjection Event Observation) :
    projection.comp (identity Event) = projection := by
  ext events
  rfl

/-- Whole-trace projection composition is associative. -/
@[simp] theorem comp_assoc
    (outer : ObservationProjection Upper Observation)
    (middle : ObservationProjection Middle Upper)
    (inner : ObservationProjection Event Middle) :
    (outer.comp middle).comp inner = outer.comp (middle.comp inner) := by
  ext events
  rfl

end ObservationProjection

end Grass
