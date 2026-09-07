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

/-- A single infinite event stream observed through all of its coherent finite
restrictions. The witness prevents an arbitrary family of unrelated finite
lists from masquerading as one infinite observation. -/
structure InfiniteObservation
    {Event : Type u} {Observation : Type v}
    (projection : ObservationProjection Event Observation) where
  approximant : Nat -> List Observation
  singleStream : exists priorEvents : List Event, exists eventAt : Nat -> Event,
    forall length,
      approximant length = projection.project
        (priorEvents ++
          List.ofFn (fun index : Fin length => eventAt index))

namespace InfiniteObservation

variable {Event : Type u} {Observation : Type v}
  {projection : ObservationProjection Event Observation}

/-- Observe every finite restriction of one event stream, retaining the exact
finite history which preceded that stream. -/
def ofEventStream (projection : ObservationProjection Event Observation)
    (priorEvents : List Event) (eventAt : Nat -> Event) :
    InfiniteObservation projection where
  approximant length := projection.project
    (priorEvents ++ List.ofFn (fun index : Fin length => eventAt index))
  singleStream := ⟨priorEvents, eventAt, fun _ => rfl⟩

/-- `InfiniteObservation.approximant_ofEventStream` exposes the exact finite
restriction selected by `InfiniteObservation.ofEventStream`. -/
@[simp]
theorem approximant_ofEventStream (projection : ObservationProjection Event Observation)
    (priorEvents : List Event) (eventAt : Nat -> Event) (length : Nat) :
    (ofEventStream projection priorEvents eventAt).approximant length =
      projection.project
        (priorEvents ++ List.ofFn (fun index : Fin length => eventAt index)) :=
  rfl

/-- `InfiniteObservation.single_stream_coherent` recovers the one-stream witness
retained by every infinite observation. -/
theorem single_stream_coherent (observations : InfiniteObservation projection) :
    exists priorEvents : List Event, exists eventAt : Nat -> Event,
      forall length,
        observations.approximant length = projection.project
          (priorEvents ++
            List.ofFn (fun index : Fin length => eventAt index)) :=
  observations.singleStream

/-- Infinite observations are equal when every finite approximant is equal;
the retained one-stream evidence is proof-irrelevant. -/
@[ext]
theorem ext {left right : InfiniteObservation projection}
    (approximant : forall length, left.approximant length =
      right.approximant length) : left = right := by
  cases left
  cases right
  congr
  funext length
  exact approximant length

/-- Equal finite histories and pointwise-equal streams produce the same
infinite observation. -/
theorem ofEventStream_congr
    {leftPrior rightPrior : List Event}
    {leftEvents rightEvents : Nat -> Event}
    (prior : leftPrior = rightPrior)
    (events : forall index, leftEvents index = rightEvents index) :
    ofEventStream projection leftPrior leftEvents =
      ofEventStream projection rightPrior rightEvents := by
  apply ext
  intro length
  simp [prior, funext events]

end InfiniteObservation

/-- The specification-visible observation of a complete functional execution,
distinguishing a finite result from one coherent infinite observation. -/
inductive CompleteObservation
    {Event : Type u} {Observation : Type v}
    (projection : ObservationProjection Event Observation) : Type v where
  | finite (observations : List Observation)
  | infinite (observations : InfiniteObservation projection)

end Grass
