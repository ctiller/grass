import Grass.Platform.Win32.RawPrefix
import Grass.Semantics.Observation

/-! The fixed raw endpoint projection. Raw histories still retain every CPU,
service and diagnostic edge; projection does not establish coverage, external
agency, or permission to erase an infinite execution. -/

namespace Grass.Platform.Win32.Raw

/-- Select an actual endpoint observation without reconstructing it from
registers or inferring it from provider activity. -/
def endpointObservation (event : ULift.{1} Event) : Option Observation :=
  match event.down.kind with
  | .endpoint observation => some observation
  | .internal | .cpu _ | .outsideProfile _ => none

/-- Public raw observations are exactly the endpoint events in execution order. -/
def observationProjection : Grass.ObservationProjection (ULift.{1} Event) Observation where
  project events := events.filterMap endpointObservation

/-- Projection preserves the split between an actual prefix and its suffix. -/
theorem observationProjection_append (before after : List (ULift.{1} Event)) :
    observationProjection.project (before ++ after) =
      observationProjection.project before ++ observationProjection.project after := by
  exact List.filterMap_append

/-- Each selected endpoint is retained with its actual call and payload. -/
theorem endpointObservation_exact (event : Event) (observation : Observation)
    (endpoint : event.kind = .endpoint observation) :
    endpointObservation ⟨event⟩ = some observation := by
  simp [endpointObservation, endpoint]

end Grass.Platform.Win32.Raw
