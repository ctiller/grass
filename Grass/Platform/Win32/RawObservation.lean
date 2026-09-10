import Grass.Platform.Win32.RawPrefix
import Grass.Semantics.Observation
import Grass.Semantics.History

/-! The fixed raw endpoint projection. Raw histories still retain every CPU,
service and diagnostic edge; projection does not establish coverage, external
agency, or permission to erase an infinite execution. -/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical

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

/-- Update the public history observation from one actual raw event. Only
publication and process-exit endpoints contribute. The call identity remains
present in the full event history; this fixed public view exposes its bytes and
numeric exit status. -/
def observeEvent (observed : Vec Byte × Option Nat) (event : ULift.{1} Event) :
    Vec Byte × Option Nat :=
  match event.down.kind with
  | .endpoint (.published _ bytes) => (observed.1 ++ bytes, observed.2)
  | .endpoint (.processExited _ status) => (observed.1, some status.toNat)
  | .endpoint (.stdoutAcquired ..) | .endpoint (.apiReturned ..) |
      .internal | .cpu _ | .outsideProfile _ => observed

/-- Canonical public observation of a raw choice-bearing history trace.
Published endpoint payloads accumulate in execution order; status is selected
only by an actual process-exit endpoint. -/
def historyObservation (events : List (ULift.{1} Event)) : Vec Byte × Option Nat :=
  events.foldl observeEvent (Vec.empty, none)

@[simp] theorem historyObservation_nil : historyObservation [] = (Vec.empty, none) := rfl

@[simp] theorem historyObservation_snoc_published (events : List (ULift.{1} Event))
    (event : Event) (call : Grass.Op.CallProtocol.CallId) (bytes : Vec Byte)
    (kind : event.kind = .endpoint (.published call bytes)) :
    historyObservation (events ++ [⟨event⟩]) =
      ((historyObservation events).1 ++ bytes, (historyObservation events).2) := by
  simp [historyObservation, observeEvent, kind]

@[simp] theorem historyObservation_snoc_processExited (events : List (ULift.{1} Event))
    (event : Event) (call : Grass.Op.CallProtocol.CallId) (status : BitVec 32)
    (kind : event.kind = .endpoint (.processExited call status)) :
    historyObservation (events ++ [⟨event⟩]) =
      ((historyObservation events).1, some status.toNat) := by
  simp [historyObservation, observeEvent, kind]

/-- Apply the fixed observer to the actual path retained by any raw history. -/
def observeHistory {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag)}
    (history : (system loaded realization environment interpretation covered).History) :
    Vec Byte × Option Nat :=
  historyObservation history.path.events

end Grass.Platform.Win32.Raw
