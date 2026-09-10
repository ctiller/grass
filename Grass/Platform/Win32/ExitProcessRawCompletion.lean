import Grass.Platform.Win32.RawStep

/-! Install the checked terminal observation with unchanged archived logs.
No protocol-return boundary is appended. Actual enclosing history, native
observation applicability, and terminal obligations remain separate. -/

namespace Grass.Platform.Win32.ExitProcess.Completion

open Grass.Core Grass.Op
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

variable {environment : ConsoleEnvironment} {before : RawState} {observed : Observation}

/-- Canonical empty log suffix with the exact observed terminal result. -/
def event (completion : Completion environment before observed) : Raw.Event :=
  Raw.Event.between before completion.after
    (.endpoint (.processExited observed.call observed.status))

theorem event_exact (completion : Completion environment before observed) :
    completion.event.memory = [] ∧ completion.event.boundaries = [] :=
  Raw.Event.between_suffixes
    (List.append_nil before.machine.machine.events).symm
    (List.append_nil before.metadata.boundaries).symm

theorem event_appends (completion : Completion environment before observed) :
    completion.event.Appends before completion.after :=
  Raw.Event.between_appends
    (List.append_nil before.machine.machine.events).symm
    (List.append_nil before.metadata.boundaries).symm

/-- The checked observation equation installs this exact archival snapshot.
The graph premises assert only existing log/graph agreement. -/
theorem rawStep (completion : Completion environment before observed)
    (completed : complete? environment before observed = some completion)
    {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {realization : WriteFile.Realization} {interpretation : WriteFile.ReturnInterpretation}
    {graph nextGraph : Raw.Graph}
    (priorGraph : graph.WellFormed before)
    (nextWellFormed : nextGraph.WellFormed completion.after)
    (extendsGraph : graph.Extends nextGraph) :
    Raw.RawStep loaded realization environment interpretation graph before
      (.exitObservation observed.call observed.status) completion.event completion.after nextGraph :=
  Raw.RawStep.completedExit completion completed
    ⟨completion.event_appends, priorGraph, nextWellFormed, extendsGraph⟩

end Grass.Platform.Win32.ExitProcess.Completion
