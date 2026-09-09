import Grass.Platform.Win32.RawStep
import Tests.Platform.Win32WriteFileService

namespace Grass.Tests.Win32RawStep

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32 Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader
open Grass.Platform.Win32.Raw Grass.Tests.Win32WriteFileService

theorem empty_graph_path (a b : WriteFile.CausalNode) :
    ¬ Relation.TransGen (fun x y => (x, y) ∈ ([] : Graph)) a b := by
  intro path
  cases path with
  | single h => simp at h
  | tail _ h => simp at h

theorem empty_graph_valid (state : RawState) : Graph.WellFormed [] state := by
  constructor
  · intro edge member
    simp at member
  · intro node
    exact empty_graph_path node node

theorem empty_graph_realizes (state : WriteFile.ProtocolState) :
    Graph.Realizes [] Grass.Tests.Win32WriteFile.noEffects.causal state := by
  intro a b
  constructor
  · intro impossible
    exact False.elim impossible
  · intro path
    exact False.elim (empty_graph_path a b path)

def quietEvent : Event := ⟨[], [], .internal⟩

/-- Construct the installed case from the actual five-loan handoff and checked
quiet provider step. The loaded image is irrelevant to this service-only case;
this fixture does not claim an actual CALL or native dispatch. -/
theorem quiet_service {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    RawStep loaded Grass.Tests.Win32WriteFile.noEffects [] before
      (.providerService call record.agent action) quietEvent receipt₁.after [] := by
  apply RawStep.service receipt₁
  · exact ⟨by constructor <;> rfl, empty_graph_valid _, empty_graph_valid _,
      Graph.extends_refl []⟩
  · rfl
  · exact empty_graph_realizes _
  · exact empty_graph_realizes _

/-- A provider service choice cannot forge a stdout acquisition observation,
even if the caller supplies otherwise arbitrary suffix and graph data. -/
theorem service_cannot_acquire_stdout {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {graph nextGraph : Graph} {start finish : RawState} {event : Event}
    {id stdoutCall : CallProtocol.CallId} {agent : ContextId} {handle : BitVec 64}
    {chosen : WriteFile.Action}
    (wrong : event.kind = .endpoint (.stdoutAcquired stdoutCall handle)) :
    ¬ RawStep loaded realization graph start (.providerService id agent chosen)
      event finish nextGraph := by
  intro step
  obtain ⟨_, output, _, _, _, kind, _, _⟩ := step.service_receipt
  rw [wrong] at kind
  split at kind
  · cases kind
  · cases EventKind.endpoint.inj kind

end Grass.Tests.Win32RawStep
