import Grass.Platform.Win32.RawPendingService
import Tests.Platform.Win32RawServicePrefix

/-! The existing two-edge fixture has real pending endpoints. Inversion covers
any admitted choice between its first pair, not merely the chosen quiet edge. -/

namespace Grass.Tests.Win32RawPendingService

open Grass.Platform.Win32 Grass.Platform.Win32.Loader Grass.Platform.Win32.Raw
open Grass.Tests.Win32RawServicePrefix Grass.Tests.Win32WriteFileService
open Grass.Tests.Win32RawStep

theorem choices_between_first_frontiers {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) {choice : Choice} {event : Event}
    (step : RawStep loaded Grass.Tests.Win32WriteFile.noEffects
      Grass.Tests.Win32WriteFileConsolePublication.environment noReturnInterpretation
      [] (raw 0) choice event (raw 1) []) :
    ∃ selectedAction, choice = .providerService call record.agent selectedAction := by
  obtain ⟨_, selectedAction, _, _, _, _, selected, _⟩ :=
    step.pending_to_pending_service receipt₁.control receipt₁.after_control
  exact ⟨selectedAction, selected⟩

/-- Two actual internal service events retain pending control. No third edge
or infinite extension is required by the contiguous-segment proof. -/
theorem two_edge_pending {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    (raw 2).control = .pending call record.caller record.agent := by
  let states : Fin 3 → ExecutionState.RawState := fun index => raw index.val
  let graphs : Fin 3 → Graph := fun _ => []
  let choices : Fin 2 → Choice := fun _ => .providerService call record.agent action
  let events : Fin 2 → Event := fun _ => quietEvent
  have steps : ∀ index : Fin 2,
      RawStep loaded Grass.Tests.Win32WriteFile.noEffects
        Grass.Tests.Win32WriteFileConsolePublication.environment noReturnInterpretation
        (graphs index.castSucc) (states index.castSucc) (choices index) (events index)
        (states index.succ) (graphs index.succ) := fun index => two_steps loaded index.val index.isLt
  exact RawStep.pending_segment states graphs choices events steps 0 2 (by decide)
    (by rfl) (by intro offset below; exact Or.inl rfl) 2 (by decide)

end Grass.Tests.Win32RawPendingService
