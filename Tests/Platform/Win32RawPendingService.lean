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

end Grass.Tests.Win32RawPendingService
