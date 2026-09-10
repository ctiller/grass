import Grass.Platform.Win32.RawServiceContinuation
import Tests.Platform.Win32RawStep

namespace Grass.Tests.Win32RawServiceContinuation

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader
open Grass.Platform.Win32.Raw
open Grass.Tests.Win32RawStep
open Grass.Tests.Win32WriteFileService

/-! This finite regression checks the raw-to-service continuation bridge on the
actual five-loan fixture. It makes no infinite-execution or physical
nonresponse claim; the general suffix theorem is checked independently by the
library module. -/

/-- The second checked quiet receipt is also an installed raw service edge,
giving the fixture two consecutive actual edges without identifying their raw
states. -/
theorem quiet_service₂ {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    RawStep loaded Grass.Tests.Win32WriteFile.noEffects Grass.Tests.Win32WriteFileConsolePublication.environment [] receipt₁.after
      (.providerService call record.agent action) quietEvent receipt₂.after [] := by
  apply RawStep.service receipt₂
  · exact ⟨by constructor <;> rfl, empty_graph_valid _, empty_graph_valid _,
      Graph.extends_refl []⟩
  · rfl
  · exact empty_graph_realizes _
  · exact empty_graph_realizes _

/-- Both consecutive raw edges preserve the full metadata, while same-record
inversion recovers receipts tied to the actual pending occurrence and runtime
table. The unrelated runtime entry remains framed across the first edge. -/
theorem actual_two_edge_bridge {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    receipt₂.after.metadata = before.metadata ∧
      ∃ (output : Vec Byte)
        (service : WriteFile.ServiceReceipt Grass.Tests.Win32WriteFile.noEffects
          before call record action output),
        service.runtime = runtime ∧
        service.after.calls.lookup unrelatedCall = some .exitProcess ∧
        service.after.metadata = before.metadata ∧
        ¬ service.runtime.accepted = 1 := by
  have first := quiet_service loaded
  have second := quiet_service₂ loaded
  have firstMetadata := RawStep.service_metadata first
  have secondMetadata := RawStep.service_metadata second
  have pending : before.metadata.pending.lookup call =
      some (WriteFile.embedPending record) := by rfl
  obtain ⟨output, service, _, serviceAfter, _, _, _⟩ :=
    RawStep.service_receipt_sameRecord first pending
  refine ⟨secondMetadata.trans firstMetadata, output, service, ?_, ?_,
    service.metadata_unchanged, ?_⟩
  · exact every_receipt_uses_actual_runtime service
  · rw [serviceAfter]
    exact receipt₁_preserves_unrelated_runtime
  · exact invented_runtime_frontier_rejected service

end Grass.Tests.Win32RawServiceContinuation
