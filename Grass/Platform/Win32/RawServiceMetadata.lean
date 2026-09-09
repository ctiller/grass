import Grass.Platform.Win32.RawStep

/-!
# Raw service metadata inversion

These bounded inversions expose metadata preservation and recover the exact
pending WriteFile occurrence for an already classified raw service step. They
add no classification or exhaustiveness claim for arbitrary raw transitions.
-/

namespace Grass.Platform.Win32.Raw.RawStep

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
  {graph nextGraph : Graph} {before after : RawState} {event : Event}
  {call : CallProtocol.CallId} {agent : ContextId} {action : WriteFile.Action}

/-- An actual classified provider service step preserves the complete raw
protocol metadata. -/
theorem service_metadata
    (step : RawStep loaded realization graph before (.providerService call agent action)
      event after nextGraph) :
    after.metadata = before.metadata := by
  obtain ⟨record, output, receipt, _, rfl, _, _, _⟩ := service_receipt step
  exact receipt.metadata_unchanged

/-- If the raw metadata names a supplied WriteFile occurrence at the serviced
call, inversion recovers a receipt indexed by that same occurrence. -/
theorem service_receipt_sameRecord
    {record : CallProtocol.Pending WriteFile.Request}
    (step : RawStep loaded realization graph before (.providerService call agent action)
      event after nextGraph)
    (pending : before.metadata.pending.lookup call =
      some (WriteFile.embedPending record)) :
    ∃ (output : Vec Byte)
      (receipt : WriteFile.ServiceReceipt realization before call record action output),
      record.agent = agent ∧ receipt.after = after ∧
      event.kind = (if output.length = 0 then .internal
        else .endpoint (.published call output)) ∧
      graph.Realizes realization.causal receipt.protocol ∧
      nextGraph.Realizes realization.causal receipt.nextProtocol := by
  obtain ⟨actual, output, receipt, actualAgent, receiptAfter, kind, prior, next⟩ :=
    service_receipt step
  have metadata := (CallProtocol.Metadata.pack?_fields receipt.projected).2
  have protocolPending : receipt.protocol.pending = before.metadata.pending :=
    congrArg CallProtocol.Metadata.pending metadata
  have sameEmbedded : WriteFile.embedPending actual = WriteFile.embedPending record := by
    apply Option.some.inj
    exact receipt.pre.pending.lookup.symm.trans
      ((congrArg (fun table => table.lookup call) protocolPending).trans pending)
  have sameRecord : actual = record := WriteFile.embedPending_injective sameEmbedded
  subst actual
  exact ⟨output, receipt, actualAgent, receiptAfter, kind, prior, next⟩

end Grass.Platform.Win32.Raw.RawStep
