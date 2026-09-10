import Grass.Platform.Win32.EvaluatedCall
import Grass.Platform.Win32.ApiDispatch
import Grass.Platform.Win32.RawState

/-! Deterministic incoming CALL preparation shared by actual endpoint consumers.
All retained evidence comes from one incoming raw state and one checked CPU
evaluation. Endpoint ABI handoff, provider observations and graphs remain with
their existing checkers. Refusal supplies no execution edge. -/

namespace Grass.Platform.Win32.CallEntry

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

/-- Check caller readiness, execute the actual CALL, and select its loaded import.
Source encoding and expected API are checked against the computed receipt and
dispatch. Existing dependent pairs retain the evidence without a second carrier. -/
def prepare? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (raw : RawState)
    (expectedApi : Signatures.Api) (expectedEncoding : InsnEncoding) :
    Option (Σ checked : ExecutionState.State ApiRequest, Σ policy : CpuAccessPolicy,
      Σ called : CallFactory.Success policy checked.machine,
        { dispatch : ApiDispatch.Binding loaded
            (called.receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 called.displacement.toInt)
            called.receipt.read.value //
          raw.checked? = some checked ∧ checked.ControlConsistent ∧
          Cpu.policy? loaded checked.machine = some policy ∧
          CheckedExecution.normal policy checked.machine checked.machine.statusFlags = some (.ok (.call called)) ∧
          ApiDispatch.ofCall? loaded called = some dispatch ∧
          dispatch.api = expectedApi ∧ called.receipt.fetch.site.encoding = expectedEncoding }) :=
  match raw.checked? with
  | none => none
  | some checked =>
    match projected : checked.callProtocol? with
    | none => none
    | some protocol =>
      if control : checked.control = .caller inputs.thread then
      if registered : protocol.machine.contexts.lookup inputs.thread = some .thread then
      if available : CallProtocol.callerPending protocol inputs.thread = false then
        have ready : checked.ControlConsistent := by
          unfold ExecutionState.State.ControlConsistent
          rw [control]
          exact ⟨protocol, projected, ⟨.thread, registered⟩, available⟩
        match selected : Cpu.policy? loaded checked.machine with
        | none => none
        | some policy =>
          match evaluated : CheckedExecution.normal policy checked.machine checked.machine.statusFlags with
          | some (.ok (.call called)) =>
            if encoding : called.receipt.fetch.site.encoding = expectedEncoding then
              match dispatched : ApiDispatch.ofCall? loaded called with
              | none => none
              | some dispatch =>
                if api : dispatch.api = expectedApi then
                  some ⟨checked, policy, called, dispatch, rfl, ready, selected,
                    evaluated, dispatched, api, encoding⟩
                else none
            else none
          | _ => none
      else none else none else none

end Grass.Platform.Win32.CallEntry

namespace Grass.Platform.Win32.Raw.EvaluatedCall

open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32.Loader

/-- Derive evaluation provenance directly from the selected factory equation. -/
def ofFactory {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {before : ExecutionState.State ApiRequest} {policy : CpuAccessPolicy}
    {called : CallFactory.Success policy before.machine}
    (selected : Cpu.policy? loaded before.machine = some policy)
    (evaluated : CheckedExecution.normal policy before.machine before.machine.statusFlags =
      some (.ok (.call called))) : EvaluatedCall loaded before called.receipt :=
  { policy, selected, flags := before.machine.statusFlags, success := called,
    evaluated, receiptExact := HEq.rfl }

end Grass.Platform.Win32.Raw.EvaluatedCall
