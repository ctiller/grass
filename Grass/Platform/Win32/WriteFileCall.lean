import Grass.Platform.Win32.WriteFileHandoff
import Grass.Platform.Win32.CpuPolicy
import Grass.ISA.X86.Execution.CallNormal

/-!
# Actual CALL to checked WriteFile custody

This boundary retains the actual CALL result and repacks the original protocol
metadata against that result. It binds the saved slot and continuation to the
instruction receipt before issuing the full ABI batch. Import-symbol resolution
and native provider identity remain separate obligations.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86
open Grass.Platform.Win32.Loader

/-- The fixed Windows policy and loaded roots used by this actual CALL receipt.
The target read uses the separate data selector at its computed numeric address. -/
structure CallPolicy {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Execution.CallNormal before afterFetch afterRead afterStore displacement) where
  policy : Execution.CpuAccessPolicy
  selected : Cpu.policy? loaded before = some policy
  fetchPolicy : receipt.fetch.run.policy = policy.operationPolicy
  context : receipt.fetch.run.context = policy.context
  contextKind : receipt.fetch.run.contextKind = policy.contextKind
  cause : receipt.fetch.run.cause = policy.cause
  code : receipt.fetch.descriptor.provenance = policy.code
  stack : receipt.storeDescriptor.provenance = policy.stack
  data : Cpu.dataProvenance? loaded
    (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt) 8 =
      some receipt.readDescriptor.provenance

/-- Repack the same metadata after the actual CPU transition. A failed check
remains a refusal; this function never resets pending calls or identity supplies. -/
def reachedCall? (before : ExecutionState.State ApiRequest)
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement) :
    Option (ExecutionState.State ApiRequest) :=
  if valid : (before.metadata.pack? receipt.result.machine).isSome then
    some
      { machine := receipt.result
        metadata := before.metadata
        control := before.control
        protocolValid := valid }
  else none

/-- `reachedCall?_fields` proves preservation of all metadata and control and uses exactly
the architectural result of the supplied actual CALL. -/
theorem reachedCall?_fields {before after : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    (success : reachedCall? before receipt = some after) :
    after.machine = receipt.result ∧ after.metadata = before.metadata ∧
      after.control = before.control := by
  unfold reachedCall? at success
  split at success
  · cases Option.some.inj success
    exact ⟨rfl, rfl, rfl⟩
  · contradiction

/-- One actual CALL, its exact reached carrier, and the full checked handoff.
This is a custody binding, not evidence that the selected target is a native
WriteFile export or that the provider has returned. -/
structure CallHandoff {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (before : ExecutionState.State ApiRequest)
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement)
    (request : Request) (agent : ContextId) where
  policy : CallPolicy loaded receipt
  callerReady : before.ControlConsistent
  reached : ExecutionState.State ApiRequest
  reachedExact : reachedCall? before receipt = some reached
  abi : Abi.StackPlan reached.machine request
  continuation : abi.continuation = receipt.fetch.site.fallthroughRip
  returnProvenance : abi.returnSlot.provenance = receipt.storeDescriptor.provenance
  returnRange : abi.returnSlot.range = receipt.storeDescriptor.range
  handoff : EntryHandoff reached request abi agent
  caller : handoff.caller = inputs.thread

end Grass.Platform.Win32.WriteFile
