import Grass.Platform.Win32.CpuPolicy
import Grass.Platform.Win32.ApiRequest
import Grass.Platform.Win32.ExecutionState
import Grass.ISA.X86.Execution.CallNormal
import Grass.ISA.X86.Execution.CallFactory

/-!
# API-independent actual CALL entry

This boundary binds the fixed Windows CPU policy to an actual CALL factory
receipt and repacks the reached execution carrier. Provider identity, ABI
handoff, and return behavior remain separate obligations.
-/

namespace Grass.Platform.Win32.CallEntry

open Grass.Memory Grass.ISA.X86
open Grass.Platform.Win32.Loader

/-- The fixed Windows policy and loaded roots used by an actual CALL receipt. -/
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

/-- Derive the Windows binding from a successful fixed CALL factory receipt. -/
def CallPolicy.ofFactory {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : Execution.State}
    {policy : Execution.CpuAccessPolicy}
    (selected : Cpu.policy? loaded before = some policy)
    (success : Execution.CallFactory.Success policy before) :
    CallPolicy loaded success.receipt := by
  have operation : policy.operationPolicy = Cpu.operationPolicy := by
    obtain ⟨_, _, _, _, _, _, _, _, _, operation, _, _⟩ := Cpu.policy?_inputs selected
    exact operation
  have data : policy.data = Cpu.dataProvenance? loaded := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, data⟩ := Cpu.policy?_inputs selected
    exact data
  have metadata := success.fetched.observed.dispatch_metadata
    success.fetched.dispatched success.fetched.dispatch_exact
  refine ⟨policy, selected, ?_, ?_, ?_, ?_, ?_, success.stack_provenance, ?_⟩
  · rw [success.fetch_exact, metadata.1, success.fetched.policy_exact]
    rw [Execution.FetchFactory.fetchPolicy, operation]
    rfl
  · rw [success.fetch_exact, metadata.2.1, success.fetched.context_exact]
  · rw [success.fetch_exact, metadata.2.2.1, success.fetched.contextKind_exact]
  · rw [success.fetch_exact, metadata.2.2.2.1, success.fetched.cause_exact]
  · rw [success.fetch_exact, metadata.2.2.2.2, success.fetched.descriptor_exact]
    rfl
  · rw [← data]
    exact success.data_selected

/-- Repack the same metadata after the actual CPU transition. -/
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

/-- `reachedCall?_fields` retains metadata and control and identifies the exact CALL result. -/
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

end Grass.Platform.Win32.CallEntry
