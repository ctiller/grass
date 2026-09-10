import Grass.Platform.Win32.ProviderResume
import Grass.Platform.Win32.GetStdHandleRuntime
import Grass.Platform.Win32.WriteFileRuntime

/-!
# Resume inputs derived from the issued CALL

Both returning APIs use the same fixed-policy and reached-plan projections.
The endpoint theorems below start at the actual handoff and its computed runtime
insertion. They establish the initial frame link only. A later resume still
needs a reached provider state, preservation through its actual history, and
the selected provider-return interpretation.
-/

namespace Grass.Platform.Win32

open Grass.Core Grass.Memory Grass.ISA.X86
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

namespace ProviderResume

/-- `ofCallEntry` obtains every original-policy field from the same actual
CALL binding; uniqueness of the fixed selector identifies a later selection. -/
theorem PolicyBinding.ofCallEntry {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before afterFetch afterRead afterStore displacement}
    (binding : CallEntry.CallPolicy loaded receipt) : PolicyBinding loaded receipt := by
  constructor
  intro policy selected
  have same : policy = binding.policy :=
    Option.some.inj (selected.symm.trans binding.selected)
  subst policy
  exact ⟨binding.selected, binding.fetchPolicy, binding.context,
    binding.contextKind, binding.cause, binding.stack⟩

/-- `ofReachedPlan` projects the common frame once from the exact reached
plan. Its lookup premise alone is data agreement, not a history theorem;
the API handoff consumers below supply their computed insertion. -/
theorem Link.ofReachedPlan {before reached : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    (reachedExact : CallEntry.reachedCall? before receipt = some reached)
    (plan : ReturnHome.Plan reached.machine)
    (continuation : plan.continuation = receipt.fetch.site.fallthroughRip)
    (provenance : plan.returnSlot.provenance = receipt.storeDescriptor.provenance)
    (range : plan.returnSlot.range = receipt.storeDescriptor.range)
    {after : RawState} {call : Grass.Op.CallProtocol.CallId} {runtime : CallRuntime}
    (lookup : after.calls.lookup call = some runtime)
    (frame : returnFrame? runtime = some (ReturnFrame.ofPlan plan)) :
    Link after call runtime (ReturnFrame.ofPlan plan) receipt := by
  refine ⟨lookup, frame, ?_, continuation, provenance, range⟩
  change reached.machine.gpr .rsp = receipt.result.gpr .rsp
  rw [(CallEntry.reachedCall?_fields reachedExact).1]

end ProviderResume

/-- `resumeInputs` derives the initial resume inputs from GetStdHandle's actual
CALL, checked handoff, and computed runtime entry. It proves no return step. -/
theorem GetStdHandle.CallHandoff.resumeInputs
    {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded before receipt agent)
    (prior : CallRuntimeTable) :
    ProviderResume.PolicyBinding loaded receipt ∧
      ProviderResume.Link (entered.afterRaw prior) entered.handoff.call
        (.getStdHandle entered.frame) entered.frame receipt := by
  exact ⟨ProviderResume.PolicyBinding.ofCallEntry entered.policy,
    ProviderResume.Link.ofReachedPlan entered.reachedExact entered.abi
      entered.continuation entered.returnProvenance entered.returnRange
      (entered.afterRaw_call prior) rfl⟩

/-- `resumeInputs` uses the same common projections for WriteFile, retaining
the issued CALL and the actual runtime insertion with its fifth argument. -/
theorem WriteFile.CallHandoff.resumeInputs
    {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : WriteFile.Request} {agent : ContextId}
    (entered : WriteFile.CallHandoff loaded before receipt request agent)
    (prior : CallRuntimeTable) :
    ProviderResume.PolicyBinding loaded receipt ∧
      ProviderResume.Link (entered.rawAfter prior) entered.handoff.call
        (.writeFile entered.runtime) entered.runtime.toReturnFrame receipt := by
  exact ⟨ProviderResume.PolicyBinding.ofCallEntry entered.policy,
    ProviderResume.Link.ofReachedPlan entered.reachedExact entered.abi.toPlan
      entered.continuation entered.returnProvenance entered.returnRange
      (entered.rawAfter_lookup prior) rfl⟩

end Grass.Platform.Win32
