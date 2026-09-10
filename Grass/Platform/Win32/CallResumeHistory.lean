import Grass.Platform.Win32.CallResumeBinding
import Grass.Platform.Win32.RawServicePreservation

/-!
# Original issued frame after a finite service history

The service prefix starts at the actual WriteFile handoff's computed raw state.
Its existing preservation theorem supplies the endpoint runtime and whole
pending record. This connects the original CALL to resume inputs without
reconstructing a frame from coincidentally equal values. No edge after the
finite endpoint, provider return, or physical transfer is assumed or proved.
-/

namespace Grass.Platform.Win32.WriteFile.CallHandoff

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState
open Grass.Platform.Win32.Raw

/-- `resumeInputsAfterService` transports the actual issued CALL's frame through
only the supplied finite same-call service edges, retaining the full occurrence. -/
theorem resumeInputsAfterService
    {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
    {request : Request} {provider : ContextId}
    (entered : CallHandoff loaded before receipt request provider) (prior : CallRuntimeTable)
    {realization : Realization}
    {environment : ConsoleEnvironment}
    (raw : Nat → RawState) (graph : Nat → Graph)
    (agent : Nat → ContextId) (action : Nat → Action) (event : Nat → Event)
    (length : Nat) (root : raw 0 = entered.rawAfter prior)
    (steps : ∀ n, n < length → RawStep loaded realization environment (graph n) (raw n)
      (.providerService entered.handoff.call (agent n) (action n))
      (event n) (raw (n + 1)) (graph (n + 1))) :
    ProviderResume.PolicyBinding loaded receipt ∧
      (raw length).metadata = (entered.rawAfter prior).metadata ∧
      (raw length).metadata.pending.lookup entered.handoff.call =
        some (embedPending entered.handoff.record) ∧
      ∃ runtime,
        ProviderResume.Link (raw length) entered.handoff.call (.writeFile runtime)
          entered.runtime.toReturnFrame receipt ∧
        runtime.fifthSlot = entered.runtime.fifthSlot ∧
        runtime.loanPlan = entered.runtime.loanPlan := by
  have initial := entered.resumeInputs prior
  have lookup : (raw 0).calls.lookup entered.handoff.call =
      some (.writeFile entered.runtime) := by
    rw [root]
    exact entered.rawAfter_lookup prior
  have pending : (raw 0).metadata.pending.lookup entered.handoff.call =
      some (embedPending entered.handoff.record) := by
    rw [root]
    exact entered.handoff.recorded
  obtain ⟨metadata, retained, runtime, runtimeLookup, frame, fifth, plan⟩ :=
    RawStep.service_prefix_runtime raw graph agent action event length steps
      entered.runtime lookup entered.handoff.record pending length (Nat.le_refl _)
  refine ⟨initial.1, metadata.trans (congrArg RawState.metadata root), retained,
    runtime, ?_, fifth, plan⟩
  exact ⟨runtimeLookup, congrArg some frame, initial.2.entryRsp,
    initial.2.continuation, initial.2.returnProvenance, initial.2.returnRange⟩

end Grass.Platform.Win32.WriteFile.CallHandoff
