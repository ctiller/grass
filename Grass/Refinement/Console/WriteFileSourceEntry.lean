import Grass.Platform.Win32.WriteFilePrepare
import Grass.Platform.Win32.WriteFileStackPlan
import Grass.Refinement.Console.WriteFileResume

/-! Compute the existing call handoff from the checked argument and stack-plan
producers. Source count provenance is supplied by the actual source LEA. This
does not construct the intervening LEA-to-CALL setup execution. -/

namespace Grass.Refinement.Console.WriteFileSourceEntry

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Std.Console
open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

/-- Compose existing checked doors on the actual CALL result, retaining the
original protocol metadata. No new carrier or return semantics are introduced. -/
def prepareCall? {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} (before : ExecutionState.State ApiRequest)
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    (call : CallNormal before.machine afterFetch afterTarget afterCall displacement)
    (binding : CallPolicy loaded call) (ready : before.ControlConsistent)
    (buffer count : Argument) (bytes : Vec Byte) (fifth : Argument) (provider : ContextId) :
    Option (CallHandoff loaded before call (EntryFactory.requestOf call.result buffer count bytes) provider) := by
  cases reachedEq : reachedCall? before call with
  | none => exact none
  | some reached =>
      have same := (reachedCall?_fields reachedEq).1
      rcases reached with ⟨machine, metadata, control, valid⟩
      dsimp only at same
      subst machine
      cases preparedEq : EntryFactory.prepare? call.result buffer count bytes fifth with
      | error _ => exact none
      | ok entry =>
          cases plannedEq : Abi.StackPlanFactory.deriveLoaded? binding entry with
          | error _ => exact none
          | ok plan =>
              cases handedEq : entryHandoff? ⟨call.result, metadata, control, valid⟩
                  (EntryFactory.requestOf call.result buffer count bytes) plan provider with
              | none => exact none
              | some handoff =>
                  exact if caller : handoff.caller = inputs.thread then
                    some { policy := binding, callerReady := ready
                           reached := ⟨call.result, metadata, control, valid⟩
                           reachedExact := reachedEq, abi := plan
                           continuation := Abi.StackPlanFactory.loaded_continuation_exact plannedEq
                           returnProvenance := Abi.StackPlanFactory.loaded_return_provenance_exact plannedEq
                           returnRange := Abi.StackPlanFactory.loaded_return_range_exact plannedEq
                           handoff := handoff, caller := caller }
                  else none

/-- The source-selected count argument goes directly into the computed request.
The evaluator and source policy identities remain explicit inputs; no setup
path from the LEA result to the pre-CALL state is asserted by this function. -/
def prepareSourceCall? {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} (before : ExecutionState.State ApiRequest)
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    (call : CallNormal before.machine afterFetch afterTarget afterCall displacement)
    (binding : CallPolicy loaded call) (ready : before.ControlConsistent)
    (_evaluated : Raw.EvaluatedCall loaded before call)
    {leaPolicy : CpuAccessPolicy} {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {leaBefore : State}
    (lea : WriteFileCountAddress.SourceLea leaPolicy source leaBefore)
    (_leaSelected : Cpu.policy? loaded leaBefore = some leaPolicy)
    (buffer : Argument) (bytes : Vec Byte) (fifth : Argument) (provider : ContextId) :
    Option (CallHandoff loaded before call
      (EntryFactory.requestOf call.result buffer lea.argument bytes) provider) :=
  prepareCall? before call binding ready buffer lea.argument bytes fifth provider

open WriteAllX86 WriteFileLoad WriteFileResume

/-- Consume the computed source request and original handoff. Count-slot identity
is fixed by construction, so no requestSlot premise remains. Actual setup
execution between the supplied source LEA and CALL remains outside this slice. -/
theorem returned_body
    {R Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
    {spec : Grass.SpecProcess resources}
    {projection : Grass.Console.CapturedTargetProjection spec Status}
    {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {callBefore : ExecutionState.State ApiRequest}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {call : CallNormal callBefore.machine afterFetch afterTarget afterCall displacement}
    {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset}
    {leaPolicy : CpuAccessPolicy} {leaBefore : State}
    (lea : WriteFileCountAddress.SourceLea leaPolicy source leaBefore)
    (leaPolicySelected : Cpu.policy? loaded leaBefore = some leaPolicy)
    (binding : CallPolicy loaded call) (ready : callBefore.ControlConsistent)
    (evaluated : Raw.EvaluatedCall loaded callBefore call)
    (buffer : Argument) (bytes : Vec Byte) (fifth : Argument) {provider : ContextId}
    (entered : CallHandoff loaded callBefore call
      (EntryFactory.requestOf call.result buffer lea.argument bytes) provider)
    (_produced : prepareSourceCall? callBefore call binding ready evaluated lea
      leaPolicySelected buffer bytes fifth provider = some entered)
    (prior : CallRuntimeTable)
    {realization : Realization}
    (raw : Nat → RawState) (graph : Nat → Raw.Graph)
    (agent : Nat → ContextId) (action : Nat → Action) (event : Nat → Raw.Event)
    (length : Nat) (root : raw 0 = entered.rawAfter prior)
    (steps : ∀ n, n < length → Raw.RawStep loaded realization (graph n) (raw n)
      (.providerService entered.handoff.call (agent n) (action n))
      (event n) (raw (n + 1)) (graph (n + 1)))
    {providerState after : ProtocolState}
    {frontier : Prefix entered.abi.loanPlan providerState entered.handoff.call entered.handoff.record}
    {history : History entered.abi.loanPlan realization entered.handoff.beforeProtocol
      entered.handoff.call entered.handoff.record frontier}
    {relation : WriteFileHistory.HandoffRelation (plan := entered.abi.loanPlan) projection}
    {aligned : WriteFileHistory.Aligned relation history}
    {interpretation : ReturnInterpretation} {result : ReturnResult}
    (returned : WriteFileHistory.Returned aligned interpretation result after)
    (projected : (raw length).metadata.pack? (raw length).machine.machine = some providerState)
    {runtime : WriteFileRuntime}
    (resume : ProviderResume.Success loaded (afterReturn (raw length) after) entered.handoff.call
      (.writeFile runtime) entered.runtime.toReturnFrame call)
    (_resumeRan : ProviderResume.resume loaded (afterReturn (raw length) after) entered.handoff.call
      (.writeFile runtime) entered.runtime.toReturnFrame call
      (entered.resumeInputsAfterService prior raw graph agent action event length root steps).1
      resume.link resume.preserved = .ok resume)
    (output : ProviderResume.WriteFileOutput (afterReturn (raw length) after) result)
    (success : result.rawBool ≠ 0) (positive : 0 < returned.count.value)
    (guard : TestZeroRun .rax resume.after.machine)
    (guards : WriteAllGuardSource.AllSelection source)
    (guardSource : SourceGuard guards.candidate.rawTest.output guards.candidate.failed.output guard)
    {bodyPolicy : CpuAccessPolicy} (body : WriteAllBody.Run bodyPolicy source guard.result)
    (_bodySelected : body.selected = guards.candidate.post)
    (bodyPolicySelected : Cpu.policy? loaded guard.result = some bodyPolicy)
    (leaAuthored : lea.item.instruction =
      ⟨.lea, [.register ⟨.r9, .w64⟩, .address "transferred"]⟩)
    {base : Nat}
    (placed : CursorRegisters projection.target.payload base returned.cursor callBefore.machine) :
    runtime.toReturnFrame = entered.runtime.toReturnFrame ∧
    providerState.machine = (raw length).machine.machine ∧
    resume.after.machine.rip.toNat = guardSource.tested.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes
        guards.candidate.rawTest.output.index ∧
    guard.result.rip = guard.branch.execution.fetch.site.fallthroughRip ∧
    CursorRegisters projection.target.payload base (advance returned.cursor returned.count)
      body.update.result ∧
    body.update.result.gpr .r12 = callBefore.machine.gpr .r12 ∧
    body.update.result.gpr .rsp = callBefore.machine.gpr .rsp ∧
    body.update.result.rip = BitVec.ofNat 64 (body.load.source.site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes
        body.selected.candidate.loop.candidate.headIndex) ∧
    body.update.result.machine.memory = after.machine.memory := by
  exact WriteFileResume.returned_body entered prior raw graph agent action event length root steps
    returned projected resume _resumeRan output success positive guard guards guardSource body
    _bodySelected bodyPolicySelected lea leaPolicySelected leaAuthored rfl placed

end Grass.Refinement.Console.WriteFileSourceEntry
