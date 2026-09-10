import Grass.Refinement.Console.WriteFileSourceEntry
import Grass.Refinement.Console.WriteFileCountArgument
import Grass.Refinement.Console.WriteFileResume

/-! The incoming WriteFile contract is checked on the actual CALL state. Its
canonical source-local count argument does not require any preceding LEA. -/

namespace Grass.Refinement.Console.WriteFileCountEntry

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Std.Console
open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState
open WriteAllX86 WriteFileLoad WriteFileResume

/-- Supply the static count local to the existing incoming-state checker.
Actual CALL evaluation is an occurrence obligation; how R9 acquired its value
is deliberately absent from the callee contract. -/
def prepareCountCall? {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} (before : ExecutionState.State ApiRequest)
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    (call : CallNormal before.machine afterFetch afterTarget afterCall displacement)
    (binding : CallPolicy loaded call) (ready : before.ControlConsistent)
    (_evaluated : Raw.EvaluatedCall loaded before call)
    {frame : SourceFrame.Result} {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset}
    (selectedLocal : SourceResolve.LoadSelection source)
    (buffer : Argument) (bytes : Vec Byte) (fifth : Argument) (provider : ContextId) :
    Option (CallHandoff loaded before call
      (EntryFactory.requestOf call.result buffer
        (WriteFileCountArgument.argument binding.policy selectedLocal) bytes) provider) :=
  if selectedLocal.result.slot = "transferred" then
    WriteFileSourceEntry.prepareCall? before call binding ready buffer
      (WriteFileCountArgument.argument binding.policy selectedLocal) bytes fifth provider
  else none

theorem prepareCountCall?_slot {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {call : CallNormal before.machine afterFetch afterTarget afterCall displacement}
    {binding : CallPolicy loaded call} {ready : before.ControlConsistent}
    {evaluated : Raw.EvaluatedCall loaded before call}
    {frame : SourceFrame.Result} {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset}
    {selectedLocal : SourceResolve.LoadSelection source} {buffer : Argument} {bytes : Vec Byte}
    {fifth : Argument} {provider : ContextId} {entered}
    (produced : prepareCountCall? before call binding ready evaluated selectedLocal
      buffer bytes fifth provider = some entered) : selectedLocal.result.slot = "transferred" := by
  unfold prepareCountCall? at produced
  split at produced
  · assumption
  · contradiction

theorem body_argument {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callPolicy bodyPolicy : CpuAccessPolicy}
    {callBefore loadBefore : State} {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset}
    (callSelected : Cpu.policy? loaded callBefore = some callPolicy)
    (selectedLocal : SourceResolve.LoadSelection source)
    (body : WriteAllBody.Run bodyPolicy source loadBefore)
    (bodySelected : Cpu.policy? loaded loadBefore = some bodyPolicy)
    (sameSlot : body.load.source.selection.result.slot = selectedLocal.result.slot) :
    body.load.source.access.descriptor.provenance =
        (WriteFileCountArgument.argument callPolicy selectedLocal).provenance ∧
      body.load.source.access.descriptor.range =
        (WriteFileCountArgument.argument callPolicy selectedLocal).range := by
  refine ⟨?_, ?_⟩
  · rw [body.load.descriptor_exact]
    exact (MemoryMoveFactory.memoryMove_load_stack body.load.ran).trans
      (WriteFileCountArgument.stack_same callSelected bodySelected)
  · exact body.load.source.range.trans
      (WriteFileCountArgument.range_same body.load.source.selection selectedLocal sameSlot)

/-- The checked incoming-state contract and static local binding close the
return/body composition without any executed-LEA or count-identity premise. -/
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
    (selectedLocal : SourceResolve.LoadSelection source)
    (binding : CallPolicy loaded call) (ready : callBefore.ControlConsistent)
    (evaluated : Raw.EvaluatedCall loaded callBefore call)
    (buffer : Argument) (bytes : Vec Byte) (fifth : Argument) {provider : ContextId}
    (entered : CallHandoff loaded callBefore call
      (EntryFactory.requestOf call.result buffer (WriteFileCountArgument.argument binding.policy selectedLocal) bytes) provider)
    (_produced : prepareCountCall? callBefore call binding ready evaluated selectedLocal
      buffer bytes fifth provider = some entered)
    (prior : CallRuntimeTable)
    {realization : Realization} {environment : ConsoleEnvironment}
    (raw : Nat → RawState) (graph : Nat → Raw.Graph)
    (agent : Nat → ContextId) (action : Nat → Action) (event : Nat → Raw.Event)
    (length : Nat) (root : raw 0 = entered.rawAfter prior)
    (steps : ∀ n, n < length → Raw.RawStep loaded realization environment (graph n) (raw n)
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
  have named := prepareCountCall?_slot _produced
  have bodySlot := (WriteAllBody.load_operand body.selected body.load.source.selection
    (body.load.source.selected.symm.trans body.checksSource.loadSelected)).2
  have argument := body_argument binding.selected selectedLocal body bodyPolicySelected
    (bodySlot.trans named.symm)
  exact WriteFileResume.returned_body_bound entered prior raw graph agent action event length root steps
    returned projected resume _resumeRan output success positive guard guards guardSource body
    _bodySelected bodyPolicySelected argument.1 argument.2 placed

end Grass.Refinement.Console.WriteFileCountEntry
