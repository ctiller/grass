import Grass.Platform.Win32.CallResumeHistory
import Grass.Platform.Win32.ProviderResumeFinalization
import Grass.Refinement.Console.WriteAllBody

/-! Compose the existing matched-return bookkeeping and checked resume candidate
with the reached source body. This is not an installed raw return transition:
provider transfer, caller-control restoration and runtime consumption remain
endpoint obligations. In particular, the original request must still be proved
to contain the computed source count argument.
-/

namespace Grass.Refinement.Console.WriteFileResume

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Std.Console
open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState
open WriteAllX86 WriteFileLoad

/-- Compatibility door for the shared settled-state computation. -/
abbrev afterReturn := ProviderResume.afterReturn

/-- The shared actual-read memory frame. -/
abbrev resume_memory := @ProviderResume.resume_memory

theorem resume_nonvolatile {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : ExecutionState.State ApiRequest}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {call : CallNormal callBefore.machine afterFetch afterTarget afterCall displacement}
    {request : Request} {provider : ContextId}
    (entered : CallHandoff loaded callBefore call request provider)
    {before : RawState} {runtime : WriteFileRuntime}
    (resume : ProviderResume.Success loaded before entered.handoff.call (.writeFile runtime)
      entered.runtime.toReturnFrame call)
    (register : { r : Gpr // r ∈ Grass.ABI.Win64.nonvolatileRegisters ∧ r ≠ .rsp }) :
    resume.after.machine.gpr register.val = callBefore.machine.gpr register.val := by
  have preserved := resume.nonvolatile_exact register
  change resume.after.machine.gpr register.val = entered.runtime.saved register at preserved
  rw [entered.runtime_saved] at preserved
  exact preserved

theorem resume_cursor {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : ExecutionState.State ApiRequest}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {call : CallNormal callBefore.machine afterFetch afterTarget afterCall displacement}
    {request : Request} {provider : ContextId}
    (entered : CallHandoff loaded callBefore call request provider)
    {before : RawState} {runtime : WriteFileRuntime}
    (resume : ProviderResume.Success loaded before entered.handoff.call (.writeFile runtime)
      entered.runtime.toReturnFrame call)
    {payload : Vec Byte} {base : Nat} {cursor : WriteCursor payload}
    (placed : CursorRegisters payload base cursor callBefore.machine) :
    CursorRegisters payload base cursor resume.after.machine := by
  have pointer := resume_nonvolatile entered resume ⟨.r13, by decide⟩
  have remaining := resume_nonvolatile entered resume ⟨.r14, by decide⟩
  refine ⟨?_, ?_, placed.addressFits, placed.countFits⟩
  · rw [pointer]
    exact placed.pointer
  · rw [remaining]
    exact placed.remaining

theorem guard_frame {before : State} (guard : TestZeroRun .rax before) :
    guard.result.gpr = before.gpr ∧
    guard.result.machine.memory = before.machine.memory :=
  ⟨guard.branch.gpr_frame.trans (test_gpr guard.tested),
    guard.branch.state_frame.1.trans guard.tested.state_frame.1⟩

theorem guard_cursor {before : State} (guard : TestZeroRun .rax before)
    {payload : Vec Byte} {base : Nat} {cursor : WriteCursor payload}
    (placed : CursorRegisters payload base cursor before) :
    CursorRegisters payload base cursor guard.result := by
  refine ⟨?_, ?_, placed.addressFits, placed.countFits⟩
  · rw [(guard_frame guard).1]
    exact placed.pointer
  · rw [(guard_frame guard).1]
    exact placed.remaining

theorem guard_success {before : State} (guard : TestZeroRun .rax before)
    {result : ReturnResult} (output : (before.gpr .rax).setWidth 32 = result.rawBool)
    (success : result.rawBool ≠ 0) :
    guard.result.rip = guard.branch.execution.fetch.site.fallthroughRip := by
  apply guard.branch.not_taken_rip
  change guard.tested.result.statusFlags.zf = false
  rw [guard.zero_flag, output]
  exact beq_eq_false_iff_ne.mpr success

theorem body_gpr_frame {policy : CpuAccessPolicy} {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    (body : WriteAllBody.Run policy source before) (register : Gpr)
    (notCount : register ≠ .rax) (notPointer : register ≠ .r13) (notRemaining : register ≠ .r14) :
    body.update.result.gpr register = before.gpr register := by
  have destination := WriteAllBody.load_destination body.selected body.load.source.selection
    (body.load.source.selected.symm.trans body.checksSource.loadSelected)
  rw [body.update.gpr_frame register notPointer notRemaining, body.checks.gpr_frame]
  exact WriteAllBody.load_gpr_frame body.load.source register (by rw [destination]; exact notCount)

/-- The finite raw prefix, not coincidental frame fields, identifies the
runtime used by the checked resume candidate with the original issued frame. -/
theorem historical_frame {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : ExecutionState.State ApiRequest}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {call : CallNormal callBefore.machine afterFetch afterTarget afterCall displacement}
    {request : Request} {provider : ContextId}
    (entered : CallHandoff loaded callBefore call request provider) (prior : CallRuntimeTable)
    {realization : Realization} {environment : ConsoleEnvironment}
    {interpretation : ReturnInterpretation}
    (raw : Nat → RawState) (graph : Nat → Raw.Graph)
    (agent : Nat → ContextId) (action : Nat → Action) (event : Nat → Raw.Event)
    (length : Nat) (root : raw 0 = entered.rawAfter prior)
    (steps : ∀ n, n < length → Raw.RawStep loaded realization environment interpretation (graph n) (raw n)
      (.providerService entered.handoff.call (agent n) (action n))
      (event n) (raw (n + 1)) (graph (n + 1)))
    {after : ProtocolState} {runtime : WriteFileRuntime}
    (resume : ProviderResume.Success loaded (afterReturn (raw length) after) entered.handoff.call
      (.writeFile runtime) entered.runtime.toReturnFrame call) :
    (raw length).metadata.pending.lookup entered.handoff.call = some (embedPending entered.handoff.record) ∧
    runtime.toReturnFrame = entered.runtime.toReturnFrame ∧
    runtime.fifthSlot = entered.runtime.fifthSlot ∧ runtime.loanPlan = entered.runtime.loanPlan := by
  obtain ⟨_binding, _metadata, pending, actualRuntime, linked, fifth, plan⟩ :=
    entered.resumeInputsAfterService prior raw graph agent action event length root steps
  have lookup : (raw length).calls.lookup entered.handoff.call = some (.writeFile runtime) :=
    resume.link.runtimeLookup
  have same := CallRuntime.writeFile.inj (Option.some.inj (lookup.symm.trans linked.runtimeLookup))
  subst actualRuntime
  exact ⟨pending, Option.some.inj linked.runtimeFrame, fifth, plan⟩

/-- Common original-history-to-body proof over the actual load descriptor.
Argument producers discharge its provenance and range equations independently
of the instruction recipe used to establish the incoming call state. -/
theorem returned_body_bound
    {R Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
    {spec : Grass.SpecProcess resources}
    {projection : Grass.Console.CapturedTargetProjection spec Status}
    {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {callBefore : ExecutionState.State ApiRequest}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {call : CallNormal callBefore.machine afterFetch afterTarget afterCall displacement}
    {request : Request} {provider : ContextId}
    (entered : CallHandoff loaded callBefore call request provider) (prior : CallRuntimeTable)
    {realization : Realization} {environment : ConsoleEnvironment}
    {interpretation : ReturnInterpretation}
    (raw : Nat → RawState) (graph : Nat → Raw.Graph)
    (agent : Nat → ContextId) (action : Nat → Action) (event : Nat → Raw.Event)
    (length : Nat) (root : raw 0 = entered.rawAfter prior)
    (steps : ∀ n, n < length → Raw.RawStep loaded realization environment interpretation (graph n) (raw n)
      (.providerService entered.handoff.call (agent n) (action n))
      (event n) (raw (n + 1)) (graph (n + 1)))
    {providerState after : ProtocolState}
    {frontier : Prefix entered.abi.loanPlan providerState entered.handoff.call entered.handoff.record}
    {history : History entered.abi.loanPlan realization entered.handoff.beforeProtocol
      entered.handoff.call entered.handoff.record frontier}
    {relation : WriteFileHistory.HandoffRelation (plan := entered.abi.loanPlan) projection}
    {aligned : WriteFileHistory.Aligned relation history}
    {result : ReturnResult}
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
    {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset}
    (guard : TestZeroRun .rax resume.after.machine)
    (guards : WriteAllGuardSource.AllSelection source)
    (guardSource : SourceGuard guards.candidate.rawTest.output guards.candidate.failed.output guard)
    {bodyPolicy : CpuAccessPolicy} (body : WriteAllBody.Run bodyPolicy source guard.result)
    (_bodySelected : body.selected = guards.candidate.post)
    (_bodyPolicySelected : Cpu.policy? loaded guard.result = some bodyPolicy)
    (provenance : body.load.source.access.descriptor.provenance =
      entered.handoff.record.request.countSlot.provenance)
    (range : body.load.source.access.descriptor.range =
      entered.handoff.record.request.countSlot.range)
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
  have actualFrame := historical_frame entered prior raw graph agent action event length root steps resume
  have resumed := resume_cursor entered resume placed
  have atLoad := guard_cursor guard resumed
  have memory : guard.result.machine.memory = after.machine.memory :=
    (guard_frame guard).2.trans (resume_memory resume)
  have closed := WriteAllBody.Run.returned_reenters_head returned body atLoad memory success positive
    provenance range
  have sourceReached := guardSource.tested.rip_exact
  rw [guardSource.testSelected] at sourceReached
  refine ⟨actualFrame.2.1, (CallProtocol.Metadata.pack?_fields projected).1, sourceReached,
    guard_success guard (resume.writeFile_output_retained output) success, closed.1, ?_, ?_,
    closed.2.1, closed.2.2⟩
  · rw [body_gpr_frame body .r12 (by decide) (by decide) (by decide), (guard_frame guard).1]
    exact resume_nonvolatile entered resume ⟨.r12, by decide⟩
  · rw [body_gpr_frame body .rsp (by decide) (by decide) (by decide), (guard_frame guard).1]
    exact resume.rsp_original

end Grass.Refinement.Console.WriteFileResume
