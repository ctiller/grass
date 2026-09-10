import Grass.Refinement.Console.WriteFileResume
import Grass.Op.CallProtocolSettlement

/-! Mechanical finalization of the actual post-slot-read candidate. These laws
do not install a raw transition or assert physical provider transfer. -/

namespace Grass.Refinement.Console.WriteFileResume

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {callBefore : State}
  {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
  {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
  {before : RawState} {settled : ProtocolState} {callId : CallProtocol.CallId}
  {runtime : CallRuntime} {frame : ReturnFrame}

/-- Packing uses the actual post-read machine, including its new event. Only
memory equality is needed by the existing protocol validity checker. -/
theorem resume_pack
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call) :
    (resume.after.metadata.pack? resume.after.machine.machine).isSome := by
  apply (CallProtocol.Metadata.pack?_isSome _ _).mpr
  rw [resume_memory resume, resume.raw_frame.1]
  exact ⟨settled.grantsCovered, settled.pendingValid⟩

/-- The actual read records the fixed Windows caller context. -/
theorem resume_caller_registered
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call) :
    resume.after.machine.machine.contexts.lookup inputs.thread = some .thread := by
  have contexts : resume.slot.afterRead.contexts =
      ((afterReturn before settled).machine.machine.noteContext
        resume.slot.receipt.run.context resume.slot.receipt.run.contextKind).contexts := by
    apply (congrArg MachineState.contexts resume.slot.receipt.run.prepared_result).trans
    unfold performPreparedAccess
    repeat' first | rfl | split
  obtain ⟨_, _, _, _, _, _, context, kind, _⟩ :=
    Cpu.policy?_inputs resume.originalPolicy.selected
  rw [resume.machine_afterRead, contexts]
  simp only [MachineState.noteContext, resume.slot.context_exact,
    resume.slot.contextKind_exact, context, kind, FiniteMap.lookup_insert_self]

/-- Runtime consumption preserves the actual read state and settled metadata;
only this call is removed and caller control is selected. -/
theorem finalized_fields
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call)
    (caller : ContextId) :
    let final := { resume.after.eraseCall callId with control := .caller caller }
    final.machine = resume.after.machine ∧ final.metadata = settled.metadata ∧
      final.control = .caller caller ∧ final.calls.lookup callId = none ∧
      (∀ other, other ≠ callId → final.calls.lookup other = resume.after.calls.lookup other) := by
  refine ⟨rfl, resume.raw_frame.1, rfl, RawState.eraseCall_lookup _ _, ?_⟩
  intro other different
  exact RawState.eraseCall_other _ different

/-- The caller-control check uses a fresh projection of the actual read state.
The absence of a pending caller is supplied by the matched protocol return. -/
theorem finalized_control
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call)
    (notPending : CallProtocol.callerPending settled inputs.thread = false) :
    RawState.ControlConsistent
      { resume.after.eraseCall callId with control := .caller inputs.thread } := by
  let final : RawState := { resume.after.eraseCall callId with control := .caller inputs.thread }
  have valid : final.ProtocolValid := resume_pack resume
  let checked : ExecutionState.State ApiRequest :=
    ⟨final.machine, final.metadata, final.control, valid⟩
  refine ⟨checked, ExecutionState.State.raw_checked? checked final.calls, ?_⟩
  change ∃ protocol, checked.callProtocol? = some protocol ∧
    (∃ kind, protocol.machine.contexts.lookup inputs.thread = some kind) ∧
    CallProtocol.callerPending protocol inputs.thread = false
  cases packed : checked.callProtocol? with
  | none =>
      have existsProtocol := checked.callProtocol?_isSome
      simp [packed] at existsProtocol
  | some protocol =>
      have fields := ExecutionState.State.callProtocol?_fields packed
      refine ⟨protocol, rfl, ?_, ?_⟩
      · exact ⟨.thread, (congrArg (fun machine => machine.contexts.lookup inputs.thread)
          fields.1).trans (resume_caller_registered resume)⟩
      · have metadata : protocol.metadata = settled.metadata :=
          fields.2.trans resume.raw_frame.1
        have pending := congrArg CallProtocol.Metadata.pending metadata
        change protocol.pending = settled.pending at pending
        change protocol.pending.entries.any _ = false
        rw [pending]
        exact notPending

/-- Both edge suffixes come from the actual protocol return and slot read.
No ordering edge between those logs is synthesized here. -/
theorem finalized_logs
    {plan : LoanPlan} {realization : Realization} {initial providerState : ProtocolState}
    {record : CallProtocol.Pending Request} {frontier : Prefix plan providerState callId record}
    {history : History plan realization initial callId record frontier}
    {selected : ReturnInterpretation} {result : ReturnResult}
    (returned : MatchedReturn selected history result settled)
    (projected : before.metadata.pack? before.machine.machine = some providerState)
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call) :
    let final := { resume.after.eraseCall callId with control := .caller record.caller }
    ∃ readEvent, final.machine.machine.events = before.machine.machine.events ++ [readEvent] ∧
      final.metadata.boundaries = before.metadata.boundaries ++
        [.returned callId record.caller record.agent record.ids] ∧
      readEvent.event.valueRead = some resume.slot.receipt.read.observed := by
  obtain ⟨readEvent, appended, value⟩ := resume.slot.receipt.event
  have fields := CallProtocol.Metadata.pack?_fields projected
  refine ⟨readEvent, ?_, ?_, value⟩
  · change resume.after.machine.machine.events = _
    rw [resume.machine_afterRead, appended]
    change settled.machine.events ++ [readEvent] = _
    rw [returned.effects.machineUpdated, fields.1]
  · change resume.after.metadata.boundaries = _
    rw [resume.raw_frame.1]
    change settled.boundaries = _
    rw [returned.effects.boundaries]
    exact congrArg (fun metadata => metadata.boundaries ++
      [.returned callId record.caller record.agent record.ids]) fields.2

/-- Every successful fresh projection retains the actual post-read machine and
the consumed pending occurrence. Replaying its protocol return is rejected. -/
theorem finalized_protocol
    {plan : LoanPlan} {realization : Realization} {initial providerState : ProtocolState}
    {record : CallProtocol.Pending Request} {frontier : Prefix plan providerState callId record}
    {history : History plan realization initial callId record frontier}
    {selected : ReturnInterpretation} {result : ReturnResult}
    (returned : MatchedReturn selected history result settled)
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call)
    {protocol : ProtocolState}
    (packed : resume.after.metadata.pack? resume.after.machine.machine = some protocol) :
    protocol.machine = resume.after.machine.machine ∧
      protocol.pending.lookup callId = none ∧
      CallProtocol.return? protocol callId record.caller record.agent record.ids = none := by
  have fields := CallProtocol.Metadata.pack?_fields packed
  have metadata := fields.2.trans resume.raw_frame.1
  have pending := congrArg CallProtocol.Metadata.pending metadata
  change protocol.pending = settled.pending at pending
  have removed : protocol.pending.lookup callId = none := by
    rw [pending]
    exact returned.consumed.1
  refine ⟨fields.1, removed, ?_⟩
  simp [CallProtocol.return?, removed]

/-- The actual matched return discharges caller suspension. The original
handoff identifies the fixed Windows caller; no new readiness premise is added. -/
theorem returned_control
    {original : ExecutionState.State ApiRequest}
    {receipt : CallNormal original.machine afterFetch afterTarget afterCall displacement}
    {request : Request} {provider : ContextId}
    (entered : CallHandoff loaded original receipt request provider)
    {realization : Realization} {providerState : ProtocolState}
    {frontier : Prefix entered.abi.loanPlan providerState entered.handoff.call entered.handoff.record}
    {history : History entered.abi.loanPlan realization entered.handoff.beforeProtocol
      entered.handoff.call entered.handoff.record frontier}
    {selected : ReturnInterpretation} {result : ReturnResult}
    (returned : MatchedReturn selected history result settled)
    {currentRuntime : WriteFileRuntime}
    (resume : ProviderResume.Success loaded (afterReturn before settled) entered.handoff.call
      (.writeFile currentRuntime) entered.runtime.toReturnFrame receipt) :
    RawState.ControlConsistent
      { resume.after.eraseCall entered.handoff.call with control := .caller entered.handoff.record.caller } := by
  have notPending := CallProtocol.return?_callerPending_false returned.ran
  change CallProtocol.callerPending settled entered.handoff.caller = false at notPending
  change RawState.ControlConsistent
    { resume.after.eraseCall entered.handoff.call with control := .caller entered.handoff.caller }
  rw [entered.caller] at notPending ⊢
  exact finalized_control resume notPending

end Grass.Refinement.Console.WriteFileResume
