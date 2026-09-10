import Grass.Platform.Win32.ProviderResume
import Grass.Op.CallProtocolSettlement

/-! Mechanical finalization of the actual post-slot-read candidate. These laws
do not install a raw transition or assert physical provider transfer. -/

namespace Grass.Platform.Win32.ProviderResume

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

/-- Install the exact protocol return's bookkeeping data before reading the
returned slot. This view preserves actual CPU registers and raw control/runtime;
it does not itself assert a raw transition or a physical provider return. -/
def afterReturn (before : RawState) (returned : CallProtocol.State ApiRequest) : RawState :=
  { before with machine := { before.machine with machine := returned.machine }
                metadata := returned.metadata }

theorem resume_memory {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (resume : ProviderResume.Success loaded before callId runtime frame call) :
    resume.after.machine.machine.memory = before.machine.machine.memory := by
  rw [resume.machine_afterRead]
  exact resume.slot.receipt.state_frame.1

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {callBefore : State}
  {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
  {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
  {before : RawState} {settled : CallProtocol.State ApiRequest} {callId : CallProtocol.CallId}
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
    {providerState : CallProtocol.State ApiRequest} {record : CallProtocol.Pending ApiRequest}
    (returned : CallProtocol.return? providerState callId record.caller record.agent record.ids =
      some (record, settled))
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
    rw [(CallProtocol.return?_effects returned).machineUpdated, fields.1]
  · change resume.after.metadata.boundaries = _
    rw [resume.raw_frame.1]
    change settled.boundaries = _
    rw [(CallProtocol.return?_effects returned).boundaries]
    exact congrArg (fun metadata => metadata.boundaries ++
      [.returned callId record.caller record.agent record.ids]) fields.2

/-- Every successful fresh projection retains the actual post-read machine and
the consumed pending occurrence. Replaying its protocol return is rejected. -/
theorem finalized_protocol
    {providerState : CallProtocol.State ApiRequest} {record : CallProtocol.Pending ApiRequest}
    (returned : CallProtocol.return? providerState callId record.caller record.agent record.ids =
      some (record, settled))
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call)
    {protocol : CallProtocol.State ApiRequest}
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
    exact CallProtocol.return?_removes_pending returned
  refine ⟨fields.1, removed, ?_⟩
  simp [CallProtocol.return?, removed]

/-- Actual protocol return clears caller suspension for either returning API.
The identity equation connects that record to the fixed Windows thread. -/
theorem returned_control
    {providerState : CallProtocol.State ApiRequest} {record : CallProtocol.Pending ApiRequest}
    (returned : CallProtocol.return? providerState callId record.caller record.agent record.ids =
      some (record, settled))
    (caller : record.caller = inputs.thread)
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call) :
    RawState.ControlConsistent
      { resume.after.eraseCall callId with control := .caller record.caller } := by
  have notPending := CallProtocol.return?_callerPending_false returned
  rw [caller] at notPending ⊢
  exact finalized_control resume notPending

end Grass.Platform.Win32.ProviderResume
