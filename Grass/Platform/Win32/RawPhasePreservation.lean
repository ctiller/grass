import Grass.Platform.Win32.RawStep

/-! Local phase facts extracted from actual raw edges. These are preservation
clauses, not enabledness or a classification of every reachable Hello state.
In particular CPU outcomes retain their reached machine even when its protocol
check fails. No refusal is turned into success or external waiting here. -/

namespace Grass.Platform.Win32.Raw.RawStep

open Grass.Core Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
  {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
  {graph nextGraph : Graph} {before after : RawState} {event : Event}

/-- Each actual API entry establishes a checked pending state for the loaded
caller's thread and selected provider. This does not establish a reply edge. -/
theorem entry_phase {request : ApiRequest} {agent : ContextId}
    (step : RawStep loaded realization environment interpretation graph before (.apiEntry request agent)
      event after nextGraph) :
    after.ProtocolValid ∧ ∃ call, after.control = .pending call inputs.thread agent := by
  cases step with
  | writeFileEntry entered evaluated dispatch selected requestMatches agreement kind =>
      exact ⟨entered.handoff.after.protocolValid, entered.handoff.call,
        congrArg (Control.pending entered.handoff.call · _) entered.caller⟩
  | getStdHandleEntry entered evaluated dispatch selected requestMatches agreement kind =>
      exact ⟨entered.handoff.after.protocolValid, entered.handoff.call,
        congrArg (Control.pending entered.handoff.call · _) entered.caller⟩
  | exitProcessEntry entered evaluated dispatch selected requestMatches agreement kind =>
      exact ⟨entered.handoff.after.protocolValid, entered.handoff.call,
        congrArg (Control.pending entered.handoff.call · _) entered.caller⟩

/-- An actual stdout result resumes the fixed caller with checked control and
retires that runtime occurrence. All handle values remain as observed. -/
theorem stdout_phase {call : CallProtocol.CallId}
    {gpr : Grass.ISA.X86.Gpr → BitVec 64} {rflags : BitVec 64}
    (step : RawStep loaded realization environment interpretation graph before (.stdoutResult call gpr rflags)
      event after nextGraph) :
    after.ProtocolValid ∧ after.ControlConsistent ∧
      after.control = .caller inputs.thread ∧ after.calls.lookup call = none := by
  have consistent := step.stdout_result.2.2.2.2
  have valid : after.ProtocolValid := by
    obtain ⟨checked, packed, _⟩ := consistent
    exact (RawState.checked?_isSome after).mp (by rw [packed]; rfl)
  refine ⟨valid, consistent, ?_, step.stdout_result.2.2.2.1⟩
  cases step with
  | getStdHandleReturn observed completion completed agreement =>
      exact completion.fields.2.2.1.trans
        (congrArg Control.caller (GetStdHandle.CallHandoff.caller _))

/-- CPU execution changes only the machine in the raw carrier. This covers
checked outside-profile outcomes without claiming their protocol validity. -/
theorem cpu_frame {choice : Grass.ISA.X86.Execution.CheckedChoice}
    (step : RawStep loaded realization environment interpretation graph before (.cpu choice)
      event after nextGraph) :
    after.metadata = before.metadata ∧ after.control = before.control ∧
      after.calls = before.calls := by
  obtain ⟨_, _, _, _, _, rfl⟩ := step.cpu_checked
  exact ⟨rfl, rfl, rfl⟩

/-- Runtime/pending domain linkage depends only on the framed fields, not on
whether the reached CPU machine can be repacked as a checked carrier. -/
theorem cpu_runtimeLinked {choice : Grass.ISA.X86.Execution.CheckedChoice}
    (step : RawStep loaded realization environment interpretation graph before (.cpu choice)
      event after nextGraph) (linked : before.RuntimeLinked) : after.RuntimeLinked := by
  obtain ⟨metadata, _, calls⟩ := step.cpu_frame
  simpa only [RawState.RuntimeLinked, metadata, calls] using linked

/-- A CPU edge is either completed CPU execution or an explicit reached
outside-profile diagnostic; neither is a provider-wait observation. -/
theorem cpu_event {choice : Grass.ISA.X86.Execution.CheckedChoice}
    (step : RawStep loaded realization environment interpretation graph before (.cpu choice)
      event after nextGraph) :
    event.kind = .cpu .completed ∨ ∃ reason, event.kind = .outsideProfile reason := by
  cases step with
  | cpuCompleted control selected evaluated completed agreement kind => exact Or.inl kind
  | cpuFailure control selected evaluated mapped agreement kind => exact Or.inr ⟨_, kind⟩
  | cpuUncovered control selected nonNormal evaluated agreement kind => exact Or.inr ⟨_, kind⟩

/-- A bounded sequence of actual CPU edges retains the original protocol,
control and runtime table. No edge is required beyond the supplied length. -/
theorem cpu_prefix_frame (raw : Nat → RawState) (graphs : Nat → Graph)
    (choices : Nat → Grass.ISA.X86.Execution.CheckedChoice) (events : Nat → Event)
    (length : Nat)
    (steps : ∀ n, n < length → RawStep loaded realization environment interpretation (graphs n) (raw n)
      (.cpu (choices n)) (events n) (raw (n + 1)) (graphs (n + 1))) :
    ∀ n, n ≤ length → (raw n).metadata = (raw 0).metadata ∧
      (raw n).control = (raw 0).control ∧ (raw n).calls = (raw 0).calls := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      intro bounded
      obtain ⟨metadata, control, calls⟩ := ih (by omega)
      obtain ⟨nextMetadata, nextControl, nextCalls⟩ := (steps n (by omega)).cpu_frame
      exact ⟨nextMetadata.trans metadata, nextControl.trans control, nextCalls.trans calls⟩

end Grass.Platform.Win32.Raw.RawStep
