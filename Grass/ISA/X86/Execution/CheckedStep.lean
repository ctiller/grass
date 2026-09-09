import Grass.ISA.X86.Execution.BodyComputationFactory
import Grass.ISA.X86.Execution.ComputationFactory
import Grass.ISA.X86.Execution.PushFactory
import Grass.ISA.X86.Execution.CallFactory
import Grass.ISA.X86.Execution.MemoryMoveFactory
import Grass.ISA.X86.Execution.CheckedChoice

/-!
# Evaluated checked CPU transitions

The relation is the graph of a fixed evaluator. Normal outcomes come from
actual instruction factories. Undefined arithmetic status bits remain explicit
choices constrained by the production instruction effect. Invalid choices are
not admitted. Non-normal alternatives retain the uncovered input prefix; they
do not fabricate a physical fault, trap, interruption or abort transfer.

This covers this evaluated checker only. Physical execution adequacy, event
priority, saved state and platform delivery remain separate obligations.
-/

namespace Grass.ISA.X86.Execution.CheckedExecution

open Grass.Memory Grass.Op

/-- Typed diagnostics retain the complete original factory refusal. -/
inductive Failure where
  | fetch (reason : FetchFactory.Failure)
  | computation (reason : ComputationFactory.Failure)
  | body (reason : BodyComputationFactory.Failure)
  | push (reason : PushFactory.Failure)
  | call (reason : CallFactory.Failure)
  | memoryMove (reason : MemoryMoveFactory.Failure)
  | unsupported (reached : State) (encoding : InsnEncoding)

/-- Each successful family retains the actual constructed execution receipt. -/
inductive Success (policy : CpuAccessPolicy) (before : State) where
  | move (receipt : ComputationFactory.MoveSuccess before)
  | subRsp (receipt : ComputationFactory.SubRspSuccess before)
  | push (receipt : PushFactory.Success before)
  | call (receipt : CallFactory.Success policy before)
  | arithmetic (receipt : BodyComputationFactory.ArithmeticSuccess policy before)
  | branch (receipt : BodyComputationFactory.BranchSuccess policy before)
  | lea (receipt : BodyComputationFactory.LeaSuccess policy before)
  | memoryMove (receipt : MemoryMoveFactory.CompleteSuccess policy before)

def Success.outcome {policy : CpuAccessPolicy} {before : State} :
    Success policy before → CpuOutcome
  | .move success => .progressed success.result .completed
  | .subRsp success => .progressed success.result .completed
  | .push success => .progressed success.receipt.result .completed
  | .call success => .progressed success.result
      (.called success.receipt.fetch.site.fallthroughRip)
  | .arithmetic success => .progressed success.result .completed
  | .branch success => .progressed success.result .completed
  | .lea success => .progressed success.result .completed
  | .memoryMove success => .progressed success.execution.result .completed

private def accessReason {descriptor : AccessDescriptor} :
    RunFactory.AccessFailure descriptor → ApplicabilityFailure
  | .rejected reason => .operation reason
  | .violations _ => .accessViolations
  | .preparationUnavailable _ reason => .accessPreparation reason
  | .answerUnavailable _ => .accessAnswerUnavailable

private def fetchFailure : FetchFactory.Failure → CpuOutcome
  | .address reached reason => .outsideProfile reached (.addressPlanning reason)
  | .access reached _ reason => .outsideProfile reached (accessReason reason)
  | .applicability reached reason => .outsideProfile reached reason

private def computationFailure : ComputationFactory.Failure → CpuOutcome
  | .fetch reason => fetchFailure reason
  | .unsupported reached _ => .outsideProfile reached .unsupportedSelection
  | .accessFreeRejected reached reason => .outsideProfile reached (.operation reason)

private def pushFailure : PushFactory.Failure → CpuOutcome
  | .fetch reason => fetchFailure reason
  | .unsupported reached _ => .outsideProfile reached .unsupportedSelection
  | .stackUnderflow reached => .outsideProfile reached .stackUnderflow
  | .stackAddress reached reason => .outsideProfile reached (.addressPlanning reason)
  | .store reached _ reason => .outsideProfile reached (accessReason reason)

private def callFailure : CallFactory.Failure → CpuOutcome
  | .fetch reason => fetchFailure reason
  | .unsupported reached _ => .outsideProfile reached .unsupportedSelection
  | .missingData reached address => .outsideProfile reached (.missingData address)
  | .dataAddress reached reason | .stackAddress reached reason =>
      .outsideProfile reached (.addressPlanning reason)
  | .read reached _ reason | .store reached _ reason =>
      .outsideProfile reached (accessReason reason)
  | .stackUnderflow reached => .outsideProfile reached .stackUnderflow

private def bodyFailure : BodyComputationFactory.Failure → Option CpuOutcome
  | .fetch reason => some (fetchFailure reason)
  | .unsupported reached _ => some (.outsideProfile reached .unsupportedSelection)
  | .accessFreeRejected reached reason => some (.outsideProfile reached (.operation reason))
  | .flagsRejected _ _ => none
  | .targetOutOfRange reached _ => some (.outsideProfile reached .branchTargetOutOfRange)

private def memoryMoveFailure : MemoryMoveFactory.Failure → CpuOutcome
  | .fetch reason => fetchFailure reason
  | .unsupported reached encoding => .outsideProfile reached (.instruction encoding)
  | .address reached reason => .outsideProfile reached (.addressPlanning reason)
  | .access reached _ reason => .outsideProfile reached (accessReason reason)

/-- Execute a normal instruction from one actual fetch. `none` means only that
the caller's arithmetic status choice was not admitted by `Flags.Allows`. -/
def normal (policy : CpuAccessPolicy) (before : State)
    (flags : RegisterSemantics.Flags Bool) :
    Option (Except Failure (Success policy before)) :=
  match FetchFactory.fetch policy before with
  | .error reason => some (.error (.fetch reason))
  | .ok fetched =>
      match fetched.dispatched.selection.instruction with
      | .move _ =>
          some <| (ComputationFactory.moveFromFetched before fetched).map .move
            |>.mapError .computation
      | .stack (.subRsp immediate) =>
          if completedSubStatus before immediate = flags then
            some <| (ComputationFactory.subRspFromFetched before fetched).map .subRsp
              |>.mapError .computation
          else none
      | .stack (.push _) =>
          some <| (PushFactory.pushFromFetched before fetched).map .push |>.mapError .push
      | .callRip _ =>
          some <| (CallFactory.callFromFetched before fetched).map .call |>.mapError .call
      | .arithmetic _ =>
          match BodyComputationFactory.arithmeticFromFetched before flags fetched with
          | .error (.flagsRejected _ _) => none
          | .error reason => some (.error (.body reason))
          | .ok success => some (.ok (.arithmetic success))
      | .branch _ =>
          some <| (BodyComputationFactory.branchFromFetched before fetched).map .branch
            |>.mapError .body
      | .lea _ =>
          some <| (BodyComputationFactory.leaFromFetched before fetched).map .lea
            |>.mapError .body
      | .memoryMove _ =>
          match MemoryMoveFactory.fromFetched fetched with
          | .error reason => some (.error (.memoryMove reason))
          | .ok execution => some (.ok (.memoryMove ⟨fetched, execution⟩))
      | .ud2 => some (.error (.unsupported
          { before with machine := fetched.after } fetched.dispatched.fetch.site.encoding))

def Failure.outcome : Failure → Option CpuOutcome
  | .fetch reason => some (fetchFailure reason)
  | .computation reason => some (computationFailure reason)
  | .body reason => bodyFailure reason
  | .push reason => some (pushFailure reason)
  | .call reason => some (callFailure reason)
  | .memoryMove reason => some (memoryMoveFailure reason)
  | .unsupported reached encoding => some (.outsideProfile reached (.instruction encoding))

def resultOutcome {policy : CpuAccessPolicy} {before : State} :
    Except Failure (Success policy before) → Option CpuOutcome
  | .ok success => some success.outcome
  | .error reason => reason.outcome

/-- The fixed checked evaluator. Non-normal choices expose the corresponding
unimplemented transfer without asserting that the event is physically admitted. -/
def evaluate (policy : CpuAccessPolicy) (before : State) : CheckedChoice → Option CpuOutcome
  | .normal flags => (normal policy before flags).bind resultOutcome
  | .fault class_ => some (.outsideProfile before (.faultTransfer class_))
  | .trap class_ => some (.outsideProfile before (.trapTransfer class_))
  | .interruption vector => some (.outsideProfile before (.interruptionTransfer vector))
  | .abort class_ => some (.outsideProfile before (.abortTransfer class_))

/-- `CheckedStep` is exactly the graph of `evaluate`. -/
def CheckedStep (policy : CpuAccessPolicy) (before : State)
    (choice : CheckedChoice) (outcome : CpuOutcome) : Prop :=
  evaluate policy before choice = some outcome

theorem deterministic {policy : CpuAccessPolicy} {before : State} {choice : CheckedChoice}
    {first second : CpuOutcome} (hfirst : CheckedStep policy before choice first)
    (hsecond : CheckedStep policy before choice second) : first = second :=
  Option.some.inj (hfirst.symm.trans hsecond)

theorem normal_success {policy : CpuAccessPolicy} {before : State}
    {flags : RegisterSemantics.Flags Bool} {success : Success policy before}
    (checked : normal policy before flags = some (.ok success)) :
    CheckedStep policy before (.normal flags) success.outcome := by
  simp [CheckedStep, evaluate, checked, resultOutcome]

theorem normal_failure {policy : CpuAccessPolicy} {before : State}
    {flags : RegisterSemantics.Flags Bool} {failure : Failure} {outcome : CpuOutcome}
    (typed : normal policy before flags = some (.error failure))
    (mapped : failure.outcome = some outcome) :
    CheckedStep policy before (.normal flags) outcome := by
  simp [CheckedStep, evaluate, typed, resultOutcome, mapped]

theorem normal_checked_cases {policy : CpuAccessPolicy} {before : State}
    {flags : RegisterSemantics.Flags Bool} {outcome : CpuOutcome}
    (checked : CheckedStep policy before (.normal flags) outcome) :
    ∃ result, normal policy before flags = some result ∧
      resultOutcome result = some outcome := by
  cases found : normal policy before flags with
  | none => simp [CheckedStep, evaluate, found] at checked
  | some result =>
      refine ⟨result, rfl, ?_⟩
      simpa [CheckedStep, evaluate, found, resultOutcome] using checked

end Grass.ISA.X86.Execution.CheckedExecution
