import Grass.Platform.Win32.RawPendingService

/-! Pending-control classification along supplied actual infinite executions. -/

namespace Grass.Platform.Win32.Raw.RawStep

open Grass.Core Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
  {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}

/-- Along a supplied pointwise actual infinite execution, an initial pending
occurrence either reaches caller control somewhere or retains the same pending
identity at every point. Infinitude is used only to rule out an intermediate
terminal state via its next actual edge. -/
theorem infinite_pending_or_resumed
    (states : Nat → RawState) (graphs : Nat → Graph)
    (choices : Nat → Choice) (events : Nat → Event)
    (steps : ∀ index, RawStep loaded realization environment interpretation
      (graphs index) (states index) (choices index) (events index)
      (states (index + 1)) (graphs (index + 1)))
    {call : CallProtocol.CallId} {caller provider : ContextId}
    (initial : (states 0).control = .pending call caller provider) :
    (∃ index resumedCaller, (states index).control = .caller resumedCaller) ∨
      ∀ index, (states index).control = .pending call caller provider := by
  classical
  by_cases resumed : ∃ index resumedCaller, (states index).control = .caller resumedCaller
  · exact Or.inl resumed
  · refine Or.inr ?_
    intro index
    induction index with
    | zero => exact initial
    | succ index inductionHypothesis =>
        cases nextControl : (states (index + 1)).control with
        | caller resumedCaller =>
            exact False.elim (resumed ⟨index + 1, resumedCaller, nextControl⟩)
        | pending nextCall nextCaller nextProvider =>
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, callExact, callerExact,
              providerExact⟩ :=
              pending_to_pending_service (steps index) inductionHypothesis nextControl
            subst nextCall
            subst nextCaller
            subst nextProvider
            rfl
        | terminal terminalCall status =>
            exact False.elim
              (RawStep.terminal_no_step nextControl (steps (index + 1)))

/-- If caller control never appears, every actual edge is the same pending
occurrence's service edge, with its original receipt, publication choice, and
causal graph evidence exposed. -/
theorem infinite_services_of_no_caller
    (states : Nat → RawState) (graphs : Nat → Graph)
    (choices : Nat → Choice) (events : Nat → Event)
    (steps : ∀ index, RawStep loaded realization environment interpretation
      (graphs index) (states index) (choices index) (events index)
      (states (index + 1)) (graphs (index + 1)))
    {call : CallProtocol.CallId} {caller provider : ContextId}
    (initial : (states 0).control = .pending call caller provider)
    (noCaller : ∀ index resumedCaller, (states index).control ≠ .caller resumedCaller) :
    ∀ index,
      ∃ (record : CallProtocol.Pending WriteFile.Request) (action : WriteFile.Action)
        (output : Vec Byte)
        (receipt : WriteFile.ServiceReceipt realization (states index) call record action output),
        record.caller = caller ∧ record.agent = provider ∧
        choices index = .providerService call provider action ∧
        receipt.after = states (index + 1) ∧
        (events index).kind = (if output.length = 0 then .internal
          else .endpoint (.published call output)) ∧
        (graphs index).Realizes realization.causal receipt.protocol ∧
        (graphs (index + 1)).Realizes realization.causal receipt.nextProtocol := by
  have notResumed : ¬ ∃ index resumedCaller,
      (states index).control = .caller resumedCaller := by
    rintro ⟨index, resumedCaller, resumed⟩
    exact noCaller index resumedCaller resumed
  have pending := (infinite_pending_or_resumed states graphs choices events steps initial).resolve_left
    notResumed
  intro index
  obtain ⟨record, action, output, receipt, recordCaller, recordAgent, choice,
    after, kind, priorCausal, nextCausal, _, _, _⟩ :=
    pending_to_pending_service (steps index) (pending index) (pending (index + 1))
  exact ⟨record, action, output, receipt, recordCaller, recordAgent, choice,
    after, kind, priorCausal, nextCausal⟩

end Grass.Platform.Win32.Raw.RawStep
