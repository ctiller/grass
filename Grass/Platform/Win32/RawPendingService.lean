import Grass.Platform.Win32.RawStep

/-! Invert an actual edge between pending phases. This classifies an existing
edge only; it does not establish enabledness, or assert that all states of an
arbitrary prefix remain pending. Entry ancestry is a separate obligation. -/

namespace Grass.Platform.Win32.Raw.RawStep

open Grass.Core Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- Every actual pending-to-pending edge is the same call's service edge.
The receipt, choice, publication and graphs are those of this transition. -/
theorem pending_to_pending_service {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {before after : RawState} {graph nextGraph : Graph} {choice : Choice} {event : Event}
    {call nextCall : CallProtocol.CallId} {caller provider nextCaller nextProvider : ContextId}
    (step : RawStep loaded realization environment interpretation graph before choice event after nextGraph)
    (pending : before.control = .pending call caller provider)
    (nextPending : after.control = .pending nextCall nextCaller nextProvider) :
    ∃ (record : CallProtocol.Pending WriteFile.Request) (action : WriteFile.Action)
      (output : Vec Byte) (receipt : WriteFile.ServiceReceipt realization before call record action output),
      record.caller = caller ∧ record.agent = provider ∧
      choice = .providerService call provider action ∧ receipt.after = after ∧
      event.kind = (if output.length = 0 then .internal else .endpoint (.published call output)) ∧
      graph.Realizes realization.causal receipt.protocol ∧
      nextGraph.Realizes realization.causal receipt.nextProtocol ∧
      nextCall = call ∧ nextCaller = caller ∧ nextProvider = provider := by
  cases step with
  | writeFileEntry entered evaluated dispatch selected requestMatches agreement kind =>
      have ready := (WriteFile.reachedCall?_fields entered.reachedExact).2.2.symm.trans
        entered.handoff.control
      exact Control.noConfusion (ready.symm.trans pending)
  | getStdHandleEntry entered evaluated dispatch selected requestMatches agreement kind =>
      have ready := (WriteFile.reachedCall?_fields entered.reachedExact).2.2.symm.trans
        entered.handoff.control
      exact Control.noConfusion (ready.symm.trans pending)
  | exitProcessEntry entered evaluated dispatch selected requestMatches agreement kind =>
      have ready := (WriteFile.reachedCall?_fields entered.reachedExact).2.2.symm.trans
        entered.handoff.control
      exact Control.noConfusion (ready.symm.trans pending)
  | getStdHandleReturn observed completion completed agreement =>
      exact Control.noConfusion (completion.fields.2.2.1.symm.trans nextPending)
  | writeFileReturn evaluated observed returned completion completed caller providerContext agreement =>
      exact Control.noConfusion (completion.fields.2.2.1.symm.trans nextPending)
  | completedExit completion completed agreement =>
      exact Control.noConfusion (completion.control.symm.trans nextPending)
  | cpuCompleted control selected evaluated completed agreement kind =>
      exact Control.noConfusion (control.symm.trans pending)
  | cpuFailure control selected evaluated mapped agreement kind =>
      exact Control.noConfusion (control.symm.trans pending)
  | cpuUncovered control selected nonNormal evaluated agreement kind =>
      exact Control.noConfusion (control.symm.trans pending)
  | service receipt agreement kind priorCausal nextCausal =>
      obtain ⟨rfl, rfl, rfl⟩ := Control.pending.inj (receipt.control.symm.trans pending)
      exact ⟨_, _, _, receipt, rfl, rfl, rfl, rfl, kind, priorCausal, nextCausal,
        Control.pending.inj (nextPending.symm.trans receipt.after_control)⟩

end Grass.Platform.Win32.Raw.RawStep
