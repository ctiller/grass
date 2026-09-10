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

/-- Before the next completion observation, an actual internal or publication
edge preserves the pending identity. Publication's call identity is justified
by the service inversion, not assumed from the event label. -/
theorem pending_internal_or_publication {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {before after : RawState} {graph nextGraph : Graph} {choice : Choice} {event : Event}
    {call : CallProtocol.CallId} {caller provider : ContextId}
    (step : RawStep loaded realization environment interpretation graph before choice event after nextGraph)
    (pending : before.control = .pending call caller provider)
    (continuing : event.kind = .internal ∨
      ∃ observedCall bytes, event.kind = .endpoint (.published observedCall bytes)) :
    after.control = .pending call caller provider := by
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
      rcases continuing with impossible | ⟨_, _, impossible⟩ <;> cases impossible
  | writeFileReturn evaluated observed returned completion completed caller providerContext agreement =>
      rcases continuing with impossible | ⟨_, _, impossible⟩ <;> cases impossible
  | completedExit completion completed agreement =>
      rcases continuing with impossible | ⟨_, _, impossible⟩ <;> cases impossible
  | cpuCompleted control selected evaluated completed agreement kind =>
      exact Control.noConfusion (control.symm.trans pending)
  | cpuFailure control selected evaluated mapped agreement kind =>
      exact Control.noConfusion (control.symm.trans pending)
  | cpuUncovered control selected nonNormal evaluated agreement kind =>
      exact Control.noConfusion (control.symm.trans pending)
  | service receipt agreement kind priorCausal nextCausal =>
      exact receipt.after_control.trans (receipt.control.symm.trans pending)

/-- Propagate the actual entry's pending control across a contiguous slice of
the enclosing indexed derivation. Only this slice's recorded internal and
publication events are classified; no assumption is made beyond its endpoint. -/
theorem pending_segment {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
    {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
    {total : Nat} (states : Fin (total + 1) → RawState) (graphs : Fin (total + 1) → Graph)
    (choices : Fin total → Choice) (events : Fin total → Event)
    (steps : ∀ index, RawStep loaded realization environment interpretation
      (graphs index.castSucc) (states index.castSucc) (choices index) (events index)
      (states index.succ) (graphs index.succ))
    (start count : Nat) (within : start + count ≤ total)
    {call : CallProtocol.CallId} {caller provider : ContextId}
    (pending : (states ⟨start, by omega⟩).control = .pending call caller provider)
    (continuing : ∀ offset, (below : offset < count) →
      (events ⟨start + offset, by omega⟩).kind = .internal ∨
        ∃ observedCall bytes,
          (events ⟨start + offset, by omega⟩).kind = .endpoint (.published observedCall bytes)) :
    ∀ offset, (bounded : offset ≤ count) →
      (states ⟨start + offset, by omega⟩).control = .pending call caller provider := by
  intro offset
  induction offset with
  | zero => exact fun _ => pending
  | succ offset ih =>
      intro bounded
      have below : offset < count := by omega
      exact pending_internal_or_publication (steps ⟨start + offset, by omega⟩)
        (ih (by omega)) (continuing offset below)

end Grass.Platform.Win32.Raw.RawStep
