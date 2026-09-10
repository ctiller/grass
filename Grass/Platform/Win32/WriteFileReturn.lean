import Grass.Platform.Win32.WriteFileResult

variable {plan : Grass.Platform.Win32.WriteFile.LoanPlan}

/-! A matched return consumes an actual reached history and protocol return.
Physical ABI/result correspondence remains selected conditional evidence.
-/
namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical

/-- Events contributed by this derivation's committed edges, in order.
Each edge's exact append evidence fixes the suffix; no independent list is supplied. -/
def History.providerEvents {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    (history : History plan realization initial call record frontier) : List ValidMemoryEvent :=
  match history with
  | .handoff .. => []
  | @History.step _ _ _ _ _ before after _ _ previous _ _ _ =>
      previous.providerEvents ++ after.machine.events.drop before.machine.events.length

/-- A committed edge's mechanically selected suffix is its exact causal event list. -/
theorem CausalEvidence.suffix {model : CausalModel} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {action : Action}
    {before after : ProtocolState} {added : List ValidMemoryEvent}
    (evidence : CausalEvidence plan model call record action before after added) :
    after.machine.events.drop before.machine.events.length = added := by
  rw [evidence.events]
  simp

/-- The entire reached event log is exactly the handoff base followed by this
history's committed effects. -/
theorem History.events_eq {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state call record}
    (history : History plan realization initial call record frontier) :
    state.machine.events = initial.machine.events ++ history.providerEvents := by
  induction history with
  | handoff frontier ran _ _ _ =>
      obtain ⟨memory, _, machine⟩ := (CallProtocol.handoff?_records ran).2.2.2.2.2
      simp [History.providerEvents, machine]
  | @step before after pre post previous action output committed ih =>
      obtain ⟨added, evidence⟩ := committed.causal
      change _ = initial.machine.events ++
        (previous.providerEvents ++ after.machine.events.drop before.machine.events.length)
      rw [evidence.suffix, ← List.append_assoc, ← ih]
      exact evidence.events

/-- Selected physical interpretation of the actual return and raw result. -/
abbrev ReturnInterpretation := Realization → CallProtocol.CallId → CallProtocol.Pending Request →
  ProtocolState → ProtocolState → Nat → ReturnResult → Prop

/-- The same graph places the represented matched return after this history's effects. -/
structure ReturnCausality {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {before : ProtocolState} {frontier : Prefix plan before call record}
    (history : History plan realization initial call record frontier)
    (after : ProtocolState) : Prop where
  fresh : ¬ Represented before (.returned call)
  valid : realization.causal.Valid after
  historyExtends : ∀ a b, realization.causal.precedes before a b → realization.causal.precedes after a b
  entryReturn : realization.causal.precedes after (.entry call) (.returned call)
  effectsReturn : ∀ event ∈ history.providerEvents,
    realization.causal.precedes after (.event event.event.id) (.returned call)

/-- No synthesized return: bookkeeping, raw interpretation and graph evidence
must all describe the endpoint of this reached history. -/
structure MatchedReturn (selected : ReturnInterpretation)
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {before : ProtocolState} {frontier : Prefix plan before call record}
    (history : History plan realization initial call record frontier)
    (result : ReturnResult) (after : ProtocolState) : Prop where
  ran : CallProtocol.return? before call record.caller record.agent record.ids =
    some (embedPending record, after)
  interpreted : selected realization call record before after frontier.accepted result
  conforms : result.Conforms before.machine.memory record.request frontier.accepted
  causal : ReturnCausality history after

/-- Transport to a supplied history at the same original protocol root and
endpoint, retaining the accepted frontier. Exact log suffix equality supplies
the history-dependent causal clause; no equality of derivations is claimed. -/
theorem MatchedReturn.on_history {selected : ReturnInterpretation}
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {before after : ProtocolState} {frontier actualFrontier : Prefix plan before call record}
    {history : History plan realization initial call record frontier} {result : ReturnResult}
    (returned : MatchedReturn selected history result after)
    (actualHistory : History plan realization initial call record actualFrontier)
    (accepted : actualFrontier.accepted = frontier.accepted) :
    MatchedReturn selected actualHistory result after := by
  have events : actualHistory.providerEvents = history.providerEvents :=
    List.append_cancel_left (actualHistory.events_eq.symm.trans history.events_eq)
  refine ⟨returned.ran, ?_, ?_, ?_⟩
  · simpa only [accepted] using returned.interpreted
  · simpa only [accepted] using returned.conforms
  · refine ⟨returned.causal.fresh, returned.causal.valid, returned.causal.historyExtends,
      returned.causal.entryReturn, ?_⟩
    intro event member
    exact returned.causal.effectsReturn event (events ▸ member)

/-- Exact protocol effects follow from the actual return, including custody consumption. -/
theorem MatchedReturn.effects {selected : ReturnInterpretation}
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {before after : ProtocolState} {frontier : Prefix plan before call record}
    {history : History plan realization initial call record frontier} {result : ReturnResult}
    (returned : MatchedReturn selected history result after) :
    CallProtocol.ReturnEffects before after call record.caller record.agent record.ids (embedPending record) :=
  CallProtocol.return?_effects returned.ran

/-- Count observation survives bookkeeping return; this is not an executed caller read. -/
theorem MatchedReturn.conforms_after {selected : ReturnInterpretation}
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {before after : ProtocolState} {frontier : Prefix plan before call record}
    {history : History plan realization initial call record frontier} {result : ReturnResult}
    (returned : MatchedReturn selected history result after) :
    result.Conforms after.machine.memory record.request frontier.accepted :=
  returned.conforms.transport returned.effects.allocations_unchanged
    returned.effects.backings_unchanged

/-- Actual return removes exactly this pending occurrence and its loans, and
rejects replay. The reached publication remains the accepted request prefix. -/
theorem MatchedReturn.consumed {selected : ReturnInterpretation}
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {before after : ProtocolState} {frontier : Prefix plan before call record}
    {history : History plan realization initial call record frontier} {result : ReturnResult}
    (returned : MatchedReturn selected history result after) :
    after.pending.lookup call = none ∧
    (∀ id ∈ record.ids, after.machine.memory.grantAt? id = none) ∧
    CallProtocol.return? after call record.caller record.agent record.ids = none ∧
    history.published = record.request.bytes.take frontier.accepted :=
  ⟨CallProtocol.return?_removes_pending returned.ran,
   CallProtocol.return?_loans_removed returned.ran,
   CallProtocol.return?_replay_rejected returned.ran, history.published_eq_output⟩

/-- Physical correspondence for a separately supplied caller step. -/
abbrev CallerInterpretation := ReturnInterpretation → Realization → CallProtocol.CallId →
  CallProtocol.Pending Request → ReturnResult → Action → ProtocolState →
  ProtocolState → Prop

/-- Optional caller continuation, retaining the matched endpoint and actual checker.
No matched return asserts that such a continuation exists. -/
structure CallerContinuation {selected : ReturnInterpretation}
    {realization : Realization} {initial : ProtocolState}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {before after : ProtocolState} {frontier : Prefix plan before call record}
    {history : History plan realization initial call record frontier} {result : ReturnResult}
    (returned : MatchedReturn selected history result after)
    (correspondence : CallerInterpretation) (action : Action)
    (next : ProtocolState) : Prop where
  ran : CallProtocol.step? after action.policy action.operation record.caller action.kind
    action.cause action.faultAt = some next
  interpreted : correspondence selected realization call record result action after next
  clean : next.machine.violations.IsEmpty
  valid : realization.causal.Valid next
  historyExtends : ∀ a b, realization.causal.precedes after a b → realization.causal.precedes next a b
  events : ∃ added, next.machine.events = after.machine.events ++ added ∧
    (∀ event ∈ added, ∀ old ∈ after.machine.events, event.event.id ≠ old.event.id) ∧
    (∀ event ∈ added, event.event.context.id = record.caller ∧
      realization.causal.precedes next (.returned call) (.event event.event.id))

end Grass.Platform.Win32.WriteFile
