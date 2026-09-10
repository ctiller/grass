import Grass.Platform.Win32.WriteFileReturnHistory
import Grass.Platform.Win32.RawPendingService

/-! Consume a contiguous slice of one indexed raw derivation, retaining its
original entered binding. The enclosing entry occurrence is supplied by the
caller; endpoint agreement does not recover entry ancestry. -/

namespace Grass.Platform.Win32.WriteFile.CallHandoff

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Raw

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {before : ExecutionState.State ApiRequest}
  {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
  {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
  {request : Request} {provider : ContextId}
  (entered : CallHandoff loaded before receipt request provider) (prior : CallRuntimeTable)
  {realization : Realization} {environment : ConsoleEnvironment} {interpretation : ReturnInterpretation}
  {total : Nat} (states : Fin (total + 1) → RawState) (graphs : Fin (total + 1) → Graph)
  (choices : Fin total → Choice) (events : Fin total → Event)
  (steps : ∀ index, RawStep loaded realization environment interpretation
    (graphs index.castSucc) (states index.castSucc) (choices index) (events index)
    (states index.succ) (graphs index.succ))
  (start count : Nat) (within : start + count ≤ total)
  (root : states ⟨start, by omega⟩ = entered.rawAfter prior)
  (continuing : ∀ offset, (below : offset < count) →
    (events ⟨start + offset, by omega⟩).kind = .internal ∨
      ∃ observedCall bytes,
        (events ⟨start + offset, by omega⟩).kind = .endpoint (.published observedCall bytes))
  (causal : HandoffCausality realization.causal entered.handoff.call entered.handoff.record
    entered.handoff.beforeProtocol entered.handoff.afterProtocol)

/-- Append exactly the slice's actual service receipts using the existing fold.
The empty slice retains the original handoff history without selecting an action.
Clamped indices only extend the finite arrays for that fold; no edge outside
the slice is required or used. -/
noncomputable def serviceHistorySegment :
    Σ endpoint, Σ reached : Prefix entered.abi.loanPlan endpoint entered.handoff.call entered.handoff.record,
      { _accumulated : History entered.abi.loanPlan realization entered.handoff.beforeProtocol
          entered.handoff.call entered.handoff.record reached //
        (states ⟨start + count, by omega⟩).metadata.pack?
          (states ⟨start + count, by omega⟩).machine.machine = some endpoint ∧
        ∃ runtime, (states ⟨start + count, by omega⟩).calls.lookup entered.handoff.call =
          some (.writeFile runtime) ∧ runtime.loanPlan = entered.abi.loanPlan ∧
          runtime.accepted = reached.accepted } := by
  classical
  by_cases empty : count = 0
  · subst count
    refine ⟨_, _, entered.handoff.history realization causal, ?_, entered.runtime, ?_, rfl, rfl⟩
    · exact (congrArg (fun raw : RawState => raw.metadata.pack? raw.machine.machine) root).trans
        entered.handoff.after_projected
    · exact (congrArg (fun raw : RawState => raw.calls.lookup entered.handoff.call) root).trans
        (entered.rawAfter_lookup prior)
  · have pending := RawStep.pending_segment states graphs choices events steps start count within
      (show (states ⟨start, by omega⟩).control = .pending entered.handoff.call
        entered.handoff.record.caller entered.handoff.record.agent by rw [root]; rfl) continuing
    have actions : ∀ offset : Fin count, ∃ action,
        choices ⟨start + offset.val, by omega⟩ =
          .providerService entered.handoff.call entered.handoff.record.agent action := by
      intro offset
      obtain ⟨record, action, output, service, _, _, selected, _⟩ :=
        RawStep.pending_to_pending_service (steps ⟨start + offset.val, by omega⟩)
          (pending offset.val (by omega)) (pending (offset.val + 1) (by omega))
      exact ⟨action, selected⟩
    let raw := fun n => states ⟨start + min n count, by have := Nat.min_le_right n count; omega⟩
    let graph := fun n => graphs ⟨start + min n count, by have := Nat.min_le_right n count; omega⟩
    let index := fun n => (⟨min n (count - 1), by have := Nat.min_le_right n (count - 1); omega⟩ : Fin count)
    let action := fun n => Classical.choose (actions (index n))
    let event := fun n => events ⟨start + (index n).val, by have := (index n).isLt; omega⟩
    have serviceSteps : ∀ n, n < count → RawStep loaded realization environment interpretation
        (graph n) (raw n) (.providerService entered.handoff.call entered.handoff.record.agent (action n))
        (event n) (raw (n + 1)) (graph (n + 1)) := by
      intro n below
      have selected := Classical.choose_spec (actions (index n))
      have edge := steps ⟨start + (index n).val, by have := (index n).isLt; omega⟩
      rw [selected] at edge
      simpa only [raw, graph, event, action, index, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, Nat.min_eq_left (by omega : n ≤ count - 1),
        Nat.min_eq_left (by omega : n ≤ count), Nat.min_eq_left (by omega : n + 1 ≤ count),
        Nat.add_assoc] using edge
    simpa only [raw, Nat.min_self] using entered.serviceHistory prior raw graph (fun _ => entered.handoff.record.agent)
      action event count (by simpa only [raw, Nat.zero_min, Nat.add_zero] using root) serviceSteps causal

/-- A slice without service edges keeps the exact original handoff history. -/
theorem serviceHistorySegment_zero (within : start + 0 ≤ total)
    (root : states ⟨start, by omega⟩ = entered.rawAfter prior)
    (continuing : ∀ offset, (below : offset < 0) →
      (events ⟨start + offset, by omega⟩).kind = .internal ∨
        ∃ observedCall bytes,
          (events ⟨start + offset, by omega⟩).kind = .endpoint (.published observedCall bytes)) :
    HEq (entered.serviceHistorySegment prior states graphs choices events steps start 0 within root continuing causal).2.2.val
      (entered.handoff.history realization causal) := by
  simp [serviceHistorySegment]

/-- The observation fixes the same endpoint and accepted count, so matched
return evidence transports to this segment's constructed original-entry history.
This identifies its causal event suffix, not equality of history derivations. -/
theorem returnedAfterSegment
    {providerState settled : ProtocolState}
    {frontier : Prefix entered.abi.loanPlan providerState entered.handoff.call entered.handoff.record}
    {history : History entered.abi.loanPlan realization entered.handoff.beforeProtocol
      entered.handoff.call entered.handoff.record frontier}
    {result : ReturnResult} {gpr : Gpr → BitVec 64} {rflags : BitVec 64}
    (observed : Return.Observation entered frontier (states ⟨start + count, by omega⟩) result gpr rflags)
    (returned : MatchedReturn interpretation history result settled) :
    MatchedReturn interpretation
      (entered.serviceHistorySegment prior states graphs choices events steps start count within root continuing causal).2.2.val
      result settled := by
  let folded := entered.serviceHistorySegment prior states graphs choices events steps start count within root continuing causal
  have endpoint : providerState = folded.1 :=
    Option.some.inj (observed.projected.symm.trans folded.2.2.property.1)
  have accepted : folded.2.1.accepted = frontier.accepted := by
    obtain ⟨runtime, lookup, _, accepted⟩ := folded.2.2.property.2
    have same : runtime = observed.runtime :=
      CallRuntime.writeFile.inj (Option.some.inj (lookup.symm.trans observed.link.runtimeLookup))
    exact accepted.symm.trans ((congrArg WriteFileRuntime.accepted same).trans observed.accepted)
  cases endpoint
  exact returned.on_history folded.2.2.val accepted

end Grass.Platform.Win32.WriteFile.CallHandoff
