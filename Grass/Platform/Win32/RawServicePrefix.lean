import Grass.Platform.Win32.RawServiceMetadata
import Grass.Platform.Win32.WriteFileServiceContinuation

/-! Fold only the supplied finite same-call service edges into the original
provider history. No edge beyond the finite endpoint, provider return, or
enclosing-run classification is supplied by this construction. -/

namespace Grass.Platform.Win32.Raw.RawStep

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader
open Grass.Platform.Win32.WriteFile

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : Realization}
  {environment : ConsoleEnvironment} {interpretation : ReturnInterpretation}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}

/-- The resulting history is built by appending the actual inverted receipts,
starting with the supplied original history. Choice only extracts data from
the existing proof-valued raw relation; it supplies no executable provider. -/
noncomputable def foldServicePrefix
    (raw : Nat → RawState) (graph : Nat → Graph)
    (agent : Nat → ContextId) (action : Nat → Action) (event : Nat → Event)
    (length : Nat)
    (steps : ∀ n, n < length → RawStep loaded realization environment interpretation
      (graph n) (raw n) (.providerService call (agent n) (action n))
      (event n) (raw (n + 1)) (graph (n + 1)))
    {plan : LoanPlan} {initial state : ProtocolState}
    {frontier : Prefix plan state call record}
    (history : History plan realization initial call record frontier)
    (projected : (raw 0).metadata.pack? (raw 0).machine.machine = some state)
    (runtime : WriteFileRuntime)
    (lookup : (raw 0).calls.lookup call = some (.writeFile runtime))
    (planEq : runtime.loanPlan = plan) (accepted : runtime.accepted = frontier.accepted) :
    Σ endpoint, Σ reached : Prefix plan endpoint call record,
      { _accumulated : History plan realization initial call record reached //
        (raw length).metadata.pack? (raw length).machine.machine = some endpoint ∧
        ∃ currentRuntime, (raw length).calls.lookup call = some (.writeFile currentRuntime) ∧
          currentRuntime.loanPlan = plan ∧ currentRuntime.accepted = reached.accepted } := by
  classical
  induction length with
  | zero => exact ⟨state, frontier, history, projected, runtime, lookup, planEq, accepted⟩
  | succ length ih =>
    let previous := ih (fun n below => steps n (Nat.lt_trans below (Nat.lt_succ_self length)))
    have pending : (raw length).metadata.pending.lookup call = some (embedPending record) := by
      have metadata := (CallProtocol.Metadata.pack?_fields previous.2.2.property.1).2
      exact (congrArg (fun data : CallProtocol.Metadata ApiRequest => data.pending.lookup call)
        metadata).symm.trans previous.2.1.pending.lookup
    let inverted := service_receipt_sameRecord (steps length (Nat.lt_succ_self length)) pending
    let receipt := Classical.choose (Classical.choose_spec inverted)
    have facts := Classical.choose_spec (Classical.choose_spec inverted)
    have sameState : receipt.protocol = previous.1 :=
      Option.some.inj (receipt.projected.symm.trans previous.2.2.property.1)
    have coordinates : receipt.runtime.loanPlan = plan ∧ receipt.pre.accepted = previous.2.1.accepted := by
      obtain ⟨priorRuntime, priorLookup, priorPlan, priorAccepted⟩ := previous.2.2.property.2
      have same := CallRuntime.writeFile.inj (Option.some.inj (receipt.runtimeLookup.symm.trans priorLookup))
      exact ⟨(congrArg WriteFileRuntime.loanPlan same).trans priorPlan,
        receipt.accepted.trans ((congrArg WriteFileRuntime.accepted same).trans priorAccepted)⟩
    let extended := receipt.extendHistory previous.2.2.val coordinates.1 sameState coordinates.2
    refine ⟨receipt.nextProtocol, extended.1, extended.2, ?_, receipt.nextRuntime, ?_,
      receipt.after_loanPlan.trans coordinates.1, ?_⟩
    · exact (congrArg (fun next : RawState => next.metadata.pack? next.machine.machine)
        facts.2.1).symm.trans receipt.after_projected
    · exact (congrArg (fun next : RawState => next.calls.lookup call)
        facts.2.1).symm.trans receipt.after_runtimeLookup
    · exact receipt.after_accepted.trans
        (receipt.extendHistory_accepted previous.2.2.val coordinates.1 sameState coordinates.2).symm

variable (raw : Nat → RawState) (graph : Nat → Graph)
  (agent : Nat → ContextId) (action : Nat → Action) (event : Nat → Event)
  {plan : LoanPlan} {initial state : ProtocolState}
  {frontier : Prefix plan state call record}
  (history : History plan realization initial call record frontier)
  (projected : (raw 0).metadata.pack? (raw 0).machine.machine = some state)
  (runtime : WriteFileRuntime) (lookup : (raw 0).calls.lookup call = some (.writeFile runtime))
  (planEq : runtime.loanPlan = plan) (accepted : runtime.accepted = frontier.accepted)

theorem foldServicePrefix_zero
    (steps : ∀ n, n < 0 → RawStep loaded realization environment interpretation
      (graph n) (raw n) (.providerService call (agent n) (action n))
      (event n) (raw (n + 1)) (graph (n + 1))) :
    HEq (foldServicePrefix raw graph agent action event 0 steps history projected runtime lookup planEq accepted).2.2.val
      history := HEq.rfl

theorem foldServicePrefix_events (length : Nat)
    (steps : ∀ n, n < length → RawStep loaded realization environment interpretation
      (graph n) (raw n) (.providerService call (agent n) (action n))
      (event n) (raw (n + 1)) (graph (n + 1))) :
    let folded := foldServicePrefix raw graph agent action event length steps
      history projected runtime lookup planEq accepted
    folded.2.2.val.providerEvents =
      (raw length).machine.machine.events.drop initial.machine.events.length := by
  dsimp only
  let folded := foldServicePrefix raw graph agent action event length steps
    history projected runtime lookup planEq accepted
  have machine := (CallProtocol.Metadata.pack?_fields folded.2.2.property.1).1
  have events : (raw length).machine.machine.events = initial.machine.events ++ folded.2.2.val.providerEvents :=
    (congrArg MachineState.events machine).symm.trans folded.2.2.val.events_eq
  rw [events]
  simp
  rfl

/-- The next history is literally the previous fold extended with this raw
edge's actual receipt, action and publication. No alternative path is selected. -/
theorem foldServicePrefix_step (length : Nat)
    (steps : ∀ n, n < length + 1 → RawStep loaded realization environment interpretation
      (graph n) (raw n) (.providerService call (agent n) (action n))
      (event n) (raw (n + 1)) (graph (n + 1))) :
    let previous := foldServicePrefix raw graph agent action event length
      (fun n below => steps n (Nat.lt_trans below (Nat.lt_succ_self length)))
      history projected runtime lookup planEq accepted
    let next := foldServicePrefix raw graph agent action event (length + 1) steps
      history projected runtime lookup planEq accepted
    ∃ (output : Vec Byte) (receipt : ServiceReceipt realization (raw length) call record (action length) output),
      record.agent = agent length ∧ receipt.after = raw (length + 1) ∧
      (event length).kind = (if output.length = 0 then .internal else .endpoint (.published call output)) ∧
      (graph length).Realizes realization.causal receipt.protocol ∧
      (graph (length + 1)).Realizes realization.causal receipt.nextProtocol ∧
      ∃ (samePlan : receipt.runtime.loanPlan = plan) (sameState : receipt.protocol = previous.1)
        (sameAccepted : receipt.pre.accepted = previous.2.1.accepted),
        next.1 = receipt.nextProtocol ∧
        HEq next.2.2.val (receipt.extendHistory previous.2.2.val samePlan sameState sameAccepted).2 := by
  classical
  dsimp only
  let previous := foldServicePrefix raw graph agent action event length
    (fun n below => steps n (Nat.lt_trans below (Nat.lt_succ_self length)))
    history projected runtime lookup planEq accepted
  have pending : (raw length).metadata.pending.lookup call = some (embedPending record) := by
    have metadata := (CallProtocol.Metadata.pack?_fields previous.2.2.property.1).2
    exact (congrArg (fun data : CallProtocol.Metadata ApiRequest => data.pending.lookup call)
      metadata).symm.trans previous.2.1.pending.lookup
  let inverted := service_receipt_sameRecord (steps length (Nat.lt_succ_self length)) pending
  let receipt := Classical.choose (Classical.choose_spec inverted)
  have facts := Classical.choose_spec (Classical.choose_spec inverted)
  refine ⟨_, receipt, facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2, ?_⟩
  have sameState : receipt.protocol = previous.1 :=
    Option.some.inj (receipt.projected.symm.trans previous.2.2.property.1)
  have coordinates : receipt.runtime.loanPlan = plan ∧ receipt.pre.accepted = previous.2.1.accepted := by
    obtain ⟨priorRuntime, priorLookup, priorPlan, priorAccepted⟩ := previous.2.2.property.2
    have same := CallRuntime.writeFile.inj (Option.some.inj (receipt.runtimeLookup.symm.trans priorLookup))
    exact ⟨(congrArg WriteFileRuntime.loanPlan same).trans priorPlan,
      receipt.accepted.trans ((congrArg WriteFileRuntime.accepted same).trans priorAccepted)⟩
  exact ⟨coordinates.1, sameState, coordinates.2, rfl, HEq.rfl⟩

end Grass.Platform.Win32.Raw.RawStep
