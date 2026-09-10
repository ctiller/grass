import Grass.Platform.Win32.RawServiceMetadata
import Grass.Platform.Win32.WriteFileServiceContinuation

/-! Connect a suffix of the installed raw relation to provider continuation
evidence. Every supplied edge must have the explicit provider-service choice
for the same call. This does not classify arbitrary raw infinity, install a
complete execution model, or supply a global raw infinite-consistency witness.
The original reachable provider history and all raw streams remain inputs;
the conclusions retain their pending record, actions, publications and graphs. -/

namespace Grass.Platform.Win32.Raw.RawStep

open Grass.Core Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
  {environment : ConsoleEnvironment}
  {call : CallProtocol.CallId}

/-- `service_suffix_metadata` proves that every edge in an explicitly
service-classified suffix preserves the entire protocol metadata. -/
theorem service_suffix_metadata
    (raw : Nat → RawState) (graph : Nat → Graph)
    (agent : Nat → ContextId) (action : Nat → WriteFile.Action) (event : Nat → Event)
    (steps : ∀ n, RawStep loaded realization environment (graph n) (raw n)
      (.providerService call (agent n) (action n)) (event n) (raw (n + 1)) (graph (n + 1)))
    (n : Nat) : (raw n).metadata = (raw 0).metadata := by
  induction n with
  | zero => rfl
  | succ n ih => exact (service_metadata (steps n)).trans ih

/-- Invert every actual service edge, identify one full pending record through
the preserved table, and extract a continuation rooted in the supplied history.
The initial runtime bindings are explicit reached-state obligations. No native
provider adequacy, arbitrary-suffix classification or permanent wait is asserted. -/
theorem service_suffix_continuation
    (raw : Nat → RawState) (graph : Nat → Graph)
    (agent : Nat → ContextId) (action : Nat → WriteFile.Action) (event : Nat → Event)
    (steps : ∀ n, RawStep loaded realization environment (graph n) (raw n)
      (.providerService call (agent n) (action n)) (event n) (raw (n + 1)) (graph (n + 1)))
    {plan : WriteFile.LoanPlan} {initial state : WriteFile.ProtocolState}
    {record : CallProtocol.Pending WriteFile.Request}
    {frontier : WriteFile.Prefix plan state call record}
    (history : WriteFile.History plan realization initial call record frontier)
    (projected : (raw 0).metadata.pack? (raw 0).machine.machine = some state)
    (runtime : WriteFileRuntime)
    (runtimeLookup : (raw 0).calls.lookup call = some (.writeFile runtime))
    (runtimePlan : runtime.loanPlan = plan)
    (runtimeAccepted : runtime.accepted = frontier.accepted) :
    ∃ continuation : WriteFile.InfiniteContinuation history, ∀ n,
      (raw n).metadata = (raw 0).metadata ∧
      (raw n).metadata.pack? (raw n).machine.machine = some (continuation.point n).1 ∧
      (∃ currentRuntime, (raw n).calls.lookup call = some (.writeFile currentRuntime) ∧
        currentRuntime.accepted = (continuation.point n).2.accepted) ∧
      agent n = record.agent ∧ continuation.action n = action n ∧
      (event n).kind = (if (continuation.output n).length = 0 then .internal
        else .endpoint (.published call (continuation.output n))) ∧
      (graph n).Realizes realization.causal (continuation.point n).1 ∧
      (graph (n + 1)).Realizes realization.causal (continuation.point (n + 1)).1 := by
  classical
  have metadata := service_suffix_metadata raw graph agent action event steps
  have pendingZero : (raw 0).metadata.pending.lookup call =
      some (WriteFile.embedPending record) := by
    rw [← (CallProtocol.Metadata.pack?_fields projected).2]
    exact frontier.pending.lookup
  have pending : ∀ n, (raw n).metadata.pending.lookup call =
      some (WriteFile.embedPending record) := by
    intro n
    rw [metadata n]
    exact pendingZero
  have inverted := fun n => service_receipt_sameRecord (steps n) (pending n)
  let output := fun n => Classical.choose (inverted n)
  let receipt := fun n => Classical.choose (Classical.choose_spec (inverted n))
  have facts := fun n => Classical.choose_spec (Classical.choose_spec (inverted n))
  have agentExact := fun n => (facts n).1
  have advances := fun n => (facts n).2.1
  have kind := fun n => (facts n).2.2.1
  have priorCausal := fun n => (facts n).2.2.2.1
  have nextCausal := fun n => (facts n).2.2.2.2
  have stateZero : state = (receipt 0).protocol :=
    Option.some.inj (projected.symm.trans (receipt 0).projected)
  have runtimeZero : runtime = (receipt 0).runtime :=
    CallRuntime.writeFile.inj
      (Option.some.inj (runtimeLookup.symm.trans (receipt 0).runtimeLookup))
  have planZero : plan = (receipt 0).runtime.loanPlan :=
    runtimePlan.symm.trans (congrArg WriteFileRuntime.loanPlan runtimeZero)
  have acceptedZero : frontier.accepted = (receipt 0).pre.accepted :=
    runtimeAccepted.symm.trans ((congrArg WriteFileRuntime.accepted runtimeZero).trans
      (receipt 0).accepted.symm)
  let continuation := WriteFile.ServiceReceipt.extractInfiniteContinuationFrom
    raw action output receipt advances history planZero stateZero acceptedZero
  have pointState := WriteFile.ServiceReceipt.extractInfiniteContinuationFrom_point_state
    raw action output receipt advances history planZero stateZero acceptedZero
  have pointAccepted := WriteFile.ServiceReceipt.extractInfiniteContinuationFrom_point_accepted
    raw action output receipt advances history planZero stateZero acceptedZero
  refine ⟨continuation, fun n => ?_⟩
  have nextProtocol := (WriteFile.ServiceReceipt.stream_continuity
    raw action output receipt advances n).1
  refine ⟨metadata n, ?_, ?_, (agentExact n).symm, rfl, kind n, ?_, ?_⟩
  · rw [pointState n]
    exact (receipt n).projected
  · exact ⟨(receipt n).runtime, (receipt n).runtimeLookup, (pointAccepted n).symm⟩
  · rw [pointState n]
    exact priorCausal n
  · rw [pointState (n + 1), nextProtocol]
    exact nextCausal n

end Grass.Platform.Win32.Raw.RawStep
