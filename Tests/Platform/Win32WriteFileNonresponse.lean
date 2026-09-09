import Grass.Platform.Win32.WriteFileNonresponse
import Tests.Platform.Win32WriteFile


/-! Conditional evidence fixtures: every endpoint below is an explicit model witness;
none is evidence of native dispatch, blocking, or physical adequacy. -/
namespace Grass.Tests.WriteFileNonresponseFixtures

open Grass.Op Grass.Std.Logical Grass.Platform.Win32.WriteFile
open Grass.Tests.Win32WriteFile

/-- A deliberately synthetic endpoint predicate for the existing reachable
quiet history. Its equalities make the selected model occurrence explicit. -/
def syntheticStall : StalledPredicate := fun realization occurrence pending state accepted =>
  realization = noEffects ∧ occurrence = call ∧ pending = record ∧ state = quietState ∧ accepted = 0

theorem syntheticEndpoint : StalledNonresponse syntheticStall quietHistory :=
  ⟨by exact ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Selecting no endpoint rejects the same real root history. -/
def noStall : StalledPredicate := fun _ _ _ _ _ => False

theorem noStall_rejected : ¬ StalledNonresponse noStall quietHistory := by
  intro observed
  exact observed.observed

/-- A selected relation for a different occurrence cannot label this endpoint. -/
def wrongOccurrenceStall : StalledPredicate := fun _ occurrence _ _ _ =>
  occurrence = pending.callSupply.fresh.1

theorem wrongOccurrence_rejected : ¬ StalledNonresponse wrongOccurrenceStall quietHistory := by
  intro observed
  have wrong := observed.observed
  change call = pending.callSupply.fresh.1 at wrong
  exact (by decide : call ≠ pending.callSupply.fresh.1) wrong

/-- Fixed-cut continuations add no output at any next derived history. This is
generic over a supplied continuation and makes no claim that one exists. -/
theorem fixedCut_historyAt_succ_published
    {realization : Realization} {initial : ProtocolState}
    {occurrence : CallProtocol.CallId} {pending : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state occurrence pending}
    {history : History plan realization initial occurrence pending frontier}
    {continuation : InfiniteContinuation history} (fixed : FixedCut continuation) (n : Nat) :
    (continuation.historyAt (n + 1)).published = (continuation.historyAt n).published := by
  rw [InfiniteContinuation.historyAt_succ]
  simp [History.published, fixed.output_empty n]

/-- Even a full accepted cut has a structural stalled-endpoint witness only
when a caller supplies a predicate and a reachable history. It supplies neither
history existence nor a claim that a synchronous API may fail to return. -/
theorem fullAccepted_endpoint_requires_only_witness
    {realization : Realization} {initial : ProtocolState}
    {occurrence : CallProtocol.CallId} {pending : CallProtocol.Pending Request}
    {state : ProtocolState} {frontier : Prefix plan state occurrence pending}
    (selected : StalledPredicate)
    (history : History plan realization initial occurrence pending frontier)
    (_full : frontier.accepted = pending.request.requested)
    (observed : selected realization occurrence pending state frontier.accepted) :
    StalledNonresponse selected history :=
  ⟨observed⟩

end Grass.Tests.WriteFileNonresponseFixtures
