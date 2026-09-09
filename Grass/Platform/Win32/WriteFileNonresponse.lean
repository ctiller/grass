import Grass.Platform.Win32.WriteFile

/-! # Infinite synchronous WriteFile continuations

This evidence consumer records finite evidence at every point of an infinite
continuation. It supplies neither physical existence nor a default explanation
for stalling.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.Op Grass.Std.Logical

/-- An infinite continuation from one reachable pending endpoint. Every edge is
an actual committed provider step for the same call, record, and realization,
and every finite point remains reachable from the original handoff. -/
structure InfiniteContinuation
    {realization : Realization} {initial : CallProtocol.State Request}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : CallProtocol.State Request} {frontier : Prefix state call record}
    (history : History realization initial call record frontier) where
  point : Nat → Σ nextState, Prefix nextState call record
  start : point 0 = ⟨state, frontier⟩
  action : Nat → Action
  output : Nat → Vec Byte
  committed : ∀ n, CommittedStep realization
    (point n).2 (point (n + 1)).2 (action n) (output n)

/-- Accumulate the exact root history along the committed edge stream. Later
reachability is derived rather than selected independently at each point. -/
def InfiniteContinuation.historyAt
    {realization : Realization} {initial : CallProtocol.State Request}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : CallProtocol.State Request} {frontier : Prefix state call record}
    {history : History realization initial call record frontier}
    (continuation : InfiniteContinuation history) :
    (n : Nat) → History realization initial call record (continuation.point n).2
  | 0 => by
      rw [continuation.start]
      exact history
  | n + 1 =>
      .step (continuation.historyAt n) (continuation.action n)
        (continuation.output n) (continuation.committed n)

/-- The derived history at the start is the supplied reachable history, after
transport along `InfiniteContinuation.start`. -/
theorem InfiniteContinuation.historyAt_zero
    {realization : Realization} {initial : CallProtocol.State Request}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : CallProtocol.State Request} {frontier : Prefix state call record}
    {history : History realization initial call record frontier}
  (continuation : InfiniteContinuation history) :
    HEq (continuation.historyAt 0) history := by
  simp [InfiniteContinuation.historyAt]

/-- Each later history is exactly the previous derived history extended by the
stored committed edge. -/
@[simp] theorem InfiniteContinuation.historyAt_succ
    {realization : Realization} {initial : CallProtocol.State Request}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : CallProtocol.State Request} {frontier : Prefix state call record}
    {history : History realization initial call record frontier}
    (continuation : InfiniteContinuation history) (n : Nat) :
    continuation.historyAt (n + 1) =
      .step (continuation.historyAt n) (continuation.action n)
        (continuation.output n) (continuation.committed n) := rfl

/-- A fixed-acceptance continuation records the extra premise that every point
retains the acceptance count at the supplied reachable frontier. -/
structure FixedCut
    {realization : Realization} {initial : CallProtocol.State Request}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : CallProtocol.State Request} {frontier : Prefix state call record}
    {history : History realization initial call record frontier}
    (continuation : InfiniteContinuation history) : Prop where
  accepted : ∀ n, (continuation.point n).2.accepted = frontier.accepted

/-- `FixedCut.accepted` and each edge's `Publication.suffix` force every
incremental output chunk to be empty. -/
theorem FixedCut.output_empty
    {realization : Realization} {initial : CallProtocol.State Request}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : CallProtocol.State Request} {frontier : Prefix state call record}
    {history : History realization initial call record frontier}
    {continuation : InfiniteContinuation history}
    (fixed : FixedCut continuation) (n : Nat) :
    continuation.output n = Vec.empty := by
  have same : (continuation.point (n + 1)).2.accepted =
      (continuation.point n).2.accepted :=
    (fixed.accepted (n + 1)).trans (fixed.accepted n).symm
  rw [(continuation.committed n).publication.suffix, same]
  simp

/-- An application-selected relation explaining why one exact pending
occurrence is externally stalled at a state and accepted count. The realization
is an explicit input to the relation rather than an erased association. -/
def StalledPredicate := Realization → CallProtocol.CallId →
  CallProtocol.Pending Request →
  CallProtocol.State Request → Nat → Prop

/-- An externally justified stalled observation at one exact reachable pending
endpoint. `history` supplies reachability and preserves the occurrence and
custody evidence already indexed by `Prefix`; `observed` is the only stall
witness. Earlier output progress may use any later finite `History`, including
`InfiniteContinuation.historyAt` when available, without inventing subsequent
actions. This proposition supplies no default predicate or physical adequacy,
and does not assert that possible reply transitions are disabled. -/
structure StalledNonresponse (stalledPredicate : StalledPredicate)
    {realization : Realization} {initial : CallProtocol.State Request}
    {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
    {state : CallProtocol.State Request} {frontier : Prefix state call record}
    (history : History realization initial call record frontier) : Prop where
  observed : stalledPredicate realization call record state frontier.accepted

end Grass.Platform.Win32.WriteFile
