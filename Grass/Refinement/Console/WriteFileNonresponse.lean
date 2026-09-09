import Grass.Refinement.Console.WriteFileHistory

/-! Conditional nonresponse projection at the exact folded endpoint.
Stalled evidence and actual fixed-cut infinite provider execution remain distinct
carriers. Neither constructs physical nonresponse, all-cut reachability, return,
or stabilization of an arbitrary infinite stream. Possible upper replies remain
enabled at this same frontier. No caller/CFG spin is an admissible input.
-/

namespace Grass.Refinement.Console.WriteFileHistory

open Grass.Console Grass.Semantics Grass.Std.Logical Grass.Op
open Grass.Platform.Win32.WriteFile

variable {R Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
  {spec : SpecProcess resources}
  {projection : CapturedTargetProjection spec Status}
  {realization : Realization} {initial state : CallProtocol.State Request}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
  {frontier : Prefix state call record}
  {history : History realization initial call record frontier}
  {relation : HandoffRelation projection}

/-- Endpoint stall evidence over the retained provider history and alignment. -/
structure Stalled (predicate : StalledPredicate) (aligned : Aligned relation history) : Prop where
  evidence : StalledNonresponse predicate history

namespace Stalled

variable {predicate : StalledPredicate} {aligned : Aligned relation history}

/-- Map a supplied external stall to the permitted wait at this folded endpoint;
the lower evidence remains available in `Stalled.evidence`. -/
def waiting (_stalled : Stalled predicate aligned) :
    Grass.RelationalSystem.PermanentWait (Behavior.boundary projection.target.payload) aligned.upper :=
  ⟨aligned.endpoint, aligned.upper_located, trivial⟩

def complete (stalled : Stalled predicate aligned) : projection.componentComplete :=
  .waiting aligned.upper stalled.waiting

theorem same_cut (stalled : Stalled predicate aligned) :
    stalled.waiting.occurrence = aligned.endpoint := rfl

/-- The exact lower occurrence and its held custody remain part of the input. -/
theorem pending (_stalled : Stalled predicate aligned) : PendingAt state call record :=
  frontier.pending

end Stalled

/-- `FixedNonresponse.continuation` requires `InfiniteContinuation` provider
steps; `FixedNonresponse.fixed` separately requires constant acceptance. -/
structure FixedNonresponse (aligned : Aligned relation history) where
  continuation : InfiniteContinuation history
  fixed : FixedCut continuation

namespace FixedNonresponse

variable {aligned : Aligned relation history}

def waiting (_response : FixedNonresponse aligned) :
    Grass.RelationalSystem.PermanentWait (Behavior.boundary projection.target.payload) aligned.upper :=
  ⟨aligned.endpoint, aligned.upper_located, trivial⟩

def complete (response : FixedNonresponse aligned) : projection.componentComplete :=
  .waiting aligned.upper response.waiting

/-- Every finite endpoint is rooted in the same original provider history. -/
def historyAt (response : FixedNonresponse aligned) (n : Nat) :
    History realization initial call record (response.continuation.point n).2 :=
  response.continuation.historyAt n

def alignedAt (response : FixedNonresponse aligned) (n : Nat) :
    Aligned relation (response.historyAt n) := aligned.alignedAt response.continuation n

/-- The complete folded history is unchanged along every finite stream prefix. -/
theorem upper_at (response : FixedNonresponse aligned) (n : Nat) :
    (response.alignedAt n).upper = aligned.upper :=
  aligned.alignedAt_fixed_upper response.continuation response.fixed n

theorem cut_at (response : FixedNonresponse aligned) (n : Nat) :
    WriteFileProjection.cut aligned.start.cut aligned.start.suffix
      (response.continuation.point n).2 = aligned.endpoint := by
  apply OutputCut.ext
  change aligned.start.cut.offset + (response.continuation.point n).2.accepted =
    aligned.start.cut.offset + frontier.accepted
  rw [response.fixed.accepted n]

theorem output_empty (response : FixedNonresponse aligned) (n : Nat) :
    response.continuation.output n = Vec.empty := response.fixed.output_empty n

theorem pending_at (response : FixedNonresponse aligned) (n : Nat) :
    PendingAt (response.continuation.point n).1 call record :=
  (response.continuation.point n).2.pending

theorem same_cut (response : FixedNonresponse aligned) :
    response.waiting.occurrence = aligned.endpoint := rfl

end FixedNonresponse
end Grass.Refinement.Console.WriteFileHistory
