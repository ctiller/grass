import Grass.Refinement.Console.WriteFileNonresponse
import Grass.Platform.Win32.WriteFileStabilization

/-! An actual infinite provider continuation eventually supplies fixed-cut
nonresponse at its exact accumulated history. This theorem consumes provider
execution and caller alignment; it does not classify raw executions or assert
that a physical provider continuation exists. Earlier publications are retained
by `historyAt`, and the resulting evidence retains the exact shifted stream. -/

namespace Grass.Refinement.Console.WriteFileHistory

open Grass.Console Grass.Semantics Grass.Std.Logical Grass.Op
open Grass.Platform.Win32.WriteFile

variable {R Outcome Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
  {spec : CapturedSpecification resources Outcome}
  {projection : CapturedTargetProjection spec Status}
  {plan : LoanPlan} {realization : Realization} {initial state : ProtocolState}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
  {frontier : Prefix plan state call record}
  {history : History plan realization initial call record frontier}
  {relation : HandoffRelation (plan := plan) projection}

/-- The wait is reached after the actual finite publication prefix, with the
same original handoff and the exact remaining provider stream. No responsiveness
assumption or conversion of a caller/CPU infinite loop is involved. -/
theorem Aligned.eventually_fixedNonresponse (aligned : Aligned relation history)
    (continuation : InfiniteContinuation history) :
    ∃ index, ∃ response : FixedNonresponse (aligned.alignedAt continuation index),
      response.continuation = continuation.shift index ∧
      (continuation.historyAt index).published = (continuation.point index).2.output := by
  obtain ⟨index, fixed⟩ := continuation.stabilizes
  exact ⟨index, ⟨continuation.shift index, fixed⟩, rfl,
    continuation.shift_root_published index⟩

end Grass.Refinement.Console.WriteFileHistory
