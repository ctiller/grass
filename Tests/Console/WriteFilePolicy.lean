import Grass.Refinement.Console.WriteFilePolicy

namespace Grass.Tests.Console.WriteFilePolicy

open Grass.Console Grass.Semantics Grass.Std.Logical Grass.Std.Console Grass.Op
open Grass.Platform.Win32.WriteFile
open Grass.Refinement.Console.WriteFileHistory

variable {R Outcome Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
  {spec : CapturedSpecification resources Outcome}
  {projection : CapturedTargetProjection spec Status}
  {realization : Realization} {initial before after : CallProtocol.State Request}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
  {frontier : Prefix before call record}
  {history : History realization initial call record frontier}
  {relation : HandoffRelation projection} {aligned : Aligned relation history}
  {selected : ReturnInterpretation} {result : ReturnResult}

/-- Failure at full output retains failure and does not emit the payload twice. -/
example (returned : Returned aligned selected result after) (failed : result.rawBool = 0)
    (full : frontier.accepted = record.request.bytes.length) :
    aligned.endpoint = OutputCut.full projection.target.payload ∧
      result.reportedCount = none ∧
      Behavior.emittedBytes (returned.logicalFinish .writeFailed
        (advance returned.cursor returned.count) (returned.failure_decision failed)).path.events =
        Behavior.emittedBytes aligned.upper.path.events :=
  ⟨aligned.endpoint_full full, returned.failure_no_count failed,
    returned.finish_no_republication _ _ (returned.failure_decision failed)⟩

/-- Noncanonical nonzero BOOL plus observed zero DWORD follows no-progress policy. -/
example (returned : Returned aligned selected result after) (raw : result.rawBool = 2)
    (reported : result.reportedCount = some 0) :
    returned.decision = .done .noProgress returned.cursor := by
  have succeeded : result.rawBool ≠ 0 := by rw [raw]; decide
  obtain ⟨value, same, _, count⟩ := returned.success_count succeeded
  have zero : value = 0 := Option.some.inj (same.symm.trans reported)
  have accepted : frontier.accepted = 0 := by
    change value.toNat = frontier.accepted at count
    rw [zero] at count
    exact count.symm
  exact returned.zero_success_decision succeeded accepted

/-- Positive partial success exposes only the remaining suffix, not a new call. -/
example (returned : Returned aligned selected result after) (success : result.rawBool ≠ 0)
    (positive : 0 < frontier.accepted)
    (proper : aligned.endpoint.offset < projection.target.payload.length) :
    (advance returned.cursor returned.count).remaining = aligned.endpoint.remaining ∧
      (advance returned.cursor returned.count).remaining.length < returned.cursor.remaining.length :=
  (returned.retry_ready _ (returned.partial_success_decision success positive proper)).2

/-- A full successful reply enables a logical finish with no extra publication. -/
example (returned : Returned aligned selected result after) (success : result.rawBool ≠ 0)
    (full : frontier.accepted = record.request.bytes.length) :
    Behavior.emittedBytes (returned.logicalFinish .success
      (advance returned.cursor returned.count) (returned.full_success_decision success full)).path.events =
      Behavior.emittedBytes aligned.upper.path.events :=
  returned.finish_no_republication _ _ (returned.full_success_decision success full)

/-- The call-site premise excludes applying this caller policy to an empty suffix. -/
example (returned : Returned aligned selected result after)
    (empty : aligned.start.cut.offset = projection.target.payload.length) : False := by
  have nonempty := returned.nonempty
  omega

/-- A proof of memory/protocol return does not supply the caller-site premise. -/
example (_matched : MatchedReturn selected history result after) : True := by
  fail_if_success
    have _wrong : Returned aligned selected result after := ⟨_matched⟩
  trivial

/-- Return evidence cannot be substituted from another reached history. -/
example (_returned : Returned aligned selected result after)
    (_other : History realization initial call record frontier)
    (_otherAligned : Aligned relation _other) : True := by
  fail_if_success
    have _wrong : Returned _otherAligned selected result after := _returned
  trivial

/-- Selected result interpretation remains bound to this return classification. -/
example (_returned : Returned aligned selected result after) (_other : ReturnInterpretation) : True := by
  fail_if_success
    have _wrong : Returned aligned _other result after := _returned
  trivial

/-- Logical policy classification cannot be reused as a physical caller step. -/
example (_returned : Returned aligned selected result after)
    (_correspondence : CallerInterpretation) (_action : Action) (_next : CallProtocol.State Request) : True := by
  fail_if_success
    have _wrong : CallerContinuation _returned.matched _correspondence _action _next := _returned
  trivial

end Grass.Tests.Console.WriteFilePolicy
