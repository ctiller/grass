import Grass.Refinement.Console.WriteFileNonresponse

/-! These are evidence consumers, not invented physical Windows executions.
They pressure-test composition at arbitrary reached prefixes and reject erased
context, caller history, or nonresponse distinctions at elaboration time. -/

namespace Grass.Tests.Console.WriteFileHistory

open Grass.Console Grass.Semantics Grass.Std.Logical Grass.Op
open Grass.Platform.Win32.WriteFile
open Grass.Refinement.Console.WriteFileHistory

variable {R Outcome Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
  {spec : CapturedSpecification resources Outcome}
  {projection : CapturedTargetProjection spec Status}
  {realization : Realization} {initial state : CallProtocol.State Request}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
  {frontier : Prefix state call record}
  {history : History realization initial call record frontier}
  {relation : HandoffRelation projection}

/-- A silent action followed by output retains the original prefix and order. -/
example (aligned : Aligned relation history)
    {middle last : CallProtocol.State Request}
    {mid : Prefix middle call record} {post : Prefix last call record}
    (first second : Action) (silent bytes : Vec Byte)
    (zero : CommittedStep realization frontier mid first silent)
    (positive : CommittedStep realization mid post second bytes)
    (same : mid.accepted = frontier.accepted) (more : mid.accepted < post.accepted) :
    ((aligned.extend first silent zero).extend second bytes positive).upper.path.events =
      aligned.upper.path.events ++ [.emitted bytes] :=
  ((aligned.extend first silent zero).extend_positive_events second bytes positive more).trans
    (congrArg (fun upper : projection.system.History => upper.path.events ++ [.emitted bytes])
      (aligned.extend_zero first silent zero same))

/-- Full output plus an external stalled observation maps to the full-cut wait. -/
example (aligned : Aligned relation history) {predicate : StalledPredicate}
    (stalled : Stalled predicate aligned)
    (full : frontier.accepted = record.request.bytes.length) :
    stalled.waiting.occurrence = OutputCut.full projection.target.payload :=
  stalled.same_cut.trans (aligned.endpoint_full full)

/-- The stalled carrier imposes no infinite-continuation premise. -/
example (aligned : Aligned relation history) (predicate : StalledPredicate)
    (observed : predicate realization call record state frontier.accepted) :
    Stalled predicate aligned := ⟨⟨observed⟩⟩

example (aligned : Aligned relation history)
    (stalled : Stalled (fun _ _ _ _ _ => False) aligned) : False := stalled.evidence.observed

/-- A retained fixed stream has actual rooted finite endpoints at the same cut. -/
example (aligned : Aligned relation history) (response : FixedNonresponse aligned) (n : Nat) :
    aligned.start.cut.emitted ++ (response.historyAt n).published = aligned.endpoint.emitted :=
  (Grass.Refinement.Console.WriteFileProjection.history_prefix_exact
    aligned.start.cut aligned.start.suffix (response.historyAt n)).trans
    (congrArg OutputCut.emitted (response.cut_at n))

/-- Equal cut counts never authorize replacing the reached upper history. -/
example (aligned : Aligned relation history) (response : FixedNonresponse aligned) (n : Nat) :
    (response.alignedAt n).upper.path.choices = aligned.upper.path.choices :=
  congrArg (fun upper : projection.system.History => upper.path.choices) (response.upper_at n)

/-- Distinct provider contexts are explicit arguments of the selected relation. -/
example (_aligned : Aligned relation history) (_otherRealization : Realization)
    (_otherInitial : CallProtocol.State Request)
    (_otherHistory : History _otherRealization _otherInitial call record frontier) : True := by
  fail_if_success
    have _wrong : Aligned relation _otherHistory := _aligned
  trivial

/-- Changing the selected handoff relation needs a new alignment proof. -/
example (_aligned : Aligned relation history) (_other : HandoffRelation projection) : True := by
  fail_if_success
    have _wrong : Aligned _other history := _aligned
  trivial

/-- Another reached caller history cannot reuse the original root witness. -/
example (_aligned : Aligned relation history) (_other : Start projection record)
    (_sameCut : _other.cut = _aligned.start.cut) : True := by
  fail_if_success
    have _wrong : Aligned relation history := ⟨_other, _aligned.aligned⟩
  trivial

/-- A stall does not fabricate an actual infinite provider step stream. -/
example (_aligned : Aligned relation history) {predicate : StalledPredicate}
    (_stalled : Stalled predicate _aligned) : True := by
  fail_if_success
    have _wrong : FixedNonresponse _aligned := _stalled
  trivial

/-- Pure pending custody does not discharge the selected external stall law. -/
example (_aligned : Aligned relation history) (_predicate : StalledPredicate) : True := by
  fail_if_success
    have _wrong : Stalled _predicate _aligned := ⟨⟨frontier.pending⟩⟩
  trivial

end Grass.Tests.Console.WriteFileHistory
