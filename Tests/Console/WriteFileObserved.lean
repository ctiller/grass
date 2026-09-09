import Grass.Refinement.Console.WriteFileObserved

namespace Grass.Tests.Console.WriteFileObserved

open Grass.Console Grass.Semantics Grass.Std.Logical Grass.Std.Console Grass.Op
open Grass.Platform.Win32.WriteFile
open Grass.Refinement.Console.WriteFileHistory

variable {R Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
  {spec : SpecProcess resources} {projection : CapturedTargetProjection spec Status}
  {realization : Realization} {initial before after : CallProtocol.State Request}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
  {frontier : Prefix before call record}
  {history : History realization initial call record frontier}
  {relation : HandoffRelation projection} {aligned : Aligned relation history}

/-- Provider output, including a full suffix, stays a writing wait until reply. -/
example {predicate : StalledPredicate} (stalled : Stalled predicate aligned)
    (full : frontier.accepted = record.request.bytes.length) :
    stalled.observedWait.occurrence = .output (OutputCut.full projection.target.payload) :=
  stalled.observed_same_cut.trans (congrArg ObservedBehavior.Request.output (aligned.endpoint_full full))

/-- Waiting at output does not silently acquire an observation occurrence. -/
example (selection : ObservedBehavior.Selection projection.view.request projection.target.rendering) :
    ¬ (observedModel projection).boundary.Pending aligned.observedHistory (.observation selection) :=
  ObservedBehavior.no_observation_while_writing aligned.observed_located

/-- Every finite prefix of an actual fixed stream retains exact observed choices. -/
example (response : FixedNonresponse aligned) (n : Nat) :
    (response.alignedAt n).observedHistory.path.choices = aligned.observedHistory.path.choices :=
  congrArg (fun h : (observedModel projection).History => h.path.choices) (response.observed_at n)

/-- Zero provider publication preserves the complete history, not just a cut. -/
example {nextState : CallProtocol.State Request} {post : Prefix nextState call record}
    (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output)
    (same : post.accepted = frontier.accepted) :
    (aligned.extend action output step).observedHistory = aligned.observedHistory :=
  aligned.observed_extend_zero action output step same

/-- A positive publication after a zero action appends to the original full
observed history; the zero action cannot invent a prefix event. -/
example {middle final : CallProtocol.State Request}
    {mid : Prefix middle call record} {post : Prefix final call record}
    (zeroAction action : Action) (zeroOutput output : Vec Byte)
    (zeroStep : CommittedStep realization frontier mid zeroAction zeroOutput)
    (same : mid.accepted = frontier.accepted)
    (step : CommittedStep realization mid post action output)
    (positive : mid.accepted < post.accepted) :
    (((aligned.extend zeroAction zeroOutput zeroStep).extend action output step).observedHistory).path.events =
      aligned.observedHistory.path.events ++ [.emitted output] := by
  have appended := congrArg (fun h : (observedModel projection).History => h.path.events)
    ((aligned.extend zeroAction zeroOutput zeroStep).observed_extend_positive action output step positive)
  have retained := congrArg (fun h : (observedModel projection).History => h.path.events)
    (aligned.observed_extend_zero zeroAction zeroOutput zeroStep same)
  exact appended.trans (show _ = _ from congrArg (fun events => events ++ [ObservedBehavior.Event.emitted output]) retained)

/-- The conditional done branch appends a report to the exact prior trace. -/
example {selected : ReturnInterpretation} {result : ReturnResult}
    (returned : Returned aligned selected result after) (outcome : WriteOutcome)
    (next : WriteCursor projection.target.payload) (done : returned.decision = .done outcome next) :
    (returned.reportingHistory outcome next done).path.events =
      aligned.observedHistory.path.events ++ [.reported (returned.reportingSelection outcome next done)] :=
  congrArg (fun h : (observedModel projection).History => h.path.events)
    (returned.reporting_append outcome next done)

/-- Failed return after full publication reports failure without completing
observation or repeating any bytes. -/
example {selected : ReturnInterpretation} {result : ReturnResult}
    (returned : Returned aligned selected result after) (failed : result.rawBool = 0)
    (full : frontier.accepted = record.request.bytes.length) :
    (returned.reportingSelection .writeFailed _ (returned.failure_decision failed)).cut =
      OutputCut.full projection.target.payload ∧
    ¬ (observedModel projection).system.Terminal
      (returned.reportingHistory .writeFailed _ (returned.failure_decision failed)).state () :=
  ⟨aligned.endpoint_full full, returned.reporting_not_terminal _ _ (returned.failure_decision failed)⟩

/-- A retry carries the original observed prefix and exact remaining bytes. -/
example {selected : ReturnInterpretation} {result : ReturnResult}
    (returned : Returned aligned selected result after) (next : WriteCursor projection.target.payload)
    (retry : returned.decision = .retry next) :
    returned.retryObservedHistory next retry = aligned.observedHistory ∧
      next.remaining = aligned.endpoint.remaining :=
  ⟨(returned.retry_observed_exact next retry).1, (returned.retry_observed_exact next retry).2.2⟩

/-- A same-cut unrelated caller prefix cannot replace the embedding's source. -/
example (_other : Aligned relation history) (_sameCut : _other.endpoint = aligned.endpoint) : True := by
  fail_if_success
    have _wrong : ObservedEmbedding.HistoryEmbedding projection.view.request projection.target.rendering
      _other.upper := aligned.observedEmbedding
  trivial

/-- A conditional reporting history is not a physical CallerContinuation. -/
example {selected : ReturnInterpretation} {result : ReturnResult}
    (_returned : Returned aligned selected result after) (_outcome : WriteOutcome)
    (_next : WriteCursor projection.target.payload) (_done : _returned.decision = .done _outcome _next)
    (_correspondence : CallerInterpretation) (_action : Action) (_state : CallProtocol.State Request) : True := by
  fail_if_success
    have _wrong : CallerContinuation _returned.matched _correspondence _action _state :=
      _returned.reportingHistory _outcome _next _done
  trivial

end Grass.Tests.Console.WriteFileObserved

