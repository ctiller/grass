import Grass.Refinement.Console.WriteFilePolicy
import Grass.Refinement.Console.WriteFileNonresponse
import Grass.Console.ObservedEmbedding
import Grass.Console.ObservedEmbeddingSteps

/-! Connect actual aligned WriteFile witnesses to the observed console wrapper.
All views derive from the same captured root; `wholeModel_exact` supplies the
root correspondence. Reporting follows a conditional caller policy, not an
executed caller branch or committed terminal observation. No call ID, next
handoff, PC/GPR execution or physical termination witness is constructed here.
-/

namespace Grass.Refinement.Console.WriteFileHistory

open Grass.Console Grass.Semantics Grass.Std.Logical Grass.Std.Console Grass.Op
open Grass.Platform.Win32.WriteFile

variable {R Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
  {spec : SpecProcess resources}
  {projection : CapturedTargetProjection spec Status}
  {plan : LoanPlan} {realization : Realization} {initial before after : ProtocolState}
  {call : CallProtocol.CallId} {record : CallProtocol.Pending Request}
  {frontier : Prefix plan before call record}
  {history : History plan realization initial call record frontier}
  {relation : HandoffRelation (plan := plan) projection}

/-- The concrete observed view is computed from the already captured request. -/
abbrev observedModel (projection : CapturedTargetProjection spec Status) :=
  ObservedBehavior.model projection.view.request projection.target.rendering

/-- Transport a reached observed history through the proved exact root identity. -/
def rootHistory (projection : CapturedTargetProjection spec Status)
    (observed : (observedModel projection).History) : projection.wholeModel.History :=
  cast (congrArg BehaviorModel.History projection.wholeModel_exact.symm) observed

/-- This transport preserves the selected completion constructor; it is not an
independent certificate, acceptance predicate, or root denotation. -/
def rootComplete (projection : CapturedTargetProjection spec Status)
    (observed : (observedModel projection).Complete) : projection.wholeModel.Complete :=
  cast (congrArg BehaviorModel.Complete projection.wholeModel_exact.symm) observed

namespace Aligned

noncomputable def observedEmbedding (aligned : Aligned relation history) :
    ObservedEmbedding.HistoryEmbedding projection.view.request projection.target.rendering aligned.upper :=
  ObservedEmbedding.embedHistory projection.view.request projection.target.rendering aligned.upper

noncomputable def observedHistory (aligned : Aligned relation history) : (observedModel projection).History :=
  aligned.observedEmbedding.observed

noncomputable def rootObservedHistory (aligned : Aligned relation history) : projection.wholeModel.History :=
  rootHistory projection aligned.observedHistory

theorem observed_located (aligned : Aligned relation history) :
    aligned.observedHistory.state = .writing aligned.endpoint :=
  aligned.observedEmbedding.endpoint.pending_observed
    projection.view.request projection.target.rendering aligned.upper_located

/-- Every supplied component choice/event remains paired in order with the
observed trace; zero provider actions remain in the retained lower history. -/
noncomputable def observed_trace (aligned : Aligned relation history) :
    ObservedEmbedding.TraceMap projection.view.request projection.target.rendering
      aligned.upper.path.choices aligned.upper.path.events
      aligned.observedHistory.path.choices aligned.observedHistory.path.events :=
  aligned.observedEmbedding.trace

theorem observed_bytes (aligned : Aligned relation history) :
    ObservedBehavior.emittedBytes aligned.observedHistory.path.events = aligned.endpoint.emitted :=
  (ObservedBehavior.history_accounting aligned.observedHistory).trans
    (congrArg ObservedBehavior.committed aligned.observed_located)

/-- Observed bytes are precisely the reached caller prefix and this actual
provider history's publication; the embedding adds no bytes of its own. -/
theorem observed_output_exact (aligned : Aligned relation history) :
    ObservedBehavior.emittedBytes aligned.observedHistory.path.events =
      Behavior.emittedBytes aligned.start.upper.path.events ++ history.published := by
  have initialBytes := Accounting.history_accounting
    (payload := projection.target.payload) aligned.start.upper
  have initialCut := congrArg Accounting.committed aligned.start.located
  exact aligned.observed_bytes.trans
    ((WriteFileProjection.history_prefix_exact aligned.start.cut aligned.start.suffix history).symm.trans
      (congrArg (fun bytes => bytes ++ history.published) (initialBytes.trans initialCut).symm))

/-- A zero publication leaves the entire reached observed history unchanged. -/
theorem observed_extend_zero (aligned : Aligned relation history)
    {nextState : ProtocolState} {post : Prefix plan nextState call record}
    (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output)
    (same : post.accepted = frontier.accepted) :
    (aligned.extend action output step).observedHistory = aligned.observedHistory :=
  congrArg (fun upper : projection.componentSystem.History =>
    (ObservedEmbedding.embedHistory projection.view.request projection.target.rendering upper).observed)
    (aligned.extend_zero action output step same)

/-- The exact observed suffix corresponding to a positive provider publication. -/
noncomputable def observedPublicationPath (aligned : Aligned relation history)
    {nextState : ProtocolState} {post : Prefix plan nextState call record}
    (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output)
    (positive : frontier.accepted < post.accepted) :
    (observedModel projection).system.Path aligned.observedHistory.state aligned.observedHistory.graph
      (.writing (aligned.extend action output step).endpoint) () :=
  Grass.RelationalSystem.Path.snoc (system := (observedModel projection).system) .nil
    (.output aligned.endpoint (.advance (aligned.extend action output step).endpoint (by
      change aligned.start.cut.offset + frontier.accepted < aligned.start.cut.offset + post.accepted
      omega))) (.emitted output) (.writing (aligned.extend action output step).endpoint) ()
    ⟨aligned.observed_located, congrArg ObservedBehavior.Event.emitted
      (WriteFileProjection.publication_between aligned.start.cut aligned.start.suffix step), rfl⟩

/-- Positive publication appends to the exact previously reached observed history. -/
theorem observed_extend_positive (aligned : Aligned relation history)
    {nextState : ProtocolState} {post : Prefix plan nextState call record}
    (action : Action) (output : Vec Byte)
    (step : CommittedStep realization frontier post action output)
    (positive : frontier.accepted < post.accepted) :
    (aligned.extend action output step).observedHistory =
      aligned.observedHistory.append (aligned.observedPublicationPath action output step positive) := by
  have source := congrArg (fun upper : projection.componentSystem.History =>
    (ObservedEmbedding.embedHistory projection.view.request projection.target.rendering upper).observed)
    (aligned.extend_positive action output step positive)
  apply source.trans
  have outputEq := WriteFileProjection.publication_between aligned.start.cut aligned.start.suffix step
  subst output
  exact ObservedEmbedding.embedHistory_advance projection.view.request projection.target.rendering
    aligned.upper aligned.endpoint (aligned.extend action _ step).endpoint
    (by change aligned.start.cut.offset + frontier.accepted < aligned.start.cut.offset + post.accepted; omega)
    aligned.upper_located

end Aligned

namespace Stalled

variable {aligned : Aligned relation history} {predicate : StalledPredicate}

noncomputable def observedWait (stalled : Stalled predicate aligned) :
    Grass.RelationalSystem.PermanentWait (observedModel projection).boundary aligned.observedHistory :=
  ObservedEmbedding.embedPermanentWait projection.view.request projection.target.rendering stalled.waiting

theorem observed_same_cut (stalled : Stalled predicate aligned) :
    stalled.observedWait.occurrence = .output aligned.endpoint := rfl

/-- Conditional output nonresponse at the exact reached embedded history. -/
noncomputable def observedComplete (stalled : Stalled predicate aligned) :
    (observedModel projection).Complete := .waiting aligned.observedHistory stalled.observedWait

noncomputable def rootObservedComplete (stalled : Stalled predicate aligned) : projection.wholeModel.Complete :=
  rootComplete projection stalled.observedComplete

end Stalled

namespace FixedNonresponse

variable {aligned : Aligned relation history}

theorem observed_at (response : FixedNonresponse aligned) (n : Nat) :
    (response.alignedAt n).observedHistory = aligned.observedHistory :=
  congrArg (fun upper : projection.componentSystem.History =>
    (ObservedEmbedding.embedHistory projection.view.request projection.target.rendering upper).observed)
    (response.upper_at n)

noncomputable def observedWait (response : FixedNonresponse aligned) :
    Grass.RelationalSystem.PermanentWait (observedModel projection).boundary aligned.observedHistory :=
  ObservedEmbedding.embedPermanentWait projection.view.request projection.target.rendering response.waiting

theorem observed_same_cut (response : FixedNonresponse aligned) :
    response.observedWait.occurrence = .output aligned.endpoint := rfl

noncomputable def observedComplete (response : FixedNonresponse aligned) :
    (observedModel projection).Complete := .waiting aligned.observedHistory response.observedWait

noncomputable def rootObservedComplete (response : FixedNonresponse aligned) : projection.wholeModel.Complete :=
  rootComplete projection response.observedComplete

end FixedNonresponse

namespace Returned

variable {aligned : Aligned relation history} {selected : ReturnInterpretation} {result : ReturnResult}

def reportingSelection (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    ObservedBehavior.Selection projection.view.request projection.target.rendering :=
  ⟨aligned.endpoint, cause outcome, returned.finish_allowed outcome next done⟩

/-- Embed the actual supplied component finish; do not replace its prefix with
a same-cut canonical history or commit a terminal observation. -/
noncomputable def reportingEmbedding (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    ObservedEmbedding.HistoryEmbedding projection.view.request projection.target.rendering
      (returned.logicalFinish outcome next done) :=
  ObservedEmbedding.embedHistory projection.view.request projection.target.rendering
    (returned.logicalFinish outcome next done)

noncomputable def reportingHistory (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) : (observedModel projection).History :=
  (returned.reportingEmbedding outcome next done).observed

noncomputable def rootReportingHistory (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) : projection.wholeModel.History :=
  rootHistory projection (returned.reportingHistory outcome next done)

theorem reporting_located (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    (returned.reportingHistory outcome next done).state =
      .reporting (returned.reportingSelection outcome next done) :=
  ((returned.reportingEmbedding outcome next done).endpoint.finished_observed
    projection.view.request projection.target.rendering rfl).equation

/-- One reporting step from the same reached observed prefix; there is no
observation reply or new output in this suffix. -/
noncomputable def reportingPath (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    (observedModel projection).system.Path aligned.observedHistory.state aligned.observedHistory.graph
      (.reporting (returned.reportingSelection outcome next done)) () :=
  Grass.RelationalSystem.Path.snoc (system := (observedModel projection).system) .nil
    (.output aligned.endpoint (.finish (cause outcome)))
    (.reported (returned.reportingSelection outcome next done))
    (.reporting (returned.reportingSelection outcome next done)) ()
    ⟨returned.finish_allowed outcome next done, aligned.observed_located, rfl, rfl⟩

/-- Conditional finish appends exactly one report to the retained observed history. -/
theorem reporting_append (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    returned.reportingHistory outcome next done =
      aligned.observedHistory.append (returned.reportingPath outcome next done) :=
  ObservedEmbedding.embedHistory_finish projection.view.request projection.target.rendering
    aligned.upper aligned.endpoint (cause outcome) (returned.finish_allowed outcome next done)
    aligned.upper_located

theorem reporting_not_terminal (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    ¬ (observedModel projection).system.Terminal
      (returned.reportingHistory outcome next done).state () :=
  ObservedEmbedding.embedded_terminal_not_terminal projection.view.request projection.target.rendering
    ⟨aligned.endpoint, cause outcome, rfl, returned.finish_allowed outcome next done⟩

theorem reporting_no_republication (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    ObservedBehavior.emittedBytes (returned.reportingHistory outcome next done).path.events =
      ObservedBehavior.emittedBytes aligned.observedHistory.path.events :=
  ((ObservedBehavior.history_accounting (returned.reportingHistory outcome next done)).trans
    (congrArg ObservedBehavior.committed (returned.reporting_located outcome next done))).trans
    aligned.observed_bytes.symm

theorem reporting_outcome (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    (returned.reportingSelection outcome next done).publicOutcome =
      projection.view.request.outcome (cause outcome) := rfl

theorem reporting_status (returned : Returned aligned selected result after)
    (outcome : WriteOutcome) (next : WriteCursor projection.target.payload)
    (done : returned.decision = .done outcome next) :
    returned.projectedStatus outcome next done = projection.target.encodeOutcome
      (returned.reportingSelection outcome next done).publicOutcome := rfl

/-- Retry readiness keeps this exact observed history. A fresh physical call
requires separate caller and handoff evidence absent from this definition. -/
noncomputable def retryObservedHistory (_returned : Returned aligned selected result after)
    (_next : WriteCursor projection.target.payload) (_retry : _returned.decision = .retry _next) :
    (observedModel projection).History := aligned.observedHistory

theorem retry_observed_exact (returned : Returned aligned selected result after)
    (next : WriteCursor projection.target.payload) (retry : returned.decision = .retry next) :
    returned.retryObservedHistory next retry = aligned.observedHistory ∧
      next.committed = aligned.endpoint.offset ∧ next.remaining = aligned.endpoint.remaining :=
  ⟨rfl, (returned.retry_ready next retry).1, (returned.retry_ready next retry).2.1⟩

end Returned
end Grass.Refinement.Console.WriteFileHistory
