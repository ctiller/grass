import Grass.Refinement.HistorySimulation
import Grass.Refinement.BehaviorCorrespondence

/-! An implementation conforms for every actual history, response and complete
execution. Permitted abstract alternatives need not all be implemented. Exact
correspondence remains separate; explicit authored capabilities and progress do
not follow merely from directed conformance. -/

namespace Grass
open RelationalSystem

/-- Interpret each actual request and dependent response. Permitted lower waits
must be permitted above; no abstract response-existence promise is introduced. -/
structure DirectedWaitTranslation {Outcome : Type} (lower : BehaviorModel Outcome) (upper : BehaviorModel Outcome) where
  request : lower.Request → upper.Request
  response : (r : lower.Request) → lower.protocol.Response r →
    upper.protocol.Response (request r)
  allowed : ∀ r answer, lower.protocol.Allowed r answer →
    upper.protocol.Allowed (request r) (response r answer)
  permanent : ∀ r, lower.protocol.AllowsPermanentWait r →
    upper.protocol.AllowsPermanentWait (request r)

namespace DirectedWaitTranslation

def ofExact {Outcome : Type} {lower : BehaviorModel Outcome} {upper : BehaviorModel Outcome}
    (exact : WaitTranslation lower upper) : DirectedWaitTranslation lower upper where
  request := exact.request
  response := exact.response
  allowed := exact.allowed
  permanent r := (exact.permanent r).mp

end DirectedWaitTranslation

namespace ImplementationConformance
variable {Outcome : Type} {lower : BehaviorModel Outcome} {upper : BehaviorModel Outcome}

abbrev Finite (observe : lower.Observation → upper.Observation) :=
  HistorySimulation lower.system upper.system
    (fun history => (lower.observe history).map observe) upper.observe

/-- Every actual reply-headed extension has a matching upper extension of the
same related frontier, including its dependent reply interpretation. -/
structure WaitMatch {observe : lower.Observation → upper.Observation}
    (finite : Finite observe) (waits : DirectedWaitTranslation lower upper)
    (left : lower.History) (right : upper.History)
    (leftWait : PermanentWait lower.boundary left)
    (rightWait : PermanentWait upper.boundary right) : Prop where
  related : finite.Rel left right
  requestExact : waits.request (lower.boundary.request leftWait.occurrence) =
    upper.boundary.request rightWait.occurrence
  replyForth : ∀ answer,
    lower.protocol.Allowed (lower.boundary.request leftWait.occurrence) answer →
    ∀ extension : BehaviorMatching.ReplyExtension lower left leftWait answer,
    ∃ other : BehaviorMatching.ReplyExtension upper right rightWait
      (requestExact ▸ waits.response _ answer),
      finite.Rel extension.history other.history

abbrev CompleteMatch {observe : lower.Observation → upper.Observation}
    (finite : Finite observe) (waits : DirectedWaitTranslation lower upper) :=
  BehaviorMatching.CompleteMatch finite.Rel (WaitMatch finite waits)

end ImplementationConformance

/-- Directed complete conformance extends the same actual initialized histories.
Terminal, infinite, and waiting executions use the shared distinct constructors. -/
structure ImplementationConformance {Outcome : Type} (lower : BehaviorModel Outcome) (upper : BehaviorModel Outcome)
    (observe : lower.Observation → upper.Observation)
    (waits : DirectedWaitTranslation lower upper) where
  finite : ImplementationConformance.Finite observe
  completeForth : ∀ {left right}, finite.Rel left right → ∀ complete,
    BehaviorModel.Complete.StartsAfter left complete →
    ∃ other, BehaviorModel.Complete.StartsAfter right other ∧
      ImplementationConformance.CompleteMatch finite waits complete other

namespace BehaviorCorrespondence
variable {Outcome : Type} {lower : BehaviorModel Outcome} {upper : BehaviorModel Outcome}
variable {observe : lower.Observation → upper.Observation} {waits : WaitTranslation lower upper}

/-- Forget only reverse coverage. The exact relation, runs, cuts, request
occurrences, and actual reply witnesses are retained. -/
def toImplementationConformance (exact : Grass.BehaviorCorrespondence lower upper observe waits) :
    ImplementationConformance lower upper observe (DirectedWaitTranslation.ofExact waits) where
  finite := HistorySimulation.ofExact exact.finite
  completeForth := by
    intro left right related complete starts
    obtain ⟨other, otherStarts, matched⟩ := exact.completeForth related complete starts
    refine ⟨other, otherStarts, ?_⟩
    cases matched with
    | terminal left right leftDone rightDone related outcomes =>
      exact .terminal left right leftDone rightDone related outcomes
    | infinite left right leftRun rightRun alignment =>
      exact .infinite left right leftRun rightRun alignment
    | waiting left right leftWait rightWait matchedWait =>
      exact .waiting left right leftWait rightWait
        ⟨matchedWait.related, matchedWait.requestExact, matchedWait.replyForth⟩

end BehaviorCorrespondence
end Grass
