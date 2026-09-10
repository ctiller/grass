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
structure DirectedWaitTranslation {LowerOutcome UpperOutcome : Type}
    (lower : BehaviorModel LowerOutcome) (upper : BehaviorModel UpperOutcome) where
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
variable {LowerOutcome UpperOutcome : Type}
  {lower : BehaviorModel LowerOutcome} {upper : BehaviorModel UpperOutcome}

abbrev Finite (observe : lower.Observation → upper.Observation) :=
  HistorySimulation lower.system upper.system
    (fun history => (lower.observe history).map observe) upper.observe

/-- Every actual service-and-reply extension has a matching upper extension of the
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

/-- `ExternalNonresponse` retains an actual infinite lower execution. After
its explicit finite cut, the same permitted external occurrence stays pending,
every actual choice requires external agency, no choice is its completed reply,
and every reached suffix history matches the same upper waiting history.
It does not identify the infinite run with a stationary lower wait. -/
structure ExternalNonresponse {observe : lower.Observation → upper.Observation}
    (finite : Finite observe) (waits : DirectedWaitTranslation lower upper)
    (left : lower.History) (right : upper.History)
    (run : lower.system.InfiniteContinuation left.state left.graph left.path.events)
    (rightWait : PermanentWait upper.boundary right) where
  cut : Nat
  leftWait : PermanentWait lower.boundary (left.append (run.prefixPath cut))
  matched : WaitMatch finite waits (left.append (run.prefixPath cut)) right leftWait rightWait
  pending : ∀ index, lower.boundary.Pending
    (left.append (run.prefixPath (cut + index))) leftWait.occurrence
  external : ∀ index, lower.boundary.External leftWait.occurrence (run.choiceAt (cut + index))
  unanswered : ∀ index response,
    ¬ lower.boundary.Reply leftWait.occurrence response (run.choiceAt (cut + index))
  related : ∀ index, finite.Rel (left.append (run.prefixPath (cut + index))) right

namespace ExternalNonresponse

/-- `observations` exposes equality at every actual suffix cut from the same
finite simulation law; silent labels alone cannot hide a later publication. -/
theorem observations {observe : lower.Observation → upper.Observation}
    {finite : Finite observe} {waits : DirectedWaitTranslation lower upper}
    {left : lower.History} {right : upper.History}
    {run : lower.system.InfiniteContinuation left.state left.graph left.path.events}
    {rightWait : PermanentWait upper.boundary right}
    (evidence : ExternalNonresponse finite waits left right run rightWait) (index : Nat) :
    (lower.observe (left.append (run.prefixPath (evidence.cut + index)))).map observe =
      upper.observe right := finite.observations (evidence.related index)

end ExternalNonresponse

/-- Directed matching reuses strict complete matching and adds only the
proved external-nonresponse case. Exact correspondence keeps its original
strict matching relation. Program-owned infinite work has no new matching case. -/
inductive CompleteMatchWith (outcomes : Option LowerOutcome → Option UpperOutcome → Prop)
    {observe : lower.Observation → upper.Observation}
    (finite : Finite observe) (waits : DirectedWaitTranslation lower upper) :
    lower.Complete → upper.Complete → Prop where
  | strict {left right}
      (matched : BehaviorMatching.CompleteMatchWith outcomes finite.Rel (WaitMatch finite waits) left right) :
      CompleteMatchWith outcomes finite waits left right
  | externalNonresponse (left : lower.History) (right : upper.History)
      (run : lower.system.InfiniteContinuation left.state left.graph left.path.events)
      (rightWait : PermanentWait upper.boundary right)
      (evidence : ExternalNonresponse finite waits left right run rightWait) :
      CompleteMatchWith outcomes finite waits (.infinite left run) (.waiting right rightWait)

abbrev CompleteMatch {Outcome : Type} {lower upper : BehaviorModel Outcome} :=
  @CompleteMatchWith Outcome Outcome lower upper Eq

namespace CompleteMatch
export CompleteMatchWith (strict externalNonresponse)
end CompleteMatch
end ImplementationConformance

/-- Directed complete conformance extends the same actual initialized histories.
Terminal, infinite, and waiting executions use the shared distinct constructors. -/
structure ImplementationConformanceWith {LowerOutcome UpperOutcome : Type}
    (lower : BehaviorModel LowerOutcome) (upper : BehaviorModel UpperOutcome)
    (observe : lower.Observation → upper.Observation)
    (waits : DirectedWaitTranslation lower upper)
    (outcomes : Option LowerOutcome → Option UpperOutcome → Prop) where
  finite : ImplementationConformance.Finite observe
  completeForth : ∀ {left right}, finite.Rel left right → ∀ complete,
    BehaviorModel.Complete.StartsAfter left complete →
    ∃ other, BehaviorModel.Complete.StartsAfter right other ∧
      ImplementationConformance.CompleteMatchWith outcomes finite waits complete other

/-- Same-outcome conformance is the equality specialization of the shared
directed matcher, not a separate execution or proof path. -/
abbrev ImplementationConformance {Outcome : Type} (lower upper : BehaviorModel Outcome)
    (observe : lower.Observation → upper.Observation)
    (waits : DirectedWaitTranslation lower upper) :=
  ImplementationConformanceWith lower upper observe waits Eq

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
    apply ImplementationConformance.CompleteMatch.strict
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
