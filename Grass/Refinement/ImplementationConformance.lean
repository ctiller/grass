import Grass.Refinement.HistorySimulation
import Grass.Refinement.BehaviorCorrespondence

/-! An implementation conforms for every actual history, response and complete
execution. Permitted abstract alternatives need not all be implemented. Exact
correspondence remains separate; explicit authored capabilities and progress do
not follow merely from directed conformance. -/

namespace Grass
open RelationalSystem
universe uObservation

namespace ImplementationConformance
variable {LowerOutcome UpperOutcome : Type}
  {lower : BehaviorModel LowerOutcome} {upper : BehaviorModel UpperOutcome}

abbrev Finite (observe : lower.Observation → upper.Observation) :=
  HistorySimulation lower.system upper.system
    (fun history => (lower.observe history).map observe) upper.observe

variable {PublicObservation : Type uObservation}
  {observeLower : lower.History → PublicObservation}
  {observeUpper : upper.History → PublicObservation}

/-- Every actual service-and-reply extension has a matching upper extension.
An implementation can complete a preparatory request while the same upper
occurrence remains pending. Actual upper replies retain their dependent reply
interpretation; preparatory progress must prove the original occurrence pending. -/
structure WaitMatch
    (finite : HistorySimulation lower.system upper.system observeLower observeUpper)
    (left : lower.History) (right : upper.History)
    (leftWait : PermanentWait lower.boundary left)
    (rightWait : PermanentWait upper.boundary right) : Prop where
  related : finite.Rel left right
  replyForth : ∀ answer,
    lower.protocol.Allowed (lower.boundary.request leftWait.occurrence) answer →
    ∀ extension : BehaviorMatching.ReplyExtension lower left leftWait answer,
    (∃ mapped, upper.protocol.Allowed (upper.boundary.request rightWait.occurrence) mapped ∧
      ∃ other : BehaviorMatching.ReplyExtension upper right rightWait mapped,
        finite.Rel extension.history other.history) ∨
    (∃ state graph, ∃ suffix : upper.system.Path right.state right.graph state graph,
      (∀ choice ∈ suffix.choices, ∀ answer,
        ¬ upper.boundary.Reply rightWait.occurrence answer choice) ∧
      upper.boundary.Pending (right.append suffix) rightWait.occurrence ∧
      finite.Rel extension.history (right.append suffix))

/-- `ExternalNonresponse` retains an actual infinite lower execution. After
its explicit finite cut, the same permitted external occurrence stays pending,
every actual choice requires external agency, no choice is its completed reply,
and every reached suffix history matches the same upper waiting history.
It does not identify the infinite run with a stationary lower wait. -/
structure ExternalNonresponse
    (finite : HistorySimulation lower.system upper.system observeLower observeUpper)
    (left : lower.History) (right : upper.History)
    (run : lower.system.InfiniteContinuation left.state left.graph left.path.events)
    (rightWait : PermanentWait upper.boundary right) where
  cut : Nat
  leftWait : PermanentWait lower.boundary (left.append (run.prefixPath cut))
  matched : WaitMatch finite (left.append (run.prefixPath cut)) right leftWait rightWait
  pending : ∀ index, lower.boundary.Pending
    (left.append (run.prefixPath (cut + index))) leftWait.occurrence
  external : ∀ index, lower.boundary.External leftWait.occurrence (run.choiceAt (cut + index))
  unanswered : ∀ index response,
    ¬ lower.boundary.Reply leftWait.occurrence response (run.choiceAt (cut + index))
  related : ∀ index, finite.Rel (left.append (run.prefixPath (cut + index))) right

namespace ExternalNonresponse

/-- `observations` exposes equality at every actual suffix cut from the same
finite simulation law; silent labels alone cannot hide a later publication. -/
theorem observations
    {finite : HistorySimulation lower.system upper.system observeLower observeUpper}
    {left : lower.History} {right : upper.History}
    {run : lower.system.InfiniteContinuation left.state left.graph left.path.events}
    {rightWait : PermanentWait upper.boundary right}
    (evidence : ExternalNonresponse finite left right run rightWait) (index : Nat) :
    observeLower (left.append (run.prefixPath (evidence.cut + index))) =
      observeUpper right := finite.observations (evidence.related index)

end ExternalNonresponse

/-- Directed matching reuses strict complete matching and adds only the
proved external-nonresponse case. Exact correspondence keeps its original
strict matching relation. Program-owned infinite work has no new matching case. -/
inductive CompleteMatchWith (outcomes : Option LowerOutcome → Option UpperOutcome → Prop)
    (finite : HistorySimulation lower.system upper.system observeLower observeUpper) :
    lower.Complete → upper.Complete → Prop where
  | strict {left right}
      (matched : BehaviorMatching.CompleteMatchWith outcomes finite.Rel (WaitMatch finite) left right) :
      CompleteMatchWith outcomes finite left right
  | externalNonresponse (left : lower.History) (right : upper.History)
      (run : lower.system.InfiniteContinuation left.state left.graph left.path.events)
      (rightWait : PermanentWait upper.boundary right)
      (evidence : ExternalNonresponse finite left right run rightWait) :
      CompleteMatchWith outcomes finite (.infinite left run) (.waiting right rightWait)

abbrev CompleteMatch {Outcome : Type} {lower upper : BehaviorModel Outcome}
    {observe : lower.Observation → upper.Observation}
    (finite : Finite observe) :=
  CompleteMatchWith Eq finite

namespace CompleteMatch
export CompleteMatchWith (strict externalNonresponse)
end CompleteMatch
end ImplementationConformance

/-- Directed complete conformance extends the same actual initialized histories.
Terminal, infinite, and waiting executions use the shared distinct constructors. -/
structure ImplementationConformanceWith {LowerOutcome UpperOutcome : Type}
    {PublicObservation : Type uObservation}
    (lower : BehaviorModel LowerOutcome) (upper : BehaviorModel UpperOutcome)
    (observeLower : lower.History → PublicObservation)
    (observeUpper : upper.History → PublicObservation)
   
    (outcomes : Option LowerOutcome → Option UpperOutcome → Prop) where
  finite : HistorySimulation lower.system upper.system observeLower observeUpper
  completeForth : ∀ {left right}, finite.Rel left right → ∀ complete,
    BehaviorModel.Complete.StartsAfter left complete →
    ∃ other, BehaviorModel.Complete.StartsAfter right other ∧
      ImplementationConformance.CompleteMatchWith outcomes finite complete other

/-- Same-outcome conformance is the equality specialization of the shared
directed matcher, not a separate execution or proof path. -/
abbrev ImplementationConformance {Outcome : Type} (lower upper : BehaviorModel Outcome)
    (observe : lower.Observation → upper.Observation)
    :=
  ImplementationConformanceWith lower upper
    (fun history => (lower.observe history).map observe) upper.observe Eq

namespace BehaviorCorrespondence
variable {Outcome : Type} {lower : BehaviorModel Outcome} {upper : BehaviorModel Outcome}
variable {observe : lower.Observation → upper.Observation} {waits : WaitTranslation lower upper}

/-- Forget only reverse coverage. The exact relation, runs, cuts, request
occurrences, and actual reply witnesses are retained. -/
def toImplementationConformance (exact : Grass.BehaviorCorrespondence lower upper observe waits) :
    ImplementationConformance lower upper observe where
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
        ⟨matchedWait.related, by
          intro answer allowed extension
          obtain ⟨other, related⟩ := matchedWait.replyForth answer allowed extension
          apply Or.inl
          refine ⟨_, ?_, other, related⟩
          have mappedAllowed := waits.allowed _ answer allowed
          have transport {first second : upper.Request} (equal : first = second)
              (response : upper.protocol.Response first)
              (allowed : upper.protocol.Allowed first response) :
              upper.protocol.Allowed second (equal ▸ response) := by
            cases equal
            exact allowed
          exact transport matchedWait.requestExact _ mappedAllowed⟩

end BehaviorCorrespondence
end Grass
