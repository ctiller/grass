import Grass.Refinement.BehaviorMatching

/-! Complete correspondence keeps finite choices, divergent execution, terminal
outcomes and permitted external nonresponse distinct. Concrete target profiles
must fix the observation and protocol interpretations used here. -/

namespace Grass
open RelationalSystem

/-- A selected request interpretation preserves permitted nonresponse and
matches every allowed response in both directions. -/
structure WaitTranslation {Outcome : Type} (lower upper : BehaviorModel Outcome) where
  request : lower.Request → upper.Request
  response : (r : lower.Request) → lower.protocol.Response r →
    upper.protocol.Response (request r)
  allowed : ∀ r answer, lower.protocol.Allowed r answer →
    upper.protocol.Allowed (request r) (response r answer)
  responseCoverage : ∀ r answer, upper.protocol.Allowed (request r) answer →
    ∃ original, lower.protocol.Allowed r original ∧ response r original = answer
  permanent : ∀ r, lower.protocol.AllowsPermanentWait r ↔
    upper.protocol.AllowsPermanentWait (request r)

namespace BehaviorCorrespondence
variable {Outcome : Type} {lower upper : BehaviorModel Outcome}

abbrev Finite (observe : lower.Observation → upper.Observation) :=
  HistoryRelation lower.system upper.system
    (fun history => (lower.observe history).map observe) upper.observe

/-- Exact prefixes of both actual continuations meet at unbounded indices.
Finite stuttering is permitted; collapsing an infinite run to a finite one is not. -/
abbrev InfiniteAlignment {observe : lower.Observation → upper.Observation}
    (finite : Finite observe) (left : lower.History) (right : upper.History)
    (leftRun : lower.system.InfiniteContinuation left.state left.graph left.path.events)
    (rightRun : upper.system.InfiniteContinuation right.state right.graph right.path.events) :=
  BehaviorMatching.InfiniteAlignment finite.Rel left right leftRun rightRun

namespace InfiniteAlignment
export BehaviorMatching.InfiniteAlignment (mk)
end InfiniteAlignment

/-- An actual boundary reply followed by its retained finite continuation.
The first transition is mandatory; a reply cannot disappear into nil stutter. -/
abbrev ReplyExtension (model : BehaviorModel Outcome) (history : model.History)
    (waiting : PermanentWait model.boundary history)
    (answer : model.protocol.Response (model.boundary.request waiting.occurrence)) :=
  BehaviorMatching.ReplyExtension model history waiting answer

namespace ReplyExtension

export BehaviorMatching.ReplyExtension (mk)

def history {model : BehaviorModel Outcome} {before : model.History}
    {waiting : PermanentWait model.boundary before}
    {answer : model.protocol.Response (model.boundary.request waiting.occurrence)}
    (extension : ReplyExtension model before waiting answer) : model.History :=
  BehaviorMatching.ReplyExtension.history extension

theorem history_extends {model : BehaviorModel Outcome} {before : model.History}
    {waiting : PermanentWait model.boundary before}
    {answer : model.protocol.Response (model.boundary.request waiting.occurrence)}
    (extension : ReplyExtension model before waiting answer) :
    History.Extension before extension.history :=
  BehaviorMatching.ReplyExtension.history_extends extension

/-- The actual reply contributes one transition before the retained tail. -/
theorem history_length {model : BehaviorModel Outcome} {before : model.History}
    {waiting : PermanentWait model.boundary before}
    {answer : model.protocol.Response (model.boundary.request waiting.occurrence)}
    (extension : ReplyExtension model before waiting answer) :
    extension.history.path.length = before.path.length + (1 + extension.tail.length) :=
  BehaviorMatching.ReplyExtension.history_length extension

end ReplyExtension

/-- Match every actual reply-headed continuation at the two pending occurrences.
Protocol-value coverage alone does not connect answers to transitions. -/
structure WaitMatch {observe : lower.Observation → upper.Observation}
    (finite : Finite observe) (waits : WaitTranslation lower upper)
    (left : lower.History) (right : upper.History)
    (leftWait : PermanentWait lower.boundary left)
    (rightWait : PermanentWait upper.boundary right) where
  related : finite.Rel left right
  requestExact : waits.request (lower.boundary.request leftWait.occurrence) =
    upper.boundary.request rightWait.occurrence
  replyForth : ∀ answer,
    lower.protocol.Allowed (lower.boundary.request leftWait.occurrence) answer →
    ∀ extension : ReplyExtension lower left leftWait answer,
    ∃ other : ReplyExtension upper right rightWait
      (requestExact ▸ waits.response _ answer),
      finite.Rel extension.history other.history
  replyBack : ∀ answer,
    upper.protocol.Allowed (upper.boundary.request rightWait.occurrence) answer →
    ∀ extension : ReplyExtension upper right rightWait answer,
    ∃ original, lower.protocol.Allowed (lower.boundary.request leftWait.occurrence) original ∧
      (requestExact ▸ waits.response _ original) = answer ∧
      ∃ other : ReplyExtension lower left leftWait original,
        finite.Rel other.history extension.history
/-- Each constructor matches only its own completion form. Infinite alignment
retains the supplied runs; waiting uses the exact pending occurrences. -/
abbrev CompleteMatch {observe : lower.Observation → upper.Observation}
    (finite : Finite observe) (waits : WaitTranslation lower upper) :=
  BehaviorMatching.CompleteMatch finite.Rel (WaitMatch finite waits)

namespace CompleteMatch
export BehaviorMatching.CompleteMatch (terminal infinite waiting)
end CompleteMatch

end BehaviorCorrespondence

/-- Complete coverage extends the same related finite histories; no independent
prefix/tail witnesses or authored theorem demands enter this interface. -/
structure BehaviorCorrespondence {Outcome : Type} (lower upper : BehaviorModel Outcome)
    (observe : lower.Observation → upper.Observation) (waits : WaitTranslation lower upper) where
  finite : BehaviorCorrespondence.Finite observe
  completeForth : ∀ {left right}, finite.Rel left right → ∀ complete,
    BehaviorModel.Complete.StartsAfter left complete →
    ∃ other, BehaviorModel.Complete.StartsAfter right other ∧
      BehaviorCorrespondence.CompleteMatch finite waits complete other
  completeBack : ∀ {left right}, finite.Rel left right → ∀ complete,
    BehaviorModel.Complete.StartsAfter right complete →
    ∃ other, BehaviorModel.Complete.StartsAfter left other ∧
      BehaviorCorrespondence.CompleteMatch finite waits other complete

end Grass
