import Grass.Semantics.BehaviorModel
import Grass.Refinement.FiniteHistoryRelation
import Grass.Semantics.InfiniteHistory

/-! Complete correspondence keeps finite choices, divergent execution, terminal
outcomes and permitted external nonresponse distinct. Concrete target profiles
must fix the observation and protocol interpretations used here. -/

namespace Grass
open RelationalSystem

namespace BehaviorModel
variable {Outcome : Type}

def observe (model : BehaviorModel Outcome) (history : model.History) :
    List model.Observation := model.observationProjection.project history.path.events

def Complete.frontier {model : BehaviorModel Outcome} : model.Complete → model.History
  | .terminal history _ => history
  | .infinite history _ => history
  | .waiting history _ => history

def Complete.StartsAfter {model : BehaviorModel Outcome}
    (history : model.History) (complete : model.Complete) : Prop :=
  History.Extension history complete.frontier

end BehaviorModel

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
structure InfiniteAlignment {observe : lower.Observation → upper.Observation}
    (finite : Finite observe) (left : lower.History) (right : upper.History)
    (leftRun : lower.system.InfiniteContinuation left.state left.graph left.path.events)
    (rightRun : upper.system.InfiniteContinuation right.state right.graph right.path.events) where
  baseRelated : finite.Rel left right
  leftIndex : Nat → Nat
  rightIndex : Nat → Nat
  leftMonotone : ∀ i j, i ≤ j → leftIndex i ≤ leftIndex j
  rightMonotone : ∀ i j, i ≤ j → rightIndex i ≤ rightIndex j
  leftUnbounded : ∀ bound, ∃ index, bound ≤ leftIndex index
  rightUnbounded : ∀ bound, ∃ index, bound ≤ rightIndex index
  related : ∀ index, finite.Rel
    (left.append (leftRun.prefixPath (leftIndex index)))
    (right.append (rightRun.prefixPath (rightIndex index)))

/-- An actual boundary reply followed by its retained finite continuation.
The first transition is mandatory; a reply cannot disappear into nil stutter. -/
structure ReplyExtension (model : BehaviorModel Outcome) (history : model.History)
    (waiting : PermanentWait model.boundary history)
    (answer : model.protocol.Response (model.boundary.request waiting.occurrence)) where
  choice : model.system.Choice
  event : model.Event
  nextState : model.system.State
  nextGraph : model.system.Graph
  reply : model.boundary.Reply waiting.occurrence answer choice
  first : model.system.Step history.graph history.state choice event nextState nextGraph
  finalState : model.system.State
  finalGraph : model.system.Graph
  tail : model.system.Path nextState nextGraph finalState finalGraph

namespace ReplyExtension

def history {model : BehaviorModel Outcome} {before : model.History}
    {waiting : PermanentWait model.boundary before}
    {answer : model.protocol.Response (model.boundary.request waiting.occurrence)}
    (extension : ReplyExtension model before waiting answer) : model.History :=
  before.append ((Path.snoc .nil extension.choice extension.event extension.nextState
    extension.nextGraph extension.first).append extension.tail)

theorem history_extends {model : BehaviorModel Outcome} {before : model.History}
    {waiting : PermanentWait model.boundary before}
    {answer : model.protocol.Response (model.boundary.request waiting.occurrence)}
    (extension : ReplyExtension model before waiting answer) :
    History.Extension before extension.history := ⟨_, _, _, rfl⟩

/-- The actual reply contributes one transition before the retained tail. -/
theorem history_length {model : BehaviorModel Outcome} {before : model.History}
    {waiting : PermanentWait model.boundary before}
    {answer : model.protocol.Response (model.boundary.request waiting.occurrence)}
    (extension : ReplyExtension model before waiting answer) :
    extension.history.path.length = before.path.length + (1 + extension.tail.length) := by
  simp [history, History.append, Path.length_append, Path.length]

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
inductive CompleteMatch {observe : lower.Observation → upper.Observation}
    (finite : Finite observe) (waits : WaitTranslation lower upper) :
    lower.Complete → upper.Complete → Prop where
  | terminal (left : lower.History) (right : upper.History)
      (leftDone : lower.system.Terminal left.state left.graph)
      (rightDone : upper.system.Terminal right.state right.graph)
      (related : finite.Rel left right)
      (outcomes : lower.result left.state left.graph = upper.result right.state right.graph) :
      CompleteMatch finite waits (.terminal left leftDone) (.terminal right rightDone)
  | infinite (left : lower.History) (right : upper.History)
      (leftRun : lower.system.InfiniteContinuation left.state left.graph left.path.events)
      (rightRun : upper.system.InfiniteContinuation right.state right.graph right.path.events)
      (alignment : InfiniteAlignment finite left right leftRun rightRun) :
      CompleteMatch finite waits (.infinite left leftRun) (.infinite right rightRun)
  | waiting (left : lower.History) (right : upper.History)
      (leftWait : PermanentWait lower.boundary left)
      (rightWait : PermanentWait upper.boundary right)
      (matched : WaitMatch finite waits left right leftWait rightWait) :
      CompleteMatch finite waits (.waiting left leftWait) (.waiting right rightWait)

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
