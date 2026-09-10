import Grass.Semantics.BehaviorModel
import Grass.Semantics.InfiniteHistory
import Grass.Refinement.FiniteHistoryRelation

/-! Shared matching structures parameterized by the finite-history relation and
the waiting policy.  This module does not choose a direction or impose coverage. -/

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

namespace BehaviorMatching
variable {Outcome : Type} {lower : BehaviorModel Outcome} {upper : BehaviorModel Outcome}

/-- Exact prefixes of both actual continuations meet at unbounded indices. -/
structure InfiniteAlignment (R : lower.History → upper.History → Prop)
    (left : lower.History) (right : upper.History)
    (leftRun : lower.system.InfiniteContinuation left.state left.graph left.path.events)
    (rightRun : upper.system.InfiniteContinuation right.state right.graph right.path.events) where
  baseRelated : R left right
  leftIndex : Nat → Nat
  rightIndex : Nat → Nat
  leftMonotone : ∀ i j, i ≤ j → leftIndex i ≤ leftIndex j
  rightMonotone : ∀ i j, i ≤ j → rightIndex i ≤ rightIndex j
  leftUnbounded : ∀ bound, ∃ index, bound ≤ leftIndex index
  rightUnbounded : ∀ bound, ∃ index, bound ≤ rightIndex index
  related : ∀ index, R
    (left.append (leftRun.prefixPath (leftIndex index)))
    (right.append (rightRun.prefixPath (rightIndex index)))

/-- An actual boundary reply followed by its retained finite continuation. -/
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

theorem history_length {model : BehaviorModel Outcome} {before : model.History}
    {waiting : PermanentWait model.boundary before}
    {answer : model.protocol.Response (model.boundary.request waiting.occurrence)}
    (extension : ReplyExtension model before waiting answer) :
    extension.history.path.length = before.path.length + (1 + extension.tail.length) := by
  simp [history, History.append, Path.length_append, Path.length]

end ReplyExtension

/-- Completion-form matching parameterized by history and wait matching. -/
inductive CompleteMatch (R : lower.History → upper.History → Prop)
    (W : (left : lower.History) → (right : upper.History) →
      PermanentWait lower.boundary left → PermanentWait upper.boundary right → Prop) :
    lower.Complete → upper.Complete → Prop where
  | terminal (left : lower.History) (right : upper.History)
      (leftDone : lower.system.Terminal left.state left.graph)
      (rightDone : upper.system.Terminal right.state right.graph)
      (related : R left right)
      (outcomes : lower.result left.state left.graph = upper.result right.state right.graph) :
      CompleteMatch R W (.terminal left leftDone) (.terminal right rightDone)
  | infinite (left : lower.History) (right : upper.History)
      (leftRun : lower.system.InfiniteContinuation left.state left.graph left.path.events)
      (rightRun : upper.system.InfiniteContinuation right.state right.graph right.path.events)
      (alignment : InfiniteAlignment R left right leftRun rightRun) :
      CompleteMatch R W (.infinite left leftRun) (.infinite right rightRun)
  | waiting (left : lower.History) (right : upper.History)
      (leftWait : PermanentWait lower.boundary left)
      (rightWait : PermanentWait upper.boundary right)
      (matched : W left right leftWait rightWait) :
      CompleteMatch R W (.waiting left leftWait) (.waiting right rightWait)

end BehaviorMatching
end Grass
