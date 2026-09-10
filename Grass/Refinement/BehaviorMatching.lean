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
variable {Outcome LowerOutcome UpperOutcome : Type}
  {lower : BehaviorModel LowerOutcome} {upper : BehaviorModel UpperOutcome}

/-- Relate actual terminal results. Neither absent result can satisfy this
lifting; a target binding must select the relation on the retained values. -/
def ResultMatch (relation : LowerOutcome → UpperOutcome → Prop)
    (left : Option LowerOutcome) (right : Option UpperOutcome) : Prop :=
  ∃ actual authored, left = some actual ∧ right = some authored ∧ relation actual authored

@[simp] theorem resultMatch_some (relation : LowerOutcome → UpperOutcome → Prop)
    (actual : LowerOutcome) (authored : UpperOutcome) :
    ResultMatch relation (some actual) (some authored) ↔ relation actual authored := by
  simp [ResultMatch]

@[simp] theorem resultMatch_none_left (relation : LowerOutcome → UpperOutcome → Prop)
    (right : Option UpperOutcome) : ¬ ResultMatch relation none right := by
  simp [ResultMatch]

@[simp] theorem resultMatch_none_right (relation : LowerOutcome → UpperOutcome → Prop)
    (left : Option LowerOutcome) : ¬ ResultMatch relation left none := by
  simp [ResultMatch]

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

/-- An actual finite service path, its first reply for this occurrence, and a
retained finite continuation after that reply. -/
structure ReplyExtension (model : BehaviorModel Outcome) (history : model.History)
    (waiting : PermanentWait model.boundary history)
    (answer : model.protocol.Response (model.boundary.request waiting.occurrence)) where
  beforeState : model.system.State
  beforeGraph : model.system.Graph
  beforeReply : model.system.Path history.state history.graph beforeState beforeGraph
  noEarlierReplies : ∀ choice ∈ beforeReply.choices, ∀ earlier,
    ¬ model.boundary.Reply waiting.occurrence earlier choice
  pendingBeforeReply : model.boundary.Pending (history.append beforeReply) waiting.occurrence
  choice : model.system.Choice
  event : model.Event
  nextState : model.system.State
  nextGraph : model.system.Graph
  reply : model.boundary.Reply waiting.occurrence answer choice
  replyStep : model.system.Step beforeGraph beforeState choice event nextState nextGraph
  finalState : model.system.State
  finalGraph : model.system.Graph
  tail : model.system.Path nextState nextGraph finalState finalGraph

namespace ReplyExtension

def history {model : BehaviorModel Outcome} {before : model.History}
    {waiting : PermanentWait model.boundary before}
    {answer : model.protocol.Response (model.boundary.request waiting.occurrence)}
    (extension : ReplyExtension model before waiting answer) : model.History :=
  before.append (extension.beforeReply.append
    ((Path.snoc .nil extension.choice extension.event extension.nextState
      extension.nextGraph extension.replyStep).append extension.tail))

theorem history_extends {model : BehaviorModel Outcome} {before : model.History}
    {waiting : PermanentWait model.boundary before}
    {answer : model.protocol.Response (model.boundary.request waiting.occurrence)}
    (extension : ReplyExtension model before waiting answer) :
    History.Extension before extension.history := ⟨_, _, _, rfl⟩

theorem history_length {model : BehaviorModel Outcome} {before : model.History}
    {waiting : PermanentWait model.boundary before}
    {answer : model.protocol.Response (model.boundary.request waiting.occurrence)}
    (extension : ReplyExtension model before waiting answer) :
    extension.history.path.length = before.path.length +
      (extension.beforeReply.length + 1 + extension.tail.length) := by
  simp [history, History.append, Path.length_append, Path.length, Nat.add_assoc]

end ReplyExtension

/-- Completion-form matching parameterized by history, wait, and terminal
matching. Fixed target bindings use `ResultMatch` for actual result values;
same-outcome exact correspondence retains equality of optional results. -/
inductive CompleteMatchWith (outcomes : Option LowerOutcome → Option UpperOutcome → Prop)
    (R : lower.History → upper.History → Prop)
    (W : (left : lower.History) → (right : upper.History) →
      PermanentWait lower.boundary left → PermanentWait upper.boundary right → Prop) :
    lower.Complete → upper.Complete → Prop where
  | terminal (left : lower.History) (right : upper.History)
      (leftDone : lower.system.Terminal left.state left.graph)
      (rightDone : upper.system.Terminal right.state right.graph)
      (related : R left right)
      (results : outcomes (lower.result left.state left.graph) (upper.result right.state right.graph)) :
      CompleteMatchWith outcomes R W (.terminal left leftDone) (.terminal right rightDone)
  | infinite (left : lower.History) (right : upper.History)
      (leftRun : lower.system.InfiniteContinuation left.state left.graph left.path.events)
      (rightRun : upper.system.InfiniteContinuation right.state right.graph right.path.events)
      (alignment : InfiniteAlignment R left right leftRun rightRun) :
      CompleteMatchWith outcomes R W (.infinite left leftRun) (.infinite right rightRun)
  | waiting (left : lower.History) (right : upper.History)
      (leftWait : PermanentWait lower.boundary left)
      (rightWait : PermanentWait upper.boundary right)
      (matched : W left right leftWait rightWait) :
      CompleteMatchWith outcomes R W (.waiting left leftWait) (.waiting right rightWait)

/-- Equality specializes the shared matcher for models with the same outcome
type. Heterogeneous target bindings select their terminal relation explicitly. -/
abbrev CompleteMatch {lower upper : BehaviorModel Outcome} :=
  @CompleteMatchWith Outcome Outcome lower upper Eq

namespace CompleteMatch
export CompleteMatchWith (terminal infinite waiting)
end CompleteMatch

end BehaviorMatching
end Grass
