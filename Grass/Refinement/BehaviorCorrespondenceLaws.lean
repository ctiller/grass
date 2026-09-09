import Grass.Refinement.BehaviorCorrespondence

/-! Structural laws for complete behavior correspondence. These add no
progress, fairness, or authored-program assumptions. -/

namespace Grass
open RelationalSystem

namespace WaitTranslation

/-- Identity translation retains each request, response, allowance proof, and
permanent-wait decision. -/
def refl {Outcome : Type} (model : BehaviorModel Outcome) : WaitTranslation model model where
  request request := request
  response _ answer := answer
  allowed _ _ allowed := allowed
  responseCoverage _ answer allowed := ⟨answer, allowed, rfl⟩
  permanent _ := Iff.rfl

end WaitTranslation

namespace BehaviorCorrespondence

universe u
variable {Outcome : Type} {model : BehaviorModel Outcome}

private abbrev reflexiveFinite (model : BehaviorModel Outcome) :
    Finite (lower := model) (upper := model) id where
  Rel := Eq
  initialForth history empty := ⟨history, empty, rfl⟩
  initialBack history empty := ⟨history, empty, rfl⟩
  extendForth := by
    intro left right equal next extension
    subst right
    exact ⟨next, extension, rfl⟩
  extendBack := by
    intro left right equal next extension
    subst right
    exact ⟨next, extension, rfl⟩
  observations := by
    intro left right equal
    subst right
    simp
  cutForth := by
    intro left right equal count
    subst right
    exact ⟨count, rfl⟩
  cutBack := by
    intro left right equal count
    subst right
    exact ⟨count, rfl⟩

private def reflexiveAlignment (left : model.History)
    (run : model.system.InfiniteContinuation left.state left.graph left.path.events) :
    InfiniteAlignment (reflexiveFinite model) left left run run where
  baseRelated := rfl
  leftIndex index := index
  rightIndex index := index
  leftMonotone _ _ bounded := bounded
  rightMonotone _ _ bounded := bounded
  leftUnbounded bound := ⟨bound, Nat.le_refl _⟩
  rightUnbounded bound := ⟨bound, Nat.le_refl _⟩
  related _ := rfl

private theorem reflexiveWaitMatch (left : model.History)
    (waiting : PermanentWait model.boundary left) :
    WaitMatch (reflexiveFinite model) (WaitTranslation.refl model)
      left left waiting waiting where
  related := rfl
  requestExact := rfl
  replyForth _answer _allowed extension := ⟨extension, rfl⟩
  replyBack answer allowed extension := ⟨answer, allowed, rfl, extension, rfl⟩

private theorem reflexiveCompleteMatch (complete : model.Complete) :
    CompleteMatch (reflexiveFinite model) (WaitTranslation.refl model) complete complete := by
  cases complete with
  | terminal history done => exact .terminal history history done done rfl rfl
  | infinite history run => exact .infinite history history run run (reflexiveAlignment history run)
  | waiting history wait => exact .waiting history history wait wait (reflexiveWaitMatch history wait)

/-- `BehaviorCorrespondence.refl` retains the model's actual
finite histories, reply extensions, infinite runs, and prefix indices. -/
def refl (model : BehaviorModel Outcome) :
    Grass.BehaviorCorrespondence model model id (WaitTranslation.refl model) where
  finite := reflexiveFinite model
  completeForth := by
    intro left right related complete starts
    subst right
    exact ⟨complete, starts, reflexiveCompleteMatch complete⟩
  completeBack := by
    intro left right related complete starts
    subst right
    exact ⟨complete, starts, reflexiveCompleteMatch complete⟩

variable {lower upper : BehaviorModel Outcome}
variable {observe : lower.Observation → upper.Observation}
variable {waits : WaitTranslation lower upper}
variable {finite : Finite observe}

theorem terminal_not_waiting (left : lower.History) (right : upper.History)
    (leftDone : lower.system.Terminal left.state left.graph)
    (rightWait : PermanentWait upper.boundary right) :
    ¬ CompleteMatch finite waits (.terminal left leftDone) (.waiting right rightWait) := by
  intro matched
  cases matched

theorem terminal_not_infinite (left : lower.History) (right : upper.History)
    (leftDone : lower.system.Terminal left.state left.graph)
    (rightRun : upper.system.InfiniteContinuation right.state right.graph right.path.events) :
    ¬ CompleteMatch finite waits (.terminal left leftDone) (.infinite right rightRun) := by
  intro matched
  cases matched

theorem waiting_not_terminal (left : lower.History) (right : upper.History)
    (leftWait : PermanentWait lower.boundary left)
    (rightDone : upper.system.Terminal right.state right.graph) :
    ¬ CompleteMatch finite waits (.waiting left leftWait) (.terminal right rightDone) := by
  intro matched
  cases matched

theorem infinite_not_terminal (left : lower.History) (right : upper.History)
    (leftRun : lower.system.InfiniteContinuation left.state left.graph left.path.events)
    (rightDone : upper.system.Terminal right.state right.graph) :
    ¬ CompleteMatch finite waits (.infinite left leftRun) (.terminal right rightDone) := by
  intro matched
  cases matched

end BehaviorCorrespondence
end Grass
