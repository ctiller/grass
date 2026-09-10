import Grass.Semantics.BehaviorModel

/-! Classification regression, not a new deadlock semantics. An initialized
nonterminal system with no step and no external occurrence has no current
`CompleteHistory`. Requiring completion availability would exclude this model;
that exclusion is not a consequence of a transition-safety theorem. -/

namespace Grass.Tests.Refinement.UnclassifiedDeadlock
open RelationalSystem

def system : RelationalSystem Unit where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial _ _ := True
  Step _ _ _ _ _ _ := False
  Terminal _ _ := False
  InfiniteConsistent _ _ _ _ _ := True
  Extends := Eq
  extendsRefl _ := rfl
  extendsTrans := Eq.trans
  stepExtends step := False.elim step

def protocol : WaitProtocol Empty where
  Response request := nomatch request
  Allowed request := nomatch request
  AllowsPermanentWait request := nomatch request

def boundary : system.WaitBoundary protocol where
  Occurrence := Empty
  request occurrence := nomatch occurrence
  Pending _ occurrence := nomatch occurrence
  Reply occurrence := nomatch occurrence
  reply_unique occurrence := nomatch occurrence
  nonterminal _ occurrence := nomatch occurrence
  step_reply _ occurrence := nomatch occurrence
  reply_step _ occurrence := nomatch occurrence

def model : BehaviorModel Unit where
  Event := Unit
  Observation := Unit
  observationProjection := .identity _
  Request := Empty
  system := system
  protocol := protocol
  boundary := boundary
  result _ _ := none
  terminal_result _ _ := by simp [system]
  terminal_no_step terminal := False.elim terminal

def initial : model.History := History.initial (state := ()) (graph := ()) trivial

theorem initialized : initial.path.length = 0 := rfl

theorem no_step (history : model.History) (choice event next nextGraph : Unit) :
    ¬ model.system.Step history.graph history.state choice event next nextGraph := id

theorem no_current_completion : ¬ Nonempty model.Complete := by
  rintro ⟨complete⟩
  cases complete with
  | terminal history done => exact done
  | infinite history run => exact run.step 0
  | waiting history waiting => exact nomatch waiting.occurrence

end Grass.Tests.Refinement.UnclassifiedDeadlock
