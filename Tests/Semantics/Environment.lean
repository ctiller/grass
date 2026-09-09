import Grass.Semantics.Environment

namespace Grass.Tests.Semantics.Environment

open RelationalSystem BehaviorModel

private def spinningSystem : RelationalSystem Unit where
  State := Unit
  Choice := Bool
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

private def protocol : WaitProtocol Unit where
  Response := fun _ => Bool
  Allowed := fun _ _ => True
  AllowsPermanentWait := fun _ => True

private def boundary : spinningSystem.WaitBoundary protocol where
  Occurrence := Unit
  request := id
  Pending := fun _ _ => True
  Reply := fun _ response choice => response = choice
  reply_unique := by
    intro occurrence first second choice left right
    exact left.trans right.symm
  nonterminal := by simp [spinningSystem]
  step_reply := by
    intro history occurrence pending choice event next nextGraph step
    exact ⟨choice, trivial, rfl⟩
  reply_step := by
    intro history occurrence pending response allowed
    exact ⟨response, (), (), (), rfl, trivial⟩

private def model : BehaviorModel Empty where
  Event := Unit
  Observation := Unit
  observationProjection := {
    project := fun events => events }
  Request := Unit
  system := spinningSystem
  protocol := protocol
  boundary := boundary
  result := fun _ _ => none
  terminal_result := by simp [spinningSystem]
  terminal_no_step := by simp [spinningSystem]

private def forever (history : model.History) :
    model.system.InfiniteContinuation history.state history.graph history.path.events where
  stateAt := fun _ => ()
  graphAt := fun _ => ()
  choiceAt := fun _ => false
  eventAt := fun _ => ()
  stateZero := by cases history.state; rfl
  graphZero := by cases history.graph; rfl
  step := fun _ => trivial
  consistent := trivial

private theorem respondingAdequate : model.RespondingContinuationAdequate := by
  constructor
  · exact ⟨History.initial (state := ()) (graph := ()) trivial⟩
  · intro history
    exact ⟨.infinite (forever history), trivial⟩

/-- A productive infinite response stream coexists with the fixed responsive strategy. -/
example : Nonempty model.ResponsiveStrategyWitness :=
  ⟨model.respondingWitness respondingAdequate⟩

example (history : model.History) :
    EnvironmentStrategy.Generated model (EnvironmentStrategy.responding model) history :=
  model.infiniteGenerated _ history (forever history)

/-- Existence of an adequate responsive strategy cannot turn a retained
productive infinite execution into termination. -/
example : ¬ model.TerminatesUnderResponsive := by
  intro terminates
  let history : model.History := History.initial (state := ()) (graph := ()) trivial
  let generated := model.infiniteGenerated (EnvironmentStrategy.responding model)
    history (forever history)
  have terminal := terminates.2 (EnvironmentStrategy.responding model)
    (model.responding_adequate respondingAdequate) model.responding_responsive history generated
  exact terminal

/-- Both allowed response values extend the exact history; the strategy cannot
retain one Boolean result and prune the other. -/
example (strategy : model.EnvironmentStrategy) (history : model.History)
    (response : Bool) :
    ∃ choice event next nextGraph,
      model.boundary.Reply () response choice ∧
      ∃ _transition : model.system.Step history.graph history.state choice event next nextGraph,
        (history.append (.snoc .nil choice event next nextGraph _transition)).state = next :=
  model.allowedResponseHistory strategy history () trivial response trivial

end Grass.Tests.Semantics.Environment
