import Grass.Semantics.Environment

namespace Grass.Tests.Semantics.Environment

open RelationalSystem BehaviorModel

private def spinningSystem : RelationalSystem Unit where
  State := Nat
  Choice := Bool
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ state _ _ next _ => next = state + 1
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
  Occurrence := Nat
  request := fun _ => ()
  Pending := fun history occurrence => history.state = occurrence
  External := fun _ _ => True
  Reply := fun _ response choice => response = choice
  reply_unique := by
    intro occurrence first second choice left right
    exact left.trans right.symm
  nonterminal := by simp [spinningSystem]
  step_external := by intros; trivial
  step_pending_or_reply := by
    intro history occurrence pending choice event next nextGraph step
    right
    exact ⟨choice, trivial, rfl⟩
  reply_allowed := by intros; trivial
  reply_ends := by
    intro history occurrence pending response choice event next nextGraph step reply later
    change next = occurrence at later
    have step' : (show Nat from next) = (show Nat from history.state) + 1 := by
      simpa only [spinningSystem] using step
    have pending' : (show Nat from history.state) = occurrence := pending
    have impossible : occurrence = occurrence + 1 :=
      later.symm.trans (step'.trans (congrArg (· + 1) pending'))
    omega
  reply_path := by
    intro history occurrence pending response allowed
    exact ⟨history.state, history.graph, .nil, by intros; contradiction, pending, response, (),
      Nat.succ (show Nat from history.state), history.graph, rfl, by
        simp only [spinningSystem]⟩

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
  stateAt := fun index => Nat.add (show Nat from history.state) index
  graphAt := fun _ => ()
  choiceAt := fun _ => false
  eventAt := fun _ => ()
  stateZero := by simp [Nat.add]
  graphZero := by cases history.graph; rfl
  step := by intro index; simp [model, spinningSystem, Nat.add_assoc]
  consistent := trivial

private theorem respondingAdequate : model.RespondingContinuationAdequate := by
  constructor
  · exact ⟨History.initial (state := (0 : Nat)) (graph := ()) trivial⟩
  · intro history
    exact ⟨.infinite (forever history), trivial⟩

/-- A productive infinite response stream coexists with the fixed responsive strategy. -/
example : Nonempty model.ResponsiveStrategyWitness :=
  ⟨model.respondingWitness respondingAdequate (by
    intro history occurrence pending continuation
    exact ⟨0, continuation.choiceAt 0, trivial, rfl⟩)⟩

example (history : model.History) :
    EnvironmentStrategy.Generated model (EnvironmentStrategy.responding model) history :=
  model.infiniteGenerated _ history (forever history)

/-- Existence of an adequate responsive strategy cannot turn a retained
productive infinite execution into termination. -/
example : ¬ model.TerminatesUnderResponsive := by
  intro terminates
  let history : model.History := History.initial (state := (0 : Nat)) (graph := ()) trivial
  let generated := model.infiniteGenerated (EnvironmentStrategy.responding model)
    history (forever history)
  have terminal := terminates.2 (EnvironmentStrategy.responding model)
    (model.responding_adequate respondingAdequate)
    (model.responding_responsive (by
      intro current occurrence pending continuation
      exact ⟨0, continuation.choiceAt 0, trivial, rfl⟩)) history generated
  exact terminal

/-- Both allowed response values extend the exact history; the strategy cannot
retain one Boolean result and prune the other. -/
example (strategy : model.EnvironmentStrategy) (history : model.History)
    (response : Bool) :
    ∃ state graph, ∃ beforeReply : model.system.Path history.state history.graph state graph,
      (∀ choice ∈ beforeReply.choices, ∀ earlier,
        ¬ model.boundary.Reply history.state earlier choice) ∧
      model.boundary.Pending (history.append beforeReply) history.state ∧
      ∃ choice event next nextGraph,
        model.boundary.Reply history.state response choice ∧
        model.system.Step graph state choice event next nextGraph :=
  model.allowedResponseHistory strategy history history.state rfl response trivial

end Grass.Tests.Semantics.Environment
