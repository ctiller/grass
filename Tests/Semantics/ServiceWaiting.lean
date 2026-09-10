import Grass.Semantics.Environment

namespace Grass.Tests.Semantics.ServiceWaiting

open Grass RelationalSystem BehaviorModel

private inductive Phase where | awaiting | serviced | completed
  deriving DecidableEq

private inductive Choice where | service | reply
  deriving DecidableEq

private def Step (before : Phase) (choice : Choice) (event : Bool) (after : Phase) : Prop :=
  (before = .awaiting ∧ choice = .service ∧ event = false ∧ after = .serviced) ∨
  (before = .serviced ∧ choice = .service ∧ event = false ∧ after = .serviced) ∨
  (before = .serviced ∧ choice = .reply ∧ event = true ∧ after = .completed)

private abbrev system : RelationalSystem Bool where
  State := Phase
  Choice := Choice
  Graph := Unit
  Initial := fun state _ => state = .awaiting
  Step := fun _ before choice event after _ => Step before choice event after
  Terminal := fun state _ => state = .completed
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

private abbrev protocol : WaitProtocol Unit where
  Response := fun _ => Unit
  Allowed := fun _ _ => True
  AllowsPermanentWait := fun _ => False

private abbrev boundary : system.WaitBoundary protocol where
  Occurrence := Unit
  request := id
  Pending := fun history _ => history.state = .awaiting ∨ history.state = .serviced
  External := fun _ choice => choice = .service ∨ choice = .reply
  Reply := fun _ _ choice => choice = .reply
  reply_unique := by intros; rfl
  nonterminal := by
    intro history occurrence pending terminal
    rcases pending with pending | pending <;> simp_all
  step_external := by
    intro history occurrence pending choice event next nextGraph step
    rcases step with step | step | step <;> simp_all
  step_pending_or_reply := by
    intro history occurrence pending choice event next nextGraph step
    rcases step with step | step | step
    · left
      change next = .awaiting ∨ next = .serviced
      exact Or.inr step.2.2.2
    · left
      change next = .awaiting ∨ next = .serviced
      exact Or.inr step.2.2.2
    · right; simp_all
  reply_allowed := by intros; trivial
  reply_ends := by
    intro history occurrence pending response choice event next nextGraph step reply later
    rcases step with step | step | step <;> simp [History.append] at later <;> simp_all
private abbrev model : BehaviorModel Unit where
  Event := Bool
  Observation := Bool
  observationProjection := .identity _
  Request := Unit
  system := system
  protocol := protocol
  boundary := boundary
  result := fun state _ => if state = .completed then some () else none
  terminal_result := by intro state graph; simp [system]
  terminal_no_step := by
    intro state graph terminal choice event next nextGraph step
    rcases step with step | step | step <;> simp_all

private abbrev initial : model.History :=
  .initial (state := .awaiting) (graph := ()) rfl

private theorem firstService : model.system.Step () .awaiting .service false .serviced () :=
  by simp [Step]

private abbrev servicePath : model.system.Path .awaiting () .serviced () :=
  (Path.nil : model.system.Path .awaiting () .awaiting ()).snoc
    Choice.service false Phase.serviced () firstService

private abbrev serviced : model.History := initial.append servicePath

/-- The first actual service action uses external agency but is not a reply. -/
example : model.boundary.External () .service ∧ ¬ model.boundary.Reply () () .service := by
  constructor
  · exact Or.inl rfl
  · intro reply
    cases reply

/-- The allowed reply from phase zero retains the required service prefix and
the final reply event. -/
example : ∃ extension : model.system.Path .awaiting () .completed (),
    extension.choices = [.service, .reply] ∧ extension.events = [false, true] ∧
      extension.length = 2 := by
  let path : model.system.Path .awaiting () .completed () := servicePath.snoc
    Choice.reply true Phase.completed () (by simp [Step])
  exact ⟨path, rfl, rfl, by simp [path, Path.length]⟩

private def quietForever : model.system.InfiniteContinuation serviced.state serviced.graph
    serviced.path.events where
  stateAt := fun _ => .serviced
  graphAt := fun _ => ()
  choiceAt := fun _ => .service
  eventAt := fun _ => false
  stateZero := rfl
  graphZero := rfl
  step := fun _ => by simp [Step]
  consistent := trivial

private def generatedQuiet :
    EnvironmentStrategy.Generated model (EnvironmentStrategy.responding model) serviced :=
  model.infiniteGenerated _ serviced quietForever

/-- Infinite quiet service remains an actual generated run but contains no
completed reply, so activity alone does not establish responsiveness. -/
example : ¬ model.Settles () (Or.inr rfl) generatedQuiet.1 := by
  rintro ⟨index, response, allowed, reply⟩
  cases reply

example : ¬ model.EnvironmentResponsive (EnvironmentStrategy.responding model) := by
  intro responsive
  exact (show ¬ model.Settles () (Or.inr rfl) generatedQuiet.1 from by
    rintro ⟨index, response, allowed, reply⟩
    cases reply) (responsive serviced () (Or.inr rfl) generatedQuiet)

end Grass.Tests.Semantics.ServiceWaiting

