/-!
# Relational execution prefixes

The relation, rather than an interpreter, is authoritative.
`RelationalSystem.Steps` consumes each predecessor graph, while
`RelationalSystem.stepExtends` requires every transition to extend it; together
they prevent a prefix from assembling unrelated per-step graph witnesses.
-/

namespace Grass

universe u

/-- Open relational semantics with an explicit coherent execution graph. -/
structure RelationalSystem (Event : Type u) where
  State : Type u
  Choice : Type u
  Graph : Type u
  Initial : State -> Graph -> Prop
  Step : Graph -> State -> Choice -> Event -> State -> Graph -> Prop
  Terminal : State -> Graph -> Prop
  /-- Global limit condition for an infinite suffix, parameterized by the exact
  finite event trace which reached its frontier. The suffix graph begins at the
  cumulative frontier graph, so the condition can relate the complete finite
  history to every finite restriction of the infinite execution. -/
  InfiniteConsistent :
    List Event -> (Nat -> State) -> (Nat -> Graph) -> (Nat -> Choice) ->
      (Nat -> Event) -> Prop
  Extends : Graph -> Graph -> Prop
  extendsRefl : forall graph, Extends graph graph
  extendsTrans : forall {a b c}, Extends a b -> Extends b c -> Extends a c
  stepExtends : forall {before state choice event next after},
    Step before state choice event next after -> Extends before after

namespace RelationalSystem

/-- Zero or more coherent relational steps from a selected state and graph. -/
inductive Steps {Event : Type u} (system : RelationalSystem Event) : system.State ->
    system.Graph -> List Event -> system.State -> system.Graph -> Prop where
  | refl {state graph} : Steps system state graph [] state graph
  | step {state graph events current currentGraph choice event next nextGraph}
      (prior : Steps system state graph events current currentGraph)
      (transition : system.Step currentGraph current choice event next nextGraph) :
      Steps system state graph (events ++ [event]) next nextGraph

/-- An infinite coherent continuation from one exact frontier whose global
consistency condition retains the event trace already taken to that frontier. -/
structure InfiniteContinuation {Event : Type u} (system : RelationalSystem Event)
    (state : system.State) (graph : system.Graph) (priorEvents : List Event) where
  stateAt : Nat -> system.State
  graphAt : Nat -> system.Graph
  choiceAt : Nat -> system.Choice
  eventAt : Nat -> Event
  stateZero : stateAt 0 = state
  graphZero : graphAt 0 = graph
  step : forall index, system.Step (graphAt index) (stateAt index)
    (choiceAt index) (eventAt index) (stateAt (index + 1)) (graphAt (index + 1))
  consistent : system.InfiniteConsistent priorEvents stateAt graphAt choiceAt eventAt

/-- A genuine finite-terminal or trace-aware infinite continuation from a
frontier. -/
inductive Completion {Event : Type u} (system : RelationalSystem Event)
    (state : system.State) (graph : system.Graph) (priorEvents : List Event) : Type u where
  | finite {events finalState finalGraph}
      (steps : system.Steps state graph events finalState finalGraph)
      (terminal : system.Terminal finalState finalGraph) :
      Completion system state graph priorEvents
  | infinite (execution : InfiniteContinuation system state graph priorEvents) :
      Completion system state graph priorEvents

/-- A finite execution proof retaining one monotonically extended graph. -/
inductive Runs {Event : Type u} (system : RelationalSystem Event) : system.State ->
    system.Graph -> system.State -> system.Graph -> List Event -> Prop where
  | initial {state graph} (valid : system.Initial state graph) :
      Runs system state graph state graph []
  | step {initialState initialGraph state graph events choice event nextState nextGraph}
      (prior : Runs system initialState initialGraph state graph events)
      (transition : system.Step graph state choice event nextState nextGraph) :
      Runs system initialState initialGraph nextState nextGraph (events ++ [event])

/-- A finite suffix monotonically extends its starting graph. -/
theorem Steps.graphExtends
    {Event : Type u} {system : RelationalSystem Event}
    {state finalState : system.State} {graph finalGraph : system.Graph}
    {events : List Event}
    (steps : system.Steps state graph events finalState finalGraph) :
    system.Extends graph finalGraph := by
  induction steps with
  | refl => exact system.extendsRefl _
  | step prior transition inductionHypothesis =>
      exact system.extendsTrans inductionHypothesis (system.stepExtends transition)

/-- A prefix graph monotonically extends its exact initial graph. -/
theorem Runs.graphExtends
    {Event : Type u} {system : RelationalSystem Event}
    {initialState state : system.State} {initialGraph graph : system.Graph}
    {events : List Event}
    (execution : system.Runs initialState initialGraph state graph events) :
    system.Extends initialGraph graph := by
  induction execution with
  | initial valid => exact system.extendsRefl _
  | step prior transition inductionHypothesis =>
      exact system.extendsTrans inductionHypothesis (system.stepExtends transition)

/-- A packaged finite prefix suitable for runners and prefix-safety theorems.

Every admitted finite run can be packaged, including a frontier that has no
continuation. Progress is a separate property of the behavior rather than a
precondition for observing a prefix. -/
structure ExecutionPrefix {Event : Type u} (system : RelationalSystem Event) where
  initialState : system.State
  initialGraph : system.Graph
  state : system.State
  graph : system.Graph
  events : List Event
  runs : system.Runs initialState initialGraph state graph events

/-- Every valid initial configuration supplies the empty execution prefix. -/
def ExecutionPrefix.initial {Event : Type u} {system : RelationalSystem Event}
    {state : system.State} {graph : system.Graph}
    (valid : system.Initial state graph) :
    system.ExecutionPrefix where
  initialState := state
  initialGraph := graph
  state := state
  graph := graph
  events := []
  runs := .initial valid

/-- Extend a prefix by one admitted relational step. -/
def ExecutionPrefix.step {Event : Type u} {system : RelationalSystem Event}
    (prior : system.ExecutionPrefix)
    {choice : system.Choice} {event : Event}
    {nextState : system.State} {nextGraph : system.Graph}
    (transition : system.Step prior.graph prior.state choice event nextState nextGraph) :
    system.ExecutionPrefix where
  initialState := prior.initialState
  initialGraph := prior.initialGraph
  state := nextState
  graph := nextGraph
  events := prior.events ++ [event]
  runs := .step prior.runs transition

end RelationalSystem

end Grass
