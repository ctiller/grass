/-!
# Relational execution prefixes

The relation, rather than an interpreter, is authoritative.  Each step consumes
the graph witness produced by its predecessor and must extend it, preventing a
prefix from assembling unrelated per-step consistency witnesses.
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
  InfiniteConsistent :
    (Nat -> State) -> (Nat -> Graph) -> (Nat -> Choice) -> (Nat -> Event) -> Prop
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

/-- An infinite coherent continuation from one exact frontier. -/
structure InfiniteContinuation {Event : Type u} (system : RelationalSystem Event)
    (state : system.State) (graph : system.Graph) where
  stateAt : Nat -> system.State
  graphAt : Nat -> system.Graph
  choiceAt : Nat -> system.Choice
  eventAt : Nat -> Event
  stateZero : stateAt 0 = state
  graphZero : graphAt 0 = graph
  step : forall index, system.Step (graphAt index) (stateAt index)
    (choiceAt index) (eventAt index) (stateAt (index + 1)) (graphAt (index + 1))
  consistent : system.InfiniteConsistent stateAt graphAt choiceAt eventAt

/-- A genuine finite-terminal or infinite continuation from a frontier. -/
inductive Completion {Event : Type u} (system : RelationalSystem Event)
    (state : system.State) (graph : system.Graph) : Type u where
  | finite {events finalState finalGraph}
      (steps : system.Steps state graph events finalState finalGraph)
      (terminal : system.Terminal finalState finalGraph) :
      Completion system state graph
  | infinite (execution : InfiniteContinuation system state graph) :
      Completion system state graph

/--
A finite execution is one valid initial configuration plus its coherent suffix.
Keeping `Steps` as the sole inductive step closure avoids a second proof source
for graph extension and refinement mapping.
-/
structure Runs {Event : Type u} (system : RelationalSystem Event)
    (initialState : system.State) (initialGraph : system.Graph)
    (state : system.State) (graph : system.Graph) (events : List Event) : Prop where
  initialValid : system.Initial initialState initialGraph
  steps : system.Steps initialState initialGraph events state graph

namespace Runs

/-- Package a valid initial configuration as the empty run. -/
theorem initial {Event : Type u} {system : RelationalSystem Event}
    {state : system.State} {graph : system.Graph}
    (valid : system.Initial state graph) : system.Runs state graph state graph [] :=
  ⟨valid, .refl⟩

/-- Extend a run by one admitted relational step. -/
theorem step {Event : Type u} {system : RelationalSystem Event}
    {initialState state : system.State} {initialGraph graph : system.Graph}
    {events : List Event} {choice : system.Choice} {event : Event}
    {nextState : system.State} {nextGraph : system.Graph}
    (prior : system.Runs initialState initialGraph state graph events)
    (transition : system.Step graph state choice event nextState nextGraph) :
    system.Runs initialState initialGraph nextState nextGraph (events ++ [event]) :=
  ⟨prior.initialValid, .step prior.steps transition⟩

end Runs

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
    system.Extends initialGraph graph :=
  execution.steps.graphExtends

/-- A packaged finite prefix suitable for runners and prefix-safety theorems. -/
structure ExecutionPrefix {Event : Type u} (system : RelationalSystem Event) where
  initialState : system.State
  initialGraph : system.Graph
  state : system.State
  graph : system.Graph
  events : List Event
  runs : system.Runs initialState initialGraph state graph events
  completion : system.Completion state graph

/-- Every valid initial configuration supplies the empty execution prefix. -/
def ExecutionPrefix.initial {Event : Type u} {system : RelationalSystem Event}
    {state : system.State} {graph : system.Graph}
    (valid : system.Initial state graph)
    (completion : system.Completion state graph) :
    system.ExecutionPrefix where
  initialState := state
  initialGraph := graph
  state := state
  graph := graph
  events := []
  runs := .initial valid
  completion := completion

/-- Extend a prefix by one admitted relational step. -/
def ExecutionPrefix.step {Event : Type u} {system : RelationalSystem Event}
    (prior : system.ExecutionPrefix)
    {choice : system.Choice} {event : Event}
    {nextState : system.State} {nextGraph : system.Graph}
    (transition : system.Step prior.graph prior.state choice event nextState nextGraph)
    (completion : system.Completion nextState nextGraph) :
    system.ExecutionPrefix where
  initialState := prior.initialState
  initialGraph := prior.initialGraph
  state := nextState
  graph := nextGraph
  events := prior.events ++ [event]
  runs := .step prior.runs transition
  completion := completion

end RelationalSystem

end Grass
