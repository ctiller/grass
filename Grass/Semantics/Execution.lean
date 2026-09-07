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

/-- Compose two coherent finite suffixes that meet at the same state and graph. -/
theorem Steps.trans {Event : Type u} {system : RelationalSystem Event}
    {initialState middleState finalState : system.State}
    {initialGraph middleGraph finalGraph : system.Graph}
    {prefixEvents suffixEvents : List Event}
    (first : system.Steps initialState initialGraph prefixEvents middleState middleGraph)
    (suffix : system.Steps middleState middleGraph suffixEvents finalState finalGraph) :
    system.Steps initialState initialGraph (prefixEvents ++ suffixEvents)
      finalState finalGraph := by
  induction suffix with
  | refl => simpa using first
  | step prior transition inductionHypothesis =>
      simpa [List.append_assoc] using
        (Steps.step inductionHypothesis transition)

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

/-- Infinite continuations are determined by their state, graph, choice, and
event streams; all coherence fields are proof-irrelevant. -/
@[ext]
theorem InfiniteContinuation.ext {Event : Type u}
    {system : RelationalSystem Event} {state : system.State}
    {graph : system.Graph} {priorEvents : List Event}
    {left right : system.InfiniteContinuation state graph priorEvents}
    (stateAt : left.stateAt = right.stateAt)
    (graphAt : left.graphAt = right.graphAt)
    (choiceAt : left.choiceAt = right.choiceAt)
    (eventAt : left.eventAt = right.eventAt) : left = right := by
  cases left
  cases right
  cases stateAt
  cases graphAt
  cases choiceAt
  cases eventAt
  rfl

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

/--
A finite execution proof retaining one monotonically extended graph.

This remains an inductive public API so existing constructor-based `cases` and
`induction` proofs keep working. The derived `initialValid` and `steps` views
below centralize proofs shared with the suffix relation.
-/
inductive Runs {Event : Type u} (system : RelationalSystem Event) : system.State ->
    system.Graph -> system.State -> system.Graph -> List Event -> Prop where
  | initial {state graph} (valid : system.Initial state graph) :
      Runs system state graph state graph []
  | step {initialState initialGraph state graph events choice event nextState nextGraph}
      (prior : Runs system initialState initialGraph state graph events)
      (transition : system.Step graph state choice event nextState nextGraph) :
      Runs system initialState initialGraph nextState nextGraph (events ++ [event])

/-- Recover the initial-validity witness retained by a finite execution. -/
theorem Runs.initialValid {Event : Type u} {system : RelationalSystem Event}
    {initialState state : system.State} {initialGraph graph : system.Graph}
    {events : List Event}
    (execution : system.Runs initialState initialGraph state graph events) :
    system.Initial initialState initialGraph := by
  induction execution with
  | initial valid => exact valid
  | step _ _ inductionHypothesis => exact inductionHypothesis

/-- Forget initial validity and expose the coherent suffix of a finite execution. -/
theorem Runs.steps {Event : Type u} {system : RelationalSystem Event}
    {initialState state : system.State} {initialGraph graph : system.Graph}
    {events : List Event}
    (execution : system.Runs initialState initialGraph state graph events) :
    system.Steps initialState initialGraph events state graph := by
  induction execution with
  | initial _ => exact .refl
  | step _ transition inductionHypothesis => exact .step inductionHypothesis transition

/-- Rebuild a finite execution from initial validity and its coherent suffix. -/
theorem Runs.ofInitialSteps {Event : Type u} {system : RelationalSystem Event}
    {initialState state : system.State} {initialGraph graph : system.Graph}
    {events : List Event}
    (valid : system.Initial initialState initialGraph)
    (steps : system.Steps initialState initialGraph events state graph) :
    system.Runs initialState initialGraph state graph events := by
  induction steps with
  | refl => exact .initial valid
  | step _ transition inductionHypothesis => exact .step inductionHypothesis transition

/-- Append a coherent suffix to a finite execution while retaining its exact
initial configuration. -/
theorem Runs.append {Event : Type u} {system : RelationalSystem Event}
    {initialState state finalState : system.State}
    {initialGraph graph finalGraph : system.Graph}
    {prefixEvents suffixEvents : List Event}
    (execution : system.Runs initialState initialGraph state graph prefixEvents)
    (suffix : system.Steps state graph suffixEvents finalState finalGraph) :
    system.Runs initialState initialGraph finalState finalGraph
      (prefixEvents ++ suffixEvents) :=
  Runs.ofInitialSteps execution.initialValid (execution.steps.trans suffix)

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

/-- Packaged prefixes are determined by their visible states, graphs, and
event trace; the retained relational derivation is proof-irrelevant. -/
@[ext]
theorem ExecutionPrefix.ext {Event : Type u} {system : RelationalSystem Event}
    {left right : system.ExecutionPrefix}
    (initialState : left.initialState = right.initialState)
    (initialGraph : left.initialGraph = right.initialGraph)
    (state : left.state = right.state)
    (graph : left.graph = right.graph)
    (events : left.events = right.events) : left = right := by
  cases left
  cases right
  cases initialState
  cases initialGraph
  cases state
  cases graph
  cases events
  rfl

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

/-- Append an already-proved coherent suffix to a packaged execution prefix. -/
def ExecutionPrefix.append {Event : Type u} {system : RelationalSystem Event}
    (prior : system.ExecutionPrefix)
    {events : List Event} {finalState : system.State} {finalGraph : system.Graph}
    (suffix : system.Steps prior.state prior.graph events finalState finalGraph) :
    system.ExecutionPrefix where
  initialState := prior.initialState
  initialGraph := prior.initialGraph
  state := finalState
  graph := finalGraph
  events := prior.events ++ events
  runs := prior.runs.append suffix

/-- Appending the empty suffix leaves a packaged prefix unchanged. -/
@[simp]
theorem ExecutionPrefix.append_refl {Event : Type u}
    {system : RelationalSystem Event} (execution : system.ExecutionPrefix) :
    execution.append (.refl) = execution := by
  apply ExecutionPrefix.ext <;> simp [ExecutionPrefix.append]

/-- Appending suffixes is associative. -/
theorem ExecutionPrefix.append_assoc {Event : Type u}
    {system : RelationalSystem Event} (execution : system.ExecutionPrefix)
    {middleEvents finalEvents : List Event}
    {middleState finalState : system.State}
    {middleGraph finalGraph : system.Graph}
    (middle : system.Steps execution.state execution.graph middleEvents
      middleState middleGraph)
    (final : system.Steps middleState middleGraph finalEvents
      finalState finalGraph) :
    (execution.append middle).append final =
      execution.append (middle.trans final) := by
  apply ExecutionPrefix.ext <;> simp [ExecutionPrefix.append, List.append_assoc]

/-- The single-step constructor is suffix append specialized to one step. -/
theorem ExecutionPrefix.step_eq_append {Event : Type u}
    {system : RelationalSystem Event} (execution : system.ExecutionPrefix)
    {choice : system.Choice} {event : Event}
    {nextState : system.State} {nextGraph : system.Graph}
    (transition : system.Step execution.graph execution.state choice event
      nextState nextGraph) :
    execution.step transition = execution.append (.step .refl transition) := by
  apply ExecutionPrefix.ext <;> simp [ExecutionPrefix.step, ExecutionPrefix.append]

end RelationalSystem

end Grass
