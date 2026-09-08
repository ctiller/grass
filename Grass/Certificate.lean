import Grass.Semantics.Execution
import Grass.Semantics.Observation
import Grass.Semantics.SpecProcess

/-!
# Stratified certificate interfaces

Executions are relational prefixes, observations come from an explicit trace
projection, and every adjacent layer supplies a prefix simulation. Domain,
process, platform, machine, and artifact libraries own the concrete witnesses.

`ArtifactFormat.loadedBehavior` is a declared model of the selected target
loader. Its correspondence to an external loader is a profile assumption that
later platform code must expose and discharge; this foundation slice proves
only the exact relationship between that model and canonical emitted bytes.
-/

namespace Grass

universe u

/-- Relational semantics and the specification-selected observation view. -/
structure ProgramBehavior (spec : SpecProcess) where
  system : RelationalSystem spec.AuditEvent
  inputOf : system.State -> spec.Input
  waitsFor : system.State -> system.Graph -> system.Choice -> Prop

namespace ProgramBehavior

variable {spec : SpecProcess}

/-- No relational step is enabled at this exact frontier. -/
def NoStep (behavior : ProgramBehavior spec)
    (state : behavior.system.State) (graph : behavior.system.Graph) : Prop :=
  forall {choice event nextState nextGraph},
    ¬ behavior.system.Step graph state choice event nextState nextGraph

/-- Structural evidence that a frontier has no enabled relational step because
it is waiting on one exact environment request. -/
structure EnvironmentPending (behavior : ProgramBehavior spec)
    (state : behavior.system.State) (graph : behavior.system.Graph) : Type u where
  request : behavior.system.Choice
  waiting : behavior.waitsFor state graph request
  noStep : behavior.NoStep state graph

/-- The specification's whole-trace view of one finite execution prefix.

For a nonterminal prefix this is a provisional recomputation, not an append-only
stream commitment. Functional acceptance consumes this view only with a
terminal witness; independent demands carry safety and other non-functional
claims that a projection may not erase. -/
def observe (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix) : List spec.Observation :=
  spec.observationProjection.project execution.events

/-- Observe a complete finite or infinite continuation from an exact packaged
prefix without fabricating a terminal value for the infinite case. -/
def observeCompletion (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix)
    (completion : behavior.system.Completion execution.state execution.graph
      execution.events) :
    CompleteObservation spec.observationProjection :=
  match completion with
  | .finite (events := events) _ _ =>
      .finite (spec.observationProjection.project (execution.events ++ events))
  | .infinite continuation =>
      .infinite (InfiniteObservation.ofEventStream spec.observationProjection
        execution.events continuation.eventAt)

/-- `ProgramBehavior.observeCompletion_finite` exposes the full finite trace
used by complete observation. -/
@[simp]
theorem observeCompletion_finite (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix)
    {events : List spec.AuditEvent}
    {finalState : behavior.system.State} {finalGraph : behavior.system.Graph}
    (steps : behavior.system.Steps execution.state execution.graph events
      finalState finalGraph)
    (terminal : behavior.system.Terminal finalState finalGraph) :
    behavior.observeCompletion execution (.finite steps terminal) =
      .finite (spec.observationProjection.project
        (execution.events ++ events)) := rfl

/-- `ProgramBehavior.observeCompletion_infinite` exposes the coherent
approximant family selected from an infinite continuation. -/
@[simp]
theorem observeCompletion_infinite (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix)
    (continuation : behavior.system.InfiniteContinuation execution.state
      execution.graph execution.events) :
    behavior.observeCompletion execution (.infinite continuation) =
      .infinite (InfiniteObservation.ofEventStream
        spec.observationProjection execution.events continuation.eventAt) := rfl

/-- Every approximant used by an infinite complete observation is exactly the
ordinary observation of the corresponding appended execution prefix. -/
theorem observe_appendInfinitePrefix (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix)
    (continuation : behavior.system.InfiniteContinuation execution.state
      execution.graph execution.events)
    (length : Nat) :
    (InfiniteObservation.ofEventStream spec.observationProjection
      execution.events continuation.eventAt).approximant length =
        behavior.observe
          (execution.appendInfinitePrefix continuation length) := by
  simp [ProgramBehavior.observe,
    RelationalSystem.ExecutionPrefix.appendInfinitePrefix_events]

/-- An exhaustive maximal continuation from one exact finite frontier.

Environment-pending carries the exact finite suffix to a waiting frontier,
then an exact request and evidence that no relational step is enabled there.
It remains distinct from both finite termination and authored infinite
execution. -/
inductive MaximalContinuation (behavior : ProgramBehavior spec)
    (state : behavior.system.State) (graph : behavior.system.Graph)
    (priorEvents : List spec.AuditEvent) : Type u where
  | finite {events : List spec.AuditEvent}
      {finalState : behavior.system.State}
      {finalGraph : behavior.system.Graph}
      (steps : behavior.system.Steps state graph events finalState finalGraph)
      (terminal : behavior.system.Terminal finalState finalGraph)
  | pending {events : List spec.AuditEvent}
      {finalState : behavior.system.State}
      {finalGraph : behavior.system.Graph}
      (steps : behavior.system.Steps state graph events finalState finalGraph)
      (waiting : behavior.EnvironmentPending finalState finalGraph)
  | infinite (execution : behavior.system.InfiniteContinuation
      state graph priorEvents)

/-- Observe one maximal continuation without collapsing its disposition. -/
def observeMaximal (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix)
    (continuation : behavior.MaximalContinuation execution.state
      execution.graph execution.events) :
    CompleteObservation spec.observationProjection :=
  match continuation with
  | .finite (events := events) _ _ =>
      .finite (spec.observationProjection.project (execution.events ++ events))
  | .pending (events := events) _ _ =>
      .pending (spec.observationProjection.project (execution.events ++ events))
  | .infinite infinite =>
      .infinite (InfiniteObservation.ofEventStream spec.observationProjection
        execution.events infinite.eventAt)

/-- The prefix begins with the selected specification input. -/
def HasInput (behavior : ProgramBehavior spec)
    (input : spec.Input) (execution : behavior.system.ExecutionPrefix) : Prop :=
  behavior.inputOf execution.initialState = input

/-- Every admitted input has an initial execution, and every permitted finite
frontier has a finite-terminal, environment-pending, or infinite maximal
continuation. -/
structure Adequate (behavior : ProgramBehavior spec) : Prop where
  execution : forall input, spec.admits input ->
    Nonempty { run : behavior.system.ExecutionPrefix //
      behavior.HasInput input run }
  completion : forall run : behavior.system.ExecutionPrefix,
    Nonempty (behavior.MaximalContinuation run.state run.graph run.events)

/-- Transport adequacy along exact behavior equality. -/
theorem Adequate.cast {behavior replacement : ProgramBehavior spec}
    (exact : behavior = replacement) (adequate : replacement.Adequate) :
    behavior.Adequate := by
  cases exact
  exact adequate

end ProgramBehavior

variable {spec : SpecProcess}
variable {lower middle upper concrete abstract : ProgramBehavior spec}

/-- Behavioral inclusion from a concrete layer into its immediate abstraction. -/
structure BehaviorRefinement (concrete abstract : ProgramBehavior spec) where
  mapState : concrete.system.State -> abstract.system.State
  mapGraph : concrete.system.Graph -> abstract.system.Graph
  mapChoice : concrete.system.Choice -> abstract.system.Choice
  input : forall state, abstract.inputOf (mapState state) = concrete.inputOf state
  initial : forall {state graph}, concrete.system.Initial state graph ->
    abstract.system.Initial (mapState state) (mapGraph graph)
  step : forall {graph state choice event nextState nextGraph},
    concrete.system.Step graph state choice event nextState nextGraph ->
    abstract.system.Step (mapGraph graph) (mapState state) (mapChoice choice) event
      (mapState nextState) (mapGraph nextGraph)
  terminal : forall {state graph}, concrete.system.Terminal state graph ->
    abstract.system.Terminal (mapState state) (mapGraph graph)
  pending : forall {state graph request},
    concrete.waitsFor state graph request ->
    concrete.NoStep state graph ->
    abstract.waitsFor (mapState state) (mapGraph graph) (mapChoice request) /\
      abstract.NoStep (mapState state) (mapGraph graph)
  infiniteConsistency : forall {priorEvents stateAt graphAt choiceAt eventAt},
    concrete.system.InfiniteConsistent priorEvents stateAt graphAt choiceAt eventAt ->
    abstract.system.InfiniteConsistent priorEvents (fun index => mapState (stateAt index))
      (fun index => mapGraph (graphAt index))
      (fun index => mapChoice (choiceAt index)) eventAt

namespace BehaviorRefinement

/-- Two refinements are equal when their state, graph, and choice maps are
equal. The remaining fields are propositions witnessing that those maps
preserve the adjacent behaviors. -/
@[ext]
theorem ext {left right : BehaviorRefinement concrete abstract}
    (state : left.mapState = right.mapState)
    (graph : left.mapGraph = right.mapGraph)
    (choice : left.mapChoice = right.mapChoice) : left = right := by
  cases left
  cases right
  cases state
  cases graph
  cases choice
  rfl

/-- Refinement is reflexive. -/
def refl (behavior : ProgramBehavior spec) : BehaviorRefinement behavior behavior where
  mapState := id
  mapGraph := id
  mapChoice := id
  input := fun _ => rfl
  initial := id
  step := id
  terminal := id
  pending waiting noStep := ⟨waiting, noStep⟩
  infiniteConsistency := id

/-- Exact adjacent refinements compose without introducing a new proof route. -/
def trans (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper) :
    BehaviorRefinement lower upper where
  mapState state := middleUpper.mapState (lowerMiddle.mapState state)
  mapGraph graph := middleUpper.mapGraph (lowerMiddle.mapGraph graph)
  mapChoice choice := middleUpper.mapChoice (lowerMiddle.mapChoice choice)
  input state := by
    rw [middleUpper.input, lowerMiddle.input]
  initial initial := middleUpper.initial (lowerMiddle.initial initial)
  step step := middleUpper.step (lowerMiddle.step step)
  terminal terminal := middleUpper.terminal (lowerMiddle.terminal terminal)
  pending waiting noStep := by
    rcases lowerMiddle.pending waiting noStep with ⟨middleWaiting, middleNoStep⟩
    exact middleUpper.pending middleWaiting middleNoStep
  infiniteConsistency consistent :=
    middleUpper.infiniteConsistency (lowerMiddle.infiniteConsistency consistent)

/-- Reflexive refinement is a left identity for composition. -/
@[simp]
theorem refl_trans (refinement : BehaviorRefinement lower upper) :
    (refl lower).trans refinement = refinement := by
  apply ext <;> rfl

/-- Reflexive refinement is a right identity for composition. -/
@[simp]
theorem trans_refl (refinement : BehaviorRefinement lower upper) :
    refinement.trans (refl upper) = refinement := by
  apply ext <;> rfl

/-- Adjacent refinement composition is associative. The orientation gives
the simplifier a right-associated normal form for certificate chains. -/
@[simp]
theorem trans_assoc {highest : ProgramBehavior spec}
    (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper)
    (upperHighest : BehaviorRefinement upper highest) :
    (lowerMiddle.trans middleUpper).trans upperHighest =
      lowerMiddle.trans (middleUpper.trans upperHighest) := by
  apply ext <;> rfl

/-- Map a coherent finite suffix through a step simulation. -/
theorem mapSteps (refinement : BehaviorRefinement concrete abstract)
    {state finalState : concrete.system.State}
    {graph finalGraph : concrete.system.Graph} {events : List spec.AuditEvent}
    (steps : concrete.system.Steps state graph events finalState finalGraph) :
    abstract.system.Steps (refinement.mapState state) (refinement.mapGraph graph)
      events (refinement.mapState finalState) (refinement.mapGraph finalGraph) := by
  induction steps with
  | refl => exact .refl
  | step prior transition inductionHypothesis =>
      exact .step inductionHypothesis (refinement.step transition)

/-- Map an infinite execution while retaining its global limit condition. -/
def mapInfinite (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : concrete.system.InfiniteContinuation state graph priorEvents) :
    abstract.system.InfiniteContinuation (refinement.mapState state)
      (refinement.mapGraph graph) priorEvents where
  stateAt index := refinement.mapState (execution.stateAt index)
  graphAt index := refinement.mapGraph (execution.graphAt index)
  choiceAt index := refinement.mapChoice (execution.choiceAt index)
  eventAt := execution.eventAt
  stateZero := congrArg refinement.mapState execution.stateZero
  graphZero := congrArg refinement.mapGraph execution.graphZero
  step index := refinement.step (execution.step index)
  consistent := refinement.infiniteConsistency execution.consistent

/-- `BehaviorRefinement.mapInfinite_prefixEvents` states that mapping an
infinite continuation preserves every finite observable event prefix exactly. -/
@[simp]
theorem mapInfinite_prefixEvents
    (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : concrete.system.InfiniteContinuation state graph priorEvents)
    (length : Nat) :
    (refinement.mapInfinite execution).prefixEvents length =
      execution.prefixEvents length := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      rw [RelationalSystem.InfiniteContinuation.prefixEvents,
        RelationalSystem.InfiniteContinuation.prefixEvents,
        inductionHypothesis]
      rfl

/-- Mapping a finite restriction of an infinite continuation yields an exact
abstract `Steps` witness at the corresponding mapped frontier. -/
theorem mapInfinite_prefixSteps
    (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : concrete.system.InfiniteContinuation state graph priorEvents)
    (length : Nat) :
    abstract.system.Steps (refinement.mapState state)
      (refinement.mapGraph graph) (execution.prefixEvents length)
      (refinement.mapState (execution.stateAt length))
      (refinement.mapGraph (execution.graphAt length)) :=
  refinement.mapSteps (execution.prefixSteps length)

/-- Reflexive refinement leaves every infinite continuation unchanged. -/
theorem mapInfinite_refl (behavior : ProgramBehavior spec)
    {state : behavior.system.State} {graph : behavior.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : behavior.system.InfiniteContinuation state graph priorEvents) :
    (refl behavior).mapInfinite execution = execution := by
  apply RelationalSystem.InfiniteContinuation.ext <;> rfl

/-- Mapping an infinite continuation through a composite refinement agrees
with mapping it through the two adjacent refinements in order. -/
theorem mapInfinite_trans (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper)
    {state : lower.system.State} {graph : lower.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : lower.system.InfiniteContinuation state graph priorEvents) :
    (lowerMiddle.trans middleUpper).mapInfinite execution =
      middleUpper.mapInfinite (lowerMiddle.mapInfinite execution) := by
  apply RelationalSystem.InfiniteContinuation.ext <;> rfl

/-- Map a terminal or infinite continuation coherently. -/
def mapCompletion (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (completion : concrete.system.Completion state graph priorEvents) :
    abstract.system.Completion (refinement.mapState state) (refinement.mapGraph graph)
      priorEvents := by
  cases completion with
  | finite steps terminal =>
      exact .finite (refinement.mapSteps steps) (refinement.terminal terminal)
  | infinite execution => exact .infinite (refinement.mapInfinite execution)

/-- Map every maximal functional disposition through one refinement. -/
def mapMaximal (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (continuation : concrete.MaximalContinuation state graph priorEvents) :
    abstract.MaximalContinuation (refinement.mapState state)
      (refinement.mapGraph graph) priorEvents := by
  cases continuation with
  | finite steps terminal =>
      exact .finite (refinement.mapSteps steps) (refinement.terminal terminal)
  | pending steps waiting =>
      let mapped := refinement.pending waiting.waiting waiting.noStep
      exact .pending (refinement.mapSteps steps) {
        request := refinement.mapChoice waiting.request
        waiting := mapped.1
        noStep := mapped.2
      }
  | infinite execution => exact .infinite (refinement.mapInfinite execution)

/-- Reflexive refinement leaves every maximal continuation unchanged. -/
theorem mapMaximal_refl (behavior : ProgramBehavior spec)
    {state : behavior.system.State} {graph : behavior.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (continuation : behavior.MaximalContinuation state graph priorEvents) :
    (refl behavior).mapMaximal continuation = continuation := by
  cases continuation with
  | finite => rfl
  | pending steps waiting =>
      cases waiting
      rfl
  | infinite execution =>
      change ProgramBehavior.MaximalContinuation.infinite
          ((refl behavior).mapInfinite execution) =
        ProgramBehavior.MaximalContinuation.infinite execution
      rw [mapInfinite_refl]
      rfl

/-- Mapping a maximal continuation through a composite refinement agrees with
mapping it through the adjacent refinements in order. -/
theorem mapMaximal_trans (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper)
    {state : lower.system.State} {graph : lower.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (continuation : lower.MaximalContinuation state graph priorEvents) :
    (lowerMiddle.trans middleUpper).mapMaximal continuation =
      middleUpper.mapMaximal (lowerMiddle.mapMaximal continuation) := by
  cases continuation with
  | finite => rfl
  | pending steps waiting =>
      cases waiting
      rfl
  | infinite execution =>
      change ProgramBehavior.MaximalContinuation.infinite
          ((lowerMiddle.trans middleUpper).mapInfinite execution) =
        ProgramBehavior.MaximalContinuation.infinite
          (middleUpper.mapInfinite (lowerMiddle.mapInfinite execution))
      rw [mapInfinite_trans]
      rfl

/-- Reflexive refinement leaves every finite or infinite completion unchanged. -/
theorem mapCompletion_refl (behavior : ProgramBehavior spec)
    {state : behavior.system.State} {graph : behavior.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (completion : behavior.system.Completion state graph priorEvents) :
    (refl behavior).mapCompletion completion = completion := by
  cases completion with
  | finite => rfl
  | infinite execution =>
      change RelationalSystem.Completion.infinite
          ((refl behavior).mapInfinite execution) =
        RelationalSystem.Completion.infinite execution
      rw [mapInfinite_refl]
      rfl

/-- Mapping a completion through a composite refinement agrees with mapping it
through the two adjacent refinements in order. -/
theorem mapCompletion_trans (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper)
    {state : lower.system.State} {graph : lower.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (completion : lower.system.Completion state graph priorEvents) :
    (lowerMiddle.trans middleUpper).mapCompletion completion =
      middleUpper.mapCompletion (lowerMiddle.mapCompletion completion) := by
  cases completion with
  | finite => rfl
  | infinite execution =>
      change RelationalSystem.Completion.infinite
          ((lowerMiddle.trans middleUpper).mapInfinite execution) =
        RelationalSystem.Completion.infinite
          (middleUpper.mapInfinite (lowerMiddle.mapInfinite execution))
      rw [mapInfinite_trans]
      rfl

/-- Map an initial finite derivation coherently. -/
theorem mapRuns (refinement : BehaviorRefinement concrete abstract)
    {initialState state : concrete.system.State}
    {initialGraph graph : concrete.system.Graph} {events : List spec.AuditEvent}
    (execution : concrete.system.Runs initialState initialGraph state graph events) :
    abstract.system.Runs (refinement.mapState initialState)
      (refinement.mapGraph initialGraph) (refinement.mapState state)
      (refinement.mapGraph graph) events :=
  RelationalSystem.Runs.ofInitialSteps
    (refinement.initial execution.initialValid)
    (refinement.mapSteps execution.steps)

/-- Prefix mapping is derived from the coherent state/graph simulation. -/
def mapPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix) :
    abstract.system.ExecutionPrefix where
  initialState := refinement.mapState execution.initialState
  initialGraph := refinement.mapGraph execution.initialGraph
  state := refinement.mapState execution.state
  graph := refinement.mapGraph execution.graph
  events := execution.events
  runs := refinement.mapRuns execution.runs

/-- Reflexive refinement leaves every packaged execution prefix unchanged. -/
@[simp]
theorem mapPrefix_refl (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix) :
    (refl behavior).mapPrefix execution = execution := by
  apply RelationalSystem.ExecutionPrefix.ext <;> rfl

/-- Mapping an initial prefix agrees with constructing the initial prefix from
the mapped initial-state witness. -/
@[simp]
theorem mapPrefix_initial (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    (valid : concrete.system.Initial state graph) :
    refinement.mapPrefix (RelationalSystem.ExecutionPrefix.initial valid) =
      RelationalSystem.ExecutionPrefix.initial (refinement.initial valid) := by
  apply RelationalSystem.ExecutionPrefix.ext <;> rfl

/-- Mapping a prefix through a composite refinement agrees with mapping it
through the two adjacent refinements in order. -/
@[simp]
theorem mapPrefix_trans (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper)
    (execution : lower.system.ExecutionPrefix) :
    (lowerMiddle.trans middleUpper).mapPrefix execution =
      middleUpper.mapPrefix (lowerMiddle.mapPrefix execution) := by
  apply RelationalSystem.ExecutionPrefix.ext <;> rfl

/-- Mapping a one-step extension agrees with extending the mapped prefix by the
mapped transition. -/
@[simp]
theorem mapPrefix_step (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    {choice : concrete.system.Choice} {event : spec.AuditEvent}
    {nextState : concrete.system.State} {nextGraph : concrete.system.Graph}
    (transition : concrete.system.Step execution.graph execution.state choice
      event nextState nextGraph) :
    refinement.mapPrefix (execution.step transition) =
      (refinement.mapPrefix execution).step (refinement.step transition) := by
  apply RelationalSystem.ExecutionPrefix.ext <;> rfl

/-- `BehaviorRefinement.mapPrefix_append` states that refinement mapping
preserves suffix append and its complete event order. -/
@[simp]
theorem mapPrefix_append (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    {events : List spec.AuditEvent}
    {finalState : concrete.system.State} {finalGraph : concrete.system.Graph}
    (suffix : concrete.system.Steps execution.state execution.graph events
      finalState finalGraph) :
    refinement.mapPrefix (execution.append suffix) =
      (refinement.mapPrefix execution).append (refinement.mapSteps suffix) := by
  apply RelationalSystem.ExecutionPrefix.ext <;> rfl

/-- Refinement commutes with appending every finite restriction of an infinite
continuation to the exact packaged prefix that anchors it. -/
@[simp]
theorem mapPrefix_appendInfinitePrefix
    (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    (continuation : concrete.system.InfiniteContinuation execution.state
      execution.graph execution.events)
    (length : Nat) :
    refinement.mapPrefix
        (execution.appendInfinitePrefix continuation length) =
      (refinement.mapPrefix execution).appendInfinitePrefix
        (refinement.mapInfinite continuation) length := by
  have prefixEvents :
      (refinement.mapInfinite continuation).prefixEvents length =
        continuation.prefixEvents length := by
    rw [RelationalSystem.InfiniteContinuation.prefixEvents_eq_ofFn,
      RelationalSystem.InfiniteContinuation.prefixEvents_eq_ofFn]
    rfl
  apply RelationalSystem.ExecutionPrefix.ext <;> try rfl
  exact congrArg (execution.events ++ ·) prefixEvents.symm

/-- `BehaviorRefinement.mapPrefix_events` exposes the exact event trace retained
by prefix mapping. -/
@[simp]
theorem mapPrefix_events (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix) :
    (refinement.mapPrefix execution).events = execution.events := rfl

/-- `BehaviorRefinement.observe_mapPrefix` states that prefix mapping preserves
the specification-selected whole-trace observation. -/
@[simp]
theorem observe_mapPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix) :
    abstract.observe (refinement.mapPrefix execution) =
      concrete.observe execution := rfl

/-- `BehaviorRefinement.inputOf_mapPrefix` states that prefix mapping preserves
the specification input selected by the initial state. -/
@[simp]
theorem inputOf_mapPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix) :
    abstract.inputOf (refinement.mapPrefix execution).initialState =
      concrete.inputOf execution.initialState :=
  refinement.input execution.initialState

/-- `BehaviorRefinement.hasInput_mapPrefix` transports the packaged input
predicate exactly across a refinement. -/
@[simp]
theorem hasInput_mapPrefix (refinement : BehaviorRefinement concrete abstract)
    (input : spec.Input) (execution : concrete.system.ExecutionPrefix) :
    abstract.HasInput input (refinement.mapPrefix execution) ↔
      concrete.HasInput input execution := by
  simp [ProgramBehavior.HasInput]

/-- `BehaviorRefinement.terminal_mapPrefix` transports a terminal witness to
the exact mapped frontier. -/
theorem terminal_mapPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    (terminal : concrete.system.Terminal execution.state execution.graph) :
    abstract.system.Terminal (refinement.mapPrefix execution).state
      (refinement.mapPrefix execution).graph :=
  refinement.terminal terminal

/-- `BehaviorRefinement.mapCompletionAtPrefix` maps a completion while fixing
its result type to the exact frontier and trace of the mapped prefix. -/
def mapCompletionAtPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    (completion : concrete.system.Completion execution.state execution.graph
      execution.events) :
    abstract.system.Completion (refinement.mapPrefix execution).state
      (refinement.mapPrefix execution).graph
      (refinement.mapPrefix execution).events :=
  refinement.mapCompletion completion

/-- Map a maximal continuation while fixing its type to the exact mapped
prefix. -/
def mapMaximalAtPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    (continuation : concrete.MaximalContinuation execution.state
      execution.graph execution.events) :
    abstract.MaximalContinuation (refinement.mapPrefix execution).state
      (refinement.mapPrefix execution).graph
      (refinement.mapPrefix execution).events :=
  refinement.mapMaximal continuation

/-- `BehaviorRefinement.observeMaximal_mapMaximalAtPrefix` states that exact
maximal-continuation mapping preserves the complete observation, including the
finite trace at an environment-pending frontier. -/
@[simp]
theorem observeMaximal_mapMaximalAtPrefix
    (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    (continuation : concrete.MaximalContinuation execution.state
      execution.graph execution.events) :
    abstract.observeMaximal (refinement.mapPrefix execution)
        (refinement.mapMaximalAtPrefix execution continuation) =
      concrete.observeMaximal execution continuation := by
  cases continuation <;> rfl

/-- `BehaviorRefinement.observeCompletion_mapCompletionAtPrefix` states that
exact completion mapping preserves the complete finite or infinite observation. -/
@[simp]
theorem observeCompletion_mapCompletionAtPrefix
    (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    (completion : concrete.system.Completion execution.state execution.graph
      execution.events) :
    abstract.observeCompletion (refinement.mapPrefix execution)
        (refinement.mapCompletionAtPrefix execution completion) =
      concrete.observeCompletion execution completion := by
  cases completion <;> rfl

/-- Prefix-indexed completion mapping through the reflexive refinement leaves
the completion unchanged. -/
theorem mapCompletionAtPrefix_refl (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix)
    (completion : behavior.system.Completion execution.state execution.graph
      execution.events) :
    (refl behavior).mapCompletionAtPrefix execution completion = completion :=
  mapCompletion_refl behavior completion

/-- Prefix-indexed completion mapping through a composite refinement agrees
with mapping through the two adjacent refinements in order. -/
theorem mapCompletionAtPrefix_trans
    (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper)
    (execution : lower.system.ExecutionPrefix)
    (completion : lower.system.Completion execution.state execution.graph
      execution.events) :
    (lowerMiddle.trans middleUpper).mapCompletionAtPrefix execution completion =
      middleUpper.mapCompletionAtPrefix (lowerMiddle.mapPrefix execution)
        (lowerMiddle.mapCompletionAtPrefix execution completion) :=
  mapCompletion_trans lowerMiddle middleUpper completion

/-- Transport the concrete side of a refinement along exact behavior equality. -/
def castConcrete {replacement : ProgramBehavior spec}
    (exact : concrete = replacement)
    (refinement : BehaviorRefinement replacement abstract) :
    BehaviorRefinement concrete abstract := by
  cases exact
  exact refinement

/-- Acceptance transfers from an abstraction to a refining behavior. -/
theorem preservesAcceptance (refinement : BehaviorRefinement concrete abstract)
    (abstractSound : forall (execution : abstract.system.ExecutionPrefix),
      abstract.system.Terminal execution.state execution.graph ->
      spec.admits (abstract.inputOf execution.initialState) ->
      spec.accepts (abstract.inputOf execution.initialState)
        (abstract.observe execution))
    (execution : concrete.system.ExecutionPrefix)
    (terminal : concrete.system.Terminal execution.state execution.graph)
    (admitted : spec.admits (concrete.inputOf execution.initialState)) :
    spec.accepts (concrete.inputOf execution.initialState)
      (concrete.observe execution) := by
  have mappedAdmitted :
      spec.admits (abstract.inputOf
        (refinement.mapPrefix execution).initialState) := by
    simpa using admitted
  simpa using abstractSound (refinement.mapPrefix execution)
    (refinement.terminal_mapPrefix execution terminal) mappedAdmitted

/-- Exhaustive maximal acceptance transfers from an abstraction to a refining
behavior without treating infinite or environment-pending behavior as a
terminal trace. -/
theorem preservesCompleteAcceptance
    (refinement : BehaviorRefinement concrete abstract)
    (abstractSound : forall (execution : abstract.system.ExecutionPrefix)
      (continuation : abstract.MaximalContinuation execution.state
        execution.graph execution.events),
      spec.admits (abstract.inputOf execution.initialState) ->
      spec.AcceptsComplete (abstract.inputOf execution.initialState)
        (abstract.observeMaximal execution continuation))
    (execution : concrete.system.ExecutionPrefix)
    (continuation : concrete.MaximalContinuation execution.state
      execution.graph execution.events)
    (admitted : spec.admits (concrete.inputOf execution.initialState)) :
    spec.AcceptsComplete (concrete.inputOf execution.initialState)
      (concrete.observeMaximal execution continuation) := by
  have mappedAdmitted :
      spec.admits (abstract.inputOf
        (refinement.mapPrefix execution).initialState) := by
    simpa using admitted
  simpa using abstractSound (refinement.mapPrefix execution)
    (refinement.mapMaximalAtPrefix execution continuation) mappedAdmitted

end BehaviorRefinement

/-- Portable process/model correctness, independent of target realization. -/
structure PortableProgramCertificate (spec : SpecProcess) where
  behavior : ProgramBehavior spec
  requirements : DemandCertificateFamily spec.requirements
  adequate : behavior.Adequate
  sound : forall (execution : behavior.system.ExecutionPrefix)
    (continuation : behavior.MaximalContinuation execution.state
      execution.graph execution.events),
    spec.admits (behavior.inputOf execution.initialState) ->
    spec.AcceptsComplete (behavior.inputOf execution.initialState)
      (behavior.observeMaximal execution continuation)

/-- A projected driver and its exact refinement to the portable behavior. -/
structure ProjectedDriverCertificate {spec : SpecProcess}
    (portable : PortableProgramCertificate spec) where
  behavior : ProgramBehavior spec
  refinement : BehaviorRefinement behavior portable.behavior
  adequate : behavior.Adequate
  stage : DerivedDemandFamily spec.requirements.identities
  requirements : DemandCertificateFamily stage.demands

/-- A machine realization and its exact refinement to its selected driver. -/
structure ProviderCertificate {spec : SpecProcess}
    {portable : PortableProgramCertificate spec}
    (driver : ProjectedDriverCertificate portable) where
  behavior : ProgramBehavior spec
  refinement : BehaviorRefinement behavior driver.behavior
  adequate : behavior.Adequate
  stage : DerivedDemandFamily driver.stage.allKeys
  requirements : DemandCertificateFamily stage.demands

/-- A machine realization and its exact refinement to selected providers. -/
structure MachineCertificate {spec : SpecProcess}
    {portable : PortableProgramCertificate spec}
    {driver : ProjectedDriverCertificate portable}
    (provider : ProviderCertificate driver) where
  behavior : ProgramBehavior spec
  refinement : BehaviorRefinement behavior provider.behavior
  adequate : behavior.Adequate
  stage : DerivedDemandFamily provider.stage.allKeys
  requirements : DemandCertificateFamily stage.demands

/-- Selected artifact syntax, canonical writer/parser, and loaded semantics. -/
structure ArtifactFormat (spec : SpecProcess) where
  Artifact : Type u
  write : Artifact -> ByteArray
  Parses : ByteArray -> Artifact -> Prop
  writeParses : forall artifact, Parses (write artifact) artifact
  parseExact : forall {bytes artifact}, Parses bytes artifact -> bytes = write artifact
  artifactBehavior : Artifact -> ProgramBehavior spec
  loadedBehavior : ByteArray -> ProgramBehavior spec
  loadExact : forall {bytes artifact}, Parses bytes artifact ->
      loadedBehavior bytes = artifactBehavior artifact

/-- Exact artifact, loaded behavior, and refinement to the machine tier. -/
structure ArtifactCertificate {spec : SpecProcess}
    {portable : PortableProgramCertificate spec}
    {driver : ProjectedDriverCertificate portable}
    {provider : ProviderCertificate driver}
    (machine : MachineCertificate provider) where
  format : ArtifactFormat spec
  artifact : format.Artifact
  refinement : BehaviorRefinement (format.artifactBehavior artifact) machine.behavior
  adequate : (format.artifactBehavior artifact).Adequate
  stage : DerivedDemandFamily machine.stage.allKeys
  requirements : DemandCertificateFamily stage.demands

end Grass
