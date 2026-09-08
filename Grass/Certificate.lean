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

namespace ProgramBehavior

variable {spec : SpecProcess}

/-- The specification's whole-trace view of one finite execution prefix.

For a nonterminal prefix this is a provisional recomputation, not an append-only
stream commitment. Functional acceptance consumes this view only with a
terminal witness; independent demands carry safety and other non-functional
claims that a projection may not erase. -/
def observe (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix) : List spec.Observation :=
  spec.observationProjection.project execution.events

/-- The prefix begins with the selected specification input. -/
def HasInput (behavior : ProgramBehavior spec)
    (input : spec.Input) (execution : behavior.system.ExecutionPrefix) : Prop :=
  behavior.inputOf execution.initialState = input

/-- Every admitted input has an initial execution, and every permitted finite
frontier has either a finite-terminal or infinite continuation. -/
structure Adequate (behavior : ProgramBehavior spec) : Prop where
  execution : forall input, spec.admits input ->
    Nonempty { run : behavior.system.ExecutionPrefix //
      behavior.HasInput input run }
  completion : forall run : behavior.system.ExecutionPrefix,
    Nonempty (behavior.system.Completion run.state run.graph run.events)

/-- Transport adequacy along exact behavior equality. -/
theorem Adequate.cast {behavior replacement : ProgramBehavior spec}
    (exact : behavior = replacement) (adequate : replacement.Adequate) :
    behavior.Adequate := by
  cases exact
  exact adequate

end ProgramBehavior

variable {spec : SpecProcess}
variable {lower middle upper concrete abstract : ProgramBehavior spec}

/-- The explicit lens used by one refinement edge.

`project` selects the abstract audit segment. It is a list homomorphism so
local region summaries compose into prefixes. `observationExact` fixes the
specification-selected functional observation, while `evidence` is a separate
non-erasing channel for safety and other independent demands. -/
structure RefinementLens (spec : SpecProcess) where
  project : List spec.AuditEvent -> List spec.AuditEvent
  project_nil : project [] = []
  project_append : forall left right,
    project (left ++ right) = project left ++ project right
  observationExact : forall events,
    spec.observationProjection.project (project events) =
      spec.observationProjection.project events
  /-- For every independently keyed demand, preserve the ordered occurrences
  it marks as evidence. `List.Sublist` retains order and multiplicity while
  still permitting the abstraction to carry additional evidence. -/
  evidenceNonErasing : forall (key : RequirementKey)
    (events : List spec.AuditEvent),
    (events.filter (spec.evidenceRelevant key)).Sublist
      ((project events).filter (spec.evidenceRelevant key))

namespace RefinementLens

/-- A refinement lens is determined by its trace projection; its laws and
keyed evidence obligations are proof-irrelevant. -/
@[ext]
theorem ext {left right : RefinementLens spec}
    (project : left.project = right.project) : left = right := by
  cases left
  cases right
  cases project
  rfl

/-- The identity refinement lens. -/
def identity (spec : SpecProcess) : RefinementLens spec where
  project := id
  project_nil := rfl
  project_append := fun _ _ => rfl
  observationExact := fun _ => rfl
  evidenceNonErasing := fun _ _ => List.Sublist.refl _

/-- Apply the lower lens and then the upper lens. -/
def comp (first second : RefinementLens spec) : RefinementLens spec where
  project events := second.project (first.project events)
  project_nil := by rw [first.project_nil, second.project_nil]
  project_append left right := by
    rw [first.project_append, second.project_append]
  observationExact events := by
    rw [second.observationExact, first.observationExact]
  evidenceNonErasing key events :=
    (first.evidenceNonErasing key events).trans
      (second.evidenceNonErasing key (first.project events))

/-- A compositional projection maps a source prefix to an abstract prefix. -/
theorem project_isPrefix (lens : RefinementLens spec)
    {left right : List spec.AuditEvent} (included : left.IsPrefix right) :
    (lens.project left).IsPrefix (lens.project right) := by
  obtain ⟨suffix, rfl⟩ := included
  exact ⟨lens.project suffix, (lens.project_append left suffix).symm⟩

end RefinementLens

/-- An abstract infinite execution matches a concrete one when every abstract
prefix occurs within a projected concrete segment and every complete concrete
boundary has an exact abstract boundary. The coverage direction rejects an
infinite concrete zero-denotation loop unless the abstraction also supplies a
genuinely matching divergence. -/
structure InfiniteRefinement {concrete abstract : ProgramBehavior spec}
    (lens : RefinementLens spec)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (mapState : concrete.system.State -> abstract.system.State)
    (mapGraph : concrete.system.Graph -> abstract.system.Graph)
    (concreteExecution : concrete.system.InfiniteContinuation state graph priorEvents) where
  abstractExecution : abstract.system.InfiniteContinuation (mapState state) (mapGraph graph)
    (lens.project priorEvents)
  /-- Every abstract intermediate boundary lies inside the projection of some
  complete concrete segment. This admits multi-step expansion. -/
  abstractPrefix : forall abstractLength, exists concreteLength,
    (abstractExecution.prefixEvents abstractLength).IsPrefix
      (lens.project (concreteExecution.prefixEvents concreteLength))
  /-- Every concrete boundary has an exact abstract boundary, including its
  selected events, mapped state, and mapped graph. -/
  concreteBoundary : forall concreteLength, exists abstractLength,
    abstractExecution.prefixEvents abstractLength =
      lens.project (concreteExecution.prefixEvents concreteLength) ∧
    abstractExecution.stateAt abstractLength =
      mapState (concreteExecution.stateAt concreteLength) ∧
    abstractExecution.graphAt abstractLength =
      mapGraph (concreteExecution.graphAt concreteLength)

namespace InfiniteRefinement

/-- An infinite refinement witness is determined by its selected abstract
execution; coverage and boundary coupling are propositions. -/
@[ext]
theorem ext {concrete abstract : ProgramBehavior spec}
    {lens : RefinementLens spec}
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    {mapState : concrete.system.State -> abstract.system.State}
    {mapGraph : concrete.system.Graph -> abstract.system.Graph}
    {execution : concrete.system.InfiniteContinuation state graph priorEvents}
    {left right : InfiniteRefinement lens mapState mapGraph execution}
    (abstractExecution : left.abstractExecution = right.abstractExecution) :
    left = right := by
  cases left
  cases right
  cases abstractExecution
  rfl

end InfiniteRefinement

/-- Weak behavioral inclusion over finite segments and exact maximal behavior. -/
structure BehaviorRefinement (concrete abstract : ProgramBehavior spec) where
  lens : RefinementLens spec
  mapState : concrete.system.State -> abstract.system.State
  mapGraph : concrete.system.Graph -> abstract.system.Graph
  input : forall state, abstract.inputOf (mapState state) = concrete.inputOf state
  initial : forall {state graph}, concrete.system.Initial state graph ->
    abstract.system.Initial (mapState state) (mapGraph graph)
  segment : forall {state finalState graph finalGraph events},
    concrete.system.Steps state graph events finalState finalGraph ->
    abstract.system.Steps (mapState state) (mapGraph graph) (lens.project events)
      (mapState finalState) (mapGraph finalGraph)
  terminal : forall {state graph}, concrete.system.Terminal state graph ->
    abstract.system.Terminal (mapState state) (mapGraph graph)
  infinite : forall {state graph priorEvents}
    (execution : concrete.system.InfiniteContinuation state graph priorEvents),
    InfiniteRefinement lens mapState mapGraph execution

namespace BehaviorRefinement

/-- Two weak refinements are equal when all computational selections agree;
the remaining simulation, terminal, and evidence fields are propositions. -/
@[ext (iff := false)]
theorem ext {left right : BehaviorRefinement concrete abstract}
    (lens : left.lens = right.lens)
    (state : left.mapState = right.mapState)
    (graph : left.mapGraph = right.mapGraph)
    (infinite : HEq
      (@BehaviorRefinement.infinite spec concrete abstract left)
      (@BehaviorRefinement.infinite spec concrete abstract right)) : left = right := by
  cases left
  cases right
  cases lens
  cases state
  cases graph
  cases infinite
  rfl

/-- Build the general segment certificate from the lockstep special case. -/
def lockstep (mapState : concrete.system.State -> abstract.system.State)
    (mapGraph : concrete.system.Graph -> abstract.system.Graph)
    (mapChoice : concrete.system.Choice -> abstract.system.Choice)
    (input : forall state, abstract.inputOf (mapState state) = concrete.inputOf state)
    (initial : forall {state graph}, concrete.system.Initial state graph ->
      abstract.system.Initial (mapState state) (mapGraph graph))
    (step : forall {graph state choice event nextState nextGraph},
      concrete.system.Step graph state choice event nextState nextGraph ->
      abstract.system.Step (mapGraph graph) (mapState state) (mapChoice choice) event
        (mapState nextState) (mapGraph nextGraph))
    (terminal : forall {state graph}, concrete.system.Terminal state graph ->
      abstract.system.Terminal (mapState state) (mapGraph graph))
    (infiniteConsistency : forall {priorEvents stateAt graphAt choiceAt eventAt},
      concrete.system.InfiniteConsistent priorEvents stateAt graphAt choiceAt eventAt ->
      abstract.system.InfiniteConsistent priorEvents (fun index => mapState (stateAt index))
        (fun index => mapGraph (graphAt index))
        (fun index => mapChoice (choiceAt index)) eventAt) :
    BehaviorRefinement concrete abstract where
  lens := RefinementLens.identity spec
  mapState := mapState
  mapGraph := mapGraph
  input := input
  initial := initial
  segment steps := by
    induction steps with
    | refl => exact .refl
    | step prior transition inductionHypothesis =>
        exact .step inductionHypothesis (step transition)
  terminal := terminal
  infinite execution :=
    let mapped : abstract.system.InfiniteContinuation (mapState _) (mapGraph _)
        ((RefinementLens.identity spec).project _) := {
      stateAt := fun index => mapState (execution.stateAt index)
      graphAt := fun index => mapGraph (execution.graphAt index)
      choiceAt := fun index => mapChoice (execution.choiceAt index)
      eventAt := execution.eventAt
      stateZero := congrArg mapState execution.stateZero
      graphZero := congrArg mapGraph execution.graphZero
      step := fun index => step (execution.step index)
      consistent := infiniteConsistency execution.consistent }
    have prefixExact : forall length,
        mapped.prefixEvents length = execution.prefixEvents length := by
      intro length
      induction length with
      | zero => rfl
      | succ length inductionHypothesis =>
          simp only [RelationalSystem.InfiniteContinuation.prefixEvents]
          rw [inductionHypothesis]
    { abstractExecution := mapped
      abstractPrefix := fun length => ⟨length, by
        rw [prefixExact length]
        change (execution.prefixEvents length).IsPrefix
          (execution.prefixEvents length)
        exact ⟨[], by simp⟩⟩
      concreteBoundary := fun length => ⟨length, prefixExact length, rfl, rfl⟩ }

/-- Refinement is reflexive. -/
def refl (behavior : ProgramBehavior spec) : BehaviorRefinement behavior behavior :=
  lockstep id id id (fun _ => rfl) id id id id

/-- Map a coherent finite suffix through the segment simulation. -/
theorem mapSteps (refinement : BehaviorRefinement concrete abstract)
    {state finalState : concrete.system.State}
    {graph finalGraph : concrete.system.Graph} {events : List spec.AuditEvent}
    (steps : concrete.system.Steps state graph events finalState finalGraph) :
    abstract.system.Steps (refinement.mapState state) (refinement.mapGraph graph)
      (refinement.lens.project events)
      (refinement.mapState finalState) (refinement.mapGraph finalGraph) :=
  refinement.segment steps

/-- Map an infinite execution together with its cofinal-prefix evidence. -/
def mapInfinite (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : concrete.system.InfiniteContinuation state graph priorEvents) :
    abstract.system.InfiniteContinuation (refinement.mapState state)
      (refinement.mapGraph graph) (refinement.lens.project priorEvents) :=
  (refinement.infinite execution).abstractExecution

/-- Every finite prefix of the selected abstract execution occurs within the
projection of a concrete prefix. -/
theorem mapInfinite_prefixEvents
    (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : concrete.system.InfiniteContinuation state graph priorEvents)
    (length : Nat) : exists concreteLength,
    ((refinement.mapInfinite execution).prefixEvents length).IsPrefix
      (refinement.lens.project (execution.prefixEvents concreteLength)) :=
  (refinement.infinite execution).abstractPrefix length

/-- Every finite restriction of the selected abstract execution is witnessed
by abstract steps at its own frontier. -/
theorem mapInfinite_prefixSteps
    (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : concrete.system.InfiniteContinuation state graph priorEvents)
    (length : Nat) : abstract.system.Steps (refinement.mapState state)
      (refinement.mapGraph graph)
      ((refinement.mapInfinite execution).prefixEvents length)
      ((refinement.mapInfinite execution).stateAt length)
      ((refinement.mapInfinite execution).graphAt length) :=
  (refinement.mapInfinite execution).prefixSteps length

/-- The lockstep identity constructor leaves an infinite execution unchanged. -/
theorem mapInfinite_refl (behavior : ProgramBehavior spec)
    {state : behavior.system.State} {graph : behavior.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : behavior.system.InfiniteContinuation state graph priorEvents) :
    (refl behavior).mapInfinite execution = execution := by
  apply RelationalSystem.InfiniteContinuation.ext <;> rfl

/-- The selected infinite image covers abstract prefixes and exactly matches
projected concrete boundaries. -/
def mapInfinite_prefixes (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : concrete.system.InfiniteContinuation state graph priorEvents) :
    InfiniteRefinement refinement.lens refinement.mapState refinement.mapGraph execution :=
  refinement.infinite execution

/-- Adjacent weak refinements compose. -/
def trans (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper) :
    BehaviorRefinement lower upper where
  lens := lowerMiddle.lens.comp middleUpper.lens
  mapState state := middleUpper.mapState (lowerMiddle.mapState state)
  mapGraph graph := middleUpper.mapGraph (lowerMiddle.mapGraph graph)
  input state := by rw [middleUpper.input, lowerMiddle.input]
  initial valid := middleUpper.initial (lowerMiddle.initial valid)
  segment steps := middleUpper.mapSteps (lowerMiddle.mapSteps steps)
  terminal terminal := middleUpper.terminal (lowerMiddle.terminal terminal)
  infinite execution :=
    let first := lowerMiddle.infinite execution
    let second := middleUpper.infinite first.abstractExecution
    { abstractExecution := second.abstractExecution
      abstractPrefix := fun length => by
        obtain ⟨middleLength, upperPrefix⟩ :=
          second.abstractPrefix length
        obtain ⟨lowerLength, middlePrefix⟩ :=
          first.abstractPrefix middleLength
        exact ⟨lowerLength, upperPrefix.trans
          (middleUpper.lens.project_isPrefix middlePrefix)⟩
      concreteBoundary := fun length => by
        obtain ⟨middleLength, middleEvents, middleState, middleGraph⟩ :=
          first.concreteBoundary length
        obtain ⟨upperLength, upperEvents, upperState, upperGraph⟩ :=
          second.concreteBoundary middleLength
        have events : second.abstractExecution.prefixEvents upperLength =
            (lowerMiddle.lens.comp middleUpper.lens).project
              (execution.prefixEvents length) := by
          simp only [RefinementLens.comp]
          rw [upperEvents, middleEvents]
        exact ⟨upperLength, events,
          upperState.trans (congrArg middleUpper.mapState middleState),
          upperGraph.trans (congrArg middleUpper.mapGraph middleGraph)⟩ }

/-- Infinite execution mapping respects adjacent-refinement composition. -/
theorem mapInfinite_trans (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper)
    {state : lower.system.State} {graph : lower.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (execution : lower.system.InfiniteContinuation state graph priorEvents) :
    (lowerMiddle.trans middleUpper).mapInfinite execution =
      middleUpper.mapInfinite (lowerMiddle.mapInfinite execution) := rfl

/-- Reflexive refinement is a left identity for weak-refinement composition. -/
@[simp]
theorem refl_trans (refinement : BehaviorRefinement lower upper) :
    (refl lower).trans refinement = refinement := by
  apply ext
  · apply RefinementLens.ext
    rfl
  · rfl
  · rfl
  · apply heq_of_eq
    funext state graph priorEvents execution
    apply InfiniteRefinement.ext
    exact congrArg (fun mapped => (refinement.infinite mapped).abstractExecution)
      (mapInfinite_refl lower execution)

/-- Reflexive refinement is a right identity for weak-refinement composition. -/
@[simp]
theorem trans_refl (refinement : BehaviorRefinement lower upper) :
    refinement.trans (refl upper) = refinement := by
  apply ext
  · apply RefinementLens.ext
    rfl
  · rfl
  · rfl
  · apply heq_of_eq
    funext state graph priorEvents execution
    apply InfiniteRefinement.ext
    exact mapInfinite_refl upper (refinement.mapInfinite execution)

/-- Weak-refinement composition is associative. -/
@[simp]
theorem trans_assoc {highest : ProgramBehavior spec}
    (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper)
    (upperHighest : BehaviorRefinement upper highest) :
    (lowerMiddle.trans middleUpper).trans upperHighest =
      lowerMiddle.trans (middleUpper.trans upperHighest) := by
  apply ext
  · apply RefinementLens.ext
    rfl
  · rfl
  · rfl
  · apply heq_of_eq
    funext state graph priorEvents execution
    apply InfiniteRefinement.ext
    rfl

/-- Map a terminal or infinite continuation coherently. -/
def mapCompletion (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    {priorEvents : List spec.AuditEvent}
    (completion : concrete.system.Completion state graph priorEvents) :
    abstract.system.Completion (refinement.mapState state) (refinement.mapGraph graph)
      (refinement.lens.project priorEvents) := by
  cases completion with
  | finite steps terminal =>
      exact .finite (refinement.mapSteps steps) (refinement.terminal terminal)
  | infinite execution => exact .infinite (refinement.mapInfinite execution)

/-- Completion mapping through the identity refinement is exact. -/
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

/-- Completion mapping respects adjacent-refinement composition. -/
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
      (refinement.mapGraph graph) (refinement.lens.project events) :=
  RelationalSystem.Runs.ofInitialSteps
    (refinement.initial execution.initialValid)
    (refinement.mapSteps execution.steps)

/-- Prefix mapping is derived from the coherent segment simulation. -/
def mapPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix) :
    abstract.system.ExecutionPrefix where
  initialState := refinement.mapState execution.initialState
  initialGraph := refinement.mapGraph execution.initialGraph
  state := refinement.mapState execution.state
  graph := refinement.mapGraph execution.graph
  events := refinement.lens.project execution.events
  runs := refinement.mapRuns execution.runs

/-- The reflexive weak refinement leaves every packaged prefix unchanged. -/
@[simp]
theorem mapPrefix_refl (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix) :
    (refl behavior).mapPrefix execution = execution := by
  apply RelationalSystem.ExecutionPrefix.ext <;>
    simp [mapPrefix, refl, lockstep, RefinementLens.identity]

/-- `BehaviorRefinement.mapPrefix_initial` preserves the selected initial
configuration. -/
@[simp]
theorem mapPrefix_initial (refinement : BehaviorRefinement concrete abstract)
    {state : concrete.system.State} {graph : concrete.system.Graph}
    (valid : concrete.system.Initial state graph) :
    refinement.mapPrefix (RelationalSystem.ExecutionPrefix.initial valid) =
      RelationalSystem.ExecutionPrefix.initial (refinement.initial valid) := by
  apply RelationalSystem.ExecutionPrefix.ext <;>
    simp [mapPrefix, RelationalSystem.ExecutionPrefix.initial,
      refinement.lens.project_nil]

/-- Mapping a prefix through a composite refinement agrees with mapping it
through the two adjacent refinements in order. -/
@[simp]
theorem mapPrefix_trans (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper)
    (execution : lower.system.ExecutionPrefix) :
    (lowerMiddle.trans middleUpper).mapPrefix execution =
      middleUpper.mapPrefix (lowerMiddle.mapPrefix execution) := by
  apply RelationalSystem.ExecutionPrefix.ext <;>
    simp [mapPrefix, trans, RefinementLens.comp]

/-- `BehaviorRefinement.mapPrefix_append` preserves segment boundaries and
event order. -/
@[simp]
theorem mapPrefix_append (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    {events : List spec.AuditEvent}
    {finalState : concrete.system.State} {finalGraph : concrete.system.Graph}
    (suffix : concrete.system.Steps execution.state execution.graph events
      finalState finalGraph) :
    refinement.mapPrefix (execution.append suffix) =
      (refinement.mapPrefix execution).append (refinement.mapSteps suffix) := by
  apply RelationalSystem.ExecutionPrefix.ext <;>
    simp [mapPrefix, RelationalSystem.ExecutionPrefix.append,
      refinement.lens.project_append]

/-- A single concrete transition maps to one abstract segment, which may have
zero, one, or many abstract transitions. -/
@[simp]
theorem mapPrefix_step (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    {choice : concrete.system.Choice} {event : spec.AuditEvent}
    {nextState : concrete.system.State} {nextGraph : concrete.system.Graph}
    (transition : concrete.system.Step execution.graph execution.state choice
      event nextState nextGraph) :
    refinement.mapPrefix (execution.step transition) =
      (refinement.mapPrefix execution).append
        (refinement.mapSteps (.step .refl transition)) := by
  rw [RelationalSystem.ExecutionPrefix.step_eq_append,
    refinement.mapPrefix_append]

/-- Prefix mapping exposes exactly the lens-selected abstract trace. -/
@[simp]
theorem mapPrefix_events (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix) :
    (refinement.mapPrefix execution).events =
      refinement.lens.project execution.events := rfl

/-- Functional observations are exact even when internal audit events are
inserted, removed, or grouped by the refinement lens. -/
@[simp]
theorem observe_mapPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix) :
    abstract.observe (refinement.mapPrefix execution) =
      concrete.observe execution :=
  refinement.lens.observationExact execution.events

/-- `BehaviorRefinement.inputOf_mapPrefix` preserves the specification input
selected initially. -/
@[simp]
theorem inputOf_mapPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix) :
    abstract.inputOf (refinement.mapPrefix execution).initialState =
      concrete.inputOf execution.initialState :=
  refinement.input execution.initialState

/-- Transport the packaged input predicate exactly across a refinement. -/
@[simp]
theorem hasInput_mapPrefix (refinement : BehaviorRefinement concrete abstract)
    (input : spec.Input) (execution : concrete.system.ExecutionPrefix) :
    abstract.HasInput input (refinement.mapPrefix execution) ↔
      concrete.HasInput input execution := by
  simp [ProgramBehavior.HasInput]

/-- Transport a terminal witness to the exact mapped frontier. -/
theorem terminal_mapPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    (terminal : concrete.system.Terminal execution.state execution.graph) :
    abstract.system.Terminal (refinement.mapPrefix execution).state
      (refinement.mapPrefix execution).graph :=
  refinement.terminal terminal

/-- Map a completion at the exact projected prefix frontier. -/
def mapCompletionAtPrefix (refinement : BehaviorRefinement concrete abstract)
    (execution : concrete.system.ExecutionPrefix)
    (completion : concrete.system.Completion execution.state execution.graph
      execution.events) :
    abstract.system.Completion (refinement.mapPrefix execution).state
      (refinement.mapPrefix execution).graph
      (refinement.mapPrefix execution).events :=
  refinement.mapCompletion completion

/-- Prefix-indexed completion mapping through the identity refinement is exact. -/
theorem mapCompletionAtPrefix_refl (behavior : ProgramBehavior spec)
    (execution : behavior.system.ExecutionPrefix)
    (completion : behavior.system.Completion execution.state execution.graph
      execution.events) :
    (refl behavior).mapCompletionAtPrefix execution completion = completion :=
  mapCompletion_refl behavior completion

/-- Prefix-indexed completion mapping respects adjacent-refinement composition. -/
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

end BehaviorRefinement

/-- Portable process/model correctness, independent of target realization. -/
structure PortableProgramCertificate (spec : SpecProcess) where
  behavior : ProgramBehavior spec
  requirements : DemandCertificateFamily spec.requirements
  adequate : behavior.Adequate
  sound : forall (execution : behavior.system.ExecutionPrefix),
    behavior.system.Terminal execution.state execution.graph ->
    spec.admits (behavior.inputOf execution.initialState) ->
    spec.accepts (behavior.inputOf execution.initialState) (behavior.observe execution)

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

namespace ProjectedDriverCertificate

/-- `ProjectedDriverCertificate.allKeys_nodup` proves that the driver tier
preserves global uniqueness of stable requirement keys. -/
theorem allKeys_nodup {portable : PortableProgramCertificate spec}
    (driver : ProjectedDriverCertificate portable) : driver.stage.allKeys.Nodup :=
  driver.stage.allKeys_nodup spec.requirements.identities_nodup

end ProjectedDriverCertificate

namespace ProviderCertificate

/-- `ProviderCertificate.allKeys_nodup` proves that the provider tier preserves
global uniqueness of stable requirement keys. -/
theorem allKeys_nodup {portable : PortableProgramCertificate spec}
    {driver : ProjectedDriverCertificate portable}
    (provider : ProviderCertificate driver) : provider.stage.allKeys.Nodup :=
  provider.stage.allKeys_nodup driver.allKeys_nodup

end ProviderCertificate

namespace MachineCertificate

/-- `MachineCertificate.allKeys_nodup` proves that the machine tier preserves
global uniqueness of stable requirement keys. -/
theorem allKeys_nodup {portable : PortableProgramCertificate spec}
    {driver : ProjectedDriverCertificate portable}
    {provider : ProviderCertificate driver}
    (machine : MachineCertificate provider) : machine.stage.allKeys.Nodup :=
  machine.stage.allKeys_nodup provider.allKeys_nodup

end MachineCertificate

namespace ArtifactCertificate

/-- `ArtifactCertificate.allKeys_nodup` proves that the artifact tier preserves
global uniqueness of stable requirement keys. -/
theorem allKeys_nodup {portable : PortableProgramCertificate spec}
    {driver : ProjectedDriverCertificate portable}
    {provider : ProviderCertificate driver}
    {machine : MachineCertificate provider}
    (artifact : ArtifactCertificate machine) : artifact.stage.allKeys.Nodup :=
  artifact.stage.allKeys_nodup machine.allKeys_nodup

end ArtifactCertificate

end Grass
