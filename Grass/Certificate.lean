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

variable {spec : SpecProcess}
variable {lower middle upper concrete abstract : ProgramBehavior spec}

namespace BehaviorRefinement

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

end Grass
