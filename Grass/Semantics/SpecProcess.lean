import Grass.Core.Demand
import Grass.Semantics.Execution
import Grass.Semantics.Observation

/-!
# Captured specification behavior

The precious behavior signature is independent of resource selection and of
certificate layering. `BehaviorInterface` owns the authored observable types
and predicates; `ProgramBehavior` supplies one relational implementation of
that interface; and `BehaviorContract` selects the canonical implementation.

The final public `SpecProcess` remains temporarily in its legacy unindexed
shape while the selected-resource and suite interfaces land. It carries the
same behavior interface as a field so existing certificate consumers use this
split now, without creating an alternate behavior definition during the later
cutover.
-/

namespace Grass

universe u

/-- The authored input, audit, observation, admission, and acceptance surface. -/
structure BehaviorInterface where
  Input : Type u
  AuditEvent : Type u
  Observation : Type u
  admits : Input -> Prop
  observationProjection : ObservationProjection AuditEvent Observation
  accepts : Input -> List Observation -> Prop

/-- Relational semantics implementing one authored behavior interface. -/
structure ProgramBehavior (interface : BehaviorInterface) where
  system : RelationalSystem interface.AuditEvent
  inputOf : system.State -> interface.Input

namespace ProgramBehavior

variable {interface : BehaviorInterface}

/-- The interface's whole-trace view of one finite execution prefix.

For a nonterminal prefix this is a provisional recomputation, not an append-only
stream commitment. Functional acceptance consumes this view only with a
terminal witness; independent demands carry safety and other non-functional
claims that a projection may not erase. -/
def observe (behavior : ProgramBehavior interface)
    (execution : behavior.system.ExecutionPrefix) : List interface.Observation :=
  interface.observationProjection.project execution.events

/-- The prefix begins with the selected specification input. -/
def HasInput (behavior : ProgramBehavior interface)
    (input : interface.Input) (execution : behavior.system.ExecutionPrefix) : Prop :=
  behavior.inputOf execution.initialState = input

/-- Every admitted input has an initial execution, and every permitted finite
frontier has either a finite-terminal or infinite continuation. -/
structure Adequate (behavior : ProgramBehavior interface) : Prop where
  execution : forall input, interface.admits input ->
    Nonempty { run : behavior.system.ExecutionPrefix //
      behavior.HasInput input run }
  completion : forall run : behavior.system.ExecutionPrefix,
    Nonempty (behavior.system.Completion run.state run.graph run.events)

/-- Transport adequacy along exact behavior equality. -/
theorem Adequate.cast {behavior replacement : ProgramBehavior interface}
    (exact : behavior = replacement) (adequate : replacement.Adequate) :
    behavior.Adequate := by
  cases exact
  exact adequate

end ProgramBehavior

variable {interface : BehaviorInterface}
variable {lower middle upper concrete abstract : ProgramBehavior interface}

/-- Behavioral inclusion from a concrete layer into its immediate abstraction. -/
structure BehaviorRefinement
    (concrete abstract : ProgramBehavior interface) where
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
def refl (behavior : ProgramBehavior interface) : BehaviorRefinement behavior behavior where
  mapState := id
  mapGraph := id
  mapChoice := id
  input := fun _ => rfl
  initial := id
  step := id
  terminal := id
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

/-- Adjacent refinement composition is associative. -/
@[simp]
theorem trans_assoc {highest : ProgramBehavior interface}
    (lowerMiddle : BehaviorRefinement lower middle)
    (middleUpper : BehaviorRefinement middle upper)
    (upperHighest : BehaviorRefinement upper highest) :
    (lowerMiddle.trans middleUpper).trans upperHighest =
      lowerMiddle.trans (middleUpper.trans upperHighest) := by
  apply ext <;> rfl

end BehaviorRefinement

/-- Exact behavioral equivalence is mutual relational refinement. -/
structure BehaviorEquivalent
    (left right : ProgramBehavior interface) where
  forward : BehaviorRefinement left right
  backward : BehaviorRefinement right left

namespace BehaviorEquivalent

/-- Behavioral equivalence is reflexive. -/
def refl (behavior : ProgramBehavior interface) : BehaviorEquivalent behavior behavior where
  forward := .refl behavior
  backward := .refl behavior

/-- Behavioral equivalence is symmetric. The endpoint types make the supplied
`BehaviorEquivalent.backward` and `BehaviorEquivalent.forward` refinements point
in the required reversed directions. -/
def symm (equivalent : BehaviorEquivalent concrete abstract) :
    BehaviorEquivalent abstract concrete where
  forward := equivalent.backward
  backward := equivalent.forward

/-- Behavioral equivalence is transitive. When composing the supplied backward
refinements, their endpoint types determine the reverse order from the forward
path: highest through middle to lower. -/
def trans {highest : ProgramBehavior interface}
    (lowerMiddle : BehaviorEquivalent lower middle)
    (middleHighest : BehaviorEquivalent middle highest) :
    BehaviorEquivalent lower highest where
  forward := lowerMiddle.forward.trans middleHighest.forward
  backward := middleHighest.backward.trans lowerMiddle.backward

end BehaviorEquivalent

/-- One authored interface paired with its canonical relational behavior. -/
structure BehaviorContract where
  interface : BehaviorInterface.{u}
  behavior : ProgramBehavior interface

/-- Temporary legacy root. Decision 134 replaces this with the resource-indexed
captured `SpecificationSuite` root once its selected-resource dependency lands. -/
structure SpecProcess where
  interface : BehaviorInterface
  requirements : DemandFamily.{u}

/-- Existing certificate code may consume the legacy root through the behavior
interface it explicitly contains. -/
instance : Coe SpecProcess BehaviorInterface := ⟨SpecProcess.interface⟩

namespace SpecProcess

abbrev Input (spec : SpecProcess) := spec.interface.Input
abbrev AuditEvent (spec : SpecProcess) := spec.interface.AuditEvent
abbrev Observation (spec : SpecProcess) := spec.interface.Observation
def admits (spec : SpecProcess) := spec.interface.admits
def observationProjection (spec : SpecProcess) := spec.interface.observationProjection
def accepts (spec : SpecProcess) := spec.interface.accepts

end SpecProcess

end Grass
