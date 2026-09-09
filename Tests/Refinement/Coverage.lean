import Grass.Refinement.Coverage

/-!
# Backward coverage with a noninjective state map

The concrete system counts its steps.  The abstract system deliberately erases
that counter, while retaining the same event and infinite-execution behavior.
-/

namespace Grass.Tests.Refinement.Coverage

inductive NoDemand

private def noDemands : DemandFamily where
  Key := NoDemand
  keys := []
  complete := fun key => nomatch key
  unique := by simp
  identity := fun key => nomatch key
  identityInjective := fun left => nomatch left
  kind := fun key => nomatch key
  statement := fun key => nomatch key

private abbrev spec : SpecProcess where
  Input := Unit
  AuditEvent := Bool
  Observation := Bool
  admits := fun _ => True
  observationProjection := .identity Bool
  accepts := fun _ _ => True
  requirements := noDemands

private abbrev concreteSystem : RelationalSystem spec.AuditEvent where
  State := Nat
  Choice := Unit
  Graph := Unit
  Initial := fun state _ => state = 0
  Step := fun _ state _ event next _ => event = false ∧ next = state + 1
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

private abbrev abstractSystem : RelationalSystem spec.AuditEvent where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ event _ _ => event = false
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

private def concreteBehavior : ProgramBehavior spec where
  system := concreteSystem
  inputOf := fun _ => ()

private def abstractBehavior : ProgramBehavior spec where
  system := abstractSystem
  inputOf := fun _ => ()

private def refinement : BehaviorRefinement concreteBehavior abstractBehavior where
  mapState := fun _ => ()
  mapGraph := id
  mapChoice := id
  input := fun _ => rfl
  initial := fun _ => trivial
  step := fun transition => transition.1
  terminal := fun impossible => False.elim impossible
  infiniteConsistency := fun _ => trivial

private theorem liftRuns
    {initialState state : abstractSystem.State}
    {initialGraph graph : abstractSystem.Graph} {events : List spec.AuditEvent}
    (run : abstractSystem.Runs initialState initialGraph state graph events) :
    ∃ count, concreteSystem.Runs 0 () count () events := by
  induction run with
  | initial _ => exact ⟨0, .initial rfl⟩
  | step prior transition ih =>
      obtain ⟨count, lifted⟩ := ih
      exact ⟨count + 1, .step (choice := ()) lifted ⟨transition, rfl⟩⟩

private theorem prefixCoverage : Function.Surjective refinement.mapPrefix := by
  intro target
  obtain ⟨count, lifted⟩ := liftRuns target.runs
  let source : concreteSystem.ExecutionPrefix := {
    initialState := 0
    initialGraph := ()
    state := count
    graph := ()
    events := target.events
    runs := lifted
  }
  refine ⟨source, ?_⟩
  apply RelationalSystem.ExecutionPrefix.ext <;> rfl

private theorem completionCoverage (execution : concreteSystem.ExecutionPrefix) :
    Function.Surjective (refinement.mapCompletionAtPrefix execution) := by
  intro target
  cases target with
  | finite _ terminal => exact False.elim terminal
  | infinite target =>
      let lifted : concreteSystem.InfiniteContinuation execution.state execution.graph
          execution.events := {
        stateAt := fun index => execution.state + index
        graphAt := fun _ => ()
        choiceAt := target.choiceAt
        eventAt := target.eventAt
        stateZero := by simp
        graphZero := Subsingleton.elim _ _
        step := fun index => ⟨target.step index, rfl⟩
        consistent := trivial
      }
      refine ⟨RelationalSystem.Completion.infinite lifted, ?_⟩
      change RelationalSystem.Completion.infinite (refinement.mapInfinite lifted) =
        RelationalSystem.Completion.infinite target
      congr 1

private theorem coverage : BehaviorRefinement.Coverage refinement where
  prefixes := prefixCoverage
  completions := completionCoverage

/-- Coverage does not require the concrete-to-abstract state map to be injective. -/
theorem covered_state_map_is_not_injective : ¬ Function.Injective refinement.mapState := by
  intro injective
  have : (0 : Nat) = 1 := injective rfl
  omega

private def abstractInfinite :
    abstractSystem.InfiniteContinuation () () [] where
  stateAt := fun _ => ()
  graphAt := fun _ => ()
  choiceAt := fun _ => ()
  eventAt := fun _ => false
  stateZero := rfl
  graphZero := rfl
  step := fun _ => rfl
  consistent := trivial

/-- The infinite branch of completion coverage has an actual abstract target. -/
theorem covered_infinite_execution_exists :
    Nonempty (concreteSystem.InfiniteContinuation 0 () []) := by
  let initial : concreteSystem.ExecutionPrefix :=
    RelationalSystem.ExecutionPrefix.initial (state := 0) (graph := ()) rfl
  obtain ⟨lifted, mapped⟩ := coverage.completions initial
    (.infinite abstractInfinite)
  cases lifted with
  | finite _ terminal => exact False.elim terminal
  | infinite execution => exact ⟨execution⟩

/-- Coverage composes with the identity coverage supplied by the library. -/
example : BehaviorRefinement.Coverage
    (refinement.trans (BehaviorRefinement.refl abstractBehavior)) :=
  coverage.trans (.refl abstractBehavior)

end Grass.Tests.Refinement.Coverage
