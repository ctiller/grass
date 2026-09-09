import Grass.Refinement.Coverage

/-!
# Forward inclusion does not preserve abstract may behavior

This fixture records the deliberate gap between forward behavioral inclusion
and behavioral equivalence.  The abstract system may emit either Boolean and
then terminate; the concrete system retains only the `false` alternative.
Both systems are adequate and the concrete system refines the abstract one,
but an abstract execution emitting `true` has no concrete counterpart.
-/

namespace Grass.Tests.Refinement.ForwardInclusion

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

private theorem noDemandCertificates : DemandCertificateFamily noDemands where
  discharge key := nomatch key

private abbrev spec : SpecProcess where
  Input := Unit
  AuditEvent := Bool
  Observation := Bool
  admits := fun _ => True
  observationProjection := .identity Bool
  accepts := fun _ _ => True
  requirements := noDemands

/- `false` is the initial state and `true` is the terminal state. -/
private def abstractSystem : RelationalSystem spec.AuditEvent where
  State := Bool
  Choice := Bool
  Graph := Unit
  Initial := fun state _ => state = false
  Step := fun _ state choice event next _ =>
    state = false ∧ event = choice ∧ next = true
  Terminal := fun state _ => state = true
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

private def concreteSystem : RelationalSystem spec.AuditEvent where
  State := Bool
  Choice := Unit
  Graph := Unit
  Initial := fun state _ => state = false
  Step := fun _ state _ event next _ =>
    state = false ∧ event = false ∧ next = true
  Terminal := fun state _ => state = true
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

private def abstractBehavior : ProgramBehavior spec where
  system := abstractSystem
  inputOf := fun _ => ()

private def concreteBehavior : ProgramBehavior spec where
  system := concreteSystem
  inputOf := fun _ => ()

private def abstractInitial : abstractSystem.ExecutionPrefix :=
  RelationalSystem.ExecutionPrefix.initial (state := false) (graph := ()) rfl

private def concreteInitial : concreteSystem.ExecutionPrefix :=
  RelationalSystem.ExecutionPrefix.initial (state := false) (graph := ()) rfl

private theorem abstractAdequate : abstractBehavior.Adequate where
  execution input _ := by
    cases input
    exact ⟨abstractInitial, rfl⟩
  completion run := by
    change Nonempty (abstractSystem.Completion run.state run.graph run.events)
    cases h : run.state with
    | false =>
        exact ⟨.finite (.step (choice := false) (event := false)
          (nextGraph := run.graph) .refl ⟨rfl, rfl, rfl⟩) rfl⟩
    | true =>
        exact ⟨.finite .refl rfl⟩

private theorem concreteAdequate : concreteBehavior.Adequate where
  execution input _ := by
    cases input
    exact ⟨concreteInitial, rfl⟩
  completion run := by
    change Nonempty (concreteSystem.Completion run.state run.graph run.events)
    cases h : run.state with
    | false =>
        exact ⟨.finite (.step (choice := ()) (event := false)
          (nextGraph := run.graph) .refl ⟨rfl, rfl, rfl⟩) rfl⟩
    | true =>
        exact ⟨.finite .refl rfl⟩

private def abstractPortable : PortableProgramCertificate spec where
  behavior := abstractBehavior
  requirements := noDemandCertificates
  adequate := abstractAdequate
  sound := fun _ _ _ => trivial

/-- The surviving concrete behavior is forward-included in the portable one. -/
private def forwardRefinement :
    BehaviorRefinement concreteBehavior abstractBehavior where
  mapState := id
  mapGraph := id
  mapChoice := fun _ => false
  input := fun _ => rfl
  initial := id
  step := by
    rintro _ _ _ _ _ _ ⟨state, event, next⟩
    exact ⟨state, event, next⟩
  terminal := id
  infiniteConsistency := fun _ => trivial

private def abstractTrueExecution : abstractSystem.ExecutionPrefix :=
  abstractInitial.step (choice := true) (nextGraph := ()) ⟨rfl, rfl, rfl⟩

/-- The abstract observable alternative `true` is genuinely reachable. -/
theorem abstract_may_emit_true :
    ∃ run : abstractBehavior.system.ExecutionPrefix,
      true ∈ abstractBehavior.observe run := by
  refine ⟨abstractTrueExecution, ?_⟩
  change true ∈ ([] : List spec.AuditEvent) ++ ([true] : List spec.AuditEvent)
  rw [List.mem_append]
  exact Or.inr (List.mem_singleton_self true)

private theorem concrete_runs_emit_only_false
    {initialState state : concreteSystem.State}
    {initialGraph graph : concreteSystem.Graph} {events : List spec.AuditEvent}
    (run : concreteSystem.Runs initialState initialGraph state graph events) :
    ∀ event : spec.AuditEvent, event ∈ events → event = false := by
  induction run with
  | initial _ =>
      intro event present
      simp at present
  | step prior transition ih =>
      intro event present
      rw [List.mem_append, List.mem_singleton] at present
      rcases present with priorEvent | lastEvent
      · exact ih event priorEvent
      · simpa [lastEvent] using transition.2.1

/-- No concrete execution can exhibit the deleted `true` alternative. -/
theorem concrete_cannot_emit_true :
    ¬ ∃ run : concreteBehavior.system.ExecutionPrefix,
      true ∈ concreteBehavior.observe run := by
  rintro ⟨run, present⟩
  have false_eq : true = false := concrete_runs_emit_only_false run.runs true present
  cases false_eq

/-- Choice deletion is precisely what backward prefix coverage rules out. -/
theorem forwardRefinement_not_covered :
    ¬ BehaviorRefinement.Coverage forwardRefinement := by
  intro coverage
  obtain ⟨target, emitsTrue⟩ := abstract_may_emit_true
  obtain ⟨source, rfl⟩ := coverage.prefixes target
  apply concrete_cannot_emit_true
  refine ⟨source, ?_⟩
  simpa only [BehaviorRefinement.observe_mapPrefix] using emitsTrue

/-- No actual projected-driver certificate can use the adequate concrete
behavior and forward-only deletion refinement. The contradiction is obtained
from the certificate's mandatory `coverage` field, so removing that field makes
this regression fail to elaborate. -/
theorem forward_only_cannot_form_projected_driver :
    ¬ ∃ driver : ProjectedDriverCertificate abstractPortable,
      ∃ behaviorExact : driver.behavior = concreteBehavior,
        BehaviorRefinement.castConcrete behaviorExact.symm driver.refinement =
          forwardRefinement := by
  rintro ⟨driver, behaviorExact, refinementExact⟩
  have covered := BehaviorRefinement.Coverage.castConcrete
    behaviorExact.symm driver.coverage
  rw [refinementExact] at covered
  exact forwardRefinement_not_covered covered

/- Keep all three witnesses live in the fixture: both adequacy proofs and the
forward refinement coexist with the differing may-execution properties. -/
example : abstractBehavior.Adequate := abstractAdequate
example : concreteBehavior.Adequate := concreteAdequate
example : BehaviorRefinement concreteBehavior abstractBehavior := forwardRefinement

end Grass.Tests.Refinement.ForwardInclusion
