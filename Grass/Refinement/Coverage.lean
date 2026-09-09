import Grass.Certificate

/-!
# Backward coverage of the existing execution maps

`BehaviorRefinement` maps concrete executions forward. `Coverage` adds the
opposite existence facts for its exact prefix and completion maps. These facts
compose without requiring the state or graph maps to be invertible.

This module is deliberately limited to the current execution vocabulary.
Finite `ExecutionPrefix` values do not retain their sequence of choices;
`Completion.infinite` does retain its choice stream. Surjectivity of these maps
does not supply a missing branching-strategy model, a permanent-wait execution
constructor, or a stuttering simulation. The certificate gate requires this
backward coverage beside every adjacent refinement, so verified emission
preserves represented whole histories.

The predicate transport theorems quantify over arbitrary properties of these
existing abstract objects. They do not inspect or create certificates for the
author's theorem family.
-/

namespace Grass

variable {spec : SpecProcess}

/-- Package an existing finite prefix with one of its represented completions;
this adds no transition or completion case. -/
abbrev ProgramBehavior.CompletedHistory (behavior : ProgramBehavior spec) :=
  Σ execution : behavior.system.ExecutionPrefix,
    behavior.system.Completion execution.state execution.graph execution.events

namespace BehaviorRefinement

variable {spec : SpecProcess}
  {lower middle upper concrete abstract : ProgramBehavior spec}

/-- Map both parts of a represented history with the existing coherent maps. -/
def mapHistory (refinement : BehaviorRefinement concrete abstract)
    (history : concrete.CompletedHistory) : abstract.CompletedHistory :=
  ⟨refinement.mapPrefix history.1, refinement.mapCompletionAtPrefix history.1 history.2⟩

namespace Coverage

/-- Identity refinement covers every represented prefix and completion unchanged. -/
theorem refl (behavior : ProgramBehavior spec) : Coverage (BehaviorRefinement.refl behavior) where
  prefixes := fun execution => ⟨execution, mapPrefix_refl behavior execution⟩
  completions := fun execution completion =>
    ⟨completion, mapCompletionAtPrefix_refl behavior execution completion⟩

/-- `trans` composes backward coverage along the same adjacent refinement maps. -/
theorem trans {first : BehaviorRefinement lower middle}
    {second : BehaviorRefinement middle upper}
    (firstCoverage : Coverage first) (secondCoverage : Coverage second) :
    Coverage (first.trans second) where
  prefixes := by
    intro target
    obtain ⟨mid, midEq⟩ := secondCoverage.prefixes target
    obtain ⟨source, sourceEq⟩ := firstCoverage.prefixes mid
    refine ⟨source, ?_⟩
    rw [mapPrefix_trans, sourceEq, midEq]
  completions := by
    intro execution target
    obtain ⟨mid, midEq⟩ := secondCoverage.completions (first.mapPrefix execution) target
    obtain ⟨source, sourceEq⟩ := firstCoverage.completions execution mid
    refine ⟨source, ?_⟩
    rw [mapCompletionAtPrefix_trans, sourceEq, midEq]

/-- Universal abstract prefix properties hold exactly when they hold on all
mapped concrete prefixes, by `forall_prefix_iff`. -/
theorem forall_prefix_iff {refinement : BehaviorRefinement concrete abstract}
    (coverage : Coverage refinement) (property : abstract.system.ExecutionPrefix → Prop) :
    (∀ execution, property (refinement.mapPrefix execution)) ↔ ∀ execution, property execution := by
  constructor
  · intro holds target
    obtain ⟨source, rfl⟩ := coverage.prefixes target
    exact holds source
  · intro holds source
    exact holds (refinement.mapPrefix source)

/-- `exists_prefix_iff` prevents a covered implementation from deleting an
abstract possibility expressed as a property of packaged prefixes. -/
theorem exists_prefix_iff {refinement : BehaviorRefinement concrete abstract}
    (coverage : Coverage refinement) (property : abstract.system.ExecutionPrefix → Prop) :
    (∃ execution, property (refinement.mapPrefix execution)) ↔ ∃ execution, property execution := by
  constructor
  · rintro ⟨source, holds⟩
    exact ⟨_, holds⟩
  · rintro ⟨target, holds⟩
    obtain ⟨source, rfl⟩ := coverage.prefixes target
    exact ⟨source, holds⟩

/-- `forall_completion_iff` transports every property of completions from one
exact mapped frontier, retaining the finite/infinite distinction. -/
theorem forall_completion_iff {refinement : BehaviorRefinement concrete abstract}
    (coverage : Coverage refinement) (execution : concrete.system.ExecutionPrefix)
    (property : abstract.system.Completion (refinement.mapPrefix execution).state
      (refinement.mapPrefix execution).graph (refinement.mapPrefix execution).events → Prop) :
    (∀ completion, property (refinement.mapCompletionAtPrefix execution completion)) ↔
      ∀ completion, property completion := by
  constructor
  · intro holds target
    obtain ⟨source, rfl⟩ := coverage.completions execution target
    exact holds source
  · intro holds source
    exact holds (refinement.mapCompletionAtPrefix execution source)

/-- `exists_completion_iff` preserves possibilities at each covered frontier,
not just existence of some unrelated complete execution. -/
theorem exists_completion_iff {refinement : BehaviorRefinement concrete abstract}
    (coverage : Coverage refinement) (execution : concrete.system.ExecutionPrefix)
    (property : abstract.system.Completion (refinement.mapPrefix execution).state
      (refinement.mapPrefix execution).graph (refinement.mapPrefix execution).events → Prop) :
    (∃ completion, property (refinement.mapCompletionAtPrefix execution completion)) ↔
      ∃ completion, property completion := by
  constructor
  · rintro ⟨source, holds⟩
    exact ⟨_, holds⟩
  · rintro ⟨target, holds⟩
    obtain ⟨source, rfl⟩ := coverage.completions execution target
    exact ⟨source, holds⟩

/-- `histories` covers dependent pairs of prefixes and their completions using
the same lifted frontier, rather than unrelated witnesses for each part. -/
theorem histories {refinement : BehaviorRefinement concrete abstract}
    (coverage : Coverage refinement) : Function.Surjective refinement.mapHistory := by
  rintro ⟨target, completion⟩
  obtain ⟨source, rfl⟩ := coverage.prefixes target
  obtain ⟨lifted, rfl⟩ := coverage.completions source completion
  exact ⟨⟨source, lifted⟩, rfl⟩

/-- `lift_infinite` lifts an abstract infinite continuation at the same mapped
frontier; a finite completion cannot replace it. -/
theorem lift_infinite {refinement : BehaviorRefinement concrete abstract}
    (coverage : Coverage refinement) (execution : concrete.system.ExecutionPrefix)
    (target : abstract.system.InfiniteContinuation (refinement.mapPrefix execution).state
      (refinement.mapPrefix execution).graph (refinement.mapPrefix execution).events) :
    ∃ source : concrete.system.InfiniteContinuation execution.state execution.graph
      execution.events, refinement.mapInfinite source = target := by
  obtain ⟨completion, equal⟩ := coverage.completions execution (.infinite target)
  cases completion with
  | finite steps terminal => cases equal
  | infinite source =>
    exact ⟨source, by injection equal⟩

/-- `forall_history_iff` transports arbitrary predicates of represented
abstract prefix/completion pairs, with no per-predicate compiler certificate. -/
theorem forall_history_iff {refinement : BehaviorRefinement concrete abstract}
    (coverage : Coverage refinement) (property : abstract.CompletedHistory → Prop) :
    (∀ history, property (refinement.mapHistory history)) ↔ ∀ history, property history := by
  constructor
  · intro holds target
    obtain ⟨source, rfl⟩ := coverage.histories target
    exact holds source
  · intro holds source
    exact holds (refinement.mapHistory source)

/-- `exists_history_iff` retains possible complete represented histories. -/
theorem exists_history_iff {refinement : BehaviorRefinement concrete abstract}
    (coverage : Coverage refinement) (property : abstract.CompletedHistory → Prop) :
    (∃ history, property (refinement.mapHistory history)) ↔ ∃ history, property history := by
  constructor
  · rintro ⟨source, holds⟩
    exact ⟨_, holds⟩
  · rintro ⟨target, holds⟩
    obtain ⟨source, rfl⟩ := coverage.histories target
    exact ⟨source, holds⟩

end Coverage
end BehaviorRefinement
end Grass
