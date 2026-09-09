import Grass.Console.Contract
import Grass.Semantics.SpecificationDemands

namespace Grass.Console
open Resource Specification RelationalSystem Semantics

theorem observedResponsiveAdequate {Outcome : Type} (request : LineRequest Outcome)
    (rendering : LineRendering) :
    (ObservedBehavior.model request rendering).RespondingContinuationAdequate where
  root := ⟨ObservedBehavior.writingAt request rendering (OutputCut.zero _)⟩
  continuation := by
    intro history
    obtain ⟨extension⟩ := (ObservedBehavior.completionAdequate request rendering).complete history
    exact ⟨.terminal extension.path extension.finished, trivial⟩

/-- Strict finite rank and response at both frontiers prove the authored
conditional termination statement for every generated maximal continuation. -/
theorem observedTerminatesUnderResponsive {Outcome : Type} (request : LineRequest Outcome)
    (rendering : LineRendering) :
    (ObservedBehavior.model request rendering).TerminatesUnderResponsive := by
  let model := ObservedBehavior.model request rendering
  refine ⟨⟨model.respondingWitness (observedResponsiveAdequate request rendering)⟩, ?_⟩
  intro strategy _adequate responsive history generated
  rcases generated with ⟨continuation, compatible⟩
  cases continuation with
  | terminal path finished => trivial
  | infinite continuation => exact False.elim (ObservedBehavior.no_infinite_continuation continuation)
  | waiting path wait =>
      exact False.elim (model.responsive_no_wait strategy responsive _ wait compatible)

theorem lineDemandsCorrect {R Outcome : Type} [model : ResourceModel R] {resources : R}
    (request : LineRequest Outcome) (snapshot : ConsoleResourceSnapshot model resources) :
    ∀ demand ∈ lineDemands request snapshot, demand.statement := by
  intro demand member
  simp only [lineDemands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact fun _ history => ObservedBehavior.history_accounting history
  · exact fun rendering =>
      ⟨fun cut => ⟨ObservedBehavior.writingWait request rendering cut⟩,
       fun selection => ⟨ObservedBehavior.reportingWait request rendering selection⟩⟩
  · exact snapshot.selectedAxes_empty

/-- The unchanged authored console theorem includes base rows and the requested
standard responsive-termination fragment, without a lowering certificate. -/
theorem writeLineContractCorrect {R Outcome : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) (line : TextLine) (policy : ConsoleWriteOutcomePolicy Outcome) :
    MeetsAllSpecificationTheorems
      ((SpecProcess.ofRelational (writeLineContract resources line policy)).withLiveness
        (.terminatesUnder [.environmentResponsive])) := by
  constructor
  intro key
  change (((SpecProcess.ofRelational (writeLineContract resources line policy)).withLiveness
    (.terminatesUnder [.environmentResponsive])).authorRows[key.val]).statement
  have member := List.getElem_mem key.isLt
  change _ ∈ (lineDemands (LineRequest.mk line policy) (ConsoleWriteResources.captured resources) ++
    [_]) at member
  rcases List.mem_append.mp member with base | extra
  · exact lineDemandsCorrect _ _ _ base
  · simp only [List.mem_singleton] at extra
    rw [extra]
    change ∀ rendering (_input : Unit), True →
      if LivenessAssumption.environmentResponsive ∈ [LivenessAssumption.environmentResponsive] then
        (ObservedBehavior.model (LineRequest.mk line policy) rendering).TerminatesUnderResponsive
      else _
    intro rendering _ _
    simp only [List.mem_singleton, ↓reduceIte]
    exact observedTerminatesUnderResponsive _ rendering

end Grass.Console
