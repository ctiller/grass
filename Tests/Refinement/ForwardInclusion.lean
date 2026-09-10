import Tests.Refinement.ImplementationConformance

/-! Directed conformance permits abstract choice deletion. -/

namespace Grass.Tests.Refinement.ForwardInclusion

open RelationalSystem
open Grass.Tests.Refinement.ImplementationConformance

example : Grass.ImplementationConformance successOnly successOrError id
    successTranslation := successConformance

/-- Exact correspondence cannot erase the abstract error alternative. -/
theorem no_exact_correspondence
    (waits : WaitTranslation successOnly successOrError)
    (exact : BehaviorCorrespondence successOnly successOrError id waits) : False := by
  obtain ⟨left, empty, related⟩ := exact.finite.initialBack
    successOrErrorErrorInitial rfl
  obtain ⟨other, starts, matched⟩ := exact.completeBack related
    (.terminal successOrErrorErrorInitial trivial) (History.Extension.refl _)
  cases matched with
  | terminal leftHistory rightHistory leftDone rightDone histories outcomes =>
      change some true = some false at outcomes
      cases outcomes

end Grass.Tests.Refinement.ForwardInclusion
