import Grass.Refinement.BehaviorCorrespondenceLaws
import Tests.Refinement.ForwardInclusion

/-! Reverse coverage belongs to exact correspondence, separately from the directed gate. -/

namespace Grass.Tests.Refinement.Coverage

open Grass.Tests.Refinement.ImplementationConformance

example : BehaviorCorrespondence successOnly successOnly id
    (WaitTranslation.refl successOnly) :=
  BehaviorCorrespondence.refl successOnly

example : ImplementationConformance successOnly successOnly id
    (DirectedWaitTranslation.ofExact (WaitTranslation.refl successOnly)) :=
  (BehaviorCorrespondence.refl successOnly).toImplementationConformance

example : ImplementationConformance successOnly successOrError id successTranslation :=
  successConformance

example : ¬ ∃ waits : WaitTranslation successOnly successOrError,
    Nonempty (BehaviorCorrespondence successOnly successOrError id waits) := by
  rintro ⟨waits, ⟨exact⟩⟩
  exact Grass.Tests.Refinement.ForwardInclusion.no_exact_correspondence waits exact

end Grass.Tests.Refinement.Coverage
