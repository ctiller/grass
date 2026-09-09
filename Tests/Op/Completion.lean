import Grass.Op.Completion
import Tests.Op.FakeIsa

/-!
Completion receipts require an observed `.ran` result. These fixtures show both
a selected completed step and a distinct ran result that records a denial, so a
receipt never implies a successful clean event on its own.
-/

namespace Grass.Tests.Op.Completion

open Grass.Core Grass.Memory Grass.Op
open Grass.Tests.FakeIsa

private def loadOperation : SomeOperation := SomeOperation.of Alpha.load

private def loadSequence : SubstepSequence :=
  loadOperation.facets.substeps?.getD .none_

-- The real fixture load reaches `.ran`; its exact selected no-fault receipt is
-- the generic run-step equation, not an ISA-specific claim.
example :
    stepAlpha state₀ .load =
      .ran (runStep policy (state₀.noteContext thread₀ .thread) loadSequence
        thread₀ .thread ⟨⟨"alpha"⟩⟩ .none) := by
  exact congrArg StepOutcome.ran
    (ran_noFault_eq_runStep policy state₀ loadOperation thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (fun _ => .none) loadSequence _ (by rfl) (by rfl) (by rfl))

-- A state-level denial is still a `.ran` outcome, but it appends a violation
-- and emits no event. Therefore none of Completion's equations asserts a
-- successful clean access or event merely from `.ran`.
example : ∃ after, stepAlpha state₀ .staleEpoch = .ran after ∧
    ¬ after.violations.IsEmpty ∧ after.events = [] := by
  refine ⟨_, rfl, by decide, by decide⟩

end Grass.Tests.Op.Completion
