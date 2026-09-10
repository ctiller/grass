import Grass.Process.Function.ExecutionBounds
import Tests.Process.SerialFixtures

/-! The existing realized doubling routine exercises an actual one-step bound,
its exact process endpoint, and rejection of an inserted internal stutter. -/

namespace Grass.Process.Tests.SerialBounds

open Grass.Process
open Grass.Process.Tests.Serial

/-- Every source-following execution reaches the precise process result within
one internal step, including preservation of the untouched second field. -/
theorem every_doubling_execution (before : Cell)
    (run : Nat → doublingSource.Machine)
    (starts : run 0 = (before, false))
    (advances : ∀ index next, doublingSource.decide (run index) = .internal next →
      run (index + 1) = next) :
    ∃ index ≤ 1,
      doublingSource.decide (run index) = .exit () ∧
      doublingSource.read (run index) = (before.1 * 2, before.2) ∧
      doublingProcess.Step before (.external .wake) (doublingSource.read (run index)) 0 [] := by
  obtain ⟨index, within, exit, decision, post, step⟩ :=
    doublingCollapses.actual_execution_bounded (fun _ _ => 1) rfl () before trivial
      run starts advances
  cases exit
  exact ⟨index, within, decision, post, step⟩

/-- An entry cannot be reported as a zero-work exit. -/
theorem no_zero_work_exit (before : Cell) (run : Nat → doublingSource.Machine)
    (starts : run 0 = (before, false)) :
    ¬ ∃ index ≤ 0, (doublingSource.decide (run index)).IsExit := by
  rintro ⟨index, within, exits⟩
  have zero : index = 0 := Nat.eq_zero_of_le_zero within
  subst index
  rw [starts, doubling_decides_at_entry] at exits
  exact exits

/-- Padding the source with a stationary step cannot satisfy the actual
execution premise even when the initial counter happens to be zero. -/
theorem stationary_entry_is_not_an_execution (before : Cell) :
    ¬ (∀ index next,
      doublingSource.decide ((fun _ : Nat => (before, false)) index) = .internal next →
      (fun _ : Nat => (before, false)) (index + 1) = next) := by
  intro follows
  have impossible := follows 0 (doubled before) (doubling_decides_at_entry before)
  have samePhase := congrArg Prod.snd impossible
  cases samePhase

end Grass.Process.Tests.SerialBounds
