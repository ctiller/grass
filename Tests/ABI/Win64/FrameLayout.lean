import Grass.ABI.Win64.Convention

/-!
# Win64 call-frame calculation at an alternate shape

This fixture crosses the saved-register parity branch with six arguments, a
12-byte local aligned to eight bytes, and two saved registers.  Generic layout
laws carry the assurance; the final conjunction is only a regression rendering
of their computed inputs.
-/

namespace Grass.Tests.ABI.Win64.FrameLayout

open Grass.ABI.Win64 Grass.ISA.X86

private def alternate : CallFrameLayout where
  argumentCount := 6
  localBytes := 12
  localAlignment := 8
  savedRegisters := [.rbx, .r12]

private theorem alternate_admissible : alternate.Admissible := by decide

example : AlignedForCall alternate.savedRegisters.length
    alternate.callAllocationBytes :=
  alternate.callAllocation_aligned

example : alternate.localOffset % alternate.localAlignment = 0 :=
  alternate.localOffset_aligned alternate_admissible

example : alternate.localOffset + alternate.localBytes ≤
    alternate.callAllocationBytes :=
  alternate.allocation_contains_local

example : alternate.savedRegisterOffset 0 + 8 ≤ alternate.totalFrameBytes :=
  alternate.savedRegisterSlot_fits 0 (by decide)

example : alternate.savedRegisterOffset 1 + 8 ≤ alternate.totalFrameBytes :=
  alternate.savedRegisterSlot_fits 1 (by decide)

example :
    alternate.savedRegisterOffset 1 + 8 ≤ alternate.savedRegisterOffset 0 :=
  alternate.savedRegisterSlots_ordered (by decide) (by decide)

example :
    alternate.savedRegisterOffset 0 + 8 ≤ alternate.savedRegisterOffset 1 ∨
      alternate.savedRegisterOffset 1 + 8 ≤ alternate.savedRegisterOffset 0 :=
  alternate.savedRegisterSlots_disjoint (left := 0) (right := 1)
    (by decide) (by decide) (by decide)

/-- Computed outputs, retained as one compact regression rather than inputs to
any frame or memory proof. -/
theorem alternate_computed_outputs :
    alternate.stackArgumentBytes = 16 ∧
    alternate.localOffset = 48 ∧
    alternate.usedCallAllocationBytes = 60 ∧
    alternate.callAllocationBytes = 72 ∧
    alternate.totalFrameBytes = 88 ∧
    alternate.savedRegisterOffset 0 = 80 ∧
    alternate.savedRegisterOffset 1 = 72 := by
  decide

end Grass.Tests.ABI.Win64.FrameLayout
