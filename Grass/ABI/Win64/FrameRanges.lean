import Grass.ABI.Win64.Convention
import Grass.Memory.Range

/-!
# Relative regions of a computed Win64 frame

The range laws here are the consumer interface to the frame calculation.
Consumers place these ranges with `ByteRange.shift` and transport the laws with
`ByteRange.shift_contains_iff` and `ByteRange.shift_disjoint_iff`; they need not
unfold allocation or offset arithmetic. Machine-address bounds and instruction
encoding remain separate obligations.
-/

namespace Grass.ABI.Win64.CallFrameLayout

open Grass.Memory

def shadowRange (_layout : CallFrameLayout) : ByteRange := ⟨0, shadowSpaceBytes⟩
def stackArgumentsRange (layout : CallFrameLayout) : ByteRange :=
  ⟨shadowSpaceBytes, layout.stackArgumentBytes⟩
def localRange (layout : CallFrameLayout) : ByteRange :=
  ⟨layout.localOffset, layout.localBytes⟩
def paddingRange (layout : CallFrameLayout) : ByteRange :=
  ⟨layout.usedCallAllocationBytes,
    layout.callAllocationBytes - layout.usedCallAllocationBytes⟩
def callAllocationRange (layout : CallFrameLayout) : ByteRange :=
  ⟨0, layout.callAllocationBytes⟩
def frameRange (layout : CallFrameLayout) : ByteRange :=
  ⟨0, layout.totalFrameBytes⟩

/-- Bounded push-order indexing; register identity is `savedRegisters.get index`.
A consumer naming a particular register must carry equality to that identity. -/
def savedRegisterRange (layout : CallFrameLayout)
    (index : Fin layout.savedRegisters.length) : ByteRange :=
  ⟨layout.savedRegisterOffset index.val, 8⟩

theorem frame_contains_callAllocation (layout : CallFrameLayout) :
    layout.frameRange.Contains layout.callAllocationRange := by
  simp only [ByteRange.contains_def, frameRange, callAllocationRange, totalFrameBytes]
  omega

theorem callAllocation_contains_shadow (layout : CallFrameLayout) :
    layout.callAllocationRange.Contains layout.shadowRange := by
  have h := layout.stackArguments_end_before_local
  have h' := layout.allocation_contains_local
  simp only [ByteRange.contains_def, callAllocationRange, shadowRange]
  omega

theorem shadow_disjoint_stackArguments (layout : CallFrameLayout) :
    layout.shadowRange.Disjoint layout.stackArgumentsRange := by
  apply Or.inr; apply Or.inr; apply Or.inl
  simp only [ByteRange.stop, shadowRange, stackArgumentsRange, Nat.zero_add, Nat.le_refl]

theorem shadow_disjoint_local (layout : CallFrameLayout) :
    layout.shadowRange.Disjoint layout.localRange := by
  have h := layout.stackArguments_end_before_local
  apply Or.inr; apply Or.inr; apply Or.inl
  simp only [ByteRange.stop, shadowRange, localRange]
  omega

theorem callAllocation_contains_stackArguments (layout : CallFrameLayout) :
    layout.callAllocationRange.Contains layout.stackArgumentsRange := by
  have h := layout.stackArguments_end_before_local
  have h' := layout.allocation_contains_local
  simp only [ByteRange.contains_def, callAllocationRange, stackArgumentsRange]
  omega

theorem callAllocation_contains_local (layout : CallFrameLayout) :
    layout.callAllocationRange.Contains layout.localRange := by
  simpa only [ByteRange.contains_def, localRange, callAllocationRange, Nat.zero_add]
    using And.intro (Nat.zero_le layout.localOffset) layout.allocation_contains_local

theorem frame_contains_stackArguments (layout : CallFrameLayout) :
    layout.frameRange.Contains layout.stackArgumentsRange := by
  have h := layout.callAllocation_contains_stackArguments
  simp only [ByteRange.contains_def, callAllocationRange, stackArgumentsRange] at h
  simp only [ByteRange.contains_def, frameRange, stackArgumentsRange, totalFrameBytes]
  omega

theorem frame_contains_local (layout : CallFrameLayout) :
    layout.frameRange.Contains layout.localRange := by
  have h := layout.allocation_contains_local
  simp only [ByteRange.contains_def, frameRange, localRange, totalFrameBytes]
  omega

theorem stackArguments_disjoint_local (layout : CallFrameLayout) :
    layout.stackArgumentsRange.Disjoint layout.localRange := by
  exact Or.inr (Or.inr (Or.inl layout.stackArguments_end_before_local))

theorem local_disjoint_padding (layout : CallFrameLayout) :
    layout.localRange.Disjoint layout.paddingRange := by
  exact Or.inr (Or.inr (Or.inl (Nat.le_refl _)))

theorem callAllocation_disjoint_saved (layout : CallFrameLayout)
    (index : Fin layout.savedRegisters.length) :
    layout.callAllocationRange.Disjoint (layout.savedRegisterRange index) := by
  apply Or.inr; apply Or.inr; apply Or.inl
  simpa only [ByteRange.stop, callAllocationRange, savedRegisterRange, Nat.zero_add]
    using layout.savedRegisterOffset_at_or_above_allocation index.val index.isLt

theorem frame_contains_saved (layout : CallFrameLayout)
    (index : Fin layout.savedRegisters.length) :
    layout.frameRange.Contains (layout.savedRegisterRange index) := by
  simpa only [ByteRange.contains_def, frameRange, savedRegisterRange, Nat.zero_add]
    using And.intro (Nat.zero_le (layout.savedRegisterOffset index.val))
      (layout.savedRegisterSlot_fits index.val index.isLt)

theorem padding_disjoint_saved (layout : CallFrameLayout)
    (index : Fin layout.savedRegisters.length) :
    layout.paddingRange.Disjoint (layout.savedRegisterRange index) := by
  have h := layout.allocation_contains_local
  have h' := layout.savedRegisterOffset_at_or_above_allocation index.val index.isLt
  apply Or.inr; apply Or.inr; apply Or.inl
  simp only [ByteRange.stop, paddingRange, savedRegisterRange,
    usedCallAllocationBytes] at *
  omega

theorem saved_disjoint_saved (layout : CallFrameLayout)
    (left right : Fin layout.savedRegisters.length) (distinct : left ≠ right) :
    (layout.savedRegisterRange left).Disjoint (layout.savedRegisterRange right) := by
  have valuesDistinct : left.val ≠ right.val := fun h => distinct (Fin.ext h)
  rcases layout.savedRegisterSlots_disjoint left.isLt right.isLt valuesDistinct with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end Grass.ABI.Win64.CallFrameLayout
