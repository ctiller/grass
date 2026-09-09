import Grass.ISA.X86.RegisterSemantics

/-!
Pure arithmetic and branch-predicate laws for Hello's register operations.
These follow from the existing operand-local transfers; they add no machine
step, memory, fault or profile-admission claim. Subtraction bounds and addition
no-wrap premises are explicit. Logical AF remains unconstrained.
-/
namespace Grass.ISA.X86.RegisterSemantics

theorem test_w32_self_zero (value : BitVec 64) (flags : Flags Bool) :
    (evaluate .test .w32 value value flags).flags.equal? =
      some (value.setWidth 32 == 0) := by
  change some ((value.setWidth 32 &&& value.setWidth 32) == 0) = _
  rw [BitVec.and_self]

theorem test_w64_self_zero (value : BitVec 64) (flags : Flags Bool) :
    (evaluate .test .w64 value value flags).flags.equal? = some (value == 0) := by
  change some ((value &&& value) == 0) = _
  rw [BitVec.and_self]

theorem cmp_w32_above (destination source : BitVec 64) (flags : Flags Bool) :
    (evaluate .cmp .w32 destination source flags).flags.above? =
      some (decide ((source.setWidth 32).toNat < (destination.setWidth 32).toNat)) := by
  change some ((!decide ((destination.setWidth 32).toNat < (source.setWidth 32).toNat)) &&
      !((destination.setWidth 32 - source.setWidth 32) == 0)) = _
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [← BitVec.toNat_inj]
  omega

theorem test_w32_self_zero_iff (value : BitVec 64) (flags : Flags Bool) :
    (evaluate .test .w32 value value flags).flags.equal? = some true ↔
      value.setWidth 32 = 0 := by
  rw [test_w32_self_zero]
  simp

theorem test_w64_self_zero_iff (value : BitVec 64) (flags : Flags Bool) :
    (evaluate .test .w64 value value flags).flags.equal? = some true ↔
      value = 0 := by
  rw [test_w64_self_zero]
  simp

theorem cmp_w32_above_iff (destination source : BitVec 64) (flags : Flags Bool) :
    (evaluate .cmp .w32 destination source flags).flags.above? = some true ↔
      (source.setWidth 32).toNat < (destination.setWidth 32).toNat := by
  rw [cmp_w32_above]
  simp

open Grass.ISA.X86

theorem evaluate_sub_w32_destination (destination source : BitVec 64)
    (flags : Flags Bool) :
    (evaluate .sub .w32 destination source flags).destination destination =
      writeBack .w32 destination (destination.setWidth 32 - source.setWidth 32) := by
  rfl

theorem evaluate_sub_w32_toNat (destination source : BitVec 64) (flags : Flags Bool)
    (h : (source.setWidth 32).toNat ≤ (destination.setWidth 32).toNat) :
    ((evaluate .sub .w32 destination source flags).destination destination).toNat =
      (destination.setWidth 32).toNat - (source.setWidth 32).toNat := by
  have hle : source.setWidth 32 ≤ destination.setWidth 32 := by
    simpa only [BitVec.le_def] using h
  have hsub := BitVec.toNat_sub_of_le hle
  rw [evaluate_sub_w32_destination]
  change (0#32 ++ (destination.setWidth 32 - source.setWidth 32)).toNat = _
  rw [BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  exact hsub

theorem evaluate_sub_w32_strict_decrease (destination source : BitVec 64)
    (flags : Flags Bool)
    (hle : (source.setWidth 32).toNat ≤ (destination.setWidth 32).toNat)
    (hpos : 0 < (source.setWidth 32).toNat) :
    ((evaluate .sub .w32 destination source flags).destination destination).toNat <
      (destination.setWidth 32).toNat := by
  rw [evaluate_sub_w32_toNat destination source flags hle]
  omega

theorem evaluate_add_w64_destination (destination source : BitVec 64)
    (flags : Flags Bool) :
    (evaluate .add .w64 destination source flags).destination destination =
      destination + source := by
  rfl

theorem evaluate_add_w64_toNat (destination source : BitVec 64) (flags : Flags Bool)
    (h : destination.toNat + source.toNat < 2 ^ 64) :
    ((evaluate .add .w64 destination source flags).destination destination).toNat =
      destination.toNat + source.toNat := by
  rw [evaluate_add_w64_destination]
  exact BitVec.toNat_add_of_lt h

end Grass.ISA.X86.RegisterSemantics
