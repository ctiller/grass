import Grass.ABI.Win64.Convention
import Grass.ISA.X86.ImmediateArithmetic

/-! Encoding the allocation computed by a Win64 frame layout.
`immediate_exact` relates the signed operand to that allocation; it does not
establish a physical register-state or writable-stack precondition. -/
namespace Grass.Assembly.FrameAllocation

open Grass.ABI.Win64

structure Resolved where
  private mk ::
  layout : CallFrameLayout
  immediate : Grass.ISA.X86.ImmediateArithmetic.Immediate
  amountExact : immediate.toInt = (layout.callAllocationBytes : Int)

def resolve? (layout : CallFrameLayout) : Option Resolved :=
  if short : layout.callAllocationBytes < 2 ^ (8 - 1) then
    some ⟨layout, .i8 (BitVec.ofInt 8 layout.callAllocationBytes), by
      change (BitVec.ofInt 8 (layout.callAllocationBytes : Int)).toInt = _
      apply BitVec.toInt_ofInt_eq_self (by decide)
      · change (-128 : Int) ≤ _
        omega
      · change (layout.callAllocationBytes : Int) < 128
        change layout.callAllocationBytes < 128 at short
        omega⟩
  else if long : layout.callAllocationBytes < 2 ^ (32 - 1) then
    some ⟨layout, .i32 (BitVec.ofInt 32 layout.callAllocationBytes), by
      change (BitVec.ofInt 32 (layout.callAllocationBytes : Int)).toInt = _
      apply BitVec.toInt_ofInt_eq_self (by decide)
      · change (-2147483648 : Int) ≤ _
        omega
      · change (layout.callAllocationBytes : Int) < 2147483648
        change layout.callAllocationBytes < 2147483648 at long
        omega⟩
  else none

def Resolved.encoding (resolved : Resolved) : Grass.ISA.X86.InsnEncoding :=
  Grass.ISA.X86.ImmediateArithmetic.encode .sub .w64 .rsp resolved.immediate

theorem resolve?_layout {layout : CallFrameLayout} {resolved : Resolved}
    (success : resolve? layout = some resolved) : resolved.layout = layout := by
  unfold resolve? at success
  split at success
  · cases success; rfl
  · split at success
    · cases success; rfl
    · contradiction

theorem immediate_exact (resolved : Resolved) :
    resolved.immediate.toInt = (resolved.layout.callAllocationBytes : Int) :=
  resolved.amountExact

theorem operand_agrees_with_alignment (resolved : Resolved) :
    AlignedForCall resolved.layout.savedRegisters.length resolved.immediate.toInt.toNat := by
  rw [immediate_exact]
  simpa using resolved.layout.callAllocation_aligned

theorem encoding_decodes (resolved : Resolved) (rest : Grass.Std.Logical.ByteSeq) :
    Grass.ISA.X86.decodeInsn (resolved.encoding.toBytes ++ rest) =
      .ok (resolved.encoding, rest) :=
  Grass.ISA.X86.ImmediateArithmetic.decode_encode .sub .w64 .rsp resolved.immediate rest

end Grass.Assembly.FrameAllocation
