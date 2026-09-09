import Grass.ABI.Win64.FrameRanges
import Grass.ISA.X86.Decode
import Grass.Std.Logical.FiniteMap

/-! Local-slot address calculation shared by instruction lowering.
`Result.range_in_frame` and `Result.signed_displacement` connect the computed
operand to its allocation-relative region. Physical RSP agreement remains a
separate execution obligation. -/
namespace Grass.Assembly.LocalAddress

open Grass.ABI.Win64 Grass.ISA.X86 Grass.Memory Grass.Std.Logical

structure Result where
  private mk ::
  layout : CallFrameLayout
  rootOffset : Nat
  slot : String
  width : Nat
  offset : Nat
  positiveWidth : 0 < width
  fitsLocal : offset + width ≤ layout.localBytes
  fitsDisplacement : layout.localOffset + offset < 2 ^ 31

def resolve? (layout : CallFrameLayout) (rootOffset : Nat)
    (env : FiniteMap String Nat) (slot : String) (width : Nat) : Option Result :=
  match env.lookup slot with
  | none => none
  | some offset =>
    if positive : 0 < width then
      if fits : offset + width ≤ layout.localBytes then
        if displacement : layout.localOffset + offset < 2 ^ 31 then
          some ⟨layout, rootOffset, slot, width, offset, positive, fits, displacement⟩
        else none
      else none
    else none

def Result.displacement (result : Result) : Nat := result.layout.localOffset + result.offset
def Result.operand (result : Result) : MemOperand :=
  .base .rsp (BitVec.ofNat 32 result.displacement)
def Result.range (result : Result) : ByteRange :=
  ⟨result.rootOffset + result.displacement, result.width⟩

theorem resolve?_exact {layout : CallFrameLayout} {rootOffset : Nat}
    {env : FiniteMap String Nat} {slot : String} {width : Nat} {result : Result}
    (success : resolve? layout rootOffset env slot width = some result) :
    result.layout = layout ∧ result.rootOffset = rootOffset ∧ result.slot = slot ∧
      result.width = width ∧ env.lookup slot = some result.offset := by
  unfold resolve? at success
  cases lookup : env.lookup slot with
  | none => simp [lookup] at success
  | some offset =>
    simp only [lookup] at success
    split at success <;> try contradiction
    split at success <;> try contradiction
    split at success <;> try contradiction
    cases success
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Result.signed_displacement (result : Result) :
    (BitVec.ofNat 32 result.displacement).toInt = (result.displacement : Int) := by
  have bound := result.fitsDisplacement
  change result.displacement < 2 ^ 31 at bound
  rw [show BitVec.ofNat 32 result.displacement =
    BitVec.ofInt 32 (result.displacement : Int) by rfl]
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · change (-2147483648 : Int) ≤ _
    omega
  · change (result.displacement : Int) < 2147483648
    change result.displacement < 2147483648 at bound
    omega

theorem Result.range_in_frame (result : Result) :
    (result.layout.frameRange.shift result.rootOffset).Contains result.range := by
  change (result.layout.frameRange.shift result.rootOffset).Contains
    ((ByteRange.mk result.displacement result.width).shift result.rootOffset)
  rw [ByteRange.shift_contains_iff]
  apply result.layout.frame_contains_local.trans
  have fits := result.fitsLocal
  simp only [ByteRange.contains_def, CallFrameLayout.localRange, Result.displacement]
  constructor <;> omega

end Grass.Assembly.LocalAddress
