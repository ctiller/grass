import Grass.Assembly.LocalAddress
import Grass.ISA.X86.Decode
import Grass.Std.Logical.FiniteMap

/-! A bounded deterministic `mov dword ptr [rsp+d32], imm32` construction. -/
namespace Grass.Assembly.Store32
open Grass.ABI.Win64 Grass.Core Grass.ISA.X86 Grass.Memory Grass.Std.Logical

abbrev SlotEnv := FiniteMap String Nat

structure Input where
  slot : String
  value : BitVec 32
deriving DecidableEq, Repr

def SlotFits (layout : CallFrameLayout) (offset : Nat) : Prop := offset + 4 ≤ layout.localBytes
def D32Fits (layout : CallFrameLayout) (offset : Nat) : Prop :=
  layout.localOffset + offset < 2 ^ 31
instance (l : CallFrameLayout) (o : Nat) : Decidable (SlotFits l o) :=
  inferInstanceAs (Decidable (_ ≤ _))
instance (l : CallFrameLayout) (o : Nat) : Decidable (D32Fits l o) :=
  inferInstanceAs (Decidable (_ < _))

/-- The constructor is sealed; derived address and byte views are computed below. -/
structure Resolved where
  private mk ::
  input : Input
  layout : CallFrameLayout
  rspRootOffset : Nat
  localOffset : Nat
  encoding : InsnEncoding

def Resolved.displacement (r : Resolved) : Nat := r.layout.localOffset + r.localOffset
def Resolved.range (r : Resolved) : ByteRange := ⟨r.rspRootOffset + r.displacement, 4⟩
def Resolved.operand (r : Resolved) : MemOperand :=
  .base .rsp (BitVec.ofNat 32 r.displacement)
def Resolved.writeBytes (r : Resolved) : ByteSeq := le32 r.input.value

def resolve? (layout : CallFrameLayout) (rspRootOffset : Nat) (env : SlotEnv)
    (input : Input) : Option Resolved :=
  match _ha : LocalAddress.resolve? layout rspRootOffset env input.slot 4 with
  | none => none
  | some address =>
    match _he : movMem32Imm32 address.operand input.value with
    | none => none
    | some encoding => some ⟨input, layout, rspRootOffset, address.offset, encoding⟩

private theorem resolve?_eq {layout : CallFrameLayout} {rspRootOffset : Nat} {env : SlotEnv}
    {input : Input} {resolved : Resolved}
    (h : resolve? layout rspRootOffset env input = some resolved) :
    ∃ address encoding, LocalAddress.resolve? layout rspRootOffset env input.slot 4 = some address ∧
      movMem32Imm32 address.operand input.value = some encoding ∧
      resolved = ⟨input, layout, rspRootOffset, address.offset, encoding⟩ := by
  unfold resolve? at h
  split at h <;> try contradiction
  rename_i address ha
  split at h <;> try contradiction
  rename_i encoding he
  cases h
  exact ⟨address, encoding, ha, he, rfl⟩

theorem range_eq_rspRootOffset_add_displacement (r : Resolved) :
    r.range = ⟨r.rspRootOffset + r.displacement, 4⟩ := rfl
theorem operand_eq_rsp_displacement (r : Resolved) :
    r.operand = .base .rsp (BitVec.ofNat 32 r.displacement) := rfl

theorem encoding_equation_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) :
    movMem32Imm32 r.operand input.value = some r.encoding := by
  obtain ⟨address, e, ha, he, rfl⟩ := resolve?_eq h
  obtain ⟨hl, _, _, _, _⟩ := LocalAddress.resolve?_exact ha
  simpa [Resolved.operand, Resolved.displacement, LocalAddress.Result.operand,
    LocalAddress.Result.displacement, hl] using he

theorem writeBytes_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat} {env : SlotEnv}
    {input : Input} {r : Resolved} (h : resolve? layout rspRootOffset env input = some r) :
    r.writeBytes = le32 input.value := by
  obtain ⟨address, e, _, _, rfl⟩ := resolve?_eq h; rfl

theorem writeBytes_length_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) : r.writeBytes.length = 4 := by
  rw [writeBytes_of_resolve? h, length_le32]

theorem displacement_positive_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) : 0 < r.displacement := by
  obtain ⟨address, e, ha, _, rfl⟩ := resolve?_eq h
  obtain ⟨hl, _, _, _, _⟩ := LocalAddress.resolve?_exact ha
  have before := layout.stackArguments_end_before_local
  have shadowPositive : 0 < shadowSpaceBytes := by decide
  have displacement := address.fitsDisplacement
  simp only [Resolved.displacement] at *
  rw [hl] at displacement
  omega

theorem displacement_bounded_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) : r.displacement < 2 ^ 31 := by
  obtain ⟨address, e, ha, _, rfl⟩ := resolve?_eq h
  obtain ⟨hl, _, _, _, _⟩ := LocalAddress.resolve?_exact ha
  simpa [Resolved.displacement, LocalAddress.Result.displacement, hl] using
    address.fitsDisplacement

theorem displacement_roundtrip_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) :
    (BitVec.ofNat 32 r.displacement).toNat = r.displacement := by
  obtain ⟨address, e, ha, _, rfl⟩ := resolve?_eq h
  obtain ⟨hl, _, _, _, _⟩ := LocalAddress.resolve?_exact ha
  have hd : layout.localOffset + address.offset < 2 ^ 31 := by
    simpa [hl] using address.fitsDisplacement
  simp only [Resolved.displacement, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans hd (by decide : 2 ^ 31 < 2 ^ 32))

theorem range_in_frame_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) :
    (layout.frameRange.shift rspRootOffset).Contains r.range := by
  obtain ⟨address, e, ha, _, rfl⟩ := resolve?_eq h
  obtain ⟨hl, hr, _, hw, _⟩ := LocalAddress.resolve?_exact ha
  have contained := address.range_in_frame
  simpa [Resolved.range, Resolved.displacement, LocalAddress.Result.range,
    LocalAddress.Result.displacement, hl, hr, hw] using contained

theorem encoding_decodes_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) (rest : ByteSeq) :
    decodeInsn (r.encoding.toBytes ++ rest) = .ok (r.encoding, rest) := by
  obtain ⟨address, e, ha, he, rfl⟩ := resolve?_eq h
  exact movMem32Imm32_decodes he rest

end Grass.Assembly.Store32
