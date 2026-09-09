import Grass.ABI.Win64.FrameRanges
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
  match env.lookup input.slot with
  | none => none
  | some offset =>
      if ¬ SlotFits layout offset then none else
      if ¬ D32Fits layout offset then none else
      (movMem32Imm32 (.base .rsp (BitVec.ofNat 32 (layout.localOffset + offset)))
        input.value).map fun encoding => ⟨input, layout, rspRootOffset, offset, encoding⟩

private theorem resolve?_eq {layout : CallFrameLayout} {rspRootOffset : Nat} {env : SlotEnv}
    {input : Input} {resolved : Resolved}
    (h : resolve? layout rspRootOffset env input = some resolved) :
    ∃ offset encoding, env.lookup input.slot = some offset ∧ SlotFits layout offset ∧
      D32Fits layout offset ∧
      movMem32Imm32 (.base .rsp (BitVec.ofNat 32 (layout.localOffset + offset)))
        input.value = some encoding ∧
      resolved = ⟨input, layout, rspRootOffset, offset, encoding⟩ := by
  unfold resolve? at h
  cases hl : env.lookup input.slot with
  | none => simp [hl] at h
  | some offset =>
    rw [hl] at h
    change (if ¬ SlotFits layout offset then none else
      if ¬ D32Fits layout offset then none else
      (movMem32Imm32 (.base .rsp (BitVec.ofNat 32 (layout.localOffset + offset)))
        input.value).map fun encoding =>
          ⟨input, layout, rspRootOffset, offset, encoding⟩) = some resolved at h
    split at h
    · simp at h
    · next hf =>
      split at h
      · simp at h
      · next hd =>
        cases he : movMem32Imm32
            (.base .rsp (BitVec.ofNat 32 (layout.localOffset + offset))) input.value with
        | none => simp [he] at h
        | some encoding =>
          simp [he] at h
          cases h
          exact ⟨offset, encoding, rfl, by simpa using hf, by simpa using hd, he, rfl⟩

theorem range_eq_rspRootOffset_add_displacement (r : Resolved) :
    r.range = ⟨r.rspRootOffset + r.displacement, 4⟩ := rfl
theorem operand_eq_rsp_displacement (r : Resolved) :
    r.operand = .base .rsp (BitVec.ofNat 32 r.displacement) := rfl

theorem encoding_equation_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) :
    movMem32Imm32 r.operand input.value = some r.encoding := by
  obtain ⟨o, e, _, _, _, he, rfl⟩ := resolve?_eq h
  exact he

theorem writeBytes_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat} {env : SlotEnv}
    {input : Input} {r : Resolved} (h : resolve? layout rspRootOffset env input = some r) :
    r.writeBytes = le32 input.value := by
  obtain ⟨o, e, _, _, _, _, rfl⟩ := resolve?_eq h; rfl

theorem writeBytes_length_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) : r.writeBytes.length = 4 := by
  rw [writeBytes_of_resolve? h, length_le32]

theorem displacement_positive_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) : 0 < r.displacement := by
  obtain ⟨o, e, _, _, _, _, rfl⟩ := resolve?_eq h
  have before := layout.stackArguments_end_before_local
  have shadowPositive : 0 < shadowSpaceBytes := by decide
  simp only [Resolved.displacement] at *
  omega

theorem displacement_bounded_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) : r.displacement < 2 ^ 31 := by
  obtain ⟨o, e, _, _, hd, _, rfl⟩ := resolve?_eq h
  exact hd

theorem displacement_roundtrip_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) :
    (BitVec.ofNat 32 r.displacement).toNat = r.displacement := by
  obtain ⟨o, e, _, _, hd, _, rfl⟩ := resolve?_eq h
  simp only [Resolved.displacement, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans hd (by decide : 2 ^ 31 < 2 ^ 32))

theorem range_in_frame_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) :
    (layout.frameRange.shift rspRootOffset).Contains r.range := by
  obtain ⟨o, e, _, hf, _, _, rfl⟩ := resolve?_eq h
  change (layout.frameRange.shift rspRootOffset).Contains
    ((ByteRange.mk (layout.localOffset + o) 4).shift rspRootOffset)
  rw [ByteRange.shift_contains_iff]
  have hlocal : layout.localRange.Contains ⟨layout.localOffset + o, 4⟩ := by
    unfold SlotFits at hf
    simp only [ByteRange.contains_def, CallFrameLayout.localRange]
    constructor <;> omega
  exact layout.frame_contains_local.trans hlocal

theorem encoding_decodes_of_resolve? {layout : CallFrameLayout} {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {r : Resolved}
    (h : resolve? layout rspRootOffset env input = some r) (rest : ByteSeq) :
    decodeInsn (r.encoding.toBytes ++ rest) = .ok (r.encoding, rest) := by
  obtain ⟨o, e, _, _, _, he, rfl⟩ := resolve?_eq h
  exact movMem32Imm32_decodes he rest

end Grass.Assembly.Store32
