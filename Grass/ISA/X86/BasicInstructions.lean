import Grass.ISA.X86.Decode

/-! Bounded constructors for basic register instructions already in `opcodeTable`. -/
namespace Grass.ISA.X86.BasicInstructions

open Grass.Core Grass.ISA.X86 Grass.Std.Logical

inductive Width where
  | w32
  | w64
deriving DecidableEq, Repr

def Width.rexW : Width → Bool
  | .w32 => false
  | .w64 => true

private def regReg (opcode : Byte) (width : Width) (dst src : Gpr) : InsnEncoding :=
  let w := width.rexW
  let needsRex := w || src.rexBit || dst.rexBit
  { rex := if needsRex then some (Rex.of w src.rexBit false dst.rexBit) else none
    escape := false
    opcode := opcode
    modrm := some ⟨3, src.encodingBits, dst.encodingBits⟩
    sib := none
    disp := .none
    imm := .none }

/-- `PUSH r64`, opcode `50+rd`. -/
def push (reg : Gpr) : InsnEncoding :=
  { rex := if reg.rexBit then some (Rex.of false false false true) else none
    escape := false
    opcode := 0x50 + BitVec.setWidth 8 reg.encodingBits
    modrm := none, sib := none, disp := .none, imm := .none }

/-- `MOV dst, src`, using `89 /r`. -/
def movRegReg (width : Width) (dst src : Gpr) : InsnEncoding :=
  regReg 0x89 width dst src

/-- `MOV r32, m32`, using the shared memory-operand encoder. -/
def movReg32Mem (dst : Gpr) (src : MemOperand) : Option InsnEncoding :=
  encodeMemInsn false 0x8B false (.reg dst) src

def testRegReg (width : Width) (left right : Gpr) : InsnEncoding :=
  regReg 0x85 width left right

def cmpRegReg (width : Width) (left right : Gpr) : InsnEncoding :=
  regReg 0x39 width left right

def addRegReg (width : Width) (dst src : Gpr) : InsnEncoding :=
  regReg 0x01 width dst src

def subRegReg (width : Width) (dst src : Gpr) : InsnEncoding :=
  regReg 0x29 width dst src

def xorRegReg (width : Width) (dst src : Gpr) : InsnEncoding :=
  regReg 0x31 width dst src

/-- `UD2`, the modeled escaped opcode `0F 0B`. -/
def ud2 : InsnEncoding :=
  { rex := none, escape := true, opcode := 0x0B
    modrm := none, sib := none, disp := .none, imm := .none }

private theorem direct_decodes {i : InsnEncoding}
    (shape : specShapeFor i.escape i.opcode i.modrm.isSome i.imm.sizeOf = true)
    (wf : i.WellFormed) (rest : ByteSeq) :
    decodeInsn (i.toBytes ++ rest) = .ok (i, rest) := by
  simp only [specShapeFor] at shape
  match hf : findSpec i.escape i.opcode with
  | none => rw [hf] at shape; simp at shape
  | some spec =>
    rw [hf] at shape
    simp only [Bool.and_eq_true, beq_iff_eq] at shape
    obtain ⟨⟨hmod, hprom⟩, himm⟩ := shape
    obtain ⟨hesc, hop⟩ := findSpec_escape_opcode hf
    apply decodeInsn_toBytes rest hf
    · refine ⟨hesc, hop, hmod, ?_⟩
      rw [OpcodeSpec.immSizeFor_not_promoted hprom]
      exact himm
    · exact wf

private theorem regReg_wellFormed (opcode : Byte) (width : Width) (dst src : Gpr) :
    (regReg opcode width dst src).WellFormed := by
  simp [InsnEncoding.WellFormed, regReg]
  cases dst <;> decide

private theorem push_wellFormed (reg : Gpr) : (push reg).WellFormed := by
  simp [InsnEncoding.WellFormed, push]

private theorem ud2_wellFormed : ud2.WellFormed := by
  simp [InsnEncoding.WellFormed, ud2]

theorem push_decodes (reg : Gpr) (rest : ByteSeq) :
    decodeInsn ((push reg).toBytes ++ rest) = .ok (push reg, rest) := by
  apply direct_decodes (wf := push_wellFormed reg)
  cases reg <;> decide

theorem movRegReg_decodes (width : Width) (dst src : Gpr) (rest : ByteSeq) :
    decodeInsn ((movRegReg width dst src).toBytes ++ rest) =
      .ok (movRegReg width dst src, rest) := by
  apply direct_decodes (wf := regReg_wellFormed 0x89 width dst src)
  cases width <;> cases dst <;> cases src <;> decide

theorem movReg32Mem_decodes {dst : Gpr} {src : MemOperand} {i : InsnEncoding}
    (h : movReg32Mem dst src = some i) (rest : ByteSeq) :
    decodeInsn (i.toBytes ++ rest) = .ok (i, rest) :=
  encodeMemInsn_decodes h rfl rest

theorem testRegReg_decodes (width : Width) (left right : Gpr) (rest : ByteSeq) :
    decodeInsn ((testRegReg width left right).toBytes ++ rest) =
      .ok (testRegReg width left right, rest) := by
  apply direct_decodes (wf := regReg_wellFormed 0x85 width left right)
  cases width <;> cases left <;> cases right <;> decide

theorem cmpRegReg_decodes (width : Width) (left right : Gpr) (rest : ByteSeq) :
    decodeInsn ((cmpRegReg width left right).toBytes ++ rest) =
      .ok (cmpRegReg width left right, rest) := by
  apply direct_decodes (wf := regReg_wellFormed 0x39 width left right)
  cases width <;> cases left <;> cases right <;> decide

theorem addRegReg_decodes (width : Width) (dst src : Gpr) (rest : ByteSeq) :
    decodeInsn ((addRegReg width dst src).toBytes ++ rest) =
      .ok (addRegReg width dst src, rest) := by
  apply direct_decodes (wf := regReg_wellFormed 0x01 width dst src)
  cases width <;> cases dst <;> cases src <;> decide

theorem subRegReg_decodes (width : Width) (dst src : Gpr) (rest : ByteSeq) :
    decodeInsn ((subRegReg width dst src).toBytes ++ rest) =
      .ok (subRegReg width dst src, rest) := by
  apply direct_decodes (wf := regReg_wellFormed 0x29 width dst src)
  cases width <;> cases dst <;> cases src <;> decide

theorem xorRegReg_decodes (width : Width) (dst src : Gpr) (rest : ByteSeq) :
    decodeInsn ((xorRegReg width dst src).toBytes ++ rest) =
      .ok (xorRegReg width dst src, rest) := by
  apply direct_decodes (wf := regReg_wellFormed 0x31 width dst src)
  cases width <;> cases dst <;> cases src <;> decide

theorem ud2_decodes (rest : ByteSeq) :
    decodeInsn (ud2.toBytes ++ rest) = .ok (ud2, rest) := by
  exact direct_decodes (by decide) ud2_wellFormed rest

end Grass.ISA.X86.BasicInstructions
