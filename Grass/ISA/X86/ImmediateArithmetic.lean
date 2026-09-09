import Grass.ISA.X86.BasicInstructions

/-! Register-direct Group 1 arithmetic with typed immediate widths. -/
namespace Grass.ISA.X86.ImmediateArithmetic

open Grass.ISA.X86 Grass.Std.Logical
open Grass.ISA.X86.BasicInstructions

/-- The Group 1 operations needed by the Hello source. -/
inductive Kind where
  | sub
  | cmp
deriving DecidableEq, Repr

/-- The two immediate widths admitted by opcodes `83` and `81`. -/
inductive Immediate where
  | i8 (bits : BitVec 8)
  | i32 (bits : BitVec 32)
deriving DecidableEq, Repr

/-- Interpret the raw immediate bits as a signed value. -/
def Immediate.toInt : Immediate → Int
  | .i8 bits => bits.toInt
  | .i32 bits => bits.toInt

private def Immediate.isa : Immediate → Grass.ISA.X86.Immediate
  | .i8 bits => .i8 bits
  | .i32 bits => .i32 bits

/-- Its size is the size of the ISA immediate that the encoder emits. -/
def Immediate.size (immediate : Immediate) : Nat := immediate.isa.size

private def Kind.extension : Kind → BitVec 3
  | .sub => 5
  | .cmp => 7

private def Immediate.opcode : Immediate → Byte
  | .i8 _ => 0x83
  | .i32 _ => 0x81

/-- Encode a register-direct Group 1 operation without choosing or truncating a value. -/
def encode (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (immediate : Immediate) : InsnEncoding :=
  let w := BasicInstructions.Width.rexW width
  { rex := if w || reg.rexBit then some (Rex.of w false false reg.rexBit) else none
    escape := false
    opcode := immediate.opcode
    modrm := some ⟨ModRm.modRegisterDirect, kind.extension, reg.encodingBits⟩
    sib := none
    disp := .none
    imm := immediate.isa }

@[simp] theorem Immediate.toInt_i8 (bits : BitVec 8) :
    (Immediate.i8 bits).toInt = bits.toInt := rfl

@[simp] theorem Immediate.toInt_i32 (bits : BitVec 32) :
    (Immediate.i32 bits).toInt = bits.toInt := rfl

@[simp] theorem encode_imm_i8 (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (bits : BitVec 8) :
    (encode kind width reg (.i8 bits)).imm = .i8 bits := rfl

@[simp] theorem encode_imm_i32 (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (bits : BitVec 32) :
    (encode kind width reg (.i32 bits)).imm = .i32 bits := rfl

@[simp] theorem encode_opcode_i8 (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (bits : BitVec 8) : (encode kind width reg (.i8 bits)).opcode = 0x83 := rfl

@[simp] theorem encode_opcode_i32 (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (bits : BitVec 32) : (encode kind width reg (.i32 bits)).opcode = 0x81 := rfl

theorem encode_modrm (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (immediate : Immediate) :
    (encode kind width reg immediate).modrm =
      some ⟨ModRm.modRegisterDirect, kind.extension, reg.encodingBits⟩ := rfl

theorem encode_rex (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (immediate : Immediate) :
    (encode kind width reg immediate).rex =
      if BasicInstructions.Width.rexW width || reg.rexBit then
        some (Rex.of (BasicInstructions.Width.rexW width) false false reg.rexBit) else none := rfl

theorem encode_wellFormed (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (immediate : Immediate) : (encode kind width reg immediate).WellFormed := by
  simp [encode, InsnEncoding.WellFormed, dispKindFor]
  simp [ModRm.modRegisterDirect, ModRm.modDisp8, ModRm.modDisp32,
    ModRm.modNoDisplacement]
  rfl

/-- The byte width is derived from REX presence and the typed immediate width. -/
theorem encode_size (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (immediate : Immediate) :
    (encode kind width reg immediate).size =
      (if BasicInstructions.Width.rexW width || reg.rexBit then 1 else 0) + 2 + immediate.size := by
  cases width <;> cases reg <;> cases immediate <;> rfl

/-- Every admitted constructor round-trips through the existing decoder table. -/
theorem decode_encode (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (immediate : Immediate) (rest : ByteSeq) :
    decodeInsn ((encode kind width reg immediate).toBytes ++ rest) =
      .ok (encode kind width reg immediate, rest) := by
  cases immediate with
  | i8 bits =>
    apply decodeInsn_toBytes (s :=
      { escape := false, opcode := 0x83, hasModrm := true, immSize := .i8,
        mnemonic := "group1 r/m, imm8" })
    · rfl
    · simp [MatchesSpec, encode, Immediate.opcode, Immediate.isa,
        OpcodeSpec.immSizeFor, Immediate.sizeOf]
    · exact encode_wellFormed kind width reg (.i8 bits)
  | i32 bits =>
    apply decodeInsn_toBytes (s :=
      { escape := false, opcode := 0x81, hasModrm := true, immSize := .i32,
        mnemonic := "group1 r/m, imm32" })
    · rfl
    · simp [MatchesSpec, encode, Immediate.opcode, Immediate.isa,
        OpcodeSpec.immSizeFor, Immediate.sizeOf]
    · exact encode_wellFormed kind width reg (.i32 bits)

end Grass.ISA.X86.ImmediateArithmetic
