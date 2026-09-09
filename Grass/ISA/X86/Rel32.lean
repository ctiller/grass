import Grass.ISA.X86.EncodingTemplate

/-! Fixed-width encodings for the modeled near relative branches. -/
namespace Grass.ISA.X86.Rel32

open Grass.ISA.X86 Grass.Std.Logical

inductive Kind where
  | jump
  | equal
  | above
deriving DecidableEq, Repr

/-- Encode a raw rel32 bit pattern. This constructor assigns no target-address
semantics to the immediate; address resolution belongs to the assembly layer. -/
def encode (kind : Kind) (bits : BitVec 32) : InsnEncoding :=
  { rex := none
    escape := match kind with | .jump => false | .equal | .above => true
    opcode := match kind with | .jump => 0xE9 | .equal => 0x84 | .above => 0x87
    modrm := none
    sib := none
    disp := .none
    imm := .i32 bits }

/-- The encoded size, computed from the same constructor that emits bytes. -/
def encodedSize (kind : Kind) : Nat := (encode kind 0).size

@[simp] theorem encode_imm (kind : Kind) (bits : BitVec 32) :
    (encode kind bits).imm = .i32 bits := rfl

theorem encode_wellFormed (kind : Kind) (bits : BitVec 32) :
    (encode kind bits).WellFormed := by
  cases kind <;> simp [encode, InsnEncoding.WellFormed]

theorem size_eq (kind : Kind) (bits : BitVec 32) :
    (encode kind bits).size = encodedSize kind := by
  cases kind <;> rfl

@[simp] theorem encodedSize_jump : encodedSize .jump = 5 := rfl
@[simp] theorem encodedSize_equal : encodedSize .equal = 6 := rfl
@[simp] theorem encodedSize_above : encodedSize .above = 6 := rfl

private theorem operandSpec_present (operand : Kind × BitVec 32) :
    (findSpec (encode operand.1 operand.2).escape (encode operand.1 operand.2).opcode).isSome := by
  cases operand with | mk kind bits => cases kind <;> rfl

private def operandSpec (operand : Kind × BitVec 32) : OpcodeSpec :=
  (findSpec (encode operand.1 operand.2).escape (encode operand.1 operand.2).opcode).get
    (operandSpec_present operand)

private theorem operandSpec_jump (bits : BitVec 32) :
    operandSpec (.jump, bits) =
      { escape := false, opcode := 0xE9, hasModrm := false, immSize := .i32,
        mnemonic := "jmp rel32" } := rfl

private theorem operandSpec_equal (bits : BitVec 32) :
    operandSpec (.equal, bits) =
      { escape := true, opcode := 0x84, hasModrm := false, immSize := .i32,
        mnemonic := "jz rel32" } := rfl

private theorem operandSpec_above (bits : BitVec 32) :
    operandSpec (.above, bits) =
      { escape := true, opcode := 0x87, hasModrm := false, immSize := .i32,
        mnemonic := "ja rel32" } := rfl

private def template : EncodingTemplate (Kind × BitVec 32) where
  encode operand := encode operand.1 operand.2
  spec := operandSpec
  registered operand := by cases operand with | mk kind bits => cases kind <;> rfl
  matchesSpec operand := by
    cases operand with
    | mk kind bits =>
      cases kind <;> simp [MatchesSpec, operandSpec_jump, operandSpec_equal,
        operandSpec_above, encode, OpcodeSpec.immSizeFor, Immediate.sizeOf]
  wellFormed operand := encode_wellFormed operand.1 operand.2

theorem decode_encode (kind : Kind) (bits : BitVec 32) (rest : ByteSeq) :
    decodeInsn ((encode kind bits).toBytes ++ rest) = .ok (encode kind bits, rest) :=
  EncodingTemplate.decode_encode template (kind, bits) rest

end Grass.ISA.X86.Rel32
