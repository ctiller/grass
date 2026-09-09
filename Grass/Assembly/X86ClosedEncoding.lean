import Grass.Assembly.X86Source
import Grass.ISA.X86.BasicInstructions

/-! Encoding for source instructions whose operands are already fully closed. -/
namespace Grass.Assembly.X86ClosedEncoding
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

open Grass.ISA.X86
open Grass.ISA.X86.BasicInstructions
open Grass.Std.Logical
open Grass.Assembly.X86Source

private def sameWidth (a b : Register) : Bool := a.width = b.width

private inductive Closed where
  | push (reg : Gpr)
  | movReg (width : BasicInstructions.Width) (dst src : Gpr)
  | movImm32 (reg : Gpr) (value : BitVec 32)
  | movImm64 (reg : Gpr) (value : BitVec 64)
  | test (width : BasicInstructions.Width) (left right : Gpr)
  | cmp (width : BasicInstructions.Width) (left right : Gpr)
  | add (width : BasicInstructions.Width) (left right : Gpr)
  | sub (width : BasicInstructions.Width) (left right : Gpr)
  | xor (width : BasicInstructions.Width) (left right : Gpr)
  | ud2

private def select : Instruction → Option Closed
  | ⟨.push, [.register ⟨reg,.w64⟩]⟩ => some (.push reg)
  | ⟨.mov, [.register dst,.register src]⟩ =>
      if sameWidth dst src then some (.movReg dst.width dst.gpr src.gpr) else none
  | ⟨.mov, [.register ⟨reg,.w32⟩,.immediate value]⟩ =>
      if value < 2^32 then some (.movImm32 reg (BitVec.ofNat 32 value)) else none
  | ⟨.mov, [.register ⟨reg,.w64⟩,.immediate value]⟩ =>
      if value < 2^64 then some (.movImm64 reg (BitVec.ofNat 64 value)) else none
  | ⟨.test, [.register left,.register right]⟩ =>
      if sameWidth left right then some (.test left.width left.gpr right.gpr) else none
  | ⟨.cmp, [.register left,.register right]⟩ =>
      if sameWidth left right then some (.cmp left.width left.gpr right.gpr) else none
  | ⟨.add, [.register left,.register right]⟩ =>
      if sameWidth left right then some (.add left.width left.gpr right.gpr) else none
  | ⟨.sub, [.register left,.register right]⟩ =>
      if sameWidth left right then some (.sub left.width left.gpr right.gpr) else none
  | ⟨.xor, [.register left,.register right]⟩ =>
      if sameWidth left right then some (.xor left.width left.gpr right.gpr) else none
  | ⟨.ud2, []⟩ => some .ud2
  | _ => none

private def Closed.encoding : Closed → InsnEncoding
  | .push reg => BasicInstructions.push reg
  | .movReg width dst src => movRegReg width dst src
  | .movImm32 reg value => movRegImm32 reg value
  | .movImm64 reg value => movRegImm64 reg value
  | .test width left right => testRegReg width left right
  | .cmp width left right => cmpRegReg width left right
  | .add width left right => addRegReg width left right
  | .sub width left right => subRegReg width left right
  | .xor width left right => xorRegReg width left right
  | .ud2 => BasicInstructions.ud2

def encode (source : Instruction) : Option InsnEncoding := (select source).map Closed.encoding

private theorem movImm32_decodes (reg : Gpr) (value : BitVec 32) (rest : ByteSeq) :
    decodeInsn ((movRegImm32 reg value).toBytes ++ rest) =
      .ok (movRegImm32 reg value, rest) := by
  let spec : OpcodeSpec :=
    { escape := false
      opcode := (movRegImm32 reg value).opcode
      hasModrm := false
      immSize := .i32
      immPromotedByRexW := true
      mnemonic := "mov r32, imm32 / r64, imm64+rd" }
  apply decodeInsn_toBytes (s := spec)
  · cases reg <;> rfl
  · cases reg <;> simp [MatchesSpec, spec, movRegImm32, OpcodeSpec.immSizeFor,
      rexWSet, Gpr.rexBit, Gpr.isExtended, Gpr.index, Rex.of, Immediate.sizeOf] <;>
      decide +kernel
  · exact movRegImm32_wellFormed reg value

private theorem movImm64_decodes (reg : Gpr) (value : BitVec 64) (rest : ByteSeq) :
    decodeInsn ((movRegImm64 reg value).toBytes ++ rest) =
      .ok (movRegImm64 reg value, rest) := by
  let spec : OpcodeSpec :=
    { escape := false
      opcode := (movRegImm64 reg value).opcode
      hasModrm := false
      immSize := .i32
      immPromotedByRexW := true
      mnemonic := "mov r32, imm32 / r64, imm64+rd" }
  apply decodeInsn_toBytes (s := spec)
  · cases reg <;> rfl
  · cases reg <;> simp [MatchesSpec, spec, movRegImm64, OpcodeSpec.immSizeFor,
      rexWSet, Gpr.rexBit, Gpr.isExtended, Gpr.index, Rex.of, Immediate.sizeOf] <;>
      decide +kernel
  · exact movRegImm64_wellFormed reg value

theorem encode_decodes {source : Instruction} {encoded : InsnEncoding}
    (success : encode source = some encoded) (rest : ByteSeq) :
    decodeInsn (encoded.toBytes ++ rest) = .ok (encoded, rest) := by
  unfold encode at success
  cases h : select source with
  | none => simp [h] at success
  | some closed =>
    simp [h] at success
    subst encoded
    cases closed with
    | push reg => simpa [Closed.encoding] using push_decodes reg rest
    | movReg width dst src => simpa [Closed.encoding] using movRegReg_decodes width dst src rest
    | movImm32 reg value => simpa [Closed.encoding] using movImm32_decodes reg value rest
    | movImm64 reg value => simpa [Closed.encoding] using movImm64_decodes reg value rest
    | test width left right => simpa [Closed.encoding] using testRegReg_decodes width left right rest
    | cmp width left right => simpa [Closed.encoding] using cmpRegReg_decodes width left right rest
    | add width left right => simpa [Closed.encoding] using addRegReg_decodes width left right rest
    | sub width left right => simpa [Closed.encoding] using subRegReg_decodes width left right rest
    | xor width left right => simpa [Closed.encoding] using xorRegReg_decodes width left right rest
    | ud2 => simpa [Closed.encoding] using ud2_decodes rest

end Grass.Assembly.X86ClosedEncoding
