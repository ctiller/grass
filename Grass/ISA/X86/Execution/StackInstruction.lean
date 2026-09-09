import Grass.ISA.X86.Execution.DecodedSite
import Grass.ISA.X86.ImmediateArithmetic

/-!
# Selected stack-instruction encodings

This module recognizes the existing production encodings for `PUSH r64` and
`SUB RSP, imm`. It selects a canonical instruction description from a decoded
encoding, but does not execute it: no stack pointer, memory, flags, or fault
transfer is asserted here.
-/

namespace Grass.ISA.X86.Execution

open Grass.ISA.X86 Grass.Std.Logical

/-- The bounded instruction family used by the current stack-shaped code. -/
inductive StackInstruction where
  | push (register : Gpr)
  | subRsp (immediate : ImmediateArithmetic.Immediate)
deriving DecidableEq, Repr

namespace StackInstruction

/-- Reuse the production encoders rather than maintain a second opcode table. -/
def encoding : StackInstruction → InsnEncoding
  | .push register => BasicInstructions.push register
  | .subRsp immediate => ImmediateArithmetic.encode .sub .w64 .rsp immediate

/-- A selected description carries its exact production encoding equality. -/
structure Selection (encoding : InsnEncoding) where
  instruction : StackInstruction
  encoding_eq : instruction.encoding = encoding

/-- Search the finite architectural register set for the one production PUSH
encoding equal to the decoded encoding. -/
private def selectPush : List Gpr → (encoding : InsnEncoding) → Option (Selection encoding)
  | [], _ => none
  | register :: remaining, encoding =>
      if h : (.push register : StackInstruction).encoding = encoding then
        some ⟨.push register, h⟩
      else selectPush remaining encoding

/-- Recover a typed immediate only from the decoder's immediate field, then
compare the complete production encoding. -/
private def selectSubRsp (encoding : InsnEncoding) : Option (Selection encoding) :=
  match encoding.imm with
  | .i8 bits =>
      if h : (.subRsp (.i8 bits) : StackInstruction).encoding = encoding then
        some ⟨.subRsp (.i8 bits), h⟩
      else none
  | .i32 bits =>
      if h : (.subRsp (.i32 bits) : StackInstruction).encoding = encoding then
        some ⟨.subRsp (.i32 bits), h⟩
      else none
  | .none | .i64 _ => none

/-- Select only a byte encoding that exactly equals one production constructor. -/
def select (encoding : InsnEncoding) : Option (Selection encoding) :=
  match selectSubRsp encoding with
  | some selected => some selected
  | none => selectPush Gpr.all encoding

/-- A selected instruction is sound by the equality retained in its witness. -/
theorem Selection.encoding_sound {encoding : InsnEncoding} (selected : Selection encoding) :
    selected.instruction.encoding = encoding := selected.encoding_eq

/-- Every production PUSH encoding is selected, including volatile registers
and `rsp`; saved-register policy belongs to a later source adapter. -/
theorem select_push_complete (register : Gpr) :
    (select (.push register : StackInstruction).encoding).map (·.instruction) =
      some (.push register) := by
  cases register <;> decide

/-- Every production 64-bit `SUB RSP, imm8/imm32` encoding is selected. -/
theorem select_subRsp_complete (immediate : ImmediateArithmetic.Immediate) :
    (select (.subRsp immediate : StackInstruction).encoding).map (·.instruction) =
      some (.subRsp immediate) := by
  cases immediate with
  | i8 bits =>
    change (select (ImmediateArithmetic.encode .sub .w64 .rsp (.i8 bits))).map (·.instruction) =
      some (.subRsp (.i8 bits))
    unfold select
    unfold selectSubRsp
    rw [ImmediateArithmetic.encode_imm_i8]
    simp [StackInstruction.encoding]
  | i32 bits =>
    change (select (ImmediateArithmetic.encode .sub .w64 .rsp (.i32 bits))).map (·.instruction) =
      some (.subRsp (.i32 bits))
    unfold select
    unfold selectSubRsp
    rw [ImmediateArithmetic.encode_imm_i32]
    simp [StackInstruction.encoding]

/-- A selected decoding retains the checked original site, including its RIP,
bytes, decoder result, and next-PC certificate. -/
structure Decoded (rip : BitVec 64) (bytes : ByteSeq) where
  site : DecodedSite rip bytes
  selection : Selection site.encoding

/-- Check the observed byte sequence first, then select this bounded family. -/
def decode (rip : BitVec 64) (bytes : ByteSeq) : Except DecodedSite.Error (Option (Decoded rip bytes)) :=
  match DecodedSite.check rip bytes with
  | .error error => .error error
  | .ok site =>
      match select site.encoding with
      | none => .ok none
      | some selection => .ok (some ⟨site, selection⟩)

/-- The selected instruction is exactly what the common decoder read from the
observed bytes, and `rest` is that decoder's exact unconsumed suffix. -/
theorem Decoded.decoder_exact {rip : BitVec 64} {bytes : ByteSeq}
    (decoded : Decoded rip bytes) :
    decodeInsn bytes = .ok (decoded.selection.instruction.encoding, decoded.site.rest) := by
  rw [decoded.selection.encoding_eq]
  exact decoded.site.decoded

end StackInstruction
end Grass.ISA.X86.Execution
