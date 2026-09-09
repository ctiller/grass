import Grass.ISA.X86.RegisterSemantics

/-!
A bounded semantic decoder for the canonical register-direct encodings in
`RegisterSemantics`.

`decodeInsn` remains the byte-stream authority.  This module only gives a
semantic name to an encoding that decoder has already accepted.  It first
reconstructs the operand width and registers from REX and ModR/M fields, then
checks the six public `RegisterSemantics.Instruction.encoding` candidates.
Consequently there is no second opcode table here.  The equality check also
deliberately rejects legal x86 aliases and redundant-prefix spellings that the
canonical encoders do not produce.
-/
namespace Grass.ISA.X86.RegisterDecode

open Grass.ISA.X86 Grass.Std.Logical
open Grass.ISA.X86.RegisterSemantics

/-- The operand information common to the six supported semantic operations. -/
structure Operands where
  width : BasicInstructions.Width
  destination : Gpr
  source : Gpr
deriving DecidableEq, Repr

private def rexW : Option Rex → BitVec 1
  | some rex => rex.w
  | Option.none => 0

private def rexR : Option Rex → BitVec 1
  | some rex => rex.r
  | Option.none => 0

private def rexB : Option Rex → BitVec 1
  | some rex => rex.b
  | Option.none => 0

/--
Recover the register-direct operands carried by an encoding.  This reads only
REX and ModR/M; operation recognition is left to `select` below.
-/
def reconstruct (encoding : InsnEncoding) : Option Operands :=
  match encoding.modrm with
  | Option.none => Option.none
  | some modrm =>
      if modrm.mod = ModRm.modRegisterDirect then
        some
          { width := if rexW encoding.rex = 1 then .w64 else .w32
            destination := Gpr.ofBits (rexB encoding.rex) modrm.rm
            source := Gpr.ofBits (rexR encoding.rex) modrm.reg }
      else Option.none

/-- A semantic instruction together with the checked canonical encoding tie. -/
structure Selection (encoding : InsnEncoding) where
  instruction : RegisterSemantics.Instruction
  encoding_eq : instruction.encoding = encoding

private def selectKinds (encoding : InsnEncoding) (operands : Operands) :
    List Kind → Option (Selection encoding)
  | [] => Option.none
  | kind :: kinds =>
      let instruction : RegisterSemantics.Instruction :=
        { kind := kind
          width := operands.width
          destination := operands.destination
          source := operands.source }
      if h : instruction.encoding = encoding then
        some ⟨instruction, h⟩
      else selectKinds encoding operands kinds

/--
Recognize one of the six semantic instructions by equality with its public
encoder.  The list is a semantic-family enumeration, not an opcode table.
-/
def select (encoding : InsnEncoding) : Option (Selection encoding) := do
  let operands ← reconstruct encoding
  selectKinds encoding operands [.mov, .add, .sub, .cmp, .test, .xor]

/-- Failure before semantic selection, or an accepted but unsupported encoding. -/
inductive Error where
  | decode (error : DecodeError)
  | unsupported (encoding : InsnEncoding)
deriving DecidableEq, Repr

/--
A successful semantic decode.  Its proof field ties the selected instruction
to `encoding`; `decode_ok_decodeInsn` ties every successful wrapper call to the
exact suffix emitted by `decodeInsn`.
-/
structure Result where
  instruction : RegisterSemantics.Instruction
  encoding : InsnEncoding
  rest : ByteSeq
  encoding_eq : instruction.encoding = encoding

/-- Decode one instruction and attach semantics only to a canonical supported form. -/
def decode (bytes : ByteSeq) : Except Error Result :=
  match decodeInsn bytes with
  | .error error => .error (.decode error)
  | .ok (encoding, rest) =>
      match select encoding with
      | Option.none => .error (.unsupported encoding)
      | some selected =>
          .ok
            { instruction := selected.instruction
              encoding := encoding
              rest := rest
              encoding_eq := selected.encoding_eq }

/-- A successful wrapper result retains the exact suffix emitted by `decodeInsn`. -/
theorem decode_ok_decodeInsn {bytes : ByteSeq} {result : Result}
    (h : decode bytes = .ok result) :
    decodeInsn bytes = .ok (result.instruction.encoding, result.rest) := by
  cases hdecode : decodeInsn bytes with
  | error error => simp [decode, hdecode] at h
  | ok pair =>
      obtain ⟨encoding, rest⟩ := pair
      cases hselect : select encoding with
      | none => simp [decode, hdecode, hselect] at h
      | some selected =>
          simp [decode, hdecode, hselect] at h
          subst result
          rw [selected.encoding_eq]

/-- The semantic effect is the effect of the same instruction tied to the bytes. -/
def Result.effect (result : Result)
    (registers : Gpr → BitVec 64) (flags : Flags Bool) : Effect :=
  result.instruction.effect registers flags

theorem Result.effect_eq (result : Result)
    (registers : Gpr → BitVec 64) (flags : Flags Bool) :
    result.effect registers flags =
      evaluate result.instruction.kind result.instruction.width
        (registers result.instruction.destination)
        (registers result.instruction.source) flags := rfl

/-- A production decoding failure is preserved, with no semantic guess. -/
theorem decode_error {bytes : ByteSeq} {error : DecodeError}
    (h : decodeInsn bytes = .error error) :
    decode bytes = .error (.decode error) := by
  simp [decode, h]

/-- An accepted encoding outside the canonical semantic family is explicit. -/
theorem decode_unsupported {bytes rest : ByteSeq} {encoding : InsnEncoding}
    (hdecode : decodeInsn bytes = .ok (encoding, rest))
    (hselect : select encoding = Option.none) :
    decode bytes = .error (.unsupported encoding) := by
  simp [decode, hdecode, hselect]

end Grass.ISA.X86.RegisterDecode
