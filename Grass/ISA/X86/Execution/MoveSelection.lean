import Grass.ISA.X86.Execution.MoveNormal
import Grass.ISA.X86.RegisterDecode

/-! Canonical MOV selection for fixed CPU dispatch. Operand reconstruction is
followed by equality with the production encoder; no opcode table is added. -/

namespace Grass.ISA.X86.Execution.MoveInstruction

structure Selection (encoding : InsnEncoding) where
  instruction : MoveInstruction
  encoding_eq : instruction.encoding = encoding

private def selectImmediate (encoding : InsnEncoding) : Option (Selection encoding) :=
  match encoding.imm with
  | .i32 value =>
      let high := match encoding.rex with | some rex => rex.b | none => 0
      let destination := Gpr.ofBits high (BitVec.extractLsb' 0 3 encoding.opcode)
      let instruction := MoveInstruction.imm32 destination value
      if same : instruction.encoding = encoding then some ⟨instruction, same⟩ else none
  | _ => none

/-- `Selection.encoding_eq` binds a selected MOV to its complete canonical encoding. -/
def select (encoding : InsnEncoding) : Option (Selection encoding) :=
  match RegisterDecode.reconstruct encoding with
  | some operands =>
      let instruction := MoveInstruction.regReg operands.width operands.destination operands.source
      if same : instruction.encoding = encoding then some ⟨instruction, same⟩
      else selectImmediate encoding
  | none => selectImmediate encoding

theorem Selection.encoding_sound {encoding : InsnEncoding} (selection : Selection encoding) :
    selection.instruction.encoding = encoding := selection.encoding_eq

end Grass.ISA.X86.Execution.MoveInstruction
