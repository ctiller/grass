import Grass.ISA.X86.Execution.StackInstruction
import Grass.ISA.X86.Execution.MemoryMoveSelection
import Grass.ISA.X86.Execution.MoveSelection
import Grass.ISA.X86.Execution.ArithmeticNormal
import Grass.ISA.X86.Execution.BranchNormal
import Grass.ISA.X86.Execution.LeaNormal

/-!
# Fixed canonical instruction classification

The alternatives are semantic families with existing production encoders, not
another opcode table or a handwritten Hello sequence. Classification does not
certify an instruction outcome. In particular, recognizing CALL or UD2 supplies
neither a normal CALL receipt nor an invalid-opcode fault receipt. Memory MOV
classification delegates to the source-free memory adapter.
-/

namespace Grass.ISA.X86.Execution

/-- Canonical forms currently named by the CPU dispatcher. -/
inductive Instruction where
  | stack (instruction : StackInstruction)
  | move (instruction : MoveInstruction)
  | memoryMove (instruction : MemoryMoveNormal.Instruction)
  | arithmetic (instruction : ArithmeticInstruction)
  | branch (instruction : BranchInstruction)
  | lea (instruction : LeaInstruction)
  | callRip (displacement : BitVec 32)
  | ud2
deriving DecidableEq, Repr

namespace Instruction

/-- `encoding?` delegates each family to its existing production encoder. -/
def encoding? : Instruction → Option InsnEncoding
  | .stack instruction => some instruction.encoding
  | .move instruction => some instruction.encoding
  | .memoryMove instruction => instruction.encode?
  | .arithmetic instruction => some instruction.encoding
  | .branch instruction => some instruction.encoding
  | .lea instruction => instruction.encoding?
  | .callRip displacement => callMem64 (.ripRelative displacement)
  | .ud2 => some BasicInstructions.ud2

structure Selection (encoding : InsnEncoding) where
  instruction : Instruction
  encoding_eq : instruction.encoding? = some encoding

private def accept (encoding : InsnEncoding) (instruction : Instruction) :
    Option (Selection encoding) :=
  if same : instruction.encoding? = some encoding then some ⟨instruction, same⟩ else none

private def selectControl (encoding : InsnEncoding) : Option (Selection encoding) :=
  match encoding.disp with
  | .d32 displacement =>
      match accept encoding (.callRip displacement) with
      | some selected => some selected
      | none => accept encoding .ud2
  | _ => accept encoding .ud2

/-- `select` uses fixed family priority and retains whole-encoding equality. -/
def select (encoding : InsnEncoding) : Option (Selection encoding) :=
  match StackInstruction.select encoding with
  | some selected => some ⟨.stack selected.instruction, congrArg some selected.encoding_eq⟩
  | none =>
    match MoveInstruction.select encoding with
    | some selected => some ⟨.move selected.instruction, congrArg some selected.encoding_eq⟩
    | none =>
      match ArithmeticInstruction.select encoding with
      | some selected => some ⟨.arithmetic selected.instruction, congrArg some selected.encoding_eq⟩
      | none =>
        match BranchInstruction.select encoding with
        | some selected => some ⟨.branch selected.instruction, congrArg some selected.encoding_eq⟩
        | none =>
          match selected : LeaInstruction.select encoding with
          | some instruction => some ⟨.lea instruction, LeaInstruction.select_sound selected⟩
          | none =>
            match MemoryMoveSelection.select encoding with
            | some selected => some ⟨.memoryMove selected.instruction,
                MemoryMoveSelection.encoding_sound selected⟩
            | none => selectControl encoding

theorem Selection.encoding_sound {encoding : InsnEncoding} (selection : Selection encoding) :
    selection.instruction.encoding? = some encoding := selection.encoding_eq

end Instruction
end Grass.ISA.X86.Execution
