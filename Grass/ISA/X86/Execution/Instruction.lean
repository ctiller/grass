import Grass.ISA.X86.Execution.StackInstruction
import Grass.ISA.X86.Execution.MemoryMoveSelection
import Grass.ISA.X86.Execution.MoveSelection
import Grass.ISA.X86.Execution.ArithmeticNormal
import Grass.ISA.X86.Execution.BranchNormal
import Grass.ISA.X86.Execution.LeaNormal
import Grass.ISA.X86.SyscallEncoding

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
  | syscall
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
  | .syscall => some SyscallEncoding.encoding
  | .ud2 => some BasicInstructions.ud2

structure Selection (encoding : InsnEncoding) where
  instruction : Instruction
  encoding_eq : instruction.encoding? = some encoding

private def accept (encoding : InsnEncoding) (instruction : Instruction) :
    Option (Selection encoding) :=
  if same : instruction.encoding? = some encoding then some ⟨instruction, same⟩ else none

private def selectControl (encoding : InsnEncoding) : Option (Selection encoding) :=
  match accept encoding .syscall with
  | some selected => some selected
  | none =>
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

private theorem stack_encoding_ne_branch (stack : StackInstruction) (branch : BranchInstruction) : stack.encoding ≠ branch.encoding := by
  intro h
  cases stack with
  | push reg =>
    have hi := congrArg InsnEncoding.imm h
    cases branch <;> simp [StackInstruction.encoding, BasicInstructions.push,
      BranchInstruction.encoding, BranchInstruction.kind, BranchInstruction.displacement, Rel32.encode] at hi
  | subRsp imm =>
    have hm := congrArg InsnEncoding.modrm h
    cases imm <;> cases branch <;> simp [StackInstruction.encoding, ImmediateArithmetic.encode,
      BranchInstruction.encoding, BranchInstruction.kind, BranchInstruction.displacement, Rel32.encode] at hm
private theorem move_encoding_ne_branch (move : MoveInstruction) (branch : BranchInstruction) : move.encoding ≠ branch.encoding := by
  intro h
  cases move with
  | regReg width dst src =>
    have hm := congrArg InsnEncoding.modrm h
    have hp : ((MoveInstruction.regReg width dst src).encoding.modrm).isSome = true := by cases width <;> rfl
    rw [h] at hp
    cases branch <;> contradiction
  | imm32 dst bits =>
    have ho := congrArg InsnEncoding.opcode h
    cases dst <;> cases branch <;> simp [MoveInstruction.encoding, movRegImm32, Gpr.encodingBits,
      BranchInstruction.encoding, BranchInstruction.kind, BranchInstruction.displacement, Rel32.encode] at ho
private theorem arithmetic_encoding_ne_branch (arith : ArithmeticInstruction) (branch : BranchInstruction) : arith.encoding ≠ branch.encoding := by
  intro h
  have hp : arith.encoding.modrm.isSome = true := by
    cases arith <;> rfl
  rw [h] at hp
  cases branch <;> contradiction

/-- `select_branch_complete` proves that fixed family priority retains every
production branch constructor and its entire displacement. -/
theorem select_branch_complete (branch : BranchInstruction) :
    (select branch.encoding).map (·.instruction) = some (.branch branch) := by
  have stack : StackInstruction.select branch.encoding = none := by
    cases selected : StackInstruction.select branch.encoding with
    | none => rfl
    | some receipt =>
      exact False.elim (stack_encoding_ne_branch receipt.instruction branch receipt.encoding_eq)
  have move : MoveInstruction.select branch.encoding = none := by
    cases selected : MoveInstruction.select branch.encoding with
    | none => rfl
    | some receipt =>
      exact False.elim (move_encoding_ne_branch receipt.instruction branch receipt.encoding_eq)
  have arithmetic : ArithmeticInstruction.select branch.encoding = none := by
    cases selected : ArithmeticInstruction.select branch.encoding with
    | none => rfl
    | some receipt =>
      exact False.elim (arithmetic_encoding_ne_branch receipt.instruction branch receipt.encoding_eq)
  have complete := BranchInstruction.select_complete branch
  cases selected : BranchInstruction.select branch.encoding with
  | none => simp [selected] at complete
  | some receipt =>
    have instruction : receipt.instruction = branch := by simpa [selected] using complete
    simp only [select, stack, move, arithmetic, selected, instruction, Option.map_some]

/-- `select_branch` exposes the actual canonical selection retained by `select`. -/
theorem select_branch (branch : BranchInstruction) :
    ∃ selection, select branch.encoding = some selection ∧
      selection.instruction = .branch branch := by
  simpa only [Option.map_eq_some_iff] using select_branch_complete branch

end Instruction
end Grass.ISA.X86.Execution
