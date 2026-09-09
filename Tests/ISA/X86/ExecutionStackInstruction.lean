import Grass.ISA.X86.Execution.StackInstruction

namespace Grass.Tests.ISA.X86.Execution.StackInstruction

open Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Std.Logical

private def accepted {α β : Type} : Except α (Option β) → Bool
  | .ok (some _) => true
  | _ => false

-- PUSH recognition covers the complete production GPR family, not just saved
-- registers chosen by one source-level calling convention.
example : accepted (StackInstruction.decode 0x1000 [0x41, 0x54]) = true := by decide
example : accepted (StackInstruction.decode 0x1000 [0x41, 0x55]) = true := by decide
example : accepted (StackInstruction.decode 0x1000 [0x41, 0x56]) = true := by decide

-- Both typed immediate forms of production SUB RSP are accepted.
example : accepted (StackInstruction.decode 0x1000 [0x48, 0x83, 0xEC, 48]) = true := by decide
example : accepted (StackInstruction.decode 0x1000 [0x48, 0x81, 0xEC, 0x30, 0, 0, 0]) = true := by decide

-- The shared byte decoder may parse these, but this selector refuses encodings
-- outside the exact PUSH r64 / SUB RSP, imm family.
example : accepted (StackInstruction.decode 0x1000 [0x48, 0x83, 0xFC, 48]) = false := by decide
example : accepted (StackInstruction.decode 0x1000 [0x48, 0x83, 0xEB, 48]) = false := by decide
example : accepted (StackInstruction.decode 0x1000 [0x83, 0xEC, 48]) = false := by decide
example : accepted (StackInstruction.decode 0x1000 [0x48, 0x89, 0xC0]) = false := by decide
example : accepted (StackInstruction.decode 0x1000 [0x90]) = false := by decide

end Grass.Tests.ISA.X86.Execution.StackInstruction
