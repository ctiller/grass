import Grass.Assembly.X86BranchLayout
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.X86BranchLayout

open Grass.Assembly SourceInput X86Source X86ControlFlow X86BranchLayout

def wrap (body : List Char) : List Char :=
  (source_chars "def helloSource := asm_source {\n") ++ body ++ (source_chars "\n}")

def layoutChars? (chars : List Char) : Option Result := do
  let body ← (extractHelloSourceChars chars).toOption
  let statements ← (parseBody body).toOption
  let checked ← check? statements
  layout? checked

def closedBranches : List Char := wrap (source_chars
  "entry:\nmov rax, rbx\njz forward\nback:\nxor eax, eax\njmp entry\nforward:\nja back\nud2")

def branchCoordinates (result : Result) : List (Nat × Nat × Nat) :=
  result.outputs.filterMap fun output => output.branchOrigin?.map fun branch =>
    (branch.sourceIndex, branch.sourceOffset, branch.targetOffset)

example : (layoutChars? closedBranches).map branchCoordinates =
    some [(1, 3, 16), (3, 11, 0), (4, 16, 9)] := by decide +kernel

-- Changing the first instruction from a 64-bit to a shorter 32-bit form shifts
-- every later byte position. The lowerer receives only source; these numeric
-- tuples are regression expectations for its computed result.
def shorterPrefix : List Char := wrap (source_chars
  "entry:\nmov eax, ebx\njz forward\nback:\nxor eax, eax\njmp entry\nforward:\nja back\nud2")

example : (layoutChars? shorterPrefix).map branchCoordinates =
    some [(1, 2, 15), (3, 10, 0), (4, 15, 8)] := by decide +kernel

example : layoutChars? (wrap (source_chars "jmp missing\nud2")) = none := by decide +kernel

-- Each pending family fails independently, rather than being masked by another
-- unsupported operand earlier in the complete authored program.
example : layoutChars? (wrap (source_chars
  "call qword ptr [rip + __imp_WriteFile]\nud2")) = none := by decide +kernel
example : layoutChars? (wrap (source_chars
  "mov transferred, 0\nud2")) = none := by decide +kernel
example : layoutChars? (wrap (source_chars
  "lea r13, [rip + payload]\nud2")) = none := by decide +kernel
example : layoutChars? (wrap (source_chars
  "mov ecx, STD_OUTPUT_HANDLE\nud2")) = none := by decide +kernel
example : layoutChars? (wrap (source_chars
  "mov r14d, sizeof(payload)\nud2")) = none := by decide +kernel
example : layoutChars? (wrap (source_chars
  "lea r9, transferred.addr\nud2")) = none := by decide +kernel
example : layoutChars? (wrap (source_chars
  "arg WriteFile.overlapped, 0\nud2")) = none := by decide +kernel

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

/-- The unchanged Spike still contains symbolic slots, addresses, and an
external call, so this closed/local-branch layer refuses the whole program. -/
example : layoutChars? authored = none := by decide +kernel

theorem every_emitted_instruction_decodes (result : Result) (encoding : Grass.ISA.X86.InsnEncoding)
    (member : encoding ∈ result.encodings) (rest : Grass.Std.Logical.ByteSeq) :
    Grass.ISA.X86.decodeInsn (encoding.toBytes ++ rest) = .ok (encoding, rest) :=
  result.every_encoding_decodes encoding member rest

theorem every_resolved_branch_targets_its_computed_byte_position
    (result : Result) (output : Output) (index : Nat)
    (member : (output, index) ∈ result.outputs.zipIdx)
    (branch : BranchOrigin) (isBranch : output.branchOrigin? = some branch) :
    (ByteLayout.offset result.sizes branch.targetIndex : Int) =
      (ByteLayout.offset result.sizes index : Int) +
        (Grass.ISA.X86.Rel32.encodedSize branch.kind : Int) + branch.resolved.bits.toInt :=
  result.branch_target_equation output index member branch isBranch

end Grass.Tests.Assembly.X86BranchLayout
