import Grass.Assembly.X86ControlFlow
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.X86ControlFlow

open Grass.Assembly.SourceInput Grass.Assembly.X86Source Grass.Assembly.X86ControlFlow

def checkChars? (chars : List Char) : Option CheckedProgram := do
  let body ← (extractHelloSourceChars chars).toOption
  let statements ← (parseBody body).toOption
  check? statements

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (checkChars? authored).isSome = true := by decide +kernel

theorem actual_targets_are_in_the_derived_code (program : CheckedProgram)
    (_h : checkChars? authored = some program) (flow : Flow) (member : flow ∈ program.flows)
    (target : Nat) (edge : target ∈ flow.targets) : target < program.collected.code.length :=
  program.target_bounded flow member target edge

def wrap (body : List Char) : List Char :=
  (source_chars "def helloSource := asm_source {\n") ++ body ++ (source_chars "\n}")

-- Alias labels are allowed; duplicate names and invalid static targets are not.
example : (checkChars? (wrap (source_chars "entry:\nalias:\njmp alias"))).isSome := by decide
example : (checkChars? (wrap (source_chars "entry:\nentry:\nud2"))).isNone := by decide
example : (checkChars? (wrap (source_chars "jmp missing"))).isNone := by decide
example : (checkChars? (wrap (source_chars "jmp end\nend:"))).isNone := by decide

-- A conditional branch and a call need a possible continuation in the code.
example : (checkChars? (wrap (source_chars "entry:\nje entry"))).isNone := by decide
example : (checkChars? (wrap (source_chars "call qword ptr [rip + provider]"))).isNone := by decide
example : (checkChars? (wrap (source_chars "call qword ptr [rip + provider]\nud2"))).isSome := by decide
example : (checkChars? (wrap (source_chars "mov eax, 1"))).isNone := by decide

-- Unsupported control transfers must never acquire an ordinary next edge.
example : (checkChars? (wrap (source_chars "ret"))).isNone := by decide
example : (checkChars? (wrap (source_chars "jmp rax"))).isNone := by decide
example : (checkChars? (wrap (source_chars ""))).isNone := by decide

end Grass.Tests.Assembly.X86ControlFlow
