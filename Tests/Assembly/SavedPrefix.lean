import Grass.Assembly.SavedPrefix
import Grass.Assembly.X86Source
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.SavedPrefix

open Grass.Assembly SourceInput X86Source X86ControlFlow SavedPrefix

def wrap (body : List Char) : List Char :=
  (source_chars "def helloSource := asm_source {\n") ++ body ++ (source_chars "\n}")

def extractChars? (chars : List Char) : Option Result := do
  let body ← (extractHelloSourceChars chars).toOption
  let statements ← (parseBody body).toOption
  let program ← check? statements
  extract? program

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

example : (extractChars? authored).map Result.registers = some [.r12, .r13, .r14] := by
  decide +kernel

example : (extractChars? (wrap (source_chars "ud2"))).map Result.registers = some [] := by decide
example : extractChars? (wrap (source_chars "push r12\npush r12\nud2")) = none := by decide
example : extractChars? (wrap (source_chars "push rax\nud2")) = none := by decide
example : extractChars? (wrap (source_chars "push rsp\nud2")) = none := by decide
example : extractChars? (wrap (source_chars "mov rax, rax\npush r12\nud2")) = none := by decide
example : extractChars? (wrap (source_chars
  "push r12\ninside:\npush r13\njmp inside")) = none := by decide
example : (extractChars? (wrap (source_chars
  "push r12\nafter:\njmp after"))).isSome := by decide

theorem extracted_registers_are_distinct_and_nonvolatile (result : Result) :
    result.registers.Nodup ∧
      ∀ reg ∈ result.registers, Grass.ABI.Win64.volatility reg = .nonvolatile :=
  ⟨result.registersNodup, result.registersNonvolatile⟩

end Grass.Tests.Assembly.SavedPrefix
