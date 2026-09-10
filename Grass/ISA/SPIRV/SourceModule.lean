import Grass.Assembly.SourceInput
import Grass.ISA.SPIRV.SourceParser
import Grass.ISA.SPIRV.Module

/-! Exact standalone source-command binding for the bounded SPIR-V module checker.
The witness records shared capture, full body parsing, and module compilation
equations. It does not claim complete SPIR-V validity or GPU execution. -/
namespace Grass.ISA.SPIRV.SourceModule

open Grass.Assembly.SourceInput

structure Checked (command : List Char) where
  private mk ::
  body : Body
  statements : List SourceSyntax.Statement
  output : Module.Output
  captured : extractMarkedSourceChars "spirv_asm" command = .ok body
  parsed : SourceParser.parseBody? body.bodyChars = some statements
  compiled : Module.compile statements = .ok output

/-- All three stages consume the preceding stage's actual result. -/
def check (command : List Char) : Except String (Checked command) :=
  match captured : extractMarkedSourceChars "spirv_asm" command with
  | .error _ => .error "malformed standalone spirv_asm command"
  | .ok body =>
    match parsed : SourceParser.parseBody? body.bodyChars with
    | none => .error "unsupported or malformed SPIR-V assembly body"
    | some statements =>
      match compiled : Module.compile statements with
      | .error error => .error error
      | .ok output => .ok ⟨body, statements, output, captured, parsed, compiled⟩

/-- Word identity is indexed by the original command, never supplied as an
unconnected module-validity assumption. -/
theorem Checked.source_to_words {command : List Char} (checked : Checked command) :
    ∃ body statements,
      extractMarkedSourceChars "spirv_asm" command = .ok body ∧
      SourceParser.parseBody? body.bodyChars = some statements ∧
      Module.compile statements = .ok checked.output :=
  ⟨checked.body, checked.statements, checked.captured, checked.parsed, checked.compiled⟩

end Grass.ISA.SPIRV.SourceModule
