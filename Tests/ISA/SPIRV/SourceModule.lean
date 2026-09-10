import Grass.ISA.SPIRV.SourceModule
import Tests.Assembly.SourceSelection
import Tests.Assembly.SourceLiteral
import Grass.Trust.Audit

namespace Grass.Tests.ISA.SPIRV.SourceModule

open Grass.ISA.SPIRV
open Grass.Tests.Assembly.SourceSelection

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- Read the authored file; no shader recipe is maintained in this test. -/
def authored : List Char := include_source_chars "../../../Spikes/5_Spinning_Cube/Assembly.lean"

structure Selected (file : List Char) where
  selection : Selection file
  checked : SourceModule.Checked selection.chars

def selected? (name : String) : Option (Selected authored) := do
  let selection ← selectCommand? "spirv_asm" name authored
  let checked ← (SourceModule.check selection.chars).toOption
  some ⟨selection, checked⟩

/-- The module producer is connected to the original file slice, including its
exact words and entry metadata, rather than just a successful stage-name test. -/
theorem Selected.file_to_words {file : List Char} (selected : Selected file) :
    ∃ body statements,
      Grass.Assembly.SourceInput.extractMarkedSourceChars "spirv_asm"
        ((file.drop selected.selection.start).take
          (selected.selection.finish - selected.selection.start)) = .ok body ∧
      SourceParser.parseBody? body.bodyChars = some statements ∧
      Module.compile statements = .ok selected.checked.output := by
  rw [← selected.selection.slice_eq]
  exact selected.checked.source_to_words

def regression : IO Unit := do
  for (name, stage) in [("cubeVertex", Module.Stage.vertex), ("cubeFragment", .fragment)] do
    let some selected := selected? name
      | throw (IO.userError s!"{name}: authored source check failed")
    unless selected.checked.output.entry.stage == stage && selected.checked.output.entry.name == "main" do
      throw (IO.userError s!"{name}: entry metadata differs")

#eval regression

#print axioms Grass.ISA.SPIRV.SourceModule.Checked.source_to_words
#audit_runtime_dependencies Grass.ISA.SPIRV.SourceModule.check

end Grass.Tests.ISA.SPIRV.SourceModule
