import Grass.Assembly.SourceSplice
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.SourceSplice

open Grass.Assembly Grass.Assembly.SourceSplice
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def actualView : Option (List Nat) := do
  let body ← (SourceInput.extractHelloSourceChars authored).toOption
  let frame ← SourceFrame.derive? body
  let result ← derive? frame 0
  pure [frame.program.collected.code.length, frame.saved.savedItems.length,
    result.prologue.generated.length, result.initialization.entries.length,
    result.outputs.length, result.entryOffset, result.unwindEndOffset,
    result.initializerStartOffset, result.bodyStartOffset,
    sourceFinalIndex frame.saved.savedItems.length result.initialization.entries.length
      frame.saved.savedItems.length,
    result.sourcePosition frame.saved.savedItems.length]

example : actualView = some [42, 3, 4, 1, 44, 0, 10, 10, 21, 5, 21] := by
  decide +kernel

def actualIndexView : Option (List (Option Nat)) := do
  let body ← (SourceInput.extractHelloSourceChars authored).toOption
  let frame ← SourceFrame.derive? body
  let result ← derive? frame 0
  let lineAt (index : Nat) :=
    (result.outputs[index]?).bind FinalOutput.source? |>.map (fun output => output.origin.lineNumber)
  pure [lineAt 0, lineAt 2, lineAt 3, lineAt 4, lineAt 5, lineAt 43]

-- Source items on each side of the splice retain their exact order; the two
-- inserted positions carry no source origin.
example : actualIndexView = some [some 3, some 5, none, none, some 6, some 59] := by
  decide +kernel

def zeroSavedSource : List Char := source_chars
  "def helloSource : MachineSource plan := withStack (value : UInt32 := 0) withCallFrame WriteFile asm_source (statics := statics) {\nmov value, 0\nud2\n}"

def zeroSavedView : Option (List Nat) := do
  let body ← (SourceInput.extractHelloSourceChars zeroSavedSource).toOption
  let frame ← SourceFrame.derive? body
  let result ← derive? frame 0
  pure [frame.saved.savedItems.length, result.initialization.entries.length,
    result.outputs.length, result.entryOffset,
    sourceFinalIndex 0 result.initialization.entries.length 0,
    result.sourcePosition 0, result.bodyStartOffset]

-- Entry remains zero; source index zero denotes the body after both injected
-- instructions and therefore has a distinct index and byte position.
example : zeroSavedView = some [0, 1, 4, 0, 2, 15, 15] := by decide +kernel

end Grass.Tests.Assembly.SourceSplice
