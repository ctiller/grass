import Grass.Assembly.SourceSplice
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.SourceSplice

open Grass.Assembly Grass.Assembly.SourceSplice
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def zeroSavedSource : List Char := source_chars
  "def spliceSample : MachineSource plan := withStack (value : UInt32 := 0) withCallFrame WriteFile asm_source (statics := statics) {\nmov value, 0\nud2\n}"

def zeroSavedView : Option (List Nat) := do
  let body ← (SourceInput.extractSourceChars zeroSavedSource).toOption
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
