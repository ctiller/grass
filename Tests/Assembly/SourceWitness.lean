import Grass.Assembly.SourceWitness
import Tests.Assembly.SourceLiteral
import Tests.Assembly.SourceLinkedImage

namespace Grass.Tests.Assembly.SourceWitness

open Grass.Assembly Grass.Artifact.PE

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Literal characters read from the checked-in authored program at elaboration. -/
def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def inputs : Grass.Assembly.SourceWitness.Inputs where
  table := SourceLinkedImage.staticTable SourceLinkedImage.payload
  staticName := SourceLinkedImage.staticName
  staticCharacteristics := 0x40000040
  libraryName := "kernel32.dll"
  sections :=
    { codeName := SourceLinkedImage.codeName
      codeCharacteristics := 0x60000020
      pdataName := SourceLinkedImage.pdataName
      xdataName := SourceLinkedImage.xdataName }

/-- Reusable dependent witness for the checked-in Spike 1 source.  Consumers
receive the actual linked result and selector witnesses, not a Boolean view. -/
theorem present : (Grass.Assembly.SourceWitness.produce? authored inputs).isSome = true := by
  decide +kernel

def witness : Grass.Assembly.SourceWitness.Result authored inputs :=
  Option.get _ present

theorem produced_exact : Grass.Assembly.SourceWitness.produce? authored inputs = some witness := by
  exact Grass.Assembly.SourceWitness.eq_some_get _ present

end Grass.Tests.Assembly.SourceWitness
