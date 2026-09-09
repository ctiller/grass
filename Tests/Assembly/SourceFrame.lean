import Grass.Assembly.SourceFrame
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.SourceFrame
open Grass.Assembly SourceInput SourceFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def fromChars? (chars : List Char) : Option Result :=
  (extractHelloSourceChars chars).toOption.bind derive?

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def view (result : Result) : List Nat × List Grass.ISA.X86.Gpr :=
  ([result.layout.argumentCount, result.layout.localBytes, result.layout.callAllocationBytes],
    result.layout.savedRegisters)

-- These are observations of the source-derived layout, never compiler inputs.
example : (fromChars? authored).map view = some ([5, 4, 48], [.r12, .r13, .r14]) := by
  decide +kernel

def sample (api body : List Char) : List Char :=
  (source_chars "def helloSource : MachineSource plan := withStack (value : UInt32 := 7) withCallFrame ") ++
    api ++ (source_chars " asm_source (statics := statics) {\n") ++ body ++ (source_chars "\n}")

example : (fromChars? (sample (source_chars "WriteFile")
  (source_chars "push r12\npush r13\ncall qword ptr [rip + __imp_WriteFile]\nud2"))).map view =
    some ([5, 4, 56], [.r12, .r13]) := by decide +kernel

example : (fromChars? (sample (source_chars "WriteFile") (source_chars "ud2"))).map
    (fun result => result.header.locals.map SourceFrameHeader.Local.initialValue) =
      some [7] := by decide +kernel

-- A smaller requested frame cannot cover the actual WriteFile signature.
example : fromChars? (sample (source_chars "GetStdHandle")
    (source_chars "call qword ptr [rip + __imp_WriteFile]\nud2")) = none := by decide +kernel
example : fromChars? (sample (source_chars "Unknown") (source_chars "ud2")) = none := by decide +kernel
example : fromChars? (sample (source_chars "WriteFile")
    (source_chars "call qword ptr [rip + __imp_Unknown]\nud2")) = none := by decide +kernel

end Grass.Tests.Assembly.SourceFrame
