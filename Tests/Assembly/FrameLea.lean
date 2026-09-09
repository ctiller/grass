import Grass.Assembly.FrameLea
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.FrameLea

open Grass.Assembly Grass.ISA.X86
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def fromChars? (chars : List Char) : Option Grass.Assembly.FrameLea.Result := do
  let body ← (SourceInput.extractHelloSourceChars chars).toOption
  let frame ← SourceFrame.derive? body
  match frame.program.collected.code.filterMap (Grass.Assembly.FrameLea.resolve? frame 0) with
  | [result] => some result
  | _ => none

def view (result : Grass.Assembly.FrameLea.Result) :
    Gpr × String × Nat × Nat × List (BitVec 8) :=
  (result.destination, result.slot, result.address.displacement,
    result.address.width, result.encoding.toBytes)

-- Every observation is downstream of the actual, unchanged Hello source.
example : (fromChars? authored).map view =
    some (.r9, "transferred", 40, 4, [0x4C, 0x8D, 0x8C, 0x24, 0x28, 0, 0, 0]) := by
  decide +kernel

def sample (locals body : List Char) : List Char :=
  (source_chars "def helloSource : MachineSource plan := ") ++ locals ++
    (source_chars " withCallFrame WriteFile asm_source (statics := statics) {\n") ++
    body ++ (source_chars "\nud2\n}")

def twoLocals : List Char := source_chars
  "withStack (first : UInt32 := 0) withStack (second : UInt32 := 7)"

-- Changing source declaration order changes the machine-derived displacement.
example : (fromChars? (sample twoLocals (source_chars "lea r9, second.addr"))).map view =
    some (.r9, "second", 44, 4, [0x4C, 0x8D, 0x8C, 0x24, 0x2C, 0, 0, 0]) := by
  decide +kernel

def reversedLocals : List Char := source_chars
  "withStack (second : UInt32 := 7) withStack (first : UInt32 := 0)"
example : (fromChars? (sample reversedLocals (source_chars "lea r9, second.addr"))).map
    (fun result => result.address.displacement) = some 40 := by decide +kernel

-- Missing declarations and wrong source operand shapes cannot resolve.
example : fromChars? (sample twoLocals (source_chars "lea r9, missing.addr")) = none := by
  decide +kernel
example : fromChars? (sample twoLocals (source_chars "lea r9, [rip + second]")) = none := by
  decide +kernel
example : fromChars? (sample twoLocals (source_chars "lea r9d, second.addr")) = none := by
  decide +kernel
example : fromChars? (sample twoLocals
    (source_chars "lea r9, first.addr\nlea r9, second.addr")) = none := by
  decide +kernel

end Grass.Tests.Assembly.FrameLea
