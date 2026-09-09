import Grass.Assembly.FrameArgument
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.FrameArgument

open Grass.Assembly Grass.ISA.X86
open Grass.Assembly.FrameArgument Grass.Platform.Win32.Signatures
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def fromChars? (chars : List Char) : Option Result := do
  let body ← (SourceInput.extractHelloSourceChars chars).toOption
  let frame ← SourceFrame.derive? body
  match frame.program.collected.code.filterMap (resolve? frame 0) with
  | [result] => some result
  | _ => none

def view (result : Result) : Api × String × Nat × Nat × List (BitVec 8) :=
  (result.api, result.field, result.index, result.displacement, result.encoding.toBytes)

example : (fromChars? authored).map view = some
    (.writeFile, "overlapped", 4, 32,
      [0x48, 0xC7, 0x84, 0x24, 0x20, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

def sample (api body : List Char) : List Char :=
  (source_chars "def helloSource : MachineSource plan := withStack (value : UInt32 := 0) withCallFrame ") ++
    api ++ (source_chars " asm_source (statics := statics) {\n") ++ body ++
    (source_chars "\nud2\n}")

example : fromChars? (sample (source_chars "WriteFile")
    (source_chars "arg Unknown.overlapped, 0")) = none := by decide +kernel
example : fromChars? (sample (source_chars "WriteFile")
    (source_chars "arg WriteFile.unknown, 0")) = none := by decide +kernel
example : fromChars? (sample (source_chars "WriteFile")
    (source_chars "arg WriteFile.buffer, 0")) = none := by decide +kernel
example : fromChars? (sample (source_chars "WriteFile")
    (source_chars "arg WriteFile.file, 0")) = none := by decide +kernel
example : fromChars? (sample (source_chars "GetStdHandle")
    (source_chars "arg WriteFile.overlapped, 0")) = none := by decide +kernel
example : fromChars? (sample (source_chars "WriteFile")
    (source_chars "arg WriteFile.overlapped, 2147483648")) = none := by decide +kernel

-- The accepted immediate subset includes its positive endpoint; the emitted
-- imm32 recovers the same nonnegative signed value rather than only admitting zero.
example : (fromChars? (sample (source_chars "WriteFile")
    (source_chars "arg WriteFile.overlapped, 2147483647"))).map
      (fun result => (result.value, result.encoding.toBytes)) =
    some (2147483647, [0x48, 0xC7, 0x84, 0x24, 0x20, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0x7F]) := by
  decide +kernel

def sampleLocals (locals body : List Char) : List Char :=
  (source_chars "def helloSource : MachineSource plan := ") ++ locals ++
    (source_chars " withCallFrame WriteFile asm_source (statics := statics) {\n") ++ body ++
    (source_chars "\nud2\n}")

-- Local declarations change the source-derived local range without moving the
-- signature-derived fifth argument out of its stack slot.
example : (fromChars? (sampleLocals (source_chars
    "withStack (first : UInt32 := 0) withStack (second : UInt32 := 0)")
    (source_chars "arg WriteFile.overlapped, 0"))).map
      (fun result => (result.displacement, result.frame.layout.localBytes)) = some (32, 8) := by
  decide +kernel

example : fromChars? (sample (source_chars "WriteFile")
    (source_chars "arg WriteFile.overlapped, 0\narg WriteFile.overlapped, 1")) = none := by
  decide +kernel

end Grass.Tests.Assembly.FrameArgument

