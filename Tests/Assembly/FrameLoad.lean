import Grass.Assembly.FrameLoad
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.FrameLoad
open Grass.Assembly Grass.ISA.X86
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def fromChars? (chars : List Char) : Option Grass.Assembly.FrameLoad.Result := do
  let body ← (SourceInput.extractHelloSourceChars chars).toOption
  let frame ← SourceFrame.derive? body
  match frame.program.collected.code.filterMap (FrameLoad.resolve? frame 0) with
  | [result] => some result
  | _ => none

def view (result : Grass.Assembly.FrameLoad.Result) : Gpr × String × Nat × Nat × List (BitVec 8) :=
  (result.destination, result.slot, result.address.displacement,
    result.address.width, result.encoding.toBytes)

-- Actual authored load, with every address/encoding observation downstream of
-- the parsed frame; none of these expected values is a resolver input.
example : (fromChars? authored).map view =
    some (.rax, "transferred", 40, 4, [0x8B, 0x84, 0x24, 0x28, 0, 0, 0]) := by decide +kernel

def sample (locals body : List Char) : List Char :=
  (source_chars "def helloSource : MachineSource plan := ") ++ locals ++
    (source_chars " withCallFrame WriteFile asm_source (statics := statics) {\n") ++
    body ++ (source_chars "\nud2\n}")

def twoLocals : List Char := source_chars
  "withStack (first : UInt32 := 0) withStack (second : UInt32 := 7)"

-- Declaration order changes placement through the shared slot environment.
example : (fromChars? (sample twoLocals (source_chars "mov eax, second"))).map
    (fun result => (result.slot, result.address.displacement)) = some ("second", 44) := by
  decide +kernel

example : fromChars? (sample twoLocals (source_chars "mov eax, unknown")) = none := by decide +kernel
example : fromChars? (sample twoLocals (source_chars "mov rax, second")) = none := by decide +kernel
example : fromChars? (sample twoLocals (source_chars "mov eax, first\nmov eax, second")) = none := by
  decide +kernel

-- The generic geometry gate cannot create an empty or oversized local access.
def layout : Grass.ABI.Win64.CallFrameLayout :=
  SourceStore.frameForSlots 5 [] ["first"]
example : LocalAddress.resolve? layout 0 (SourceStore.slotEnv ["first"]) "first" 0 = none := by
  decide +kernel
example : LocalAddress.resolve? layout 0 (SourceStore.slotEnv ["first"]) "first" 5 = none := by
  decide +kernel

end Grass.Tests.Assembly.FrameLoad
