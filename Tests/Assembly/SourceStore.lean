import Grass.Assembly.SourceStore
import Grass.Assembly.SourceFrame
import Grass.Assembly.FrameStore
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.SourceStore

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Grass.Assembly Grass.Assembly.SourceInput Grass.Assembly.SourceStore
open Grass.ABI.Win64 Grass.ISA.X86

def selectedStore? (frame : SourceFrame.Result) : Option X86ControlFlow.CodeItem := do
  let candidates := frame.program.collected.code.filter fun item =>
    match item.instruction.mnemonic, item.instruction.operands with
    | .mov, [.symbol destination, .immediate _] => frame.slots.contains destination
    | _, _ => false
  match candidates with
  | [line] => some line
  | _ => none

def fromChars? (source : List Char) (rspRootOffset : Nat := 0) : Option Store32.Resolved := do
  let body ← (extractSourceChars source).toOption
  let frame ← SourceFrame.derive? body
  let item ← selectedStore? frame
  FrameStore.resolve? frame rspRootOffset item

-- Small adversarial inputs exercise the parser and resolver directly.
def sample (type body : List Char) : List Char :=
  (source_chars "def storeSample : MachineSource plan := withStack (value : ") ++ type ++
    (source_chars " := 0) withCallFrame WriteFile asm_source (statics := statics) {\n ") ++
    body ++ (source_chars "\nud2\n}")

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (fromChars? (sample (source_chars "UInt32")
    (source_chars "mov value, 305419896"))).map Store32.Resolved.writeBytes =
    some (le32 305419896) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (fromChars? (sample (source_chars "UInt64") (source_chars "mov value, 0"))).isNone =
    true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (fromChars? (sample (source_chars "UInt32")
    (source_chars "mov value, 4294967296"))).isNone = true := by decide

example : (fromChars? (sample (source_chars "UInt32")
    (source_chars "mov value, 0\n mov value, 1"))).isNone = true := by decide

-- Register operands cannot become local-memory stores through a second parser.
example : (fromChars? (source_chars
    "def registerStoreSample : MachineSource plan := withStack (rax : UInt32 := 0) withCallFrame WriteFile asm_source (statics := statics) {\nmov rax, 0\nud2\n}")).isNone := by
  decide +kernel

end Grass.Tests.Assembly.SourceStore
