import Grass.Assembly.SourceFrameHeader
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.SourceFrameHeader

open Grass.Assembly.SourceInput
open Grass.Assembly.SourceFrameHeader

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

theorem actual_header_parses :
    (extractHelloSourceChars authored).toOption.bind parse? =
      some ⟨"plan", [⟨"transferred", 0⟩], "WriteFile", "helloStatics"⟩ := by
  decide +kernel

example : parseChars? " : MachineSource p := withCallFrame Api asm_source (statics := s)".toList =
    some ⟨"p", [], "Api", "s"⟩ := by decide
example : parseChars? " : MachineSource p := withStack (x : UInt32 := 4294967295) withCallFrame Api asm_source (statics := s)".toList =
    some ⟨"p", [⟨"x", UInt32.ofNat 4294967295⟩], "Api", "s"⟩ := by decide
example : parseChars? " : MachineSource p := withStack (x : UInt32 := 4294967296) withCallFrame Api asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := withStack (x : UInt64 := 0) withCallFrame Api asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := withStack (x : UInt32 := 1 + 2) withCallFrame Api asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := withStack (x : UInt32 := 0) withStack (x : UInt32 := 1) withCallFrame Api asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := withCallFrame A withCallFrame B asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := withCallFrame Api asm_source (statics := s) trailing".toList = none := by decide
example : parseChars? " : MachineSource p := withCallFrame Api asm_source (statics = s)".toList = none := by decide

end Grass.Tests.Assembly.SourceFrameHeader
