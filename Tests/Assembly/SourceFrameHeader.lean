import Grass.Assembly.SourceFrameHeader
namespace Grass.Tests.Assembly.SourceFrameHeader
open Grass.Assembly.SourceFrameHeader
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

example : parseChars? " : MachineSource p := withCallFrame Api asm_source (statics := s)".toList = some ⟨"p", [], "Api", "s"⟩ := by decide
example : parseChars? " : MachineSource p := withStack (x : UInt32 := 0) withStack (y : UInt32 := 4294967295) withCallFrame Api asm_source (statics := s)".toList = some ⟨"p", [⟨"x", 0⟩, ⟨"y", UInt32.ofNat 4294967295⟩], "Api", "s"⟩ := by decide
example : parseChars? " : MachineSource p := withStack (x : UInt32 := 4294967296) withCallFrame Api asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := withStack (x : UInt64 := 0) withCallFrame Api asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := withStack (x : UInt32 := 1 + 2) withCallFrame Api asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := withStack (x : UInt32 := 0) withStack (x : UInt32 := 1) withCallFrame Api asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := withCallFrame A withCallFrame B asm_source (statics := s)".toList = none := by decide
example : parseChars? " : MachineSource p := withCallFrame Api asm_source (statics := s) trailing".toList = none := by decide
end Grass.Tests.Assembly.SourceFrameHeader
