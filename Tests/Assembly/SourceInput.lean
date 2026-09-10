import Grass.Assembly.SourceInput
namespace Grass.Tests.Assembly.SourceInput
open Grass.Assembly.SourceInput
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

def renamed : String :=
  "def renamed : MachineSource plan := withStack (x : UInt32 := 0) withStack (y : UInt32 := 7) withCallFrame Api asm_source (statics := s) {\n  mov x, 0\n}"

example : (extractSource renamed).toOption.map (fun body =>
    (body.headerText, body.text, uint32StackSlots body)) =
    some (" : MachineSource plan := withStack (x : UInt32 := 0) withStack (y : UInt32 := 7) withCallFrame Api asm_source (statics := s) ",
      "\n  mov x, 0\n", some ["x", "y"]) := by decide
example : (extractSource "def empty : MachineSource p := withCallFrame Api asm_source (statics := s) { }").toOption.map uint32StackSlots = some (some []) := by decide
example : (extractSource "def renamed := asm_source { nested { } }").toOption.isSome := by decide
example : (extractSource "def renamed := asm_source { body }\n\t").toOption.isSome := by decide
example : (extractSource " \ndef renamed := asm_source { body }").toOption = none := by decide
example : (extractSource "def renamed := asm_source { body } def other := 1").toOption = none := by decide
example : (extractSource "def renamed := asm_source { body").toOption = none := by decide
example : (extractSource "def renamed := asm_source { body } junk").toOption = none := by decide
example : (extractSource "-- def fake := asm_source { bogus }\ndef renamed := asm_source { ok }").toOption = none := by decide
example : (extractSource "def renamed := asm_source { /- } /- nested -/ still comment -/ ok }").toOption.isSome := by decide
example : (extractSource "def renamed := asm_source { /- unterminated").toOption = none := by decide
example : (extractSource "def renamed := \"asm_source { bogus }\"").toOption = none := by decide

def command : List Char := "def renamed : MachineSource p := withCallFrame Api asm_source (statics := s) { mov x, 0 }".toList
def commandOffsets : SourceOffsets :=
  let headerStart := "def renamed".toList.length
  let headerFinish := "def renamed : MachineSource p := withCallFrame Api asm_source (statics := s) ".toList.length
  ⟨headerStart, headerFinish, headerFinish + 1, command.length - 1⟩
example : (captureSourceChars command commandOffsets).toOption = (extractSourceChars command).toOption := by decide +kernel
example : (captureSourceChars command { commandOffsets with headerStart := commandOffsets.headerStart - 1 }).toOption = none := by decide +kernel
example : (captureSourceChars command { commandOffsets with bodyFinish := commandOffsets.bodyFinish - 1 }).toOption = none := by decide +kernel

def emptyCommand : List Char := "def café := asm_source {}".toList
def emptyOffsets : SourceOffsets := ⟨8, 23, 24, 24⟩
example : (captureSourceChars emptyCommand emptyOffsets).toOption.isSome := by decide +kernel
-- Equal empty text at a different location does not certify the original range.
example : (captureSourceChars emptyCommand
    { emptyOffsets with bodyStart := 25, bodyFinish := 25 }).toOption = none := by decide +kernel

def spirvCommand : List Char := "def renamed := spirv_asm { nested { } }".toList
def spirvOffsets : SourceOffsets := ⟨11, 25, 26, 38⟩
example : (extractMarkedSourceChars "spirv_asm" spirvCommand).toOption.isSome := by decide +kernel
example : (captureMarkedSourceChars "spirv_asm" spirvCommand spirvOffsets).toOption =
    (extractMarkedSourceChars "spirv_asm" spirvCommand).toOption := by decide +kernel
example : (captureMarkedSourceChars "asm_source" spirvCommand spirvOffsets).toOption = none := by decide +kernel
end Grass.Tests.Assembly.SourceInput
