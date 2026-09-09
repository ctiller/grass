import Grass.Assembly.SourceInput
import Tests.Assembly.SourceLiteral
namespace Grass.Tests.Assembly.SourceInput
open Grass.Assembly.SourceInput
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

def spike1Program : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"
theorem spike1_source_ingress :
    (extractHelloSourceChars spike1Program).toOption.map (fun body =>
      (symbolicStores body |>.filter (fun store => store.1 = "transferred"),
        uint32StackSlots body)) =
      some ([("transferred", 0)], some ["transferred"]) := by decide +kernel

example : (extractHelloSource "def other := asm_source { mov transferred, 0 }").toOption = none := by decide
example : (extractHelloSource
    "def helloSource := asm_source { mov transferred, 0 }\n\
     def helloSource := asm_source { mov transferred, 0 }").toOption = none := by decide
example : (extractHelloSource "def helloSource := asm_source { nested { }").toOption = none := by decide
example : (extractHelloSource
    "-- def helloSource := asm_source { bogus }\n\
     def helloSource := asm_source (statics := x) { mov transferred, 0 }").toOption.isSome := by decide
example : (extractHelloSource
    "def decoy := \"def helloSource := asm_source { bogus }\"\n\
     def helloSource := asm_source { mov transferred, 0 }").toOption.isSome := by decide
example : (extractHelloSource
    "def helloSource := asm_source { /- } /- nested -/ misleading -/ mov transferred, 0 }").toOption.isSome := by decide
example : (extractHelloSource "def helloSource := asm_source { /- unterminated").toOption = none := by decide
example : (extractHelloSource "def helloSource := \"unterminated").toOption = none := by decide
example : (extractHelloSource
    "def helloSource := asm_source { /- unterminated\n\
     def helloSource := asm_source { mov transferred, 0 }").toOption = none := by decide
example : (extractHelloSource
    "def helloSource := asm_source { \"ignored\nmov transferred, 7\" }").toOption.map
      symbolicStores = some [] := by decide
example : (extractHelloSource
    "def helloSource := withStack (x : UInt64 := 0) asm_source { mov x, 0 }").toOption.map
      uint32StackSlots = some none := by decide

end Grass.Tests.Assembly.SourceInput
