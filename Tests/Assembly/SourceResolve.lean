import Grass.Assembly.SourceResolve
import Tests.Assembly.SourceLiteral
namespace Grass.Tests.Assembly.SourceResolve
open Grass.Assembly Grass.Assembly.SourceResolve
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def checkedSymbols : Option Symbols := Symbols.mk?
  [{ name := "payload", address := 2000, byteLength := 15 }]
  [{ name := "__imp_GetStdHandle", iatAddress := 3000 },
   { name := "__imp_WriteFile", iatAddress := 3008 },
   { name := "__imp_ExitProcess", iatAddress := 3016 }]

def actualView : Option (Nat × Nat × Bool) := do
  let symbols ← checkedSymbols
  let body ← (SourceInput.extractHelloSourceChars authored).toOption
  let frame ← SourceFrame.derive? body
  let splice ← SourceSplice.derive? frame 0
  let result ← resolve? splice symbols 1000
  pure (splice.outputs.length, result.outputs.length,
    result.outputs.map Output.index = List.range splice.outputs.length)

example : actualView = some (44, 44, true) := by decide +kernel

example : Symbols.mk?
    [{ name := "payload", address := 1, byteLength := 1 },
     { name := "payload", address := 2, byteLength := 2 }] [] = none := by decide

example : Symbols.mk? []
    [{ name := "__imp_WriteFile", iatAddress := 1 },
     { name := "__imp_WriteFile", iatAddress := 2 }] = none := by decide

def resolvesWith (symbols? : Option Symbols) : Bool :=
  match symbols? with
  | none => false
  | some symbols =>
    match (SourceInput.extractHelloSourceChars authored).toOption >>= SourceFrame.derive? with
    | none => false
    | some frame => match SourceSplice.derive? frame 0 with
      | none => false
      | some splice => (resolve? splice symbols 1000).isSome

example : resolvesWith (Symbols.mk? [] []) = false := by decide +kernel

def overflowSymbols : Option Symbols := Symbols.mk?
  [{ name := "payload", address := 2000, byteLength := 2^32 }]
  [{ name := "__imp_GetStdHandle", iatAddress := 3000 },
   { name := "__imp_WriteFile", iatAddress := 3008 },
   { name := "__imp_ExitProcess", iatAddress := 3016 }]

example : resolvesWith overflowSymbols = false := by decide +kernel

def ripOverflowSymbols : Option Symbols := Symbols.mk?
  [{ name := "payload", address := 2^63, byteLength := 15 }]
  [{ name := "__imp_GetStdHandle", iatAddress := 2^63 },
   { name := "__imp_WriteFile", iatAddress := 2^63 },
   { name := "__imp_ExitProcess", iatAddress := 2^63 }]

example : resolvesWith ripOverflowSymbols = false := by decide +kernel

example : SignedRel32.resolve? 0 5 (2^31 + 5) = none := by decide

end Grass.Tests.Assembly.SourceResolve
