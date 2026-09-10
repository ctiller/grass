import Grass.Assembly.SourceResolve
import Tests.Assembly.SourceLiteral
namespace Grass.Tests.Assembly.SourceResolve
open Grass.Assembly Grass.Assembly.SourceResolve
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! A minimal standalone source fixture for generic relocation tests. It is
deliberately independent of every authored spike. -/
def source : List Char := source_chars
  "def relocationSample : MachineSource plan := withCallFrame ExitProcess asm_source (statics := objects) {\nstart:\n  lea rax, [rip + blob]\n  call qword ptr [rip + __imp_ExitProcess]\n  ud2\n}"

def checkedSymbols : Option Symbols := Symbols.mk?
  [{ name := "blob", address := 2000, byteLength := 3 }]
  [{ name := "__imp_ExitProcess", iatAddress := 3000 }]

def actualView : Option (Nat × Nat × Bool) := do
  let symbols ← checkedSymbols
  let body ← (SourceInput.extractSourceChars source).toOption
  let frame ← SourceFrame.derive? body
  let splice ← SourceSplice.derive? frame 0
  let result ← resolve? splice symbols 1000
  pure (splice.outputs.length, result.outputs.length,
    result.outputs.map Output.index = List.range splice.outputs.length)

example : actualView = some (4, 4, true) := by decide +kernel

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
    match (SourceInput.extractSourceChars source).toOption >>= SourceFrame.derive? with
    | none => false
    | some frame => match SourceSplice.derive? frame 0 with
      | none => false
      | some splice => (resolve? splice symbols 1000).isSome

example : resolvesWith (Symbols.mk? [] []) = false := by decide +kernel

def ripOverflowSymbols : Option Symbols := Symbols.mk?
  [{ name := "blob", address := 2^63, byteLength := 3 }]
  [{ name := "__imp_ExitProcess", iatAddress := 2^63 }]

example : resolvesWith ripOverflowSymbols = false := by decide +kernel

example : SignedRel32.resolve? 0 5 (2^31 + 5) = none := by decide

end Grass.Tests.Assembly.SourceResolve
