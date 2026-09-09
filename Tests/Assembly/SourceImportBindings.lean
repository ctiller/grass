import Grass.Assembly.SourceImportBindings
import Tests.Artifact.PE.ImageWriter

namespace Grass.Tests.Assembly.SourceImportBindings

open Grass.Artifact.PE Grass.Assembly.SourceImportBindings
open Tests.Artifact.PE.ImageWriter

def plan? : Option ImagePlan := (prepareImage description).toOption

def actual : Option (String × Bool × Bool) := do
  let plan ← plan?
  let result ← resolve? plan "kernel32.dll" ["__imp_ExitProcess"]
  let binding ← result.bindings[0]?
  let queried ← plan.layout.importAddressRva? result.library.libraryIndex binding.symbolIndex
  pure (binding.sourceImport.name, binding.sourceImport.iatAddress == queried,
    binding.symbol.name == Grass.Std.Logical.Text.utf8 "ExitProcess")

example : actual = some ("__imp_ExitProcess", true, true) := by decide +kernel

def accepts (candidatePlan : Option ImagePlan) (library : String) (names : List String) : Bool :=
  match candidatePlan with
  | none => false
  | some plan => (resolve? plan library names).isSome

example : accepts plan? "kernel32.dll" ["__imp_ExitProcess", "__imp_ExitProcess"] = false := by
  decide +kernel

example : accepts plan? "kernel32.dll" ["__imp_WriteFile"] = false := by decide +kernel

example : accepts plan? "missing.dll" ["__imp_ExitProcess"] = false := by decide +kernel

def duplicateLibraryPlan? : Option ImagePlan :=
  (prepareImage { description with imports := Grass.Std.Logical.Vec.fromList [kernel32, kernel32] }).toOption

example : accepts duplicateLibraryPlan? "kernel32.dll" ["__imp_ExitProcess"] = false := by
  decide +kernel

def duplicateSymbolLibrary : ImportLibrary :=
  let symbol : ImportSymbol :=
    ⟨Grass.Std.Logical.Text.utf8
      (Grass.Platform.Win32.Signatures.apiName .exitProcess)⟩
  { kernel32 with symbols := Grass.Std.Logical.Vec.fromList [symbol, symbol] }

def duplicateSymbolPlan? : Option ImagePlan :=
  (prepareImage { description with imports := Grass.Std.Logical.Vec.singleton duplicateSymbolLibrary }).toOption

example : accepts duplicateSymbolPlan? "kernel32.dll" ["__imp_ExitProcess"] = false := by
  decide +kernel

example : accepts plan? "kernel32.dll" ["__imp_Unknown"] = false := by decide +kernel

end Grass.Tests.Assembly.SourceImportBindings
