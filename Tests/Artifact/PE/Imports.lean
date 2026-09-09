import Grass.Artifact.PE.Imports

namespace Grass.Tests.Artifact.PE.Imports

open Grass.Std.Logical Grass.Artifact.PE

private def exitProcess : ImportSymbol :=
  ⟨Vec.fromList [69, 120, 105, 116, 80, 114, 111, 99, 101, 115, 115]⟩

private def kernel32 : ImportLibrary :=
  { name := Vec.fromList [107, 101, 114, 110, 101, 108, 51, 50, 46, 100, 108, 108]
    symbols := Vec.fromList [exitProcess] }

private def libraries : Vec ImportLibrary := Vec.fromList [kernel32]

private def shortSymbol : ImportSymbol := ⟨Vec.fromList [66]⟩

private def shortLibrary : ImportLibrary :=
  { name := Vec.fromList [65]
    symbols := Vec.fromList [shortSymbol] }

private def twoLibraries : Vec ImportLibrary := Vec.fromList [kernel32, shortLibrary]

example : importDescriptorTableSize 1 = 40 := by decide

example : thunkArraySize 1 = 16 := by decide

example : (writeHintName exitProcess).length = 14 := by decide

example : (layoutImportLibraries libraries).length = 1 := by decide

example : ((layoutImportLibraries libraries).get? 0).map (·.iatOffset) = some 40 := by
  decide

example : ((layoutImportLibraries libraries).get? 0).map (·.iltOffset) = some 56 := by
  decide

example : ((layoutImportLibraries libraries).get? 0).map (·.dllNameOffset) = some 86 := by
  decide

set_option maxRecDepth 4096 in
example : (writeImportSection 0x2000 libraries).length = 104 := by decide

set_option maxRecDepth 4096 in
example : (writeImportSection 0x2000 libraries).take 4 =
    Vec.fromList [0x38, 0x20, 0, 0] := by decide

example : (layoutImportLibraries twoLibraries).length = 2 := by decide

set_option maxRecDepth 4096 in
example : (writeImportSection 0x2000 twoLibraries).length = 168 := by decide

example : importLibrariesValid twoLibraries.toList = true := by decide

private def textName : SectionName :=
  ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩

private def callerDescription : ExecutableImageDescription :=
  { entryPointRva := 4096
    sections := Vec.fromList
      [{ name := textName
         contents := Vec.fromList [0x90]
         characteristics := 0x60000020 }]
    imports := libraries }

set_option maxRecDepth 4096 in
example : importSectionRva? callerDescription = some 0x2000 := by decide

set_option maxRecDepth 4096 in
example : importAddressRva? callerDescription 0 0 = some 0x2028 := by decide

example : importAddressRva? callerDescription 0 1 = none := by decide

end Grass.Tests.Artifact.PE.Imports
