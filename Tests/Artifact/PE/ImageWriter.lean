import Grass.Artifact.PE.ImageWriter

/-! These are container-layout fixtures with opaque payload bytes. They are
not executable Grass source probes and are never used as code-generation evidence. -/

namespace Tests.Artifact.PE.ImageWriter

open Grass.Artifact.PE Grass.Std.Logical

set_option maxRecDepth 10000

def textName : SectionName :=
  ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩

def kernel32 : ImportLibrary :=
  { name := Vec.fromList [107, 101, 114, 110, 101, 108, 51, 50, 46, 100, 108, 108]
    symbols := Vec.fromList [{ name := Vec.fromList [69, 120, 105, 116, 80, 114, 111, 99, 101, 115, 115] }] }

def description : ExecutableImageDescription :=
  { entryPoint := { sectionIndex := 0, offset := 1 }
    sections := Vec.fromList [
      { name := textName
        contents := Vec.fromList [0x90, 0xc3]
        characteristics := 0x60000020 }]
    imports := Vec.fromList [kernel32] }

def preparedEntry? : Option Nat :=
  match prepareImage description with
  | .ok plan => some plan.layout.entryPointRva
  | .error _ => none

def preparedIat? : Option Nat :=
  match prepareImage description with
  | .ok plan => plan.layout.importAddressRva? 0 0
  | .error _ => none

def preparedImageSize? : Option Nat :=
  match prepareImage description with
  | .ok plan => some plan.layout.sizeOfImage
  | .error _ => none

def badEntryError? : Option String :=
  match prepareImage { description with entryPoint := { sectionIndex := 0, offset := 2 } } with
  | .ok _ => none
  | .error error => some error

def generatedImportEntryError? : Option String :=
  match prepareImage { description with entryPoint := { sectionIndex := 1, offset := 0 } } with
  | .ok _ => none
  | .error error => some error

def planFor (input : ExecutableImageDescription) : Option ImagePlan :=
  (prepareImage input).toOption

def resolvedTextBase? : Option Nat := do
  let plan ← planFor description
  let resolved ← plan.resolveSectionBase? 0
  some resolved.rva

def resolvedTextEnd? : Option Nat := do
  let plan ← planFor description
  let resolved ← plan.resolveSectionLocation? ⟨0, 2⟩
  some resolved.rva

/-- Entry location is resolved from the placed `.text` section. -/
example : preparedEntry? = some 0x1001 := by decide

/-- The requested import obtains an IAT address from the same layout. -/
example : preparedIat? = some 0x2028 := by decide

/-- `.text` and generated `.idata` determine the mapped image extent. -/
example : preparedImageSize? = some 0x3000 := by decide

/-- A nonempty section exposes its checked base through offset zero. -/
example : resolvedTextBase? = some 0x1000 := by decide

/-- The exclusive end of a section is not an addressable source byte. -/
example : resolvedTextEnd? = none := by decide

/-- An entry offset at the end of its section is rejected. -/
example : badEntryError? = some "PE entry location is outside its requested section" := by decide

/-- Generated import data cannot be selected as a requested entry section. -/
example :
    generatedImportEntryError? =
      some "PE entry location is outside its requested section" := by decide

end Tests.Artifact.PE.ImageWriter
