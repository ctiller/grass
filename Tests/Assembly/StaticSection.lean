import Grass.Assembly.StaticSection

namespace Grass.Tests.Assembly.StaticSection

open Grass.Artifact.PE Grass.Assembly.StaticSection
  Grass.Assembly.StaticObjects Grass.Std.Logical

def firstBytes : Grass.Std.Logical.ByteArray := Vec.fromList [1, 2, 3]
def secondBytes : Grass.Std.Logical.ByteArray := Vec.fromList [4, 5]

def table : Table := checked
  [{ name := "first", alignment := 1, kind := .rodata, bytes := firstBytes },
   { name := "second", alignment := 8, kind := .rodata, bytes := secondBytes }]
  (by decide)

def sectionName : SectionName := ⟨Vec.fromList [46, 114, 100, 97, 116, 97], by decide⟩
def layout : Option (Layout table) := layout? table sectionName 0x40000040

example : layout.map (fun result => result.objects.map Object.offset) = some [0, 8] := by decide
example : layout.map (fun result => result.rawSection.contents) =
    some (firstBytes ++ Vec.replicate 5 0 ++ secondBytes) := by decide
example : layout.map (fun result => result.lookup? "second" |>.map
    (fun object => object.declaration.bytes)) = some (some secondBytes) := by decide

def emptyTable : Table := checked
  [{ name := "empty", alignment := 4, kind := .rodata, bytes := Vec.empty }]
  (by decide)

example : (layout? emptyTable sectionName 0x40000040).isSome = true := by decide

def planFor (rawSection : RawSection) : Option ImagePlan :=
  match prepareImage {
    entryPoint := ⟨0, 0⟩
    sections := Vec.fromList [rawSection]
    imports := Vec.empty } with
  | .ok plan => some plan
  | .error _ => none

def resolveFrom (sourceTable : Table) (name : String) : Bool :=
  match layout? sourceTable sectionName 0x40000040 with
  | none => false
  | some generated =>
      match planFor generated.rawSection with
      | none => false
      | some plan => (resolveSpan? plan generated 0 name).isSome

example : resolveFrom table "second" = true := by decide

def overAlignedTable : Table := checked
  [{ name := "over", alignment := 8192, kind := .rodata, bytes := Vec.fromList [1] }]
  (by decide)

/- The canonical first-section RVA is 4096, so an 8192-aligned object at
relative offset zero is rejected at final placement. -/
example : resolveFrom overAlignedTable "over" = false := by decide

def trailingEmptyTable : Table := checked
  [{ name := "byte", alignment := 1, kind := .rodata, bytes := Vec.fromList [1] },
   { name := "empty", alignment := 1, kind := .rodata, bytes := Vec.empty }]
  (by decide)

/- A zero-length object may resolve at the section's exclusive end; it is a
span base and is never passed to the strict byte-location resolver. -/
example : resolveFrom trailingEmptyTable "empty" = true := by decide

end Grass.Tests.Assembly.StaticSection
