import Grass.Assembly.StaticSection

/-! Universal regression check for the removal of the four runtime packing scans.

`oldLayoutOutput?` reproduces the old validator's observable result without
depending on `Layout.mk`, which is intentionally private.  The theorem below
shows that the old validator and the current constructor-based implementation
return exactly the same packed objects and raw section for every valid table.
-/
namespace Grass.Tests.Assembly.StaticSectionEquivalence

open Grass.Artifact.PE Grass.Assembly.StaticObjects Grass.Std.Logical
  Grass.Assembly.StaticSection

abbrev ObservableLayout := List Object × RawSection

/-- The four checks formerly performed by `StaticSection.layout?`, preserving
their order and their dependence on the candidate objects and raw contents. -/
def oldCheckedOutput? (objects : List Object) (rawSection : RawSection) :
    Option ObservableLayout :=
  if objects.all (fun object => decide
      (object.offset % object.declaration.alignment = 0)) = true then
    if ordered? objects = true then
      if objects.all (fun object => decide
          ((rawSection.contents.drop object.offset).take object.declaration.bytes.length =
            object.declaration.bytes)) = true then
        if objects.all (fun object => decide
            (object.endOffset ≤ rawSection.contents.length)) = true then
          some (objects, rawSection)
        else none
      else none
    else none
  else none

/-- Observable behavior of the pre-cleanup `layout?`; its private `Layout`
constructor carried proofs but did not alter these returned data. -/
def oldLayoutOutput? (table : Table) (name : SectionName)
    (characteristics : BitVec 32) : Option ObservableLayout :=
  let packed := packFrom 0 table.declarations
  let rawSection : RawSection := { name, contents := packed.2, characteristics }
  oldCheckedOutput? packed.1 rawSection

/-- The old four-scan validator accepts every packing generated from a validated
table and preserves the generated objects and raw section exactly. -/
theorem oldLayoutOutput?_eq_some (table : Table) (name : SectionName)
    (characteristics : BitVec 32) :
    oldLayoutOutput? table name characteristics =
      some ((packFrom 0 table.declarations).1,
        { name, contents := (packFrom 0 table.declarations).2, characteristics }) := by
  simp only [oldLayoutOutput?, oldCheckedOutput?,
    Grass.Assembly.StaticSection.Table.packFrom_offsetsAligned_all,
    packFrom_ordered, packFrom_zero_payloads_all, packFrom_zero_contained_all,
    ↓reduceIte]

/-- Project the proof-carrying current result to the data observable from the
old implementation. -/
def currentLayoutOutput? (table : Table) (name : SectionName)
    (characteristics : BitVec 32) : Option ObservableLayout :=
  (layout? table name characteristics).map fun layout =>
    (layout.objects, layout.rawSection)

/-- Universal behavior preservation for the cleanup: success/failure and the
entire object list and raw PE section agree, for all accepted input tables. -/
theorem old_current_equivalent (table : Table) (name : SectionName)
    (characteristics : BitVec 32) :
    oldLayoutOutput? table name characteristics =
      currentLayoutOutput? table name characteristics := by
  rw [oldLayoutOutput?_eq_some]
  rfl

/-- Negative control: the modeled payload scan rejects a candidate whose sole
object claims bytes absent from the raw section. -/
example (name : SectionName) (characteristics : BitVec 32) :
    oldCheckedOutput? [{ declaration :=
        { name := "mutant", alignment := 1, kind := .rodata,
          bytes := Vec.fromList [1] }, offset := 0 }]
      { name, contents := Vec.empty, characteristics } = none := by
  simp [oldCheckedOutput?, ordered?, Object.endOffset]

end Grass.Tests.Assembly.StaticSectionEquivalence
