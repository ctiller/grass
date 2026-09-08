import Grass.Artifact.Binary.Endian
import Grass.Artifact.PE.Layout

/-!
# PE image section table serialization

`writeSectionHeader` realizes the forty-byte image section-header record from
an already placed raw section. It consumes only artifact-layer placement and
opaque bytes; instruction encoders remain callers.

Format authority: Microsoft, [PE Format](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format),
section "Section Table (Section Headers)"; retrieved 2026-09-01 in
`docs/REFERENCES.md`.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical Grass.Artifact.Binary

/-- Serialize a short section name into its exact eight-byte field. -/
def SectionName.write (name : SectionName) : Std.Logical.ByteArray :=
  name.bytes ++ Vec.replicate (8 - name.bytes.length) 0

/-- `SectionName.write` fills the complete eight-byte field. -/
@[simp] theorem SectionName.length_write (name : SectionName) : name.write.length = 8 := by
  simp [SectionName.write]
  have fits := name.fitsShortField
  omega

/-- Serialize one placed image section. Relocation and line-number pointers are
zero because those object-file tables are not carried by a linked image. -/
def writeSectionHeader (placed : PlacedSection) : Std.Logical.ByteArray :=
  placed.source.name.write ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 placed.virtualSpan.size) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 placed.virtualSpan.start) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 placed.rawSpan.size) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 placed.rawSpan.start) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeLittleEndian (count := 4) placed.source.characteristics

/-- `writeSectionHeader` emits exactly the PE section-header width. -/
@[simp] theorem length_writeSectionHeader (placed : PlacedSection) :
    (writeSectionHeader placed).length = sectionHeaderSize := by
  simp [writeSectionHeader, sectionHeaderSize]

/-- Serialize placed section headers in source order. -/
def writeSectionTableList : List PlacedSection → Std.Logical.ByteArray
  | [] => Vec.empty
  | placed :: tail => writeSectionHeader placed ++ writeSectionTableList tail

/-- The section table contains forty bytes per placed section. -/
@[simp] theorem length_writeSectionTableList (placed : List PlacedSection) :
    (writeSectionTableList placed).length = sectionHeaderSize * placed.length := by
  induction placed with
  | nil => simp [writeSectionTableList]
  | cons head tail ih =>
      simp [writeSectionTableList, ih, sectionHeaderSize]
      omega

/-- Serialize a logical vector of placed image sections. -/
def writeSectionTable (placed : Vec PlacedSection) : Std.Logical.ByteArray :=
  writeSectionTableList placed.toList

/-- `writeSectionTable` preserves the exact section count in its byte width. -/
@[simp] theorem length_writeSectionTable (placed : Vec PlacedSection) :
    (writeSectionTable placed).length = sectionHeaderSize * placed.length := by
  change (writeSectionTableList placed.toList).length =
    sectionHeaderSize * placed.toList.length
  exact length_writeSectionTableList placed.toList

end Grass.Artifact.PE
