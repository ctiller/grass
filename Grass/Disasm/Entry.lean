import Grass.Artifact.PE.Imported

/-!
# Checked PE RVA entry-byte selection

`selectEntry` maps a requested RVA to one file-backed PE section and retains
the exact suffix of original input bytes. The RVA-to-file mapping follows the
PE section-table `VirtualAddress`, `VirtualSize`, `PointerToRawData`, and
`SizeOfRawData` fields (Microsoft PE Format, "Section Table (Section Headers)",
https://learn.microsoft.com/en-us/windows/win32/debug/pe-format). This is a
source-defined container mapping only. It neither loads an image nor proves
base selection, instruction fetch, reachability, executable permission, or a
committed machine transition. Section characteristics remain retained data.
-/

namespace Grass.Disasm.Entry

open Grass.Artifact.PE Grass.Std.Logical

/-- Selection failures are container-map results, not platform loader errors. -/
inductive Error where
  | unmapped
  | ambiguous
  | zeroFillOnly
  | inconsistentOriginalSlice
deriving DecidableEq, Repr

/-- The virtual extent designated by PE metadata. -/
def virtualExtent (parsedSection : ParsedSectionContents) : Nat :=
  parsedSection.header.virtualSize.toNat

/-- Bytes usable directly from the file are bounded by all three declarations:
the virtual extent, the raw-size field, and the retained raw byte count. -/
def fileBackedExtent (parsedSection : ParsedSectionContents) : Nat :=
  min (virtualExtent parsedSection)
    (min parsedSection.header.rawSize.toNat parsedSection.rawData.length)

/-- Decide whether a requested RVA is in a section's declared virtual extent. -/
def mapsRva (parsedSection : ParsedSectionContents) (rva : Nat) : Bool :=
  decide (parsedSection.header.virtualAddress.toNat ≤ rva ∧
    rva < parsedSection.header.virtualAddress.toNat + virtualExtent parsedSection)

/-- Exposed independently so callers and tests can see that multiple virtual
matches are refused instead of choosing the first section-table record. -/
def mappedSections (sections : List ParsedSectionContents) (rva : Nat) :
    List ParsedSectionContents :=
  sections.filter fun parsedSection => mapsRva parsedSection rva

/-- Choose exactly one virtual section. -/
def selectMappedSection (sections : List ParsedSectionContents) (rva : Nat) :
    Except Error ParsedSectionContents :=
  match mappedSections sections rva with
  | [] => .error .unmapped
  | [parsedSection] => .ok parsedSection
  | _ => .error .ambiguous

/-- The original file suffix beginning at one selected RVA, bounded at the
file-backed virtual end rather than extending into zero-fill-only virtual bytes. -/
def sectionBytes (parsedSection : ParsedSectionContents) (localOffset : Nat) : ByteSeq :=
  ((parsedSection.rawData.drop localOffset).take
    (fileBackedExtent parsedSection - localOffset)).toList

/-- Translate a mapped RVA to a file-backed local coordinate. A virtual byte
without retained raw bytes is deliberately refused rather than synthesized. -/
def fileBackedOffset (parsedSection : ParsedSectionContents) (rva : Nat) : Except Error Nat :=
  if _mapped : parsedSection.header.virtualAddress.toNat ≤ rva ∧
      rva < parsedSection.header.virtualAddress.toNat + virtualExtent parsedSection then
    let localOffset := rva - parsedSection.header.virtualAddress.toNat
    if localOffset < fileBackedExtent parsedSection then .ok localOffset
    else .error .zeroFillOnly
  else .error .unmapped

/-- An entry selection keeps its parser provenance, chosen section membership,
RVA/local-coordinate equation, and independently checked original byte slice. -/
structure Entry (input : Std.Logical.ByteArray) where
  parserProvenance : CheckedImportedImage input
  parsedSection : ParsedSectionContents
  member : parsedSection ∈ parserProvenance.result.image.sections
  rva : Nat
  localOffset : Nat
  localOffset_eq : rva = parsedSection.header.virtualAddress.toNat + localOffset
  fileOffset : Nat
  fileOffset_eq : fileOffset = parsedSection.header.rawOffset.toNat + localOffset
  fileBacked : localOffset < fileBackedExtent parsedSection
  bytes : ByteSeq
  bytes_eq : bytes = sectionBytes parsedSection localOffset
  originalBytes : bytes =
    (input.toList.drop fileOffset).take (fileBackedExtent parsedSection - localOffset)

/-- Extract the exact file-backed suffix for one requested RVA. All uses retain
`CheckedImportedImage.readExact`; a slice-consistent record alone is not enough
to construct an `Entry`. -/
def selectEntry {input : Std.Logical.ByteArray} (checkedInput : CheckedImportedImage input)
    (rva : Nat) : Except Error (Entry input) :=
  match selectMappedSection checkedInput.result.image.sections rva with
  | .error error => .error error
  | .ok parsedSection =>
      if member : parsedSection ∈ checkedInput.result.image.sections then
        match fileBackedOffset parsedSection rva with
        | .error error => .error error
        | .ok _ =>
          if mapped : parsedSection.header.virtualAddress.toNat ≤ rva ∧
              rva < parsedSection.header.virtualAddress.toNat + virtualExtent parsedSection then
          let localOffset := rva - parsedSection.header.virtualAddress.toNat
          if backed : localOffset < fileBackedExtent parsedSection then
            let fileOffset := parsedSection.header.rawOffset.toNat + localOffset
            let bytes := sectionBytes parsedSection localOffset
            if original : bytes =
                (input.toList.drop fileOffset).take (fileBackedExtent parsedSection - localOffset) then
              .ok ⟨checkedInput, parsedSection, member, rva, localOffset, by omega,
                fileOffset, rfl, backed, bytes, rfl, original⟩
            else .error .inconsistentOriginalSlice
          else .error .zeroFillOnly
          else .error .unmapped
      else .error .unmapped

end Grass.Disasm.Entry
