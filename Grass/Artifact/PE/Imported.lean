import Grass.Artifact.PE.ImageReader

/-! Bounded external AMD64 PE32+ ingestion. Follow the original DOS e_lfanew,
retain its stub, and reuse the canonical reader's field and section parsers.
Source: Microsoft PE Format, MS-DOS Stub, Signature, COFF File Header and Section
Table, https://learn.microsoft.com/en-us/windows/win32/debug/pe-format (2026-09-09).
This parser still requires contiguous raw sections, optional size 240 and 16
directories. Accepted structure is not a loader or execution certificate. -/
namespace Grass.Artifact.PE
open Grass.Grammar Grass.Std.Logical Grass.Artifact.Binary

structure ImportedPrefix where
  header : ParsedHeaderPrefix
  dosStub : Std.Logical.ByteArray

/-- Follow the on-disk NT offset instead of treating the DOS stub as a signature.
All arithmetic is unbounded Nat; takeExact checks available file bytes. -/
def readImportedPrefix (input : Std.Logical.ByteArray) : ParseResult ImportedPrefix :=
  continueRead (takeExact 2 input) fun dosMagic input =>
  continueRead (takeExact 58 input) fun dosCompatibility input =>
  continueRead (takeLittleEndian 4 input) fun ntOffset input =>
  if dosMagic = Vec.fromList [0x4d, 0x5a] then
    if 64 ≤ ntOffset.toNat then
      continueRead (takeExact (ntOffset.toNat - 64) input) fun dosStub input =>
      continueRead (readSignatureAndCoff dosMagic dosCompatibility ntOffset input)
        fun header rest => .done ⟨header, dosStub⟩ rest
    else .invalid (.malformed "NT headers overlap the DOS header")
  else .invalid (.unsupported "expected DOS MZ header")

/-- Explicit check tying every decoded section back to the original file. -/
def sectionSlicesMatch (input : Std.Logical.ByteArray)
    (sections : List ParsedSectionContents) : Bool :=
  sections.all fun parsed => decide (parsed.rawData = Vec.fromList
    ((input.toList.drop parsed.header.rawOffset.toNat).take parsed.header.rawSize.toNat))

/-- Original input indexes exact raw section slices only. This record alone does
not prove header, entry, metadata or stub parse provenance: proof consumers must
also retain the actual readImportedImage success equation. Public construction
of a slice-consistent record is not a full checked artifact identity. -/
structure ImportedImage (input : Std.Logical.ByteArray) where
  image : ParsedImage
  dosStub : Std.Logical.ByteArray
  slicesMatch : sectionSlicesMatch input image.sections = true

theorem ImportedImage.section_exact {input : Std.Logical.ByteArray}
    (result : ImportedImage input) (parsed : ParsedSectionContents)
    (member : parsed ∈ result.image.sections) :
    parsed.rawData = Vec.fromList
      ((input.toList.drop parsed.header.rawOffset.toNat).take parsed.header.rawSize.toNat) := by
  have h := List.all_eq_true.mp result.slicesMatch parsed member
  exact of_decide_eq_true h

/-- Read the actual external container, retaining unsupported/malformed and
incomplete cases. No normalization or rewriting of its bytes is performed. -/
def readImportedImage (input : Std.Logical.ByteArray) : ParseResult (ImportedImage input) :=
  continueRead (readImportedPrefix input) fun decodedPrefix rest =>
  if decodedPrefix.header.signature = Vec.fromList [0x50, 0x45, 0, 0] ∧
      decodedPrefix.header.machine = amd64Machine ∧ decodedPrefix.header.optionalHeaderSize = 240 then
    continueRead (readOptionalHeader rest) fun optional rest =>
    if optional.magic = 0x020b ∧ optional.directoryCount = 16 then
      continueRead (readSectionHeaders decodedPrefix.header.sectionCount.toNat rest) fun headers rest =>
      let headersEnd := decodedPrefix.header.ntOffset.toNat + peSignatureSize + coffHeaderSize +
        optionalHeader64Size + sectionHeaderSize * decodedPrefix.header.sectionCount.toNat
      if headersEnd ≤ optional.sizeOfHeaders.toNat then
        continueRead (takeExact (optional.sizeOfHeaders.toNat - headersEnd) rest)
          fun headerPadding rest =>
        continueRead (readSectionContents headers optional.sizeOfHeaders.toNat rest)
          fun sections suffix =>
        if suffix.length = 0 then
          if exactSlices : sectionSlicesMatch input sections = true then
            .done ⟨{ header := decodedPrefix.header, optional, headerPadding, sections },
              decodedPrefix.dosStub, exactSlices⟩ Vec.empty
          else .invalid (.malformed "section bytes disagree with original file slices")
        else .invalid .trailingInput
      else .invalid (.malformed "PE header size precedes actual section table end")
    else .invalid (.unsupported "expected PE32+ with 16 directories")
  else .invalid (.unsupported "expected AMD64 signature and 240-byte optional header")

/-- This wrapper retains actual parser provenance for all fields, in addition
to raw slice identity. It still makes no platform loadability assertion. -/
structure CheckedImportedImage (input : Std.Logical.ByteArray) where
  result : ImportedImage input
  readExact : readImportedImage input = .done result Vec.empty

/-- Freeze the successful parser equation for later entry/byte proof consumers. -/
def checkImportedImage (input : Std.Logical.ByteArray) : ParseResult (CheckedImportedImage input) :=
  match parsed : readImportedImage input with
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error
  | .done result rest =>
      if empty : rest = Vec.empty then
        .done ⟨result, by simpa only [empty] using parsed⟩ Vec.empty
      else .invalid .trailingInput

end Grass.Artifact.PE
