import Grass.Artifact.PE.PrefixReader
import Grass.Artifact.PE.OptionalReader
import Grass.Artifact.PE.SectionReader
import Grass.Artifact.PE.ImageWriter

/-! # Independent complete PE container reader

Headers are decoded field by field. Raw offsets must form the declared
contiguous file layout, and all section bytes (including padding) are retained.
This is a container reader, not a Windows loader acceptance claim.
-/

namespace Grass.Artifact.PE

open Grass.Grammar Grass.Std.Logical Grass.Artifact.Binary

/-- Read precisely the section count declared by the COFF header. -/
def readSectionHeaders : Nat → Std.Logical.ByteArray → ParseResult (List ParsedSectionHeader)
  | 0, input => .done [] input
  | n + 1, input =>
      continueRead (readSectionHeader input) fun header rest =>
      continueRead (readSectionHeaders n rest) fun tail suffix =>
      .done (header :: tail) suffix

/-- All section headers are recovered in order with their exact suffix. -/
theorem readSectionHeaders_write_append (sections : List PlacedSection)
    (suffix : Std.Logical.ByteArray) :
    readSectionHeaders sections.length (writeSectionTableList sections ++ suffix) =
      .done (sections.map PlacedSection.expectedSectionHeader) suffix := by
  induction sections with
  | nil => simp [readSectionHeaders, writeSectionTableList]
  | cons head tail ih =>
      simp only [List.length_cons, writeSectionTableList, Vec.append_assoc,
        readSectionHeaders, readSectionHeader_writeSectionHeader_append, continueRead,
        ih, List.map_cons]

/-- A section's full raw extent, including file-alignment padding. -/
structure ParsedSectionContents where
  header : ParsedSectionHeader
  rawData : Std.Logical.ByteArray
deriving DecidableEq

/-- Read the contiguous raw regions declared in the section table.
Every absolute file offset is checked before its byte count is consumed. -/
def readSectionContents : List ParsedSectionHeader → Nat →
    Std.Logical.ByteArray → ParseResult (List ParsedSectionContents)
  | [], _, input => .done [] input
  | header :: tail, cursor, input =>
      if header.rawOffset.toNat = cursor then
        continueRead (takeExact header.rawSize.toNat input) fun rawData rest =>
        continueRead (readSectionContents tail (cursor + header.rawSize.toNat) rest)
          fun contents suffix => .done (⟨header, rawData⟩ :: contents) suffix
      else .invalid (.malformed "PE raw section offset is not contiguous")

/-- Complete decoded image, including every reserved and padding byte. -/
structure ParsedImage where
  header : ParsedHeaderPrefix
  optional : ParsedOptionalHeader
  headerPadding : Std.Logical.ByteArray
  sections : List ParsedSectionContents
deriving DecidableEq

/-- Identify the supported DOS-aware AMD64 PE32+ container header. -/
def supportedImageHeader (header : ParsedHeaderPrefix) (optional : ParsedOptionalHeader) : Bool :=
  decide (header.dosMagic = Vec.fromList [0x4d, 0x5a]) &&
  decide (header.ntOffset.toNat = canonicalPeOffset) &&
  decide (header.signature = Vec.fromList [0x50, 0x45, 0, 0]) &&
  decide (header.machine = amd64Machine) &&
  decide (header.optionalHeaderSize = 240) &&
  decide (optional.magic = 0x020b) && decide (optional.directoryCount = 16)

/-- Decode one complete image. Header size and all raw offsets are checked;
unclaimed trailing bytes are rejected. -/
def readImage (input : Std.Logical.ByteArray) : ParseResult ParsedImage :=
  continueRead (readHeaderPrefix input) fun header rest =>
  continueRead (readOptionalHeader rest) fun optional rest =>
  if supportedImageHeader header optional then
    continueRead (readSectionHeaders header.sectionCount.toNat rest) fun headers rest =>
    let headersEnd := canonicalPeOffset + peSignatureSize + coffHeaderSize +
      optionalHeader64Size + sectionHeaderSize * header.sectionCount.toNat
    if headersEnd ≤ optional.sizeOfHeaders.toNat then
      continueRead (takeExact (optional.sizeOfHeaders.toNat - headersEnd) rest)
        fun headerPadding rest =>
      continueRead (readSectionContents headers optional.sizeOfHeaders.toNat rest)
        fun sections suffix =>
      if suffix.length = 0 then
        .done { header, optional, headerPadding, sections } Vec.empty
      else .invalid .trailingInput
    else .invalid (.malformed "PE header size precedes section table end")
  else .invalid (.unsupported "expected DOS-aware AMD64 PE32+ image")

end Grass.Artifact.PE
