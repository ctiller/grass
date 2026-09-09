import Grass.Artifact.Binary.EndianLaws
import Grass.Artifact.PE.ReaderCore
import Grass.Artifact.PE.SectionTable

/-!
# PE section-header reader

This reader decodes the complete forty-byte PE image section-header record
field by field.  It does not validate by replaying the writer; the connection
to `writeSectionHeader` is stated only by the round-trip theorem below.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical Grass.Artifact.Binary Grass.Grammar

/-- One decoded PE image section-header record.  `ParsedSectionHeader.name` retains all eight
on-disk bytes, including trailing NUL bytes. -/
structure ParsedSectionHeader where
  name : Std.Logical.ByteArray
  virtualSize : BitVec 32
  virtualAddress : BitVec 32
  rawSize : BitVec 32
  rawOffset : BitVec 32
  relocationPointer : BitVec 32
  linePointer : BitVec 32
  relocationCount : BitVec 16
  lineCount : BitVec 16
  characteristics : BitVec 32
deriving DecidableEq

/-- Decode every field of one PE image section header and leave the exact suffix. -/
def readSectionHeader (input : Std.Logical.ByteArray) : ParseResult ParsedSectionHeader :=
  continueRead (takeExact 8 input) fun name rest0 =>
  continueRead (takeLittleEndian 4 rest0) fun virtualSize rest1 =>
  continueRead (takeLittleEndian 4 rest1) fun virtualAddress rest2 =>
  continueRead (takeLittleEndian 4 rest2) fun rawSize rest3 =>
  continueRead (takeLittleEndian 4 rest3) fun rawOffset rest4 =>
  continueRead (takeLittleEndian 4 rest4) fun relocationPointer rest5 =>
  continueRead (takeLittleEndian 4 rest5) fun linePointer rest6 =>
  continueRead (takeLittleEndian 2 rest6) fun relocationCount rest7 =>
  continueRead (takeLittleEndian 2 rest7) fun lineCount rest8 =>
  continueRead (takeLittleEndian 4 rest8) fun characteristics rest9 =>
  .done (ParsedSectionHeader.mk name virtualSize virtualAddress rawSize rawOffset
    relocationPointer linePointer relocationCount lineCount characteristics) rest9

/-- The decoded value expected from this writer's selected linked-image form. -/
def PlacedSection.expectedSectionHeader (placed : PlacedSection) : ParsedSectionHeader :=
  { name := placed.source.name.write
    virtualSize := BitVec.ofNat 32 placed.virtualSpan.size
    virtualAddress := BitVec.ofNat 32 placed.virtualSpan.start
    rawSize := BitVec.ofNat 32 placed.rawSpan.size
    rawOffset := BitVec.ofNat 32 placed.rawSpan.start
    relocationPointer := 0
    linePointer := 0
    relocationCount := 0
    lineCount := 0
    characteristics := placed.source.characteristics }

/-- `readSectionHeader_writeSectionHeader_append` proves recovery of the complete header and
every trailing byte. -/
theorem readSectionHeader_writeSectionHeader_append (placed : PlacedSection)
    (suffix : Std.Logical.ByteArray) :
    readSectionHeader (writeSectionHeader placed ++ suffix) =
      .done placed.expectedSectionHeader suffix := by
  simp [readSectionHeader, continueRead, writeSectionHeader,
    PlacedSection.expectedSectionHeader, Vec.append_assoc, SectionName.length_write]

end Grass.Artifact.PE
