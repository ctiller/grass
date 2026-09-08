import Grass.Artifact.COFF.LineNumber

/-!
# COFF section raw data

This module couples an uninterpreted section payload to the exact byte count in
its section header. Pointer placement, overlap checks, relocation meaning, and
section-characteristic policy require the surrounding object and remain outside
this local byte grammar.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Raw section bytes whose length is the header's declared `sizeOfRawData`. -/
abbrev SectionRawData (sectionHeader : SectionHeader) :=
  SizedByteArray sectionHeader.sizeOfRawData.toNat

/-- `sectionRawDataFormat` accepts exactly the header-declared payload width. -/
def sectionRawDataFormat (sectionHeader : SectionHeader) :
    Format (SectionRawData sectionHeader) :=
  fixedBytesFormat sectionHeader.sizeOfRawData.toNat

/-- Parse one complete header-sized raw section payload. -/
def readSectionRawData (sectionHeader : SectionHeader)
    (input : Std.Logical.ByteArray) : ParseResult (SectionRawData sectionHeader) :=
  takeExactSized sectionHeader.sizeOfRawData.toNat input

/-- `readSectionRawData_short` reports the exact missing payload byte count. -/
theorem readSectionRawData_short (sectionHeader : SectionHeader)
    {input : Std.Logical.ByteArray}
    (short : input.length < sectionHeader.sizeOfRawData.toNat) :
    readSectionRawData sectionHeader input =
      .needMore (some (sectionHeader.sizeOfRawData.toNat - input.length)) := by
  exact takeExactSized_short short

/-- Serialize all bytes of a header-sized raw section payload. -/
def writeSectionRawData {sectionHeader : SectionHeader}
    (payload : SectionRawData sectionHeader) : Std.Logical.ByteArray :=
  writeExact payload

/-- `length_writeSectionRawData` recovers the header-declared payload width. -/
@[simp] theorem length_writeSectionRawData {sectionHeader : SectionHeader}
    (payload : SectionRawData sectionHeader) :
    (writeSectionRawData payload).length =
      sectionHeader.sizeOfRawData.toNat := by
  exact payload.2

/-- `readSectionRawData_write_append` preserves every following object byte. -/
@[simp] theorem readSectionRawData_write_append {sectionHeader : SectionHeader}
    (payload : SectionRawData sectionHeader)
    (rest : Std.Logical.ByteArray) :
    readSectionRawData sectionHeader (writeSectionRawData payload ++ rest) =
      .done payload rest := by
  exact takeExactSized_writeExact_append payload rest

/-- Whole-payload canonical writer/reader round trip. -/
@[simp] theorem readSectionRawData_write {sectionHeader : SectionHeader}
    (payload : SectionRawData sectionHeader) :
    readSectionRawData sectionHeader (writeSectionRawData payload) =
      .done payload Vec.empty := by
  simpa using readSectionRawData_write_append payload Vec.empty

/-- `writeSectionRawData_derives` witnesses the exact fixed-byte grammar. -/
theorem writeSectionRawData_derives {sectionHeader : SectionHeader}
    (payload : SectionRawData sectionHeader) :
    Derives (sectionRawDataFormat sectionHeader)
      (writeSectionRawData payload) payload Vec.empty := by
  exact (writeExact_realizes sectionHeader.sizeOfRawData.toNat).sound payload

end Grass.Artifact.COFF
