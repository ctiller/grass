import Grass.Artifact.PE.Imported
import Tests.Artifact.PE.Reader

/-! Focused fixtures for bounded external PE ingestion.  The byte-exact MSVC
prefix below comes from `.lake/disasm/c/store_safe.exe` (1,536 bytes): its NT
headers are at 168, it is PE/AMD64, and it has two sections.  These fixtures
exercise container decoding only; they make no loader or execution claim. -/

namespace Tests.Artifact.PE.Imported

open Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

set_option maxRecDepth 10000

/-- Bytes 64 through 167 of the checked MSVC sample, retained verbatim. -/
def msvcDosStub : Grass.Std.Logical.ByteArray := Vec.fromList [
  0x0e, 0x1f, 0xba, 0x0e, 0x00, 0xb4, 0x09, 0xcd, 0x21, 0xb8, 0x01, 0x4c,
  0xcd, 0x21, 0x54, 0x68, 0x69, 0x73, 0x20, 0x70, 0x72, 0x6f, 0x67, 0x72,
  0x61, 0x6d, 0x20, 0x63, 0x61, 0x6e, 0x6e, 0x6f, 0x74, 0x20, 0x62, 0x65,
  0x20, 0x72, 0x75, 0x6e, 0x20, 0x69, 0x6e, 0x20, 0x44, 0x4f, 0x53, 0x20,
  0x6d, 0x6f, 0x64, 0x65, 0x2e, 0x0d, 0x0d, 0x0a, 0x24, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x3d, 0x3b, 0x33, 0xdf, 0x79, 0x5a, 0x5d, 0x8c,
  0x79, 0x5a, 0x5d, 0x8c, 0x79, 0x5a, 0x5d, 0x8c, 0xef, 0xd3, 0x59, 0x8d,
  0x78, 0x5a, 0x5d, 0x8c, 0xef, 0xd3, 0x5f, 0x8d, 0x78, 0x5a, 0x5d, 0x8c,
  0x52, 0x69, 0x63, 0x68, 0x79, 0x5a, 0x5d, 0x8c]

/-- The first 192 bytes of `store_safe.exe`: DOS header, its real stub, NT
signature, and complete COFF header. -/
def msvcPrefix : Grass.Std.Logical.ByteArray :=
  Vec.fromList [
    0x4d, 0x5a, 0x90, 0x00, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,
    0xff, 0xff, 0x00, 0x00, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xa8, 0x00, 0x00, 0x00] ++ msvcDosStub ++
  Vec.fromList [
    0x50, 0x45, 0x00, 0x00, 0x64, 0x86, 0x02, 0x00, 0xbf, 0xb6, 0xa1, 0x6a,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf0, 0x00, 0x23, 0x00]

/-- The real sample's DOS and COFF prefix is decoded at its on-disk offset. -/
def msvcPrefixAccepted : Bool :=
  match readImportedPrefix msvcPrefix with
  | .done decoded rest => decide (decoded.header.ntOffset = 168 ∧
      decoded.header.signature = Vec.fromList [0x50, 0x45, 0, 0] ∧
      decoded.header.machine = amd64Machine ∧ decoded.header.sectionCount = 2 ∧
      decoded.header.timestamp = 0x6aa1b6bf ∧ decoded.header.optionalHeaderSize = 240 ∧
      decoded.header.dosCompatibility = (msvcPrefix.take 60).drop 2 ∧
      decoded.dosStub = msvcDosStub ∧
      rest.length = 0)
  | _ => false

example : msvcPrefixAccepted = true := by decide

/-- Build an external-offset image without rewriting its accepted section bytes.
Moving NT headers from 64 to 168 consumes 104 bytes of otherwise canonical
header padding, leaving the first raw section at its declared offset 512. -/
def externalFixture : Grass.Std.Logical.ByteArray :=
  (Tests.Artifact.PE.Reader.image.take 60 ++ Vec.fromList [0xa8, 0, 0, 0]) ++
    msvcDosStub ++
    (Tests.Artifact.PE.Reader.image.drop 64).take 304 ++
    (Tests.Artifact.PE.Reader.image.drop 368).take 40 ++
    Tests.Artifact.PE.Reader.image.drop 512

def importedFixture? : Option (ImportedImage externalFixture) :=
  match readImportedImage externalFixture with
  | .done decoded _ => some decoded
  | _ => none

theorem imported_fixture_exists : importedFixture?.isSome := by decide

def importedFixture : ImportedImage externalFixture :=
  importedFixture?.get imported_fixture_exists

/-- A noncanonical e_lfanew and nonzero DOS stub survive a complete parse. -/
example : importedFixture.image.header.ntOffset = 168 ∧
    importedFixture.dosStub = msvcDosStub ∧
    importedFixture.image.sections.length = 1 := by decide

example : (match importedFixture.image.sections with
  | [parsedSection] => decide
      (parsedSection.header.rawOffset = 512 ∧ parsedSection.header.rawSize = 512)
  | _ => false) = true := by decide

/-- The immutable canonical writer output is accepted as the empty-stub case. -/
example : (match readImportedImage Tests.Artifact.PE.Reader.image with
  | .done decoded rest => decide (decoded.dosStub.length = 0 ∧ rest.length = 0)
  | _ => false) = true := by decide

/-- The provenance wrapper preserves the successful full parser equation. -/
example (checked : CheckedImportedImage externalFixture)
    (_success : checkImportedImage externalFixture = .done checked Vec.empty) :
    readImportedImage externalFixture = .done checked.result Vec.empty :=
  checked.readExact

/-- Every section byte in a successful imported result is tied to this exact
input, rather than merely to a reconstructed normalized image. -/
example (parsed : ParsedSectionContents) (member : parsed ∈ importedFixture.image.sections) :
    parsed.rawData = Vec.fromList
      ((externalFixture.toList.drop parsed.header.rawOffset.toNat).take parsed.header.rawSize.toNat) :=
  ImportedImage.section_exact importedFixture parsed member

/-- NT headers may not overlap the fixed 64-byte DOS header. -/
example : (match readImportedImage (externalFixture.set 60 63) with
  | .invalid (.malformed message) => decide (message = "NT headers overlap the DOS header")
  | _ => false) = true := by decide

/-- A file ending one byte before e_lfanew has the exact four-byte signature deficit. -/
example : (match readImportedImage (externalFixture.take 168) with
  | .needMore (some missing) => decide (missing = 4)
  | _ => false) = true := by decide

/-- A one-byte-short raw payload is not accepted as a complete file. -/
example : (match readImportedImage (externalFixture.take (externalFixture.length - 1)) with
  | .needMore (some missing) => decide (missing = 1)
  | _ => false) = true := by decide

/-- A raw offset outside the file is rejected by the contiguous section layout
check before any out-of-bounds slice can be accepted. -/
example : (match readImportedImage
    ((((externalFixture.set 452 0xff).set 453 0xff).set 454 0xff).set 455 0xff) with
  | .invalid (.malformed message) => decide (message = "PE raw section offset is not contiguous")
  | _ => false) = true := by decide

end Tests.Artifact.PE.Imported
