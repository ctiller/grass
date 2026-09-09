import Grass.Disasm.Entry
import Tests.Artifact.PE.Imported

/-! Entry-selection fixtures for conditional PE RVA-to-file mapping. They prove
only checked-container and original-byte-slice facts; they do not connect an
input file to a loader, fetch, executable permission, or reachable execution. -/

namespace Grass.Tests.Disasm.Entry

open Grass.Artifact.PE Grass.Disasm.Entry Grass.Std.Logical
open Tests.Artifact.PE.Imported

set_option maxRecDepth 10000

private def checkedFixture? : Option (CheckedImportedImage externalFixture) :=
  match checkImportedImage externalFixture with
  | .done checked _ => some checked
  | _ => none

theorem checked_fixture_exists : checkedFixture?.isSome := by decide

/-- This value consumes the successful parser wrapper proof rather than using
the slice-consistent imported record directly. -/
private def checkedFixture : CheckedImportedImage externalFixture :=
  checkedFixture?.get checked_fixture_exists

private def selected? : Option (Entry externalFixture) :=
  match selectEntry checkedFixture 0x1000 with
  | .ok selected => some selected
  | .error _ => none

theorem requested_rva_selects : selected?.isSome := by decide

private def selected : Entry externalFixture := selected?.get requested_rva_selects

/-- The canonical fixture's requested RVA resolves to the original file's first
raw byte and returns only its two file-backed virtual bytes. -/
def selectedSummary : Bool :=
  decide (selected.rva = 0x1000 ∧ selected.localOffset = 0 ∧
    selected.fileOffset = 512 ∧ selected.bytes = [0x90, 0xc3])

example : selectedSummary = true := by decide

/-- The selected bytes retain both checked parser provenance and the selected
section's membership in that exact parsed image. -/
example : readImportedImage externalFixture = .done selected.parserProvenance.result Vec.empty :=
  selected.parserProvenance.readExact

example : selected.parsedSection ∈ checkedFixture.result.image.sections := selected.member

example : selected.bytes =
    (externalFixture.toList.drop selected.fileOffset).take
      (fileBackedExtent selected.parsedSection - selected.localOffset) :=
  selected.originalBytes

/-- An RVA outside every declared virtual extent is refused. -/
example : (match selectEntry checkedFixture 0x9999 with
  | .error .unmapped => true
  | _ => false) = true := by decide

 /-- This remains a whole accepted PE container after changing the one section
to virtual size eight but raw size two and trimming its raw extent. -/
private def zeroFillFixture : Grass.Std.Logical.ByteArray :=
  ((((externalFixture.set 440 8).set 448 2).set 449 0).take 514)

private def zeroFillChecked? : Option (CheckedImportedImage zeroFillFixture) :=
  match checkImportedImage zeroFillFixture with
  | .done checked _ => some checked
  | _ => none

theorem zero_fill_fixture_checked : zeroFillChecked?.isSome := by decide

private def zeroFillChecked : CheckedImportedImage zeroFillFixture :=
  zeroFillChecked?.get zero_fill_fixture_checked

/-- A mapped RVA after its two file-backed bytes is refused as zero fill by the
actual entry selector. -/
example : (match selectEntry zeroFillChecked 0x1004 with
  | .error .zeroFillOnly => true
  | _ => false) = true := by decide

/-- Insert a second section header in former header padding. It overlaps the
same virtual range but has a zero raw extent at the exact end of the file, so
the imported parser accepts the complete two-section container. -/
private def ambiguousFixture : Grass.Std.Logical.ByteArray :=
  let withSecondHeader := externalFixture.take 472 ++
    (externalFixture.drop 432).take 40 ++ externalFixture.drop 512
  let count := withSecondHeader.set 174 2
  let noRawSize := (((count.set 488 0).set 489 0).set 490 0).set 491 0
  (((noRawSize.set 492 0).set 493 4).set 494 0).set 495 0

private def ambiguousChecked? : Option (CheckedImportedImage ambiguousFixture) :=
  match checkImportedImage ambiguousFixture with
  | .done checked _ => some checked
  | _ => none

theorem ambiguous_fixture_checked : ambiguousChecked?.isSome := by decide

private def ambiguousChecked : CheckedImportedImage ambiguousFixture :=
  ambiguousChecked?.get ambiguous_fixture_checked

/-- Two declared virtual matches are refused instead of choosing the first. -/
example : (match selectEntry ambiguousChecked 0x1000 with
  | .error .ambiguous => true
  | _ => false) = true := by decide

end Grass.Tests.Disasm.Entry
