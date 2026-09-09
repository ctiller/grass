import Grass.Artifact.PE.ImageReader

/-! Deterministic model fixtures for the bounded PE container reader.
They exercise the writer/reader connection and parser refusals; they do not
claim that Windows loads or executes the resulting bytes. -/

namespace Tests.Artifact.PE.Reader

open Grass.Artifact.PE Grass.Grammar Grass.Std.Logical

set_option maxRecDepth 10000

def textName : SectionName :=
  ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩

def description : ExecutableImageDescription :=
  { entryPoint := { sectionIndex := 0, offset := 1 }
    sections := Vec.fromList [
      { name := textName
        contents := Vec.fromList [0x90, 0xc3]
        characteristics := 0x60000020 }]
    imports := Vec.empty }

def plan? : Option ImagePlan := (prepareImage description).toOption

theorem plan_exists : plan?.isSome := by decide

def plan : ImagePlan := plan?.get plan_exists
def image : Grass.Std.Logical.ByteArray := writeImage plan

/-- The complete canonical writer fixture parses to one closed image. -/
def completeWriterImageRead : Bool :=
  match readImage image with
  | .done _ rest => decide (rest.length = 0)
  | _ => false

theorem complete_writer_image_read : completeWriterImageRead = true := by
  decide

/-- The DOS signature is checked as a supported-container discriminator. -/
def wrongMzRejected : Bool :=
  match readImage (image.set 0 0) with
  | .invalid (.unsupported message) => decide (message = "expected DOS-aware AMD64 PE32+ image")
  | _ => false

theorem wrong_mz_rejected : wrongMzRejected = true := by
  decide

/-- A one-byte-short fixed header remains repairable with the exact deficit. -/
def truncatedHeaderNeedsOne : Bool :=
  match readImage (image.take 87) with
  | .needMore (some 1) => true
  | _ => false

theorem truncated_header_needs_one : truncatedHeaderNeedsOne = true := by
  decide

/-- A one-byte-short raw payload remains repairable rather than silently accepted. -/
def truncatedPayloadNeedsOne : Bool :=
  match readImage (image.take (image.length - 1)) with
  | .needMore (some 1) => true
  | _ => false

theorem truncated_payload_needs_one : truncatedPayloadNeedsOne = true := by
  decide

/-- The first section's raw-offset low word starts at byte 88 + 240 + 20.
Changing its second little-endian byte breaks the required contiguous raw layout. -/
def rawOffsetMismatchRejected : Bool :=
  match readImage (image.set 349 0) with
  | .invalid (.malformed message) => decide (message = "PE raw section offset is not contiguous")
  | _ => false

theorem raw_offset_mismatch_rejected : rawOffsetMismatchRejected = true := by
  decide

/-- A complete image is a whole-input parser; an extra byte is not ignored. -/
def trailingByteRejected : Bool :=
  match readImage (image ++ Vec.singleton 0) with
  | .invalid .trailingInput => true
  | _ => false

theorem trailing_byte_rejected : trailingByteRejected = true := by
  decide

/-- A header extent ending before the section table is rejected. -/
def shortHeaderExtentRejected : Bool :=
  match readImage (image.set 149 0) with
  | .invalid (.malformed message) => decide (message = "PE header size precedes section table end")
  | _ => false

theorem short_header_extent_rejected : shortHeaderExtentRejected = true := by decide

/-- Opaque directory bytes are retained, not silently validated as absent. -/
def noncanonicalDirectoryRetained : Bool :=
  match readImage (image.set 216 42) with
  | .done decoded rest =>
      decide (decoded.optional.remainingDirectories.get? 0 = some 42 ∧ rest.length = 0)
  | _ => false

theorem noncanonical_directory_retained : noncanonicalDirectoryRetained = true := by decide

end Tests.Artifact.PE.Reader
