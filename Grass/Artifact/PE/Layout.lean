import Grass.Artifact.PE.Description

/-!
# Absolute PE file coordinates

Every span in this module is measured from byte zero of the complete file.
The NT headers therefore begin at the DOS header's `e_lfanew` value, never at
zero of a detached header fragment. This is the coordinate discipline required
before a PE writer or reader may claim section-layout validity.

Format authority: Microsoft, [PE Format](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format),
sections "MS-DOS Stub (Image Only)", "Signature (Image Only)", "COFF File
Header (Object and Image)", "Optional Header (Image Only)", and "Section Table
(Section Headers)"; retrieved 2026-09-01 in `docs/REFERENCES.md`.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical

/-- A half-open absolute byte span `[start, start + size)` in a complete file. -/
structure FileSpan where
  start : Nat
  size : Nat
deriving DecidableEq

/-- The exclusive end of an absolute file span. -/
def FileSpan.endOffset (span : FileSpan) : Nat := span.start + span.size

/-- Two half-open spans do not overlap. -/
def FileSpan.Disjoint (left right : FileSpan) : Prop :=
  left.endOffset ≤ right.start ∨ right.endOffset ≤ left.start

instance (left right : FileSpan) : Decidable (left.Disjoint right) := by
  unfold FileSpan.Disjoint
  infer_instance

/-- Round `value` upward to the next multiple boundary. A zero alignment is
left unchanged here; image validation rejects zero before serialization. -/
def alignUp (value alignment : Nat) : Nat :=
  if alignment = 0 then value
  else value + ((alignment - value % alignment) % alignment)

/-- Alignment never moves an offset backward. -/
theorem le_alignUp (value alignment : Nat) : value ≤ alignUp value alignment := by
  unfold alignUp
  split <;> simp_all

/-- Microsoft PE Format, "MS-DOS Stub (Image Only)": the canonical adapter DOS
header stores `e_lfanew` at byte 60 and ends at byte 64. -/
def canonicalPeOffset : Nat := 64

/-- Microsoft PE Format, "Signature (Image Only)". -/
def peSignatureSize : Nat := 4

/-- Microsoft PE Format, "COFF File Header (Object and Image)". -/
def coffHeaderSize : Nat := 20

/-- Microsoft PE Format, "Optional Header (Image Only)" and PE32+ layout. -/
def optionalHeader64Size : Nat := 240

/-- Microsoft PE Format, "Section Table (Section Headers)". -/
def sectionHeaderSize : Nat := 40

/-- Size of the complete NT-header region, including the section table. -/
def ntHeadersSize (sectionCount : Nat) : Nat :=
  peSignatureSize + coffHeaderSize + optionalHeader64Size + sectionHeaderSize * sectionCount

/-- The absolute NT-header span rooted at the DOS `e_lfanew` value. -/
def ntHeadersSpan (peOffset sectionCount : Nat) : FileSpan :=
  ⟨peOffset, ntHeadersSize sectionCount⟩

/-- First legal raw-data offset for a synthesized image. -/
def firstRawOffset (peOffset sectionCount fileAlignment : Nat) : Nat :=
  alignUp (ntHeadersSpan peOffset sectionCount).endOffset fileAlignment

/-- Synthesized raw data begins at or after the absolute end of the NT headers. -/
theorem ntHeaders_end_le_firstRawOffset (peOffset sectionCount fileAlignment : Nat) :
    (ntHeadersSpan peOffset sectionCount).endOffset ≤
      firstRawOffset peOffset sectionCount fileAlignment :=
  le_alignUp _ _

/-- One requested section paired with its absolute raw-data span. -/
structure PlacedSection where
  source : RawSection
  rawSpan : FileSpan
deriving DecidableEq

/-- Place section payloads in request order, aligning each start and advancing
by the unpadded payload length. -/
def placeSectionsFrom (cursor fileAlignment : Nat) : List RawSection → List PlacedSection
  | [] => []
  | source :: tail =>
      let start := alignUp cursor fileAlignment
      let placed : PlacedSection :=
        { source
          rawSpan := ⟨start, source.contents.length⟩ }
      placed :: placeSectionsFrom placed.rawSpan.endOffset fileAlignment tail

@[simp] theorem placeSectionsFrom_length (cursor fileAlignment : Nat)
    (sections : List RawSection) :
    (placeSectionsFrom cursor fileAlignment sections).length = sections.length := by
  induction sections generalizing cursor with
  | nil => rfl
  | cons source tail ih =>
      simp only [placeSectionsFrom, List.length_cons]
      exact congrArg Nat.succ (ih _)

/-- Place all requested raw sections after the complete canonical NT-header
region. This function consumes `ExecutableImageDescription` without learning
how any section's bytes were encoded. -/
def placeRawSections (description : ExecutableImageDescription)
    (fileAlignment : Nat) : Vec PlacedSection :=
  Vec.fromList <| placeSectionsFrom
    (firstRawOffset canonicalPeOffset description.sections.length fileAlignment)
    fileAlignment description.sections.toList

/-- `placeRawSections` preserves the requested number of sections. -/
@[simp] theorem placeRawSections_length (description : ExecutableImageDescription)
    (fileAlignment : Nat) :
    (placeRawSections description fileAlignment).length = description.sections.length := by
  simp [placeRawSections, Vec.length]

end Grass.Artifact.PE
