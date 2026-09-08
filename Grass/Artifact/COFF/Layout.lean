import Grass.Artifact.Binary.Span
import Grass.Artifact.COFF.RawData
import Grass.Artifact.COFF.StringTable

/-!
# Declared COFF file spans

This module lifts fixed-width COFF pointer/count fields into overflow-free byte
spans. It owns structural file placement only: machine-specific relocation
meaning and high-level link policy stay with their producers and consumers.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Std.Logical

/-- Header, optional-header bytes, and the declared section table as one prefix. -/
def Header.prefixSpan (header : Header) : ByteSpan where
  offset := 0
  length := 20 + header.sizeOfOptionalHeader.toNat +
    40 * header.numberOfSections.toNat

/-- The symbol-cell extent declared by a COFF file header. -/
def Header.symbolTableSpan (header : Header) : ByteSpan where
  offset := header.pointerToSymbolTable.toNat
  length := 18 * header.numberOfSymbols.toNat

/-- A parsed string table begins immediately after the declared symbol cells. -/
def Header.stringTableSpan (header : Header) (strings : StringTable) : ByteSpan where
  offset := (header.symbolTableSpan).endExclusive
  length := strings.declaredSize.toNat

/-- The raw-data extent declared by one section-table entry. -/
def SectionHeader.rawDataSpan (sectionHeader : SectionHeader) : ByteSpan where
  offset := sectionHeader.pointerToRawData.toNat
  length := sectionHeader.sizeOfRawData.toNat

/-- The relocation extent declared by one section-table entry. -/
def SectionHeader.relocationSpan (sectionHeader : SectionHeader) : ByteSpan where
  offset := sectionHeader.pointerToRelocations.toNat
  length := 10 * sectionHeader.numberOfRelocations.toNat

/-- The line-number extent declared by one section-table entry. -/
def SectionHeader.lineNumberSpan (sectionHeader : SectionHeader) : ByteSpan where
  offset := sectionHeader.pointerToLineNumbers.toNat
  length := 6 * sectionHeader.numberOfLineNumbers.toNat

/-- All independently addressed extents declared by one section header. -/
def SectionHeader.declaredSpans (sectionHeader : SectionHeader) : List ByteSpan :=
  [sectionHeader.rawDataSpan, sectionHeader.relocationSpan,
    sectionHeader.lineNumberSpan]

/-- Section pointer fields agree with whether their corresponding extents exist. -/
def SectionHeader.PointersCoherent (sectionHeader : SectionHeader) : Prop :=
  sectionHeader.rawDataSpan.PointerCoherent ∧
  sectionHeader.relocationSpan.PointerCoherent ∧
  sectionHeader.lineNumberSpan.PointerCoherent

instance (sectionHeader : SectionHeader) :
    Decidable sectionHeader.PointersCoherent := by
  unfold SectionHeader.PointersCoherent
  infer_instance

/-- Every addressed span in `sections`, excluding the file prefix and symbol tail. -/
def sectionDeclaredSpans (sections : Vec SectionHeader) : List ByteSpan :=
  sections.toList.flatMap SectionHeader.declaredSpans

/-- Spans for a complete declared layout with a present symbol/string-table tail. -/
def declaredFileSpans (header : Header) (sections : Vec SectionHeader)
    (strings : StringTable) : List ByteSpan :=
  header.prefixSpan :: sectionDeclaredSpans sections ++
    [header.symbolTableSpan, header.stringTableSpan strings]

/-- Spans for either an absent or a present symbol/string-table tail. -/
def declaredObjectSpans (header : Header) (sections : Vec SectionHeader)
    (strings : Option StringTable) : List ByteSpan :=
  header.prefixSpan :: sectionDeclaredSpans sections ++
    match strings with
    | none => []
    | some table => [header.symbolTableSpan, header.stringTableSpan table]

/-- Header fields agree with whether the symbol/string-table tail is present. -/
def SymbolTailLayoutCoherent (header : Header)
    (strings : Option StringTable) : Prop :=
  match strings with
  | none => header.pointerToSymbolTable.toNat = 0 ∧
      header.numberOfSymbols.toNat = 0
  | some _ => header.pointerToSymbolTable.toNat ≠ 0

instance (header : Header) (strings : Option StringTable) :
    Decidable (SymbolTailLayoutCoherent header strings) := by
  unfold SymbolTailLayoutCoherent
  split <;> infer_instance

/-- Structural validity of the pointer/count layout for a present string table.
`DeclaredLayoutValid` checks section count, pointer coherence, container bounds,
and pairwise non-overlap in unbounded arithmetic. -/
def DeclaredLayoutValid (header : Header) (sections : Vec SectionHeader)
    (strings : StringTable) (fileLength : Nat) : Prop :=
  sections.length = header.numberOfSections.toNat ∧
  header.pointerToSymbolTable.toNat ≠ 0 ∧
  (∀ sectionHeader ∈ sections.toList, sectionHeader.PointersCoherent) ∧
  (∀ span ∈ declaredFileSpans header sections strings, span.Fits fileLength) ∧
  (declaredFileSpans header sections strings).Pairwise ByteSpan.Disjoint

instance (header : Header) (sections : Vec SectionHeader)
    (strings : StringTable) (fileLength : Nat) :
    Decidable (DeclaredLayoutValid header sections strings fileLength) := by
  unfold DeclaredLayoutValid
  infer_instance

/-- Whole-object layout validity, including the optional symbol/string tail. -/
def DeclaredObjectLayoutValid (header : Header)
    (sections : Vec SectionHeader) (strings : Option StringTable)
    (fileLength : Nat) : Prop :=
  sections.length = header.numberOfSections.toNat ∧
  SymbolTailLayoutCoherent header strings ∧
  (∀ sectionHeader ∈ sections.toList, sectionHeader.PointersCoherent) ∧
  (∀ span ∈ declaredObjectSpans header sections strings,
    span.Fits fileLength) ∧
  (declaredObjectSpans header sections strings).Pairwise ByteSpan.Disjoint

instance (header : Header) (sections : Vec SectionHeader)
    (strings : Option StringTable) (fileLength : Nat) :
    Decidable (DeclaredObjectLayoutValid header sections strings fileLength) := by
  unfold DeclaredObjectLayoutValid
  infer_instance

end Grass.Artifact.COFF
