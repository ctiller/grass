import Grass.Artifact.COFF.SectionHeader

/-!
# Count-coupled COFF section tables

This module composes a file header with exactly the number of fixed-width
section entries named by that header. It still describes syntax only: offsets,
overlap, permissions, and relocation meaning are contextual validation layers.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- A COFF file header paired with exactly its declared number of section-table
entries. `sectionCount` makes the count coupling available to every consumer. -/
structure SectionTable where
  header : Header
  sections : Vec SectionHeader
  sectionCount : sections.length = header.numberOfSections.toNat
deriving DecidableEq, Repr

/-- The grammar's proof-bearing pair before field names are restored. -/
abbrev CheckedSectionTable :=
  {table : Header × Vec SectionHeader //
    table.2.length = table.1.numberOfSections.toNat}

/-- Restore a named section table from a count-checked grammar value. -/
def SectionTable.ofChecked (table : CheckedSectionTable) : SectionTable where
  header := table.1.1
  sections := table.1.2
  sectionCount := table.2

/-- Forget only field labels, retaining the section-count proof. -/
def SectionTable.toChecked (table : SectionTable) : CheckedSectionTable :=
  ⟨(table.header, table.sections), table.sectionCount⟩

/-- Named section tables and checked grammar values are a total isomorphism. -/
def sectionTableIsomorphism : Isomorphism CheckedSectionTable SectionTable where
  forward := SectionTable.ofChecked
  backward := SectionTable.toChecked
  backward_forward := by
    intro table
    rcases table with ⟨⟨header, entries⟩, count⟩
    rfl
  forward_backward := by
    intro table
    rcases table with ⟨header, entries, count⟩
    rfl

/-- Header followed by the number of section entries declared in the header. -/
def rawSectionTableFormat : Format (Header × Vec SectionHeader) :=
  .seq headerFormat fun header =>
    .repeat header.numberOfSections.toNat sectionHeaderFormat

/-- Promote the section-count invariant into the grammar result type. -/
def checkedSectionTableFormat : Format CheckedSectionTable :=
  rawSectionTableFormat.refineValue fun table =>
    table.2.length = table.1.numberOfSections.toNat

/-- Typed COFF header-and-section-table language. -/
def sectionTableFormat : Format SectionTable :=
  checkedSectionTableFormat.iso sectionTableIsomorphism

/-- Serialize a host-independent list of section headers in source order. -/
private def writeSectionHeaderList : List SectionHeader → Std.Logical.ByteArray
  | [] => Vec.empty
  | entry :: rest => writeSectionHeader entry ++ writeSectionHeaderList rest

/-- Serialize section headers in source order. -/
def writeSectionHeaders (entries : Vec SectionHeader) : Std.Logical.ByteArray :=
  writeSectionHeaderList entries.toList

/-- Consing one entry emits that entry before the remaining table bytes. -/
@[simp] theorem writeSectionHeaders_cons (entry : SectionHeader)
    (rest : Vec SectionHeader) :
    writeSectionHeaders (Vec.singleton entry ++ rest) =
      writeSectionHeader entry ++ writeSectionHeaders rest := by
  rfl

/-- Serialized section headers occupy exactly 40 bytes each. -/
@[simp] theorem length_writeSectionHeaders (entries : Vec SectionHeader) :
    (writeSectionHeaders entries).length = 40 * entries.length := by
  induction entries using Vec.recOnCons with
  | empty => rfl
  | cons entry rest ih =>
      rw [writeSectionHeaders_cons, Vec.length_append,
        length_writeSectionHeader, ih]
      simp [Nat.mul_add]

/-- Parse exactly `count` section headers and preserve the following suffix. -/
def readSectionHeaders :
    (count : Nat) → Std.Logical.ByteArray → ParseResult (Vec SectionHeader)
  | 0, input => .done Vec.empty input
  | count + 1, input =>
    match readSectionHeader input with
    | .done entry rest =>
      match readSectionHeaders count rest with
      | .done entries suffix => .done (Vec.singleton entry ++ entries) suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error

/-- Successful bounded parsing returns exactly the requested entry count. -/
theorem readSectionHeaders_done_length {count : Nat}
    {input entries rest}
    (success : readSectionHeaders count input = .done entries rest) :
    entries.length = count := by
  induction count generalizing input entries rest with
  | zero =>
      simp only [readSectionHeaders] at success
      injection success with entriesEq
      rw [← entriesEq]
      simp
  | succ count ih =>
      simp only [readSectionHeaders] at success
      split at success <;> try contradiction
      next entry suffix parsedEntry =>
        split at success <;> try contradiction
        next tail final parsedTail =>
          injection success with entriesEq
          rw [← entriesEq, Vec.length_append]
          simp only [Vec.length_singleton]
          rw [ih parsedTail]
          omega

/-- Bounded section-header serialization and parsing round-trip with an
arbitrary following suffix. -/
@[simp] theorem readSectionHeaders_writeSectionHeaders_append
    (entries : Vec SectionHeader) (rest : Std.Logical.ByteArray) :
    readSectionHeaders entries.length (writeSectionHeaders entries ++ rest) =
      .done entries rest := by
  induction entries using Vec.recOnCons generalizing rest with
  | empty =>
      change readSectionHeaders 0 (Vec.empty ++ rest) = .done Vec.empty rest
      simp [readSectionHeaders]
  | cons entry tail ih =>
      rw [writeSectionHeaders_cons, Vec.length_append]
      simp only [Vec.length_singleton, Nat.one_add, Vec.append_assoc,
        readSectionHeaders]
      rw [readSectionHeader_writeSectionHeader_append]
      simp only
      rw [ih rest]

/-- Every serialized vector of section entries derives from the corresponding
bounded repetition grammar. -/
theorem writeSectionHeaders_derives (entries : Vec SectionHeader) :
    Derives (.repeat entries.length sectionHeaderFormat)
      (writeSectionHeaders entries) entries Vec.empty := by
  induction entries using Vec.recOnCons with
  | empty =>
      exact Derives.repeatZero sectionHeaderFormat Vec.empty
  | cons entry tail ih =>
      rw [writeSectionHeaders_cons, Vec.length_append]
      simp only [Vec.length_singleton, Nat.one_add]
      exact Derives.repeatSucc
        ((writeSectionHeader_derives entry).appendSuffix
          (writeSectionHeaders tail)) ih

/-- Parse the file header and its entire declared section table. Before the
header is available the deficit completes that header; afterward it completes
the exact declared table. -/
def readSectionTable (input : Std.Logical.ByteArray) : ParseResult SectionTable :=
  match readHeader input with
  | .done header rest =>
    let required := 40 * header.numberOfSections.toNat
    if required ≤ rest.length then
      match readSectionHeaders header.numberOfSections.toNat rest with
      | .done entries suffix =>
        if count : entries.length = header.numberOfSections.toNat then
          .done { header, sections := entries, sectionCount := count } suffix
        else
          .invalid (.malformed "section-table count mismatch")
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    else
      .needMore (some (required - rest.length))
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Serialize a count-coupled file header and section table. -/
def writeSectionTable (table : SectionTable) : Std.Logical.ByteArray :=
  writeHeader table.header ++ writeSectionHeaders table.sections

/-- Serialized table length is its 20-byte header plus 40 bytes per declared
section, as stated by `length_writeSectionTable`. -/
@[simp] theorem length_writeSectionTable (table : SectionTable) :
    (writeSectionTable table).length =
      20 + 40 * table.header.numberOfSections.toNat := by
  simp [writeSectionTable, table.sectionCount]

/-- `readSectionTable_writeSectionTable_append` gives the canonical
header-and-section-table round trip with exact suffix preservation. -/
@[simp] theorem readSectionTable_writeSectionTable_append
    (table : SectionTable) (rest : Std.Logical.ByteArray) :
    readSectionTable (writeSectionTable table ++ rest) = .done table rest := by
  rcases table with ⟨header, entries, count⟩
  simp only [readSectionTable, writeSectionTable, Vec.append_assoc]
  rw [readHeader_writeHeader_append]
  simp only
  have enough : 40 * header.numberOfSections.toNat ≤
      (writeSectionHeaders entries ++ rest).length := by
    simp [length_writeSectionHeaders, count]
  simp only [enough, ite_true]
  have parsed : readSectionHeaders header.numberOfSections.toNat
      (writeSectionHeaders entries ++ rest) = .done entries rest := by
    simpa only [← count] using
      readSectionHeaders_writeSectionHeaders_append entries rest
  rw [parsed]
  simp only [count, ↓reduceDIte]

/-- Whole-table canonical writer/reader round trip. -/
@[simp] theorem readSectionTable_writeSectionTable (table : SectionTable) :
    readSectionTable (writeSectionTable table) = .done table Vec.empty := by
  simpa using readSectionTable_writeSectionTable_append table Vec.empty

/-- Every canonical table serialization derives from the count-coupled table
grammar. -/
theorem writeSectionTable_derives (table : SectionTable) :
    Derives sectionTableFormat (writeSectionTable table) table Vec.empty := by
  rcases table with ⟨header, entries, count⟩
  unfold sectionTableFormat
  refine @Derives.iso CheckedSectionTable SectionTable checkedSectionTableFormat
    sectionTableIsomorphism _ Vec.empty
    ⟨(header, entries), count⟩ ?_
  apply Derives.lift
  unfold rawSectionTableFormat
  exact Derives.seqAppend (writeHeader_derives header) (by
    simpa only [count] using writeSectionHeaders_derives entries)

end Grass.Artifact.COFF
