import Grass.Artifact.PE.HeaderPrefix

/-!
# PE data-directory table

PE32+ optional headers end with sixteen ordered data-directory entries. This
module models their generic binary container: each entry is an uninterpreted
relative virtual address and size. Directory indices and the meaning of their
contents belong to later PE validation layers.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- One raw PE data-directory entry, without interpreting its table index. -/
structure DataDirectory where
  relativeVirtualAddress : BitVec 32
  size : BitVec 32
deriving DecidableEq, Repr

/-- Product shape consumed by the generic sequencing grammar. -/
abbrev DataDirectoryFields := BitVec 32 × BitVec 32

/-- Forget the field labels of a data-directory entry. -/
def DataDirectory.toFields (directory : DataDirectory) : DataDirectoryFields :=
  (directory.relativeVirtualAddress, directory.size)

/-- Restore a named data-directory entry from its grammar product. -/
def DataDirectory.ofFields (fields : DataDirectoryFields) : DataDirectory :=
  ⟨fields.1, fields.2⟩

/-- Named directory entries and their grammar products are a total isomorphism. -/
def dataDirectoryFieldsIsomorphism :
    Isomorphism DataDirectoryFields DataDirectory where
  forward := DataDirectory.ofFields
  backward := DataDirectory.toFields
  backward_forward := by intro fields; rcases fields with ⟨address, size⟩; rfl
  forward_backward := by intro directory; rcases directory with ⟨address, size⟩; rfl

/-- Generic binary grammar for the two little-endian directory fields. -/
def dataDirectoryFieldsFormat : Format DataDirectoryFields :=
  .seq littleEndianU32Format fun _ => littleEndianU32Format

/-- Typed language of one eight-byte PE data-directory entry. -/
def dataDirectoryFormat : Format DataDirectory :=
  dataDirectoryFieldsFormat.iso dataDirectoryFieldsIsomorphism

/-- Parse one data-directory entry with exact incomplete-prefix classification. -/
def readDataDirectory (input : Std.Logical.ByteArray) : ParseResult DataDirectory :=
  if 8 ≤ input.length then
    match takeLittleEndian 4 input with
    | .done relativeVirtualAddress rest =>
      match takeLittleEndian 4 rest with
      | .done size suffix => .done ⟨relativeVirtualAddress, size⟩ suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  else
    .needMore (some (8 - input.length))

/-- A short directory entry reports its exact missing-byte count. -/
theorem readDataDirectory_short {input : Std.Logical.ByteArray}
    (short : input.length < 8) :
    readDataDirectory input = .needMore (some (8 - input.length)) := by
  simp [readDataDirectory, Nat.not_le.mpr short]

/-- Serialize one canonical little-endian data-directory entry. -/
def writeDataDirectory (directory : DataDirectory) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) directory.relativeVirtualAddress ++
  writeLittleEndian (count := 4) directory.size

/-- Canonical data-directory entries occupy exactly eight bytes. -/
@[simp] theorem length_writeDataDirectory (directory : DataDirectory) :
    (writeDataDirectory directory).length = 8 := by
  simp [writeDataDirectory, writeLittleEndian, isoWriter, writeExact]

/-- Every canonical directory serialization derives from its typed grammar. -/
theorem writeDataDirectory_derives (directory : DataDirectory) :
    Derives dataDirectoryFormat (writeDataDirectory directory)
      directory Vec.empty := by
  rcases directory with ⟨address, size⟩
  unfold dataDirectoryFormat
  refine @Derives.iso DataDirectoryFields DataDirectory
    dataDirectoryFieldsFormat dataDirectoryFieldsIsomorphism
    _ Vec.empty (address, size) ?_
  unfold dataDirectoryFieldsFormat writeDataDirectory
  exact Derives.seqAppend
    ((writeLittleEndian_realizes 4).sound address)
    ((writeLittleEndian_realizes 4).sound size)

/-- A canonical entry round-trips while preserving an arbitrary suffix. -/
@[simp] theorem readDataDirectory_writeDataDirectory_append
    (directory : DataDirectory) (rest : Std.Logical.ByteArray) :
    readDataDirectory (writeDataDirectory directory ++ rest) =
      .done directory rest := by
  rcases directory with ⟨address, size⟩
  simp only [readDataDirectory, Vec.length_append, length_writeDataDirectory]
  have enough : 8 ≤ 8 + rest.length := by omega
  simp only [enough, ite_true, writeDataDirectory, Vec.append_assoc,
    takeLittleEndian_writeLittleEndian_append]

/-! ## Bounded directory sequences -/

/-- Host-independent recursive serializer beneath `writeDataDirectories`. -/
private def writeDataDirectoryList :
    List DataDirectory → Std.Logical.ByteArray
  | [] => Vec.empty
  | directory :: rest =>
      writeDataDirectory directory ++ writeDataDirectoryList rest

/-- Serialize data-directory entries in table order. -/
def writeDataDirectories (directories : Vec DataDirectory) :
    Std.Logical.ByteArray :=
  writeDataDirectoryList directories.toList

/-- Consing an entry emits it before the remainder of the table. -/
@[simp] theorem writeDataDirectories_cons (directory : DataDirectory)
    (rest : Vec DataDirectory) :
    writeDataDirectories (Vec.singleton directory ++ rest) =
      writeDataDirectory directory ++ writeDataDirectories rest := by
  rfl

/-- Serialized directory sequences occupy eight bytes per entry. -/
@[simp] theorem length_writeDataDirectories (directories : Vec DataDirectory) :
    (writeDataDirectories directories).length = 8 * directories.length := by
  induction directories using Vec.recOnCons with
  | empty => rfl
  | cons directory rest ih =>
      rw [writeDataDirectories_cons, Vec.length_append,
        length_writeDataDirectory, ih]
      simp [Nat.mul_add]

/-- Parse exactly `count` ordered data-directory entries. -/
def readDataDirectories :
    (count : Nat) → Std.Logical.ByteArray → ParseResult (Vec DataDirectory)
  | 0, input => .done Vec.empty input
  | count + 1, input =>
    match readDataDirectory input with
    | .done directory rest =>
      match readDataDirectories count rest with
      | .done directories suffix =>
        .done (Vec.singleton directory ++ directories) suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error

/-- Successful bounded parsing returns exactly the requested directory count. -/
theorem readDataDirectories_done_length {count : Nat}
    {input directories rest}
    (success : readDataDirectories count input = .done directories rest) :
    directories.length = count := by
  induction count generalizing input directories rest with
  | zero =>
      simp only [readDataDirectories] at success
      injection success with directoriesEq
      rw [← directoriesEq]
      simp
  | succ count ih =>
      simp only [readDataDirectories] at success
      split at success <;> try contradiction
      next directory suffix parsedDirectory =>
        split at success <;> try contradiction
        next tail final parsedTail =>
          injection success with directoriesEq restEq
          rw [← directoriesEq, Vec.length_append]
          simp only [Vec.length_singleton]
          rw [ih parsedTail]
          omega

/-- Bounded directory sequences round-trip and preserve an arbitrary suffix. -/
@[simp] theorem readDataDirectories_writeDataDirectories_append
    (directories : Vec DataDirectory) (rest : Std.Logical.ByteArray) :
    readDataDirectories directories.length
      (writeDataDirectories directories ++ rest) = .done directories rest := by
  induction directories using Vec.recOnCons generalizing rest with
  | empty =>
      change readDataDirectories 0 (Vec.empty ++ rest) = .done Vec.empty rest
      simp [readDataDirectories]
  | cons directory tail ih =>
      rw [writeDataDirectories_cons, Vec.length_append]
      simp only [Vec.length_singleton, Nat.one_add, Vec.append_assoc,
        readDataDirectories]
      rw [readDataDirectory_writeDataDirectory_append]
      simp only
      rw [ih rest]

/-- Serialized directory vectors derive from the matching repetition grammar. -/
theorem writeDataDirectories_derives (directories : Vec DataDirectory) :
    Derives (.repeat directories.length dataDirectoryFormat)
      (writeDataDirectories directories) directories Vec.empty := by
  induction directories using Vec.recOnCons with
  | empty => exact Derives.repeatZero dataDirectoryFormat Vec.empty
  | cons directory tail ih =>
      rw [writeDataDirectories_cons, Vec.length_append]
      simp only [Vec.length_singleton, Nat.one_add]
      exact Derives.repeatSucc
        ((writeDataDirectory_derives directory).appendSuffix
          (writeDataDirectories tail)) ih

/-! ## Canonical PE directory table -/

/-- The PE32+ canonical data-directory table contains exactly sixteen entries. -/
abbrev DataDirectoryTable := SizedVec DataDirectory 16

/-- Typed grammar for the canonical sixteen-entry data-directory table. -/
def dataDirectoryTableFormat : Format DataDirectoryTable :=
  (Format.repeat 16 dataDirectoryFormat).refineValue
    fun directories => directories.length = 16

/-- Parse a complete canonical directory table after preflighting all 128 bytes. -/
def readDataDirectoryTable (input : Std.Logical.ByteArray) :
    ParseResult DataDirectoryTable :=
  if 128 ≤ input.length then
    match readDataDirectories 16 input with
    | .done directories rest =>
      if count : directories.length = 16 then
        .done ⟨directories, count⟩ rest
      else
        .invalid (.malformed "data-directory table count mismatch")
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  else
    .needMore (some (128 - input.length))

/-- A short canonical table reports its exact whole-table byte deficit. -/
theorem readDataDirectoryTable_short {input : Std.Logical.ByteArray}
    (short : input.length < 128) :
    readDataDirectoryTable input = .needMore (some (128 - input.length)) := by
  simp [readDataDirectoryTable, Nat.not_le.mpr short]

/-- Serialize the sixteen entries of a canonical data-directory table. -/
def writeDataDirectoryTable (table : DataDirectoryTable) :
    Std.Logical.ByteArray :=
  writeDataDirectories table.1

/-- A canonical PE data-directory table occupies exactly 128 bytes. -/
@[simp] theorem length_writeDataDirectoryTable (table : DataDirectoryTable) :
    (writeDataDirectoryTable table).length = 128 := by
  simp [writeDataDirectoryTable]

/-- A canonical table round-trips while preserving an arbitrary suffix. -/
@[simp] theorem readDataDirectoryTable_writeDataDirectoryTable_append
    (table : DataDirectoryTable) (rest : Std.Logical.ByteArray) :
    readDataDirectoryTable (writeDataDirectoryTable table ++ rest) =
      .done table rest := by
  rcases table with ⟨directories, count⟩
  simp only [readDataDirectoryTable, writeDataDirectoryTable,
    Vec.length_append, length_writeDataDirectories]
  have enough : 128 ≤ 8 * directories.length + rest.length := by simp [count]
  simp only [enough, ite_true]
  have parsed : readDataDirectories 16
      (writeDataDirectories directories ++ rest) = .done directories rest := by
    simpa only [← count] using
      readDataDirectories_writeDataDirectories_append directories rest
  rw [parsed]
  simp only [count, ↓reduceDIte]

/-- Every canonical table serialization derives from its fixed-count grammar. -/
theorem writeDataDirectoryTable_derives (table : DataDirectoryTable) :
    Derives dataDirectoryTableFormat (writeDataDirectoryTable table)
      table Vec.empty := by
  rcases table with ⟨directories, count⟩
  unfold dataDirectoryTableFormat
  apply Derives.lift
  simpa only [writeDataDirectoryTable, count] using
    writeDataDirectories_derives directories

end Grass.Artifact.PE
