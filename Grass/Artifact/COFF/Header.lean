import Grass.Artifact.Binary.Endian

/-!
# COFF file header

The COFF file header is a fixed 20-byte record. This module owns only that
binary structure: interpretation of machine identifiers and linker policy
remain with their respective consumers.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- The seven fields of the 20-byte COFF file header. Each integer is stored
little-endian on disk; retaining bit widths in the type prevents truncation. -/
structure Header where
  machine : BitVec 16
  numberOfSections : BitVec 16
  timeDateStamp : BitVec 32
  pointerToSymbolTable : BitVec 32
  numberOfSymbols : BitVec 32
  sizeOfOptionalHeader : BitVec 16
  characteristics : BitVec 16
deriving DecidableEq, Repr

/-- The nested product used directly by the generic sequencing grammar. -/
abbrev HeaderFields :=
  BitVec 16 × BitVec 16 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 16 × BitVec 16

/-- Forget field names without losing any field or changing its width. -/
def Header.toFields (header : Header) : HeaderFields :=
  (header.machine, header.numberOfSections, header.timeDateStamp,
    header.pointerToSymbolTable, header.numberOfSymbols,
    header.sizeOfOptionalHeader, header.characteristics)

/-- Restore the named COFF record from the grammar's product value. -/
def Header.ofFields (fields : HeaderFields) : Header :=
  { machine := fields.1
    numberOfSections := fields.2.1
    timeDateStamp := fields.2.2.1
    pointerToSymbolTable := fields.2.2.2.1
    numberOfSymbols := fields.2.2.2.2.1
    sizeOfOptionalHeader := fields.2.2.2.2.2.1
    characteristics := fields.2.2.2.2.2.2 }

/-- Named headers and their grammar products are a total isomorphism. -/
def headerFieldsIsomorphism : Isomorphism HeaderFields Header where
  forward := Header.ofFields
  backward := Header.toFields
  backward_forward := by intro fields; rcases fields with ⟨a, b, c, d, e, f, g⟩; rfl
  forward_backward := by intro header; rcases header with ⟨a, b, c, d, e, f, g⟩; rfl

/-- Generic binary grammar for the seven little-endian COFF header fields. -/
def headerFieldsFormat : Format HeaderFields :=
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU16Format fun _ =>
  littleEndianU16Format

/-- The typed COFF file-header language. -/
def headerFormat : Format Header :=
  headerFieldsFormat.iso headerFieldsIsomorphism

/-- Decode one COFF header after its 20-byte bound has been established. The
public reader below owns incomplete-prefix classification. -/
private def readCompleteHeader (input : Std.Logical.ByteArray) : ParseResult Header :=
  match takeLittleEndian 2 input with
  | .done machine rest =>
    match takeLittleEndian 2 rest with
    | .done numberOfSections rest =>
      match takeLittleEndian 4 rest with
      | .done timeDateStamp rest =>
        match takeLittleEndian 4 rest with
        | .done pointerToSymbolTable rest =>
          match takeLittleEndian 4 rest with
          | .done numberOfSymbols rest =>
            match takeLittleEndian 2 rest with
            | .done sizeOfOptionalHeader rest =>
              match takeLittleEndian 2 rest with
              | .done characteristics rest => .done {
                  machine, numberOfSections, timeDateStamp,
                  pointerToSymbolTable, numberOfSymbols,
                  sizeOfOptionalHeader, characteristics } rest
              | .needMore hint => .needMore hint
              | .invalid error => .invalid error
            | .needMore hint => .needMore hint
            | .invalid error => .invalid error
          | .needMore hint => .needMore hint
          | .invalid error => .invalid error
        | .needMore hint => .needMore hint
        | .invalid error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Parse one COFF header, preserving any bytes after its fixed 20-byte prefix.
A short input reports the exact number of bytes needed to complete the header. -/
def readHeader (input : Std.Logical.ByteArray) : ParseResult Header :=
  if 20 ≤ input.length then
    readCompleteHeader input
  else
    .needMore (some (20 - input.length))

/-- Every truncated COFF header reports its exact whole-record deficit. -/
theorem readHeader_short {input : Std.Logical.ByteArray}
    (short : input.length < 20) :
    readHeader input = .needMore (some (20 - input.length)) := by
  simp [readHeader, Nat.not_le.mpr short]

/-- Serialize the canonical 20-byte representation of a COFF file header. -/
def writeHeader (header : Header) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 2) header.machine ++
  writeLittleEndian (count := 2) header.numberOfSections ++
  writeLittleEndian (count := 4) header.timeDateStamp ++
  writeLittleEndian (count := 4) header.pointerToSymbolTable ++
  writeLittleEndian (count := 4) header.numberOfSymbols ++
  writeLittleEndian (count := 2) header.sizeOfOptionalHeader ++
  writeLittleEndian (count := 2) header.characteristics

/-- A serialized COFF file header has the format-mandated width of 20 bytes. -/
@[simp] theorem length_writeHeader (header : Header) :
    (writeHeader header).length = 20 := by
  simp [writeHeader, writeLittleEndian, isoWriter, writeExact]

/-- The canonical writer emits a derivation of the typed COFF header grammar,
not merely a byte sequence that happens to satisfy the executable reader. -/
theorem writeHeader_derives (header : Header) :
    Derives headerFormat (writeHeader header) header Vec.empty := by
  rcases header with ⟨machine, sections, stamp, symbols, symbolCount, optional, flags⟩
  unfold headerFormat
  refine @Derives.iso HeaderFields Header headerFieldsFormat
    headerFieldsIsomorphism _ Vec.empty
    (machine, sections, stamp, symbols, symbolCount, optional, flags) ?_
  simp only [writeHeader, Vec.append_assoc]
  unfold headerFieldsFormat littleEndianU16Format littleEndianU32Format
  exact Derives.seqAppend
    ((writeLittleEndian_realizes 2).sound machine)
    (Derives.seqAppend
      ((writeLittleEndian_realizes 2).sound sections)
      (Derives.seqAppend
        ((writeLittleEndian_realizes 4).sound stamp)
        (Derives.seqAppend
          ((writeLittleEndian_realizes 4).sound symbols)
          (Derives.seqAppend
            ((writeLittleEndian_realizes 4).sound symbolCount)
            (Derives.seqAppend
              ((writeLittleEndian_realizes 2).sound optional)
              ((writeLittleEndian_realizes 2).sound flags))))))

/-- Reading a written header consumes exactly the header and preserves an
arbitrary following suffix. -/
@[simp] theorem readHeader_writeHeader_append (header : Header)
    (rest : Std.Logical.ByteArray) :
    readHeader (writeHeader header ++ rest) = .done header rest := by
  rcases header with ⟨machine, sections, stamp, symbols, symbolCount, optional, flags⟩
  simp only [readHeader, Vec.length_append, length_writeHeader]
  have enough : 20 ≤ 20 + rest.length := by omega
  simp only [enough, ite_true]
  simp only [readCompleteHeader, writeHeader, Vec.append_assoc]
  simp only [takeLittleEndian_writeLittleEndian_append]

/-- Whole-header writer/reader round trip. -/
@[simp] theorem readHeader_writeHeader (header : Header) :
    readHeader (writeHeader header) = .done header Vec.empty := by
  simpa using readHeader_writeHeader_append header Vec.empty

end Grass.Artifact.COFF
