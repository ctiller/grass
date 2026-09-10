import Grass.Artifact.Binary.LittleEndian

/-!
# The PE32+ image container

The byte container `Grass.Artifact.PE.format` writes and reads: an MS-DOS
stub, `PE\0\0`, a COFF file header, a PE32+ optional header with sixteen data
directories, a section table, and the section contents at file-aligned
offsets. Everything here is bytes and arithmetic; the seam instance and its
`Sectioned` obligations live in `Grass.Artifact.PE.Target`.

Written directly over `List UInt8` through `Grass.Artifact.Binary.LittleEndian`
for the same reason `Grass.Artifact.ELF.Target` is: the legacy
`Grass.Artifact.PE.*` writer serializes `Grass.Std.Logical.ByteArray` through
`Grass.Grammar`, and reusing it would cost a `Vec Byte ↔ List UInt8` crossing
at every field. Field layouts, alignment arithmetic and citations are ported;
the architecture is not.

Format authority throughout: Microsoft, PE Format
(<https://learn.microsoft.com/en-us/windows/win32/debug/pe-format>), the
sections named per field below.

## Field table

MS-DOS Stub (Image Only) — `dosHeader`, 64 bytes: `MZ`, zeroed compatibility
fields, `e_lfanew = 64` at offset 60.

Signature (Image Only) — `peSignature`, 4 bytes: `PE\0\0` at offset 64.

COFF File Header (Object and Image), 20 bytes at offset 68:

| Field | Value |
| --- | --- |
| `Machine` | the `machine` parameter (`0x8664`, `0xAA64`) |
| `NumberOfSections` | `sections.length` |
| `TimeDateStamp` | 0 (`coffFixed`) |
| `PointerToSymbolTable`, `NumberOfSymbols` | 0 (`coffFixed`) |
| `SizeOfOptionalHeader` | 240 (`coffFixed`) |
| `Characteristics` | `0x0023` = `RELOCS_STRIPPED | EXECUTABLE_IMAGE | LARGE_ADDRESS_AWARE` (`coffFixed`) |

Optional Header Standard Fields (Image Only), 24 bytes at offset 88:

| Field | Value |
| --- | --- |
| `Magic` | `0x20B`, PE32+ (`optionalMagic`) |
| `MajorLinkerVersion`, `MinorLinkerVersion` | 14, 0 (`optionalSizes`) |
| `SizeOfCode` | summed padded raw size of executable sections |
| `SizeOfInitializedData` | summed padded raw size of non-executable sections |
| `SizeOfUninitializedData` | 0 (no `.bss`: every section carries its bytes) |
| `AddressOfEntryPoint` | `entryRva`, the entry minus the image base |
| `BaseOfCode` | the first executable section's RVA, else 0 |

Optional Header Windows-Specific Fields (Image Only), 88 bytes:

| Field | Value |
| --- | --- |
| `ImageBase` | `imageBase` |
| `SectionAlignment`, `FileAlignment` | 4096, 512 |
| `MajorOperatingSystemVersion`, `MajorSubsystemVersion` | 6, 6; minors 0 |
| `MajorImageVersion`, `MinorImageVersion`, `Win32VersionValue` | 0 |
| `SizeOfImage` | image end rounded up to 4096 |
| `SizeOfHeaders` | headers rounded up to 512 |
| `CheckSum` | 0 (not required for a non-driver image) |
| `Subsystem` | 3, `IMAGE_SUBSYSTEM_WINDOWS_CUI` |
| `DllCharacteristics` | `0x0100`, `NX_COMPAT` alone: no `DYNAMIC_BASE` (`0x0040`) and no `HIGH_ENTROPY_VA` (`0x0020`), so the absolute addresses a `Sectioned` carries are the addresses the loader uses |
| `SizeOfStackReserve` | `stackReserve` |
| `SizeOfStackCommit` | `0x1000` (`optionalTail`) |
| `SizeOfHeapReserve`, `SizeOfHeapCommit` | `0x100000`, `0x1000` (`optionalTail`) |
| `LoaderFlags` | 0 (`optionalTail`) |
| `NumberOfRvaAndSizes` | 16 (`optionalTail`) |

Optional Header Data Directories (Image Only), 128 bytes: entry 1 (Import
Table) is `importDirRva`/`importDirSize`; all fifteen others are zero.

Section Table (Section Headers), 40 bytes each:

| Field | Value |
| --- | --- |
| `Name` | the eight-byte name field, NUL-padded |
| `VirtualSize` | `bytes.length` |
| `VirtualAddress` | `rva` |
| `SizeOfRawData` | `bytes.length` rounded up to 512 |
| `PointerToRawData` | running file offset from `SizeOfHeaders` |
| `PointerToRelocations`, `PointerToLinenumbers` | 0 (`sectionHeaderZeros`) |
| `NumberOfRelocations`, `NumberOfLinenumbers` | 0 (`sectionHeaderZeros`) |
| `Characteristics` | `characteristicsWord`: `MEM_READ`/`MEM_WRITE`/`MEM_EXECUTE` (bits 30/31/29) plus `CNT_CODE` or `CNT_INITIALIZED_DATA` |

## What the reader checks

`read` reproduces the canonical layout rather than trusting stored offsets: it
compares every constant block (`dosHeader`, `peSignature`, `coffFixed`,
`optionalMagic`, `optionalTail`, the zero data directories, the zero
section-header fields) against what this writer emits, requires the `Machine`
field to be the caller's, and recomputes `SizeOfHeaders`, `SizeOfRawData` and
every file offset from `NumberOfSections` and `VirtualSize` instead of reading
them. The fields it consumes without checking are exactly the ones a canonical
image derives from data it keeps: `SizeOfCode`, `SizeOfInitializedData`,
`SizeOfUninitializedData`, `BaseOfCode`, the windows-specific block, and the
section headers' `SizeOfRawData`/`PointerToRawData`.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary

/-- Round `value` up to the next multiple of `alignment`; a zero alignment is
the identity. Ported from the legacy `Grass.Artifact.PE.alignUp`. -/
def roundUp (value alignment : Nat) : Nat :=
  if alignment = 0 then value
  else if value % alignment = 0 then value
  else value + (alignment - value % alignment)

/-- Rounding never moves a value backward. -/
theorem le_roundUp (value alignment : Nat) : value ≤ roundUp value alignment := by
  unfold roundUp
  split
  · exact Nat.le_refl value
  · split
    · exact Nat.le_refl value
    · exact Nat.le_add_right _ _

/-- Rounding adds strictly less than one positive alignment unit. -/
theorem roundUp_lt_add (value : Nat) {alignment : Nat} (positive : 0 < alignment) :
    roundUp value alignment < value + alignment := by
  unfold roundUp
  rw [if_neg (Nat.ne_of_gt positive)]
  split
  · omega
  · have remainder : value % alignment < alignment := Nat.mod_lt value positive
    omega

/-- Rounding lands on a multiple of a positive alignment. -/
theorem roundUp_mod (value : Nat) {alignment : Nat} (positive : 0 < alignment) :
    roundUp value alignment % alignment = 0 := by
  unfold roundUp
  rw [if_neg (Nat.ne_of_gt positive)]
  split
  next aligned => exact aligned
  next =>
    have remainder : value % alignment < alignment := Nat.mod_lt value positive
    have fills : value % alignment + (alignment - value % alignment) = alignment := by omega
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : alignment - value % alignment < alignment),
      fills, Nat.mod_self]

/-- `FileAlignment`; the PE32+ minimum for a non-`SectionAlignment` image. -/
def fileAlign : Nat := 512

/-- `SectionAlignment`; the x64 and ARM64 page size. -/
def sectionAlign : Nat := 4096

/-- The `ImageBase` granularity the loader requires: 64 KiB. -/
def imageBaseAlign : Nat := 65536

/-- One section-table entry, "Section Table (Section Headers)". -/
def sectionHeaderBytes : Nat := 40

/-- Byte just past the section table: 64-byte DOS stub, 4-byte signature,
20-byte COFF header, 240-byte optional header, then the section table. -/
def headersEnd (sectionCount : Nat) : Nat := 328 + sectionHeaderBytes * sectionCount

/-- `SizeOfHeaders`: everything before the first section's raw data. -/
def sizeOfHeadersOf (sectionCount : Nat) : Nat := roundUp (headersEnd sectionCount) fileAlign

/-- A section in the container: the raw eight-byte `Name` field, the RVA, the
bytes, and the three permission bits `Characteristics` carries. `sizeBound`
is what makes `VirtualSize` and `SizeOfRawData` round-trip through their
32-bit fields. -/
structure PeSection where
  nameBytes : List UInt8
  nameLength : nameBytes.length = 8
  rva : UInt32
  bytes : List UInt8
  sizeBound : bytes.length + fileAlign < 4294967296
  readable : Bool
  writable : Bool
  executable : Bool
deriving DecidableEq

/-- The PE32+ image container. `importDirRva`/`importDirSize` are data
directory 1; both are zero when the image imports nothing. -/
structure Artifact where
  imageBase : UInt64
  entryRva : UInt32
  stackReserve : UInt64
  sections : List PeSection
  /-- `NumberOfSections` is 16-bit. -/
  sectionCountBound : sections.length < 65536
  importDirRva : UInt32
  importDirSize : UInt32
deriving DecidableEq

/-- `SizeOfRawData`: a section's bytes padded to `FileAlignment`. -/
def rawSize (sec : PeSection) : Nat := roundUp sec.bytes.length fileAlign

/-- `SizeOfCode`. -/
def sizeOfCode : List PeSection → Nat
  | [] => 0
  | sec :: rest => (if sec.executable then rawSize sec else 0) + sizeOfCode rest

/-- `SizeOfInitializedData`; every non-executable section counts, since this
format has no uninitialized section. -/
def sizeOfInitializedData : List PeSection → Nat
  | [] => 0
  | sec :: rest => (if sec.executable then 0 else rawSize sec) + sizeOfInitializedData rest

/-- `BaseOfCode`. -/
def baseOfCode : List PeSection → UInt32
  | [] => 0
  | sec :: rest => if sec.executable then sec.rva else baseOfCode rest

/-- The greatest mapped end RVA. -/
def imageEnd : List PeSection → Nat
  | [] => 0
  | sec :: rest => max (sec.rva.toNat + sec.bytes.length) (imageEnd rest)

/-- `SizeOfImage`: the mapped extent, including the mapped headers, rounded up
to `SectionAlignment`. -/
def sizeOfImage (sectionCount : Nat) (sections : List PeSection) : Nat :=
  roundUp (max (roundUp (sizeOfHeadersOf sectionCount) sectionAlign) (imageEnd sections))
    sectionAlign

/-- "MS-DOS Stub (Image Only)": `MZ`, zeroed compatibility fields, and
`e_lfanew` at byte 60. No DOS program body; a Windows loader reads only the
signature and `e_lfanew`. -/
def dosHeader : List UInt8 := [0x4d, 0x5a] ++ List.replicate 58 0 ++ writeU32LE 64

@[simp] theorem length_dosHeader : dosHeader.length = 64 := by simp [dosHeader]

/-- "Signature (Image Only)". -/
def peSignature : List UInt8 := [0x50, 0x45, 0, 0]

@[simp] theorem length_peSignature : peSignature.length = 4 := rfl

/-- The COFF fields after `NumberOfSections`: `TimeDateStamp`,
`PointerToSymbolTable`, `NumberOfSymbols`, `SizeOfOptionalHeader`,
`Characteristics`. `0x0023` is `IMAGE_FILE_RELOCS_STRIPPED |
IMAGE_FILE_EXECUTABLE_IMAGE | IMAGE_FILE_LARGE_ADDRESS_AWARE`: stripped
relocations are what forbid the loader to move the image. -/
def coffFixed : List UInt8 :=
  writeU32LE 0 ++ writeU32LE 0 ++ writeU32LE 0 ++ writeU16LE 240 ++ writeU16LE 0x0023

@[simp] theorem length_coffFixed : coffFixed.length = 16 := by simp [coffFixed]

/-- `Magic = 0x20B`, PE32+. -/
def optionalMagic : List UInt8 := writeU16LE 0x020b

@[simp] theorem length_optionalMagic : optionalMagic.length = 2 := by simp [optionalMagic]

/-- Linker version and the three size fields, all derived from the sections. -/
def optionalSizes (code initializedData : UInt32) : List UInt8 :=
  [14, 0] ++ writeU32LE code ++ writeU32LE initializedData ++ writeU32LE 0

@[simp] theorem length_optionalSizes (code initializedData : UInt32) :
    (optionalSizes code initializedData).length = 14 := by simp [optionalSizes]

/-- The windows-specific fields between `ImageBase` and `SizeOfStackReserve`.
`DllCharacteristics = 0x0100` is `NX_COMPAT` alone. -/
def optionalWindows (imageSize headerSize : UInt32) : List UInt8 :=
  writeU32LE 4096 ++ writeU32LE 512 ++ writeU16LE 6 ++ writeU16LE 0 ++ writeU16LE 0 ++
    writeU16LE 0 ++ writeU16LE 6 ++ writeU16LE 0 ++ writeU32LE 0 ++ writeU32LE imageSize ++
    writeU32LE headerSize ++ writeU32LE 0 ++ writeU16LE 3 ++ writeU16LE 0x0100

@[simp] theorem length_optionalWindows (imageSize headerSize : UInt32) :
    (optionalWindows imageSize headerSize).length = 40 := by simp [optionalWindows]

/-- `SizeOfStackCommit`, `SizeOfHeapReserve`, `SizeOfHeapCommit`,
`LoaderFlags`, `NumberOfRvaAndSizes`. -/
def optionalTail : List UInt8 :=
  writeU64LE 0x1000 ++ writeU64LE 0x100000 ++ writeU64LE 0x1000 ++ writeU32LE 0 ++ writeU32LE 16

@[simp] theorem length_optionalTail : optionalTail.length = 32 := by simp [optionalTail]

/-- One all-zero data directory entry: RVA and size. -/
def dataDirectoryZero : List UInt8 := writeU32LE 0 ++ writeU32LE 0

@[simp] theorem length_dataDirectoryZero : dataDirectoryZero.length = 8 := by
  simp [dataDirectoryZero]

/-- Data directories 2 through 15, all zero. -/
def dataDirectoryTail : List UInt8 := List.replicate 112 0

@[simp] theorem length_dataDirectoryTail : dataDirectoryTail.length = 112 := by
  simp [dataDirectoryTail]

/-- The section-header fields a linked image never uses. -/
def sectionHeaderZeros : List UInt8 := List.replicate 12 0

@[simp] theorem length_sectionHeaderZeros : sectionHeaderZeros.length = 12 := by
  simp [sectionHeaderZeros]

/-- Pack the permission bits into `Characteristics`: `IMAGE_SCN_MEM_READ`
(`0x40000000`), `IMAGE_SCN_MEM_WRITE` (`0x80000000`), `IMAGE_SCN_MEM_EXECUTE`
(`0x20000000`). The content class is a function of the execute bit:
`IMAGE_SCN_CNT_CODE` (`0x20`) for executable sections,
`IMAGE_SCN_CNT_INITIALIZED_DATA` (`0x40`) otherwise, so it carries no
information the three bits do not. -/
def characteristicsWord (readable writable executable : Bool) : UInt32 :=
  UInt32.ofNat
    ((if executable then 0x20000020 else 0x00000040) + (if readable then 0x40000000 else 0) +
      (if writable then 0x80000000 else 0))

/-- Unpack `Characteristics` bits 30, 31 and 29. -/
def readCharacteristics (v : UInt32) : Bool × Bool × Bool :=
  (v.toNat / 0x40000000 % 2 = 1, v.toNat / 0x80000000 % 2 = 1, v.toNat / 0x20000000 % 2 = 1)

/-- Packing and unpacking `Characteristics` round-trip, for all eight
permission combinations. -/
theorem readCharacteristics_characteristicsWord (r w x : Bool) :
    readCharacteristics (characteristicsWord r w x) = (r, w, x) := by
  cases r <;> cases w <;> cases x <;> decide

/-- One 40-byte section-table entry, at a running `PointerToRawData`. -/
def writeSectionEntry (sec : PeSection) (rawPointer : Nat) : List UInt8 :=
  sec.nameBytes ++ writeU32LE (UInt32.ofNat sec.bytes.length) ++ writeU32LE sec.rva ++
    writeU32LE (UInt32.ofNat (rawSize sec)) ++ writeU32LE (UInt32.ofNat rawPointer) ++
    sectionHeaderZeros ++ writeU32LE (characteristicsWord sec.readable sec.writable sec.executable)

/-- The section table, threading `PointerToRawData` from `SizeOfHeaders`
through each section's padded raw size. -/
def writeSectionEntries (rawCursor : Nat) : List PeSection → List UInt8
  | [] => []
  | sec :: rest => writeSectionEntry sec rawCursor ++ writeSectionEntries (rawCursor + rawSize sec) rest

/-- Section contents, each padded to `FileAlignment`, in section-table order. -/
def writePayloads : List PeSection → List UInt8
  | [] => []
  | sec :: rest =>
      sec.bytes ++ List.replicate (rawSize sec - sec.bytes.length) 0 ++ writePayloads rest

/-- Everything up to the end of the section table. -/
def writeHeaders (machine : UInt16) (artifact : Artifact) : List UInt8 :=
  dosHeader ++ peSignature ++ writeU16LE machine ++
    writeU16LE (UInt16.ofNat artifact.sections.length) ++ coffFixed ++ optionalMagic ++
    optionalSizes (UInt32.ofNat (sizeOfCode artifact.sections))
      (UInt32.ofNat (sizeOfInitializedData artifact.sections)) ++
    writeU32LE artifact.entryRva ++ writeU32LE (baseOfCode artifact.sections) ++
    writeU64LE artifact.imageBase ++
    optionalWindows (UInt32.ofNat (sizeOfImage artifact.sections.length artifact.sections))
      (UInt32.ofNat (sizeOfHeadersOf artifact.sections.length)) ++
    writeU64LE artifact.stackReserve ++ optionalTail ++ dataDirectoryZero ++
    writeU32LE artifact.importDirRva ++ writeU32LE artifact.importDirSize ++ dataDirectoryTail ++
    writeSectionEntries (sizeOfHeadersOf artifact.sections.length) artifact.sections

/-- The complete image: headers, header padding to `SizeOfHeaders`, then the
file-aligned section contents. -/
def write (machine : UInt16) (artifact : Artifact) : List UInt8 :=
  writeHeaders machine artifact ++
    List.replicate
      (sizeOfHeadersOf artifact.sections.length - headersEnd artifact.sections.length) 0 ++
    writePayloads artifact.sections

/-- What the reader keeps from one section header: `Name`, `VirtualSize`,
`VirtualAddress`, and the three permission bits. `SizeOfRawData` and
`PointerToRawData` are consumed and discarded, because this reader only reads
what this writer emits: contents follow the headers contiguously in
section-table order, so a stored offset would be redundant. -/
abbrev SectionFields : Type := List UInt8 × UInt32 × UInt32 × Bool × Bool × Bool

/-- Read `count` section headers from the head of the list. -/
def readSectionHeaders : Nat → List UInt8 → Option (List SectionFields × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes =>
      match takeBytes 8 bytes with
      | none => none
      | some (name, bytes) =>
      match readU32LE bytes with
      | none => none
      | some (virtualSize, bytes) =>
      match readU32LE bytes with
      | none => none
      | some (rva, bytes) =>
      match takeBytes 4 bytes with
      | none => none
      | some (_rawSizeField, bytes) =>
      match takeBytes 4 bytes with
      | none => none
      | some (_rawPointer, bytes) =>
      match takeBytes 12 bytes with
      | none => none
      | some (zeros, bytes) =>
      match readU32LE bytes with
      | none => none
      | some (characteristics, bytes) =>
          if zeros = sectionHeaderZeros then
            let (r, w, x) := readCharacteristics characteristics
            match readSectionHeaders n bytes with
            | none => none
            | some (tail, rest) => some ((name, virtualSize, rva, r, w, x) :: tail, rest)
          else none

/-- Split the contents region using each header's own `VirtualSize`, skipping
the file-alignment padding this writer emits after every section. -/
def splitPayloads : List SectionFields → List UInt8 → Option (List PeSection)
  | [], _ => some []
  | (name, virtualSize, rva, r, w, x) :: tail, bytes =>
      match takeBytes virtualSize.toNat bytes with
      | none => none
      | some (secBytes, bytes) =>
      match takeBytes (roundUp virtualSize.toNat fileAlign - virtualSize.toNat) bytes with
      | none => none
      | some (_padding, bytes) =>
      match splitPayloads tail bytes with
      | none => none
      | some tailSections =>
          if h : name.length = 8 ∧ secBytes.length + fileAlign < 4294967296 then
            some (⟨name, h.1, rva, secBytes, h.2, r, w, x⟩ :: tailSections)
          else none

/-- Recover an image, refusing anything but the exact canonical stub,
signature, COFF tail, optional-header magic and tail, zero data directories,
and the caller's `Machine`. -/
def read (machine : UInt16) (bytes : List UInt8) : Option Artifact :=
  match takeBytes 64 bytes with
  | none => none
  | some (dos, bytes) =>
  match takeBytes 4 bytes with
  | none => none
  | some (signature, bytes) =>
  match readU16LE bytes with
  | none => none
  | some (readMachine, bytes) =>
  match readU16LE bytes with
  | none => none
  | some (sectionCount, bytes) =>
  match takeBytes 16 bytes with
  | none => none
  | some (coff, bytes) =>
  match takeBytes 2 bytes with
  | none => none
  | some (magic, bytes) =>
  match takeBytes 14 bytes with
  | none => none
  | some (_sizes, bytes) =>
  match readU32LE bytes with
  | none => none
  | some (entryRva, bytes) =>
  match takeBytes 4 bytes with
  | none => none
  | some (_baseOfCode, bytes) =>
  match readU64LE bytes with
  | none => none
  | some (imageBase, bytes) =>
  match takeBytes 40 bytes with
  | none => none
  | some (_windows, bytes) =>
  match readU64LE bytes with
  | none => none
  | some (stackReserve, bytes) =>
  match takeBytes 32 bytes with
  | none => none
  | some (tail, bytes) =>
  match takeBytes 8 bytes with
  | none => none
  | some (exportDirectory, bytes) =>
  match readU32LE bytes with
  | none => none
  | some (importDirRva, bytes) =>
  match readU32LE bytes with
  | none => none
  | some (importDirSize, bytes) =>
  match takeBytes 112 bytes with
  | none => none
  | some (directoryTail, bytes) =>
  match readSectionHeaders sectionCount.toNat bytes with
  | none => none
  | some (headers, bytes) =>
  match takeBytes (sizeOfHeadersOf sectionCount.toNat - headersEnd sectionCount.toNat) bytes with
  | none => none
  | some (_headerPadding, bytes) =>
  match splitPayloads headers bytes with
  | none => none
  | some sections =>
      if h : dos = dosHeader ∧ signature = peSignature ∧ readMachine = machine ∧
          coff = coffFixed ∧ magic = optionalMagic ∧ tail = optionalTail ∧
          exportDirectory = dataDirectoryZero ∧ directoryTail = dataDirectoryTail ∧
          sections.length < 65536 then
        some { imageBase, entryRva, stackReserve, sections,
               sectionCountBound := h.2.2.2.2.2.2.2.2, importDirRva, importDirSize }
      else none

/-- A section's header fields as the reader recovers them. -/
def headerFields (sec : PeSection) : SectionFields :=
  (sec.nameBytes, UInt32.ofNat sec.bytes.length, sec.rva, sec.readable, sec.writable,
    sec.executable)

/-- Section headers are recovered exactly, for the exact number written, with
the exact byte suffix. -/
theorem readSectionHeaders_writeSectionEntries (rawCursor : Nat) (sections : List PeSection)
    (rest : List UInt8) :
    readSectionHeaders sections.length (writeSectionEntries rawCursor sections ++ rest) =
      some (sections.map headerFields, rest) := by
  induction sections generalizing rawCursor with
  | nil => rfl
  | cons sec sections ih =>
      have shape : writeSectionEntries rawCursor (sec :: sections) ++ rest =
          sec.nameBytes ++ (writeU32LE (UInt32.ofNat sec.bytes.length) ++
            (writeU32LE sec.rva ++ (writeU32LE (UInt32.ofNat (rawSize sec)) ++
              (writeU32LE (UInt32.ofNat rawCursor) ++ (sectionHeaderZeros ++
                (writeU32LE (characteristicsWord sec.readable sec.writable sec.executable) ++
                  (writeSectionEntries (rawCursor + rawSize sec) sections ++ rest))))))) := by
        simp [writeSectionEntries, writeSectionEntry, List.append_assoc]
      rw [List.length_cons, shape]
      simp only [readSectionHeaders, takeBytes_append_of_eq sec.nameLength,
        takeBytes_append_of_eq length_sectionHeaderZeros, takeBytes_writeU32LE_append,
        readU32LE_writeU32LE_append, readCharacteristics_characteristicsWord, ↓reduceIte, ih,
        List.map_cons, headerFields]

/-- Splitting the contents region with the headers' own `VirtualSize` values
recovers the exact sections and the exact byte suffix; `PeSection.sizeBound`
and `PeSection.nameLength` are exactly the two facts the reader has to
re-establish. -/
theorem splitPayloads_writePayloads_append (sections : List PeSection) (rest : List UInt8) :
    splitPayloads (sections.map headerFields) (writePayloads sections ++ rest) = some sections := by
  induction sections with
  | nil => rfl
  | cons sec sections ih =>
      have shape : writePayloads (sec :: sections) ++ rest =
          sec.bytes ++ (List.replicate (rawSize sec - sec.bytes.length) 0 ++
            (writePayloads sections ++ rest)) := by
        simp [writePayloads, List.append_assoc]
      have sizeEq : (UInt32.ofNat sec.bytes.length).toNat = sec.bytes.length := by
        rw [UInt32.toNat_ofNat']
        exact Nat.mod_eq_of_lt (by have := sec.sizeBound; simp [fileAlign] at this; omega)
      have padLength : (List.replicate (rawSize sec - sec.bytes.length) (0 : UInt8)).length =
          roundUp sec.bytes.length fileAlign - sec.bytes.length := by
        simp [rawSize]
      simp only [List.map_cons, headerFields, splitPayloads, sizeEq]
      rw [shape, takeBytes_append]
      simp only [takeBytes_append_of_eq padLength, ih, sec.nameLength, sec.sizeBound, and_self,
        ↓reduceDIte]

/-- The no-trailing-bytes instance, matching what `read` sees once the section
table and header padding are consumed. -/
theorem splitPayloads_writePayloads (sections : List PeSection) :
    splitPayloads (sections.map headerFields) (writePayloads sections) = some sections := by
  simpa using splitPayloads_writePayloads_append sections []

/-- The reader inverts the writer exactly, for every artifact and every
`machine`. -/
theorem read_write (machine : UInt16) (artifact : Artifact) :
    read machine (write machine artifact) = some artifact := by
  have countEq : (UInt16.ofNat artifact.sections.length).toNat = artifact.sections.length := by
    rw [UInt16.toNat_ofNat']
    exact Nat.mod_eq_of_lt artifact.sectionCountBound
  have padLength :
      (List.replicate
        (sizeOfHeadersOf artifact.sections.length - headersEnd artifact.sections.length)
        (0 : UInt8)).length =
      sizeOfHeadersOf artifact.sections.length - headersEnd artifact.sections.length :=
    List.length_replicate ..
  simp only [write, writeHeaders, List.append_assoc]
  unfold read
  simp only [takeBytes_append_of_eq length_dosHeader, takeBytes_append_of_eq length_peSignature,
    takeBytes_append_of_eq length_coffFixed, takeBytes_append_of_eq length_optionalMagic,
    takeBytes_append_of_eq (length_optionalSizes _ _),
    takeBytes_append_of_eq (length_optionalWindows _ _),
    takeBytes_append_of_eq length_optionalTail,
    takeBytes_append_of_eq length_dataDirectoryZero,
    takeBytes_append_of_eq length_dataDirectoryTail, takeBytes_append_of_eq padLength,
    takeBytes_writeU32LE_append, readU16LE_writeU16LE_append,
    readU32LE_writeU32LE_append, readU64LE_writeU64LE_append, countEq,
    readSectionHeaders_writeSectionEntries, splitPayloads_writePayloads, and_self,
    artifact.sectionCountBound, ↓reduceDIte]

end Grass.Artifact.PE
