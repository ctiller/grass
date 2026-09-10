import Grass.Artifact.Binary.LittleEndian
import Grass.Target.Artifact

/-!
# The ELF64 executable artifact format

`Grass.Artifact.ELF.format` instantiates `Grass.Target.Format Sectioned` with a
minimal, structurally real ELF64 little-endian executable: the standard
64-byte ELF header, one `PT_LOAD` program header per section (permissions
carried by `p_flags`), and the sections' bytes packed contiguously right after
the program header table. `e_machine` is a parameter of `format`, so the same
construction serves every native ISA (`0x3E` for x86-64, `0xB7` for AArch64,
...); `e_type` is fixed to `ET_EXEC`.

This format is deliberately independent of `Grass.Artifact.ELF.Header`
(which serializes over `Grass.Std.Logical.ByteArray` through the
`Grass.Grammar` parser combinators): `Format.write`/`.read` work directly over
`List UInt8`, and reusing the combinator-based reader would need a full
`Vec Byte ↔ List UInt8` crossing at every field. `Grass.Artifact.Binary`'s
fixed-width little-endian pairs (`Grass.Artifact.Binary.LittleEndian`) give an
unconditional round trip for the same field widths with none of that
conversion, so the header below is written against them instead. The field
layout is copied from `Header64`'s documented ELF64 authority (System V
generic ABI, ELF Header).

## Limitations

- Static executables only: `assemble` refuses any program with import slots,
  since a static ELF (no `PT_DYNAMIC`, no `.dynsym`/`.dynstr`) has nowhere to
  place them. A dynamically-linked ELF (`ET_DYN`, `PT_DYNAMIC`, a real import
  resolution story) is future work.
- No section header table: `e_shoff`/`e_shnum`/`e_shstrndx` are all zero, so
  section *names* have nowhere to be recorded; `assemble` accordingly refuses
  a program with a non-empty section name. Only `PT_LOAD` program headers
  carry the loadable image, which is everything a loader needs.
- `Sectioned.stackBytes` has no ELF header field (a real loader sizes the
  stack itself); `assemble` refuses a program that requests a non-zero
  reservation.
- File offsets are **not** page-aligned: `p_offset` for the first segment is
  `64 + 56 * phnum` (header plus program header table) and later segments
  follow immediately after the previous one's bytes, with no padding. A real
  ELF loader requires `p_offset ≡ p_vaddr (mod p_align)` per segment for
  `mmap`-based loading; this writer does not attempt to satisfy that, so the
  image is not guaranteed loadable by a real OS loader even though every
  `read (write artifact) = some artifact`. Getting genuine page alignment
  right (padding bytes that round-trip on both ends) is realistic future
  work, not attempted here.
-/

namespace Grass.Artifact.ELF

open Grass.Artifact.Binary Grass.Target

/-- Host `Nat`s over 64 bits do not fit any ELF64 field; this is the shared
bound every `List UInt8` length in this format is checked against. -/
abbrev widthBound : Nat := 18446744073709551616

/-- A section as the program header table records it: an address, contents
(bound to fit the 64-bit `p_filesz`/`p_memsz` fields), and the three
permission bits `p_flags` carries. -/
structure ElfSection where
  virtualAddress : UInt64
  bytes : List UInt8
  sizeBound : bytes.length < widthBound
  readable : Bool
  writable : Bool
  executable : Bool
deriving DecidableEq

/-- The ELF64 image container: the header's `e_entry` and the program
header table's sections, bound to fit the 16-bit `e_phnum` field. -/
structure Artifact where
  entry : UInt64
  sections : List ElfSection
  phnumBound : sections.length < 65536
deriving DecidableEq

/-- The 16-byte `e_ident`: `ELFCLASS64`, `ELFDATA2LSB`, `EV_CURRENT`,
`ELFOSABI_SYSV`, no extensions. -/
def IDENT : List UInt8 := [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[simp] theorem length_IDENT : IDENT.length = 16 := rfl

/-- `ET_EXEC`. -/
def ET_EXEC : UInt16 := 2

/-- The ELF64 header size, `e_ehsize`. -/
def EHDR_SIZE : Nat := 64

/-- The ELF64 program header entry size, `e_phentsize`. -/
def PHDR_SIZE : Nat := 56

/-- `PT_LOAD`. -/
def PT_LOAD : UInt32 := 1

/-- The (unenforced) alignment recorded in `p_align`. -/
def PAGE_ALIGN : UInt64 := 0x1000

/-- Pack the three ELF permission bits (`PF_X = 1`, `PF_W = 2`, `PF_R = 4`)
into `p_flags`. -/
def flagsWord (readable writable executable : Bool) : UInt32 :=
  UInt32.ofNat
    ((if executable then 1 else 0) + (if writable then 2 else 0) + (if readable then 4 else 0))

/-- Unpack `p_flags` into the three ELF permission bits. -/
def readFlagsWord (v : UInt32) : Bool × Bool × Bool :=
  (v.toNat / 4 % 2 = 1, v.toNat / 2 % 2 = 1, v.toNat % 2 = 1)

/-- Packing and unpacking `p_flags` round-trip exactly, for every combination
of the three bits. -/
theorem readFlagsWord_flagsWord (r w x : Bool) : readFlagsWord (flagsWord r w x) = (r, w, x) := by
  cases r <;> cases w <;> cases x <;> decide

/-- The fixed-size ELF64 header, `e_machine` and `e_phnum` parameterized by
the caller and the section count. -/
def writeHeader (machine : UInt16) (entry : UInt64) (phnum : UInt16) : List UInt8 :=
  IDENT ++ writeU16LE ET_EXEC ++ writeU16LE machine ++ writeU32LE 1 ++ writeU64LE entry ++
    writeU64LE (UInt64.ofNat (EHDR_SIZE + PHDR_SIZE * phnum.toNat)) ++ writeU64LE 0 ++
    writeU32LE 0 ++ writeU16LE (UInt16.ofNat EHDR_SIZE) ++ writeU16LE (UInt16.ofNat PHDR_SIZE) ++
    writeU16LE phnum ++ writeU16LE 0 ++ writeU16LE 0 ++ writeU16LE 0

/-- One `PT_LOAD` program header. -/
def writePhdr (sec : ElfSection) (offset : UInt64) : List UInt8 :=
  writeU32LE PT_LOAD ++ writeU32LE (flagsWord sec.readable sec.writable sec.executable) ++
    writeU64LE offset ++ writeU64LE sec.virtualAddress ++ writeU64LE sec.virtualAddress ++
    writeU64LE (UInt64.ofNat sec.bytes.length) ++ writeU64LE (UInt64.ofNat sec.bytes.length) ++
    writeU64LE PAGE_ALIGN

/-- The program header table, one entry per section, with each entry's file
offset the sum of the ELF and program headers plus every earlier section's
byte length. -/
def writePhdrs (baseOffset : UInt64) : List ElfSection → List UInt8
  | [] => []
  | sec :: rest =>
      writePhdr sec baseOffset ++ writePhdrs (baseOffset + UInt64.ofNat sec.bytes.length) rest

/-- The concatenated section payloads, in order. -/
def writePayloads : List ElfSection → List UInt8
  | [] => []
  | sec :: rest => sec.bytes ++ writePayloads rest

/-- The complete ELF64 image: header, program header table, payloads. -/
def write (machine : UInt16) (artifact : Artifact) : List UInt8 :=
  let phnum := UInt16.ofNat artifact.sections.length
  let baseOffset := UInt64.ofNat (EHDR_SIZE + PHDR_SIZE * artifact.sections.length)
  writeHeader machine artifact.entry phnum ++
    writePhdrs baseOffset artifact.sections ++ writePayloads artifact.sections

/-- Read `count` program header records from the head of the list, keeping
only what the reader recovers a section from: the address, the size, and the
three permission bits. Every other field (`p_type`, `p_offset`, `p_paddr`,
`p_memsz`, `p_align`) is consumed and discarded: this reader only ever reads
what this writer emits, contiguously, so it does not need to trust a stored
offset to find the bytes. -/
def readPhdrs : Nat → List UInt8 → Option (List (UInt64 × UInt64 × Bool × Bool × Bool) × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes =>
      match takeBytes 4 bytes with
      | none => none
      | some (_type, bytes) =>
      match readU32LE bytes with
      | none => none
      | some (flags, bytes) =>
      match takeBytes 8 bytes with
      | none => none
      | some (_offset, bytes) =>
      match readU64LE bytes with
      | none => none
      | some (vaddr, bytes) =>
      match takeBytes 8 bytes with
      | none => none
      | some (_paddr, bytes) =>
      match readU64LE bytes with
      | none => none
      | some (filesz, bytes) =>
      match takeBytes 8 bytes with
      | none => none
      | some (_memsz, bytes) =>
      match takeBytes 8 bytes with
      | none => none
      | some (_align, bytes) =>
          let (r, w, x) := readFlagsWord flags
          match readPhdrs n bytes with
          | none => none
          | some (tail, rest) => some ((vaddr, filesz, r, w, x) :: tail, rest)

/-- Split the payload region into sections using each header's own `filesz`.
-/
def splitPayloads :
    List (UInt64 × UInt64 × Bool × Bool × Bool) → List UInt8 → Option (List ElfSection)
  | [], _ => some []
  | (vaddr, filesz, r, w, x) :: tail, bytes =>
      match takeBytes filesz.toNat bytes with
      | none => none
      | some (secBytes, rest) =>
      match splitPayloads tail rest with
      | none => none
      | some tailSecs =>
          if h : secBytes.length < widthBound then
            some (⟨vaddr, secBytes, h, r, w, x⟩ :: tailSecs)
          else none

/-- Recover an ELF64 image from bytes, refusing anything but the exact
canonical identification, type and machine this format writes. -/
def read (machine : UInt16) (bytes : List UInt8) : Option Artifact :=
  match takeBytes 16 bytes with
  | none => none
  | some (ident, bytes) =>
      if ident = IDENT then
        match readU16LE bytes with
        | none => none
        | some (objectType, bytes) =>
        match readU16LE bytes with
        | none => none
        | some (readMachine, bytes) =>
            if objectType = ET_EXEC ∧ readMachine = machine then
              match readU32LE bytes with
              | none => none
              | some (_version, bytes) =>
              match readU64LE bytes with
              | none => none
              | some (entry, bytes) =>
              match takeBytes 8 bytes with
              | none => none
              | some (_phoff, bytes) =>
              match takeBytes 8 bytes with
              | none => none
              | some (_shoff, bytes) =>
              match takeBytes 4 bytes with
              | none => none
              | some (_flags, bytes) =>
              match takeBytes 2 bytes with
              | none => none
              | some (_ehsize, bytes) =>
              match takeBytes 2 bytes with
              | none => none
              | some (_phentsize, bytes) =>
              match readU16LE bytes with
              | none => none
              | some (phnum, bytes) =>
              match takeBytes 2 bytes with
              | none => none
              | some (_shentsize, bytes) =>
              match takeBytes 2 bytes with
              | none => none
              | some (_shnum, bytes) =>
              match takeBytes 2 bytes with
              | none => none
              | some (_shstrndx, bytes) =>
              match readPhdrs phnum.toNat bytes with
              | none => none
              | some (headers, bytes) =>
              match splitPayloads headers bytes with
              | none => none
              | some sections =>
                  if h : sections.length < 65536 then
                    some { entry, sections, phnumBound := h }
                  else none
            else none
      else none

/-- A section's program-header fields as the reader recovers them, before
they are repacked into an `ElfSection`. -/
def headerFields (sec : ElfSection) : UInt64 × UInt64 × Bool × Bool × Bool :=
  (sec.virtualAddress, UInt64.ofNat sec.bytes.length, sec.readable, sec.writable, sec.executable)

/-- Program headers are recovered exactly, for the exact number written, with
the exact byte suffix. Unconditional: every field read back is a `UInt64`
round trip, with no size bound needed yet (that is only needed to turn the
recovered `filesz` back into the section's own byte-list length, which
`splitPayloads_writePayloads_append` below does). -/
theorem readPhdrs_writePhdrs_append (baseOffset : UInt64) (sections : List ElfSection)
    (rest : List UInt8) :
    readPhdrs sections.length (writePhdrs baseOffset sections ++ rest) =
      some (sections.map headerFields, rest) := by
  induction sections generalizing baseOffset with
  | nil => rfl
  | cons sec sections ih =>
      have shape : writePhdrs baseOffset (sec :: sections) ++ rest =
          writeU32LE PT_LOAD ++ (writeU32LE (flagsWord sec.readable sec.writable sec.executable) ++
            (writeU64LE baseOffset ++ (writeU64LE sec.virtualAddress ++
              (writeU64LE sec.virtualAddress ++
                (writeU64LE (UInt64.ofNat sec.bytes.length) ++
                  (writeU64LE (UInt64.ofNat sec.bytes.length) ++
                    (writeU64LE PAGE_ALIGN ++
                      (writePhdrs (baseOffset + UInt64.ofNat sec.bytes.length) sections ++
                        rest)))))))) := by
        simp [writePhdrs, writePhdr, List.append_assoc]
      rw [List.length_cons, shape]
      simp only [readPhdrs, takeBytes_writeU32LE_append, takeBytes_writeU64LE_append,
        readU32LE_writeU32LE_append, readU64LE_writeU64LE_append, readFlagsWord_flagsWord, ih,
        List.map_cons, headerFields]

/-- Splitting the payload region with the headers' own `filesz` values
recovers the exact sections and the exact byte suffix, given each section's
byte length actually fits the 64-bit field it was written through (the
`sizeBound` every `ElfSection` already carries). -/
theorem splitPayloads_writePayloads_append (sections : List ElfSection) (rest : List UInt8) :
    splitPayloads (sections.map headerFields) (writePayloads sections ++ rest) = some sections := by
  induction sections with
  | nil => rfl
  | cons sec sections ih =>
      have shape : writePayloads (sec :: sections) ++ rest =
          sec.bytes ++ (writePayloads sections ++ rest) := by
        simp [writePayloads, List.append_assoc]
      have sizeEq : (UInt64.ofNat sec.bytes.length).toNat = sec.bytes.length := by
        rw [UInt64.toNat_ofNat']
        exact Nat.mod_eq_of_lt sec.sizeBound
      simp only [List.map_cons, headerFields, splitPayloads, sizeEq]
      rw [shape, takeBytes_append]
      simp only [ih, sec.sizeBound, ↓reduceDIte]

/-- The no-trailing-bytes instance of `splitPayloads_writePayloads_append`,
matching exactly what `read` sees once the program header table has been
consumed. -/
theorem splitPayloads_writePayloads (sections : List ElfSection) :
    splitPayloads (sections.map headerFields) (writePayloads sections) = some sections := by
  simpa using splitPayloads_writePayloads_append sections []

/-- The reader inverts the writer exactly, for every artifact and every
`machine`: `ElfSection.sizeBound`/`Artifact.phnumBound` already guarantee
every field this format's fixed 64/16-bit widths carry fits, so nothing here
can overflow. -/
theorem read_write (machine : UInt16) (artifact : Artifact) :
    read machine (write machine artifact) = some artifact := by
  have shape : write machine artifact =
      IDENT ++ (writeU16LE ET_EXEC ++ (writeU16LE machine ++ (writeU32LE 1 ++
        (writeU64LE artifact.entry ++ (writeU64LE
          (UInt64.ofNat (EHDR_SIZE + PHDR_SIZE * (UInt16.ofNat artifact.sections.length).toNat)) ++
          (writeU64LE 0 ++ (writeU32LE 0 ++ (writeU16LE (UInt16.ofNat EHDR_SIZE) ++
            (writeU16LE (UInt16.ofNat PHDR_SIZE) ++ (writeU16LE (UInt16.ofNat artifact.sections.length) ++
              (writeU16LE 0 ++ (writeU16LE 0 ++ (writeU16LE 0 ++
                (writePhdrs (UInt64.ofNat (EHDR_SIZE + PHDR_SIZE * artifact.sections.length))
                    artifact.sections ++
                  writePayloads artifact.sections)))))))))))))) := by
    simp [write, writeHeader, List.append_assoc]
  rw [shape]
  have phnumEq : (UInt16.ofNat artifact.sections.length).toNat = artifact.sections.length := by
    rw [UInt16.toNat_ofNat']
    exact Nat.mod_eq_of_lt artifact.phnumBound
  unfold read
  simp only [takeBytes_append_of_eq length_IDENT, ↓reduceIte, readU16LE_writeU16LE_append,
    phnumEq, and_self, readU32LE_writeU32LE_append, readU64LE_writeU64LE_append,
    takeBytes_writeU16LE_append, takeBytes_writeU32LE_append, takeBytes_writeU64LE_append,
    readPhdrs_writePhdrs_append, splitPayloads_writePayloads, artifact.phnumBound, ↓reduceDIte]

/-- Whether every section in a program carries no name: no section header
table means no name field. -/
def allSectionsAnonymous (program : Sectioned) : Prop := ∀ sec ∈ program.sections, sec.name = ""

instance : DecidablePred allSectionsAnonymous := fun program =>
  inferInstanceAs (Decidable (∀ sec ∈ program.sections, sec.name = ""))

/-- `Sectioned.Disjoint`, `.EntryExecutable` and `.ImportsReadable` are plain
`def`s over decidable shapes, but instance search does not unfold ordinary
`def`s to find that, so each gets its instance spelled out against the
unfolded shape (as in `Grass.Artifact.Flat`). -/
instance (program : Sectioned) : Decidable program.Disjoint :=
  inferInstanceAs
    (Decidable (program.sections.Pairwise fun left right =>
      left.endAddress ≤ right.virtualAddress ∨ right.endAddress ≤ left.virtualAddress))

instance (program : Sectioned) : Decidable program.EntryExecutable :=
  inferInstanceAs
    (Decidable (∃ sec ∈ program.sections, sec.Contains program.entry ∧ sec.executable = true))

instance (program : Sectioned) : Decidable program.ImportsReadable :=
  inferInstanceAs
    (Decidable (∀ import_ ∈ program.imports, ∃ sec ∈ program.sections,
      sec.Contains import_.slotAddress ∧ sec.readable = true))

instance : DecidablePred Sectioned.WellFormed := fun program =>
  decidable_of_iff (program.Disjoint ∧ program.EntryExecutable ∧ program.ImportsReadable)
    (Iff.intro (fun ⟨disjoint, entryExecutable, importsReadable⟩ =>
        ⟨disjoint, entryExecutable, importsReadable⟩)
      (fun wf => ⟨wf.disjoint, wf.entryExecutable, wf.importsReadable⟩))

/-- What `assemble` accepts: a well-formed, static (no import slots), unnamed
(no section header table), stack-free (no header field for it) program whose
addresses and lengths fit this format's fixed-width fields. -/
def Eligible (program : Sectioned) : Prop :=
  program.WellFormed ∧ program.imports = [] ∧ allSectionsAnonymous program ∧
    program.stackBytes = 0 ∧ program.entry < widthBound ∧
    (∀ sec ∈ program.sections, sec.virtualAddress < widthBound) ∧
    (∀ sec ∈ program.sections, sec.bytes.length < widthBound) ∧
    program.sections.length < 65536

instance : DecidablePred Eligible := fun _program =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A carried program's section paired with a proof its byte length fits
`p_filesz`/`p_memsz`. -/
def toElfSection (sec : Grass.Target.Section) (bound : sec.bytes.length < widthBound) :
    ElfSection :=
  { virtualAddress := UInt64.ofNat sec.virtualAddress, bytes := sec.bytes, sizeBound := bound,
    readable := sec.readable, writable := sec.writable, executable := sec.executable }

/-- A recovered section, regaining the empty name every carried program
already had. -/
def toSection (fs : ElfSection) : Grass.Target.Section :=
  { name := "", virtualAddress := fs.virtualAddress.toNat, bytes := fs.bytes,
    readable := fs.readable, writable := fs.writable, executable := fs.executable }

/-- Build every section's `ElfSection`, threading the whole list's size-bound
proof one element at a time so no `List.attach` bookkeeping enters the
round-trip proof below. -/
def mkSections : (sections : List Grass.Target.Section) →
    (∀ sec ∈ sections, sec.bytes.length < widthBound) → List ElfSection
  | [], _ => []
  | sec :: rest, bound =>
      toElfSection sec (bound sec (List.mem_cons_self ..)) ::
        mkSections rest (fun s member => bound s (List.mem_cons_of_mem _ member))

@[simp] theorem length_mkSections (sections : List Grass.Target.Section)
    (bound : ∀ sec ∈ sections, sec.bytes.length < widthBound) :
    (mkSections sections bound).length = sections.length := by
  induction sections with
  | nil => rfl
  | cons sec sections ih => simp [mkSections, ih]

/-- Assemble an ELF64 image, refusing a program that is not `Eligible`. -/
def assemble (program : Sectioned) : Option Artifact :=
  if h : Eligible program then
    some
      { entry := UInt64.ofNat program.entry
        sections := mkSections program.sections h.2.2.2.2.2.2.1
        phnumBound := by simpa using h.2.2.2.2.2.2.2 }
  else none

/-- The program an ELF64 image carries: sections regain the empty name and
`Nat` address every assembled program already had, the stack request is the
zero every assembled program already had, and there are no import slots. -/
def rawOf (artifact : Artifact) : Sectioned :=
  { sections := artifact.sections.map toSection
    entry := artifact.entry.toNat
    imports := []
    stackBytes := 0 }

/-- Reassembling every accepted section's forgotten name and truncated
address recovers it exactly, because `Eligible` already required the name
empty and the address to fit. -/
theorem sections_rawOf_assemble (sections : List Grass.Target.Section)
    (anon : ∀ sec ∈ sections, sec.name = "")
    (vaddrBound : ∀ sec ∈ sections, sec.virtualAddress < widthBound)
    (sizeBound : ∀ sec ∈ sections, sec.bytes.length < widthBound) :
    (mkSections sections sizeBound).map toSection = sections := by
  induction sections with
  | nil => rfl
  | cons sec sections ih =>
      have nameEq : sec.name = "" := anon sec (by simp)
      have vaddrEq : (UInt64.ofNat sec.virtualAddress).toNat = sec.virtualAddress := by
        rw [UInt64.toNat_ofNat']
        exact Nat.mod_eq_of_lt (vaddrBound sec (by simp))
      have tailAnon : ∀ s ∈ sections, s.name = "" := fun s member => anon s (by simp [member])
      have tailVaddr : ∀ s ∈ sections, s.virtualAddress < widthBound :=
        fun s member => vaddrBound s (by simp [member])
      have tailSize : ∀ s ∈ sections, s.bytes.length < widthBound :=
        fun s member => sizeBound s (by simp [member])
      simp only [mkSections, List.map_cons, ih tailAnon tailVaddr tailSize, toElfSection, toSection,
        vaddrEq]
      rw [← nameEq]

/-- Assembling preserves the program exactly. -/
theorem rawOf_assemble (program : Sectioned) (artifact : Artifact) :
    assemble program = some artifact → rawOf artifact = program := by
  intro success
  unfold assemble at success
  split at success
  next elig =>
    obtain ⟨_wf, noImports, anon, stackZero, entryBound, vaddrBound, sizeBound, _countBound⟩ := elig
    injection success with success
    subst success
    unfold rawOf
    simp only
    rw [sections_rawOf_assemble program.sections anon vaddrBound sizeBound, ← noImports,
      show (UInt64.ofNat program.entry).toNat = program.entry from by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt entryBound,
      ← stackZero]
  next => simp at success

/-- The ELF64 executable `Format`, parameterized by `e_machine` (`0x3E` for
x86-64, `0xB7` for AArch64, ...). -/
def format (machine : UInt16) : Format Sectioned where
  Artifact := Artifact
  assemble := assemble
  write := write machine
  read := read machine
  read_write := read_write machine
  rawOf := rawOf
  rawOf_assemble := rawOf_assemble

end Grass.Artifact.ELF
