import Grass.Artifact.PE.Target.Image
import Grass.Artifact.PE.Target.Imports
import Grass.Target.Artifact

/-!
# The PE32+ executable artifact format

`Grass.Artifact.PE.format` instantiates `Grass.Target.Format Sectioned` with a
PE32+ image a Windows loader accepts. The byte container, its field table and
its citations are `Grass.Artifact.PE.Target.Image`; the import directory is
`Grass.Artifact.PE.Target.Imports`. This module is the seam instance: which
programs `assemble` accepts, how a `Sectioned` becomes an image, and how an
image gives its program back.

`ImageBase` is the lowest section address rounded down to 64 KiB and every
section's RVA is its absolute address minus that base — the addresses a
`Sectioned` carries are the addresses the loader maps *when it honors the
requested base*, but decision 17 requires ASLR: `Characteristics` clears
`IMAGE_FILE_RELOCS_STRIPPED` and `DllCharacteristics` sets `DYNAMIC_BASE` and
`HIGH_ENTROPY_VA` (`Grass.Artifact.PE.Target.Image.coffFixed`,
`optionalWindows`), so the loader remains free to rebase the image.

## Base relocations

Grass programs address memory only through RIP-relative operands and the
import slots `Sectioned.imports` names; `Sectioned` has no field that could
express an absolute (base-relative) relocation, so there is never a
relocation entry for `assemble` to emit — refusing a program that "needs" one
is therefore vacuous by construction, not a missing check. What ASLR still
needs is the *directory itself*: Microsoft, PE Format, "The .reloc Section
(Image Only)", describes each block as a 4-byte page RVA and a 4-byte block
size that includes the header, with the entries (if any) following; a block
with zero following entries is a legal, if unusual, empty block. `assemble`
always emits exactly one such empty block — naming the page containing the
program's entry point, which is what keeps a well-formed, if inert, directory
present for a `DYNAMIC_BASE` loader — rather than reserving a whole `.reloc`
section for content that names zero relocations: the block is appended after
the import directory's own content, inside the same `.idata` section, and
`Grass.Artifact.PE.Target.Image.Artifact.relocDirRva`/`relocDirSize` (data
directory 5) point at it directly. A future `Sectioned` extension that could
express an absolute relocation would need this format's cooperation to emit a
non-empty block; today's `Sectioned` cannot ask for one.

## Exception directory

When `program.sections` carries a section named `.pdata` — the lowering tier
emits its bytes from `Grass.ABI.Win64.UnwindBytes`; this module never
generates unwind data — `assemble` points data directory 3 (Exception Table)
at that section's own RVA/size. Otherwise the directory stays zero.
`Artifact.hasUnwind` and `assemble_hasUnwind` expose which case held, so a
downstream platform profile that requires unwind metadata
(`docs/HELLO_UNWIND_BOUNDARY.md`) can demand it without this module deciding
that policy.

## Imports

`Sectioned.imports` names slots the loader fills. Each maximal run of
consecutive symbols naming the same library becomes one
`IMAGE_IMPORT_DESCRIPTOR`, whose `FirstThunk` is the run's own first
`slotAddress`: the Import Address Table *is* the program's declared slots, not
a copy the format placed elsewhere. `assemble` therefore requires each run's
slots to be consecutive 8-byte entries, in the order given, inside one readable
section, and requires distinct libraries across runs; it refuses otherwise.

The descriptors, lookup tables, hint/name records and DLL name strings go in a
`.idata` section the format appends after the program's own sections, at the
next page boundary past the highest section end. `idata_after_sections` is why
that cannot overlap: the chosen address is at or above every section's end.
The section is appended unconditionally — a program with no imports gets a
`.idata` holding only the terminating descriptor — so there is one layout to
write, read and prove rather than two.

## Limitations

- Section names are ASCII and at most eight bytes: the section header's `Name`
  field is eight bytes and this format emits no string table, which the
  `/nnnnnnn` long-name form would need.
- Section addresses must already be `SectionAlignment`-aligned, ordered
  ascending and clear of the mapped headers. The writer places sections where
  the program says, so it refuses a layout it cannot repair rather than moving
  code the program has already resolved addresses against.
- No TLS, no resources, no debug directory, no `CheckSum`: data directories
  other than import (1), exception (3) and base relocation (5) are zero.
  Exception directory 3 is populated only when the program supplies a
  `.pdata` section (see `Artifact.hasUnwind`); a 64-bit Windows image without
  one cannot unwind through its own frames, which matters for a program that
  raises a structured exception, not for loading. Base relocation directory 5
  is always populated, but only with a single empty block (see "Base
  relocations" above): Grass programs have no absolute relocation for
  `Sectioned` to carry, so ASLR is honest without one.
-/

namespace Grass.Artifact.PE.Target

open Grass.Target
open Grass.Artifact.Binary

/-! ## The eight-byte section `Name` field -/

/-- The section header's `Name` field: the name's bytes, NUL-padded to eight.
Microsoft PE Format, "Section Table (Section Headers)". -/
def nameField (s : String) : List UInt8 :=
  nameBytes s ++ List.replicate (8 - s.toList.length) 0

/-- The `Name` field is eight bytes exactly when the name fits it. -/
theorem length_nameField {s : String} (fits : s.toList.length ≤ 8) :
    (nameField s).length = 8 := by
  simp only [nameField, List.length_append, length_nameBytes, List.length_replicate]
  omega

/-- The name a `Name` field carries: bytes up to the first NUL. -/
def decodeNameField (bytes : List UInt8) : String :=
  decodeName (bytes.takeWhile fun b => b != 0)

/-- Writing and reading the `Name` field round-trip for every name it can
carry. -/
theorem decodeNameField_nameField {s : String} (ascii : AsciiName s) :
    decodeNameField (nameField s) = s := by
  rw [decodeNameField, nameField, takeWhile_append_replicate (nameBytes_ne_zero ascii),
    decodeName_nameBytes ascii]

/-- The appended import section's `Name`, `.idata`, spelled as bytes so no
`String` decoding enters the definition of the image. -/
def idataName : List UInt8 := [0x2e, 0x69, 0x64, 0x61, 0x74, 0x61, 0, 0]

theorem length_idataName : idataName.length = 8 := rfl

/-! ## Placement -/

/-- `ImageBase`: the lowest section address rounded down to the loader's 64 KiB
granularity. Sections are required to be ordered ascending, so the first one is
the lowest. -/
def baseAddress (program : Sectioned) : Nat :=
  match program.sections with
  | [] => 0
  | sec :: _ => sec.virtualAddress / imageBaseAlign * imageBaseAlign

/-- Summed padded raw sizes: the file extent after `SizeOfHeaders`. -/
def totalRawSize : List Grass.Target.Section → Nat
  | [] => 0
  | sec :: rest => roundUp sec.bytes.length fileAlign + totalRawSize rest

/-- The highest section end, as an RVA against the image base. -/
def endRva (base : Nat) : List Grass.Target.Section → Nat
  | [] => 0
  | sec :: rest => max (sec.virtualAddress - base + sec.bytes.length) (endRva base rest)

/-- Every section's end RVA is at or below `endRva`. -/
theorem le_endRva (base : Nat) (sections : List Grass.Target.Section) :
    ∀ sec ∈ sections, sec.virtualAddress - base + sec.bytes.length ≤ endRva base sections := by
  induction sections with
  | nil => simp
  | cons sec sections ih =>
      intro s member
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih s member) (Nat.le_max_right _ _)

/-- The RVA of the appended `.idata` section: the next page boundary past both
the mapped headers (counting `.idata`'s own section-table entry) and every
section's end. -/
def idataRva (program : Sectioned) : Nat :=
  roundUp
    (max (roundUp (sizeOfHeadersOf (program.sections.length + 1)) sectionAlign)
      (endRva (baseAddress program) program.sections))
    sectionAlign

/-- The appended import section starts at or after every program section's
end, so it can never overlap one: this is why `assemble` has no overlap case
to refuse. -/
theorem idata_after_sections (program : Sectioned) :
    ∀ sec ∈ program.sections,
      sec.virtualAddress - baseAddress program + sec.bytes.length ≤ idataRva program := by
  intro sec member
  exact Nat.le_trans (le_endRva _ _ sec member)
    (Nat.le_trans (Nat.le_max_right _ _) (le_roundUp _ _))

/-- The import section's address is non-zero, which is what makes every Import
Lookup Table entry this format writes distinguishable from the table's own zero
terminator. -/
theorem idataRva_pos (program : Sectioned) : 0 < idataRva program := by
  have headers : headersEnd (program.sections.length + 1) ≤
      sizeOfHeadersOf (program.sections.length + 1) := le_roundUp _ _
  have mapped : sizeOfHeadersOf (program.sections.length + 1) ≤
      roundUp (sizeOfHeadersOf (program.sections.length + 1)) sectionAlign := le_roundUp _ _
  have chosen : max (roundUp (sizeOfHeadersOf (program.sections.length + 1)) sectionAlign)
      (endRva (baseAddress program) program.sections) ≤ idataRva program := le_roundUp _ _
  have positive : 0 < headersEnd (program.sections.length + 1) := by
    simp only [headersEnd]
    omega
  have left := Nat.le_max_left (roundUp (sizeOfHeadersOf (program.sections.length + 1)) sectionAlign)
    (endRva (baseAddress program) program.sections)
  omega

/-! ## Grouping the import slots -/

/-- Extend the run decomposition by one symbol: it joins the leading run when
that run already names its library, and starts a new one otherwise. -/
def consRun (sym : Grass.Target.ImportSymbol) :
    List (String × List Grass.Target.ImportSymbol) →
      List (String × List Grass.Target.ImportSymbol)
  | [] => [(sym.library, [sym])]
  | (library, group) :: tail =>
      if sym.library = library then (library, sym :: group) :: tail
      else (sym.library, [sym]) :: (library, group) :: tail

/-- The import slots split into maximal runs naming one library each; one
`IMAGE_IMPORT_DESCRIPTOR` per run. -/
def importRuns : List Grass.Target.ImportSymbol →
    List (String × List Grass.Target.ImportSymbol)
  | [] => []
  | sym :: rest => consRun sym (importRuns rest)

/-- Concatenating the runs recovers the slot list exactly. -/
theorem flatten_consRun (sym : Grass.Target.ImportSymbol)
    (runs : List (String × List Grass.Target.ImportSymbol)) :
    (consRun sym runs).flatMap Prod.snd = sym :: runs.flatMap Prod.snd := by
  cases runs with
  | nil => simp [consRun]
  | cons head tail =>
      obtain ⟨library, group⟩ := head
      by_cases same : sym.library = library <;> simp [consRun, same]

/-- The runs are a decomposition, not a reordering. -/
theorem flatten_importRuns (syms : List Grass.Target.ImportSymbol) :
    (importRuns syms).flatMap Prod.snd = syms := by
  induction syms with
  | nil => rfl
  | cons sym syms ih => rw [importRuns, flatten_consRun, ih]

/-- Every symbol in a run names the run's library. -/
theorem consRun_library (sym : Grass.Target.ImportSymbol)
    (runs : List (String × List Grass.Target.ImportSymbol))
    (sound : ∀ run ∈ runs, ∀ s ∈ run.2, s.library = run.1) :
    ∀ run ∈ consRun sym runs, ∀ s ∈ run.2, s.library = run.1 := by
  cases runs with
  | nil =>
      intro run member s memberS
      simp only [consRun, List.mem_singleton] at member
      subst member
      simp only [List.mem_singleton] at memberS
      subst memberS
      rfl
  | cons head tail =>
      obtain ⟨library, group⟩ := head
      have headSound : ∀ s ∈ group, s.library = library :=
        fun s memberS => sound (library, group) (List.mem_cons_self ..) s memberS
      have tailSound : ∀ run ∈ tail, ∀ s ∈ run.2, s.library = run.1 :=
        fun run member => sound run (List.mem_cons_of_mem _ member)
      by_cases same : sym.library = library
      · simp only [consRun, same, ↓reduceIte]
        intro run member s memberS
        rcases List.mem_cons.mp member with rfl | member
        · rcases List.mem_cons.mp memberS with rfl | memberS
          · exact same
          · exact headSound s memberS
        · exact tailSound run member s memberS
      · simp only [consRun, same, ↓reduceIte]
        intro run member s memberS
        rcases List.mem_cons.mp member with rfl | member
        · simp only [List.mem_singleton] at memberS
          subst memberS
          rfl
        · rcases List.mem_cons.mp member with rfl | member
          · exact headSound s memberS
          · exact tailSound run member s memberS

/-- Every symbol in a run names the run's library. -/
theorem importRuns_library (syms : List Grass.Target.ImportSymbol) :
    ∀ run ∈ importRuns syms, ∀ s ∈ run.2, s.library = run.1 := by
  induction syms with
  | nil => simp [importRuns]
  | cons sym syms ih => exact consRun_library sym (importRuns syms) ih

/-- The first slot address of a run; the descriptor's `FirstThunk`. -/
def headSlot : List Grass.Target.ImportSymbol → Nat
  | [] => 0
  | sym :: _ => sym.slotAddress

/-- Whether a run's slots are consecutive 8-byte entries from an address, in
the order given: an `IMAGE_THUNK_DATA64` is eight bytes, and the loader fills
them in Import Lookup Table order. -/
def slotsFrom (address : Nat) : List Grass.Target.ImportSymbol → Bool
  | [] => true
  | sym :: rest => (sym.slotAddress == address) && slotsFrom (address + 8) rest

/-- The symbols a recovered descriptor stands for: consecutive slots from the
Import Address Table's own address. -/
def symbolsOf (library : String) (address : Nat) :
    List String → List Grass.Target.ImportSymbol
  | [] => []
  | symbol :: rest =>
      { library, symbol, slotAddress := address } :: symbolsOf library (address + 8) rest

/-- A run whose slots are consecutive from `address` and whose symbols all name
`library` is exactly what its recovered descriptor stands for. -/
theorem symbolsOf_group (library : String) (address : Nat)
    (group : List Grass.Target.ImportSymbol)
    (named : ∀ s ∈ group, s.library = library) (slots : slotsFrom address group = true) :
    symbolsOf library address (group.map fun s => s.symbol) = group := by
  induction group generalizing address with
  | nil => rfl
  | cons sym group ih =>
      simp only [slotsFrom, Bool.and_eq_true, beq_iff_eq] at slots
      have named' : ∀ s ∈ group, s.library = library :=
        fun s member => named s (List.mem_cons_of_mem _ member)
      rw [List.map_cons, symbolsOf, ih (address + 8) named' slots.2, ← slots.1,
        ← named sym (List.mem_cons_self ..)]

/-- One run as the import directory records it. -/
def toLibrary (base : Nat) (run : String × List Grass.Target.ImportSymbol) : Library :=
  { name := run.1, iatRva := headSlot run.2 - base, symbols := run.2.map fun s => s.symbol }

/-- The whole import requirement as the import directory records it. -/
def libraries (program : Sectioned) : List Library :=
  (importRuns program.imports).map (toLibrary (baseAddress program))

/-- The recovered import requirement's slot list. -/
def importsOf (base : Nat) (libs : List Library) : List Grass.Target.ImportSymbol :=
  libs.flatMap fun lib => symbolsOf lib.name (base + lib.iatRva) lib.symbols

/-! ## The empty base-relocation block -/

/-- The whole empty base-relocation block: a 4-byte page RVA and a 4-byte
`SizeOfBlock` of 8 (the header alone), no entries. Microsoft, PE Format, "The
.reloc Section (Image Only)". -/
def relocBlockSize : Nat := 8

/-- The page (`SectionAlignment`-aligned RVA) the block names: the page
containing the program's entry point. The choice is inert — the block has no
entries, so nothing is ever relocated through it — but naming a real code page
rather than RVA 0 keeps the block legible to a reader inspecting the image. -/
def relocPageRva (program : Sectioned) : Nat :=
  (program.entry - baseAddress program) / sectionAlign * sectionAlign

/-- The block's bytes. -/
def relocBlock (program : Sectioned) : List UInt8 :=
  writeU32LE (UInt32.ofNat (relocPageRva program)) ++ writeU32LE (UInt32.ofNat relocBlockSize)

@[simp] theorem length_relocBlock (program : Sectioned) : (relocBlock program).length = 8 := by
  simp [relocBlock]

/-! ## The exception directory -/

/-- The program's `.pdata` section, if it supplied one. This format never
generates unwind data (`Grass.ABI.Win64.UnwindBytes` is the lowering tier's
job); it only looks for the name. -/
def findPdata (program : Sectioned) : Option Grass.Target.Section :=
  program.sections.find? fun sec => sec.name == ".pdata"

/-- `IMAGE_DIRECTORY_ENTRY_EXCEPTION`'s RVA: the located `.pdata` section's
address against the image base, or zero when the program has none. -/
def exceptionRvaOf (program : Sectioned) : UInt32 :=
  match findPdata program with
  | some sec => UInt32.ofNat (sec.virtualAddress - baseAddress program)
  | none => 0

/-- `IMAGE_DIRECTORY_ENTRY_EXCEPTION`'s size: the located `.pdata` section's
own byte length, or zero when the program has none. -/
def exceptionSizeOf (program : Sectioned) : UInt32 :=
  match findPdata program with
  | some sec => UInt32.ofNat sec.bytes.length
  | none => 0

/-! ## Well-formedness -/

/-- `Sectioned.Disjoint`, `.EntryExecutable` and `.ImportsReadable` are plain
`def`s over decidable shapes, but instance search does not unfold ordinary
`def`s to find that, so each gets its instance spelled out against the
unfolded shape (as in `Grass.Artifact.Flat` and `Grass.Artifact.ELF`). -/
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

/-- Sections are ordered by address and do not touch: the section table must be
ascending by `VirtualAddress`, and this is also what makes the first section's
address the lowest, hence the image base. -/
def Ascending (program : Sectioned) : Prop :=
  program.sections.Pairwise fun left right => left.endAddress ≤ right.virtualAddress

instance : DecidablePred Ascending := fun program =>
  inferInstanceAs
    (Decidable (program.sections.Pairwise fun left right =>
      left.endAddress ≤ right.virtualAddress))

/-- Every section is placed where a PE32+ loader can map it: page-aligned, at
or above the image base, and clear of the mapped headers (sized for the
appended `.idata` entry too). -/
def Placed (program : Sectioned) : Prop :=
  ∀ sec ∈ program.sections,
    sec.virtualAddress % sectionAlign = 0 ∧
    baseAddress program ≤ sec.virtualAddress ∧
    roundUp (sizeOfHeadersOf (program.sections.length + 1)) sectionAlign ≤
      sec.virtualAddress - baseAddress program

instance : DecidablePred Placed := fun program =>
  inferInstanceAs (Decidable (∀ sec ∈ program.sections, _ ∧ _ ∧ _))

/-- Each library's slots are consecutive 8-byte entries in the order given,
inside one readable section, at an address the descriptor's 32-bit
`FirstThunk` can hold; and no two descriptors name the same library. -/
def ImportsPlaced (program : Sectioned) : Prop :=
  (∀ run ∈ importRuns program.imports,
    AsciiName run.1 ∧
    (∀ s ∈ run.2, AsciiName s.symbol) ∧
    slotsFrom (headSlot run.2) run.2 = true ∧
    baseAddress program ≤ headSlot run.2 ∧
    headSlot run.2 - baseAddress program < 4294967296 ∧
    (∃ sec ∈ program.sections, sec.readable = true ∧
      sec.virtualAddress ≤ headSlot run.2 ∧
      headSlot run.2 + 8 * run.2.length ≤ sec.endAddress)) ∧
  ((importRuns program.imports).map Prod.fst).Nodup

instance : DecidablePred ImportsPlaced := fun _program =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every value this format writes through a fixed-width field fits it: RVAs,
`VirtualSize`, `SizeOfRawData`, `SizeOfImage`, the import directory's size and
every file offset in 32 bits; `ImageBase` and `SizeOfStackReserve` in 64. -/
def Fits (program : Sectioned) : Prop :=
  (∀ sec ∈ program.sections,
    sec.name.toList.length ≤ 8 ∧
    sec.bytes.length + fileAlign < 4294967296 ∧
    sec.endAddress - baseAddress program + sectionAlign < 4294967296) ∧
  idataRva program + (idataSize (libraries program) + relocBlockSize) + sectionAlign <
    4294967296 ∧
  descriptorTableSize (libraries program).length < 4294967296 ∧
  sizeOfHeadersOf (program.sections.length + 1) + totalRawSize program.sections +
    roundUp (idataSize (libraries program) + relocBlockSize) fileAlign < 4294967296 ∧
  baseAddress program < 18446744073709551616 ∧
  program.stackBytes < 18446744073709551616 ∧
  baseAddress program ≤ program.entry ∧
  program.entry - baseAddress program < 4294967296 ∧
  program.sections.length < 65535

instance : DecidablePred Fits := fun _program =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- What `assemble` accepts. -/
def Eligible (program : Sectioned) : Prop :=
  program.WellFormed ∧ Ascending program ∧ Placed program ∧ ImportsPlaced program ∧
    Fits program ∧ (∀ sec ∈ program.sections, AsciiName sec.name)

instance : DecidablePred Eligible := fun _program =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-! ## Assembly -/

/-- A carried section as the container records it, at the RVA its absolute
address gives against the image base. -/
def toPeSection (base : Nat) (sec : Grass.Target.Section) (fits : sec.name.toList.length ≤ 8)
    (sizeBound : sec.bytes.length + fileAlign < 4294967296) : PeSection :=
  { nameBytes := nameField sec.name
    nameLength := length_nameField fits
    rva := UInt32.ofNat (sec.virtualAddress - base)
    bytes := sec.bytes
    sizeBound := sizeBound
    readable := sec.readable
    writable := sec.writable
    executable := sec.executable }

/-- A recovered section, at the absolute address its RVA gives against the
image base. -/
def toSection (base : Nat) (sec : PeSection) : Grass.Target.Section :=
  { name := decodeNameField sec.nameBytes
    virtualAddress := base + sec.rva.toNat
    bytes := sec.bytes
    readable := sec.readable
    writable := sec.writable
    executable := sec.executable }

/-- Build every section's container record, threading the whole list's bounds
one element at a time so no `List.attach` bookkeeping enters the proofs
below. -/
def mkSections (base : Nat) : (sections : List Grass.Target.Section) →
    (∀ sec ∈ sections, sec.name.toList.length ≤ 8 ∧
      sec.bytes.length + fileAlign < 4294967296) → List PeSection
  | [], _ => []
  | sec :: rest, bound =>
      toPeSection base sec (bound sec (List.mem_cons_self ..)).1
          (bound sec (List.mem_cons_self ..)).2 ::
        mkSections base rest (fun s member => bound s (List.mem_cons_of_mem _ member))

@[simp] theorem length_mkSections (base : Nat) (sections : List Grass.Target.Section)
    (bound : ∀ sec ∈ sections, sec.name.toList.length ≤ 8 ∧
      sec.bytes.length + fileAlign < 4294967296) :
    (mkSections base sections bound).length = sections.length := by
  induction sections with
  | nil => rfl
  | cons sec sections ih => simp [mkSections, ih]

/-- The appended import section: `IMAGE_SCN_CNT_INITIALIZED_DATA |
IMAGE_SCN_MEM_READ`. The Import Address Table it names lives in the program's
own sections, so `.idata` itself never needs to be writable. Its content is
the import directory followed by the empty base-relocation block
(`relocBlock`): both are read-only initialized data with no reason to occupy
separate sections, and `relocDirRva`/`relocDirSize` (in `assemble`) point
directly at the trailing block rather than at a section boundary. -/
def idataSection (program : Sectioned)
    (sizeBound : (writeIdata (idataRva program) (libraries program) ++
        relocBlock program).length + fileAlign < 4294967296) : PeSection :=
  { nameBytes := idataName
    nameLength := length_idataName
    rva := UInt32.ofNat (idataRva program)
    bytes := writeIdata (idataRva program) (libraries program) ++ relocBlock program
    sizeBound := sizeBound
    readable := true
    writable := false
    executable := false }

/-- The container's sections: the program's own, then the appended import
section. -/
def imageSections (program : Sectioned) (elig : Eligible program) : List PeSection :=
  mkSections (baseAddress program) program.sections
      (fun sec member => ⟨(elig.2.2.2.2.1.1 sec member).1, (elig.2.2.2.2.1.1 sec member).2.1⟩) ++
    [idataSection program (by
      rw [List.length_append, length_writeIdata, length_relocBlock]
      have bound := elig.2.2.2.2.1.2.1
      simp only [fileAlign, sectionAlign, relocBlockSize] at bound ⊢
      omega)]

@[simp] theorem length_imageSections (program : Sectioned) (elig : Eligible program) :
    (imageSections program elig).length = program.sections.length + 1 := by
  simp [imageSections]

/-- Assemble a PE32+ image, refusing a program that is not `Eligible`. A
program needing an absolute (base-relative) relocation cannot be refused here
by name, because `Sectioned` has no field that could express one — see the
module docstring's "Base relocations" section; the relocation directory this
always emits is unconditionally empty. -/
def assemble (program : Sectioned) : Option Artifact :=
  if h : Eligible program then
    some (Artifact.mk (UInt64.ofNat (baseAddress program))
      (UInt32.ofNat (program.entry - baseAddress program))
      (UInt64.ofNat program.stackBytes)
      (imageSections program h)
      (by
        rw [length_imageSections]
        have := h.2.2.2.2.1.2.2.2.2.2.2.2.2
        omega)
      (UInt32.ofNat (idataRva program))
      (UInt32.ofNat (descriptorTableSize (libraries program).length))
      (exceptionRvaOf program)
      (exceptionSizeOf program)
      (UInt32.ofNat (idataRva program + idataSize (libraries program)))
      (UInt32.ofNat relocBlockSize))
  else none

/-! ## What an image carries -/

/-- The program's own sections: every section but the appended import section.
Data directory 1's size is `20 * (libraries + 1)`, so a zero quotient means the
image carries no import directory and every section is the program's. -/
def carriedSections (artifact : Artifact) : List PeSection :=
  if artifact.importDirSize.toNat / 20 = 0 then artifact.sections else artifact.sections.dropLast

/-- The import slots the image's `.idata` names. An image this format did not
write may have no last section or an unparsable one; there is nothing to
recover then, and `rawOf_assemble` says nothing about such an image. -/
def recoveredImports (artifact : Artifact) : List Grass.Target.ImportSymbol :=
  if artifact.importDirSize.toNat / 20 = 0 then []
  else
    match artifact.sections.getLast? with
    | none => []
    | some idata =>
      match parseIdata (artifact.importDirSize.toNat / 20 - 1) idata.bytes with
      | none => []
      | some libs => importsOf artifact.imageBase.toNat libs

/-- The program an image carries. -/
def rawOf (artifact : Artifact) : Sectioned :=
  { sections := (carriedSections artifact).map (toSection artifact.imageBase.toNat)
    entry := artifact.imageBase.toNat + artifact.entryRva.toNat
    imports := recoveredImports artifact
    stackBytes := artifact.stackReserve.toNat }

/-- Every accepted section's name, address and permissions come back exactly:
`Eligible` already required the name to fit the eight-byte field and the RVA
to fit its 32-bit field. -/
theorem sections_rawOf_assemble (base : Nat) (sections : List Grass.Target.Section)
    (bound : ∀ sec ∈ sections, sec.name.toList.length ≤ 8 ∧
      sec.bytes.length + fileAlign < 4294967296)
    (ascii : ∀ sec ∈ sections, AsciiName sec.name)
    (placed : ∀ sec ∈ sections, base ≤ sec.virtualAddress)
    (rvaBound : ∀ sec ∈ sections, sec.virtualAddress - base < 4294967296) :
    (mkSections base sections bound).map (toSection base) = sections := by
  induction sections with
  | nil => rfl
  | cons sec sections ih =>
      have here : sec ∈ sec :: sections := List.mem_cons_self ..
      have nameEq : decodeNameField (nameField sec.name) = sec.name :=
        decodeNameField_nameField (ascii sec here)
      have addressEq : base + (UInt32.ofNat (sec.virtualAddress - base)).toNat =
          sec.virtualAddress := by
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (rvaBound sec here)]
        have := placed sec here
        omega
      simp only [mkSections, List.map_cons, toPeSection, toSection, nameEq, addressEq,
        ih (fun s member => bound s (List.mem_cons_of_mem _ member))
          (fun s member => ascii s (List.mem_cons_of_mem _ member))
          (fun s member => placed s (List.mem_cons_of_mem _ member))
          (fun s member => rvaBound s (List.mem_cons_of_mem _ member))]

/-- Every accepted import slot comes back exactly: `ImportsPlaced` required
each run's slots to be consecutive from its own first address, so a run is
recovered from its descriptor's `FirstThunk` alone. -/
theorem importsOf_libraries (base : Nat) (runs : List (String × List Grass.Target.ImportSymbol))
    (named : ∀ run ∈ runs, ∀ s ∈ run.2, s.library = run.1)
    (slots : ∀ run ∈ runs, slotsFrom (headSlot run.2) run.2 = true)
    (placed : ∀ run ∈ runs, base ≤ headSlot run.2) :
    importsOf base (runs.map (toLibrary base)) = runs.flatMap Prod.snd := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
      have here : run ∈ run :: runs := List.mem_cons_self ..
      have addressEq : base + (headSlot run.2 - base) = headSlot run.2 := by
        have := placed run here
        omega
      simp only [List.map_cons, importsOf, List.flatMap_cons, toLibrary, addressEq,
        symbolsOf_group run.1 (headSlot run.2) run.2 (named run here) (slots run here)]
      simp only [importsOf] at ih
      rw [ih (fun r member => named r (List.mem_cons_of_mem _ member))
        (fun r member => slots r (List.mem_cons_of_mem _ member))
        (fun r member => placed r (List.mem_cons_of_mem _ member))]

/-- Assembling preserves the program exactly. -/
theorem rawOf_assemble (program : Sectioned) (artifact : Artifact) :
    assemble program = some artifact → rawOf artifact = program := by
  intro success
  unfold assemble at success
  split at success
  next elig =>
    obtain ⟨_wf, _ascending, placed, importsPlaced, fits, ascii⟩ := elig
    obtain ⟨sectionFits, idataBound, directoryBound, _fileBound, baseBound, stackBound, baseLe,
      entryBound, _countBound⟩ := fits
    injection success with success
    subst success
    have baseEq : (UInt64.ofNat (baseAddress program)).toNat = baseAddress program := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt baseBound
    have countEq : (UInt32.ofNat (descriptorTableSize (libraries program).length)).toNat / 20 =
        (libraries program).length + 1 := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt directoryBound, descriptorTableSize]
      omega
    have rvaBound : ∀ sec ∈ program.sections, sec.virtualAddress - baseAddress program <
        4294967296 := by
      intro sec member
      have := (sectionFits sec member).2.2
      have : sec.virtualAddress ≤ sec.endAddress := Nat.le_add_right _ _
      omega
    unfold rawOf
    simp only [baseEq, carriedSections, recoveredImports, countEq, Nat.succ_ne_zero, ↓reduceIte,
      imageSections, idataSection, List.dropLast_concat, List.getLast?_concat, Nat.add_sub_cancel,
      parseIdata_writeIdata_append (idataRva program) (libraries program) (relocBlock program)
        (idataRva_pos program)
        (by rw [libraries] at idataBound ⊢; omega)
        (by
          intro lib member
          obtain ⟨run, memberRun, rfl⟩ := List.mem_map.mp member
          exact (importsPlaced.1 run memberRun).2.2.2.2.1)
        (by
          intro lib member
          obtain ⟨run, memberRun, rfl⟩ := List.mem_map.mp member
          exact (importsPlaced.1 run memberRun).1)
        (by
          intro lib member s memberS
          obtain ⟨run, memberRun, rfl⟩ := List.mem_map.mp member
          obtain ⟨sym, memberSym, rfl⟩ := List.mem_map.mp memberS
          exact (importsPlaced.1 run memberRun).2.1 sym memberSym)]
    rw [sections_rawOf_assemble (baseAddress program) program.sections _ ascii
        (fun sec member => (placed sec member).2.1) rvaBound,
      libraries,
      importsOf_libraries (baseAddress program) (importRuns program.imports)
        (importRuns_library program.imports)
        (fun run member => (importsPlaced.1 run member).2.2.1)
        (fun run member => (importsPlaced.1 run member).2.2.2.1),
      flatten_importRuns,
      show (UInt64.ofNat program.stackBytes).toNat = program.stackBytes from by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt stackBound,
      show baseAddress program + (UInt32.ofNat (program.entry - baseAddress program)).toNat =
          program.entry from by
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt entryBound]; omega]
  next => simp at success

/-! ## `hasUnwind` -/

/-- Every constructed section's `nameBytes` field names it exactly, so
searching the container's own sections for a name reduces to searching the
program's original sections for the same name spelled through `nameField`. -/
theorem mkSections_hasName (base : Nat) (target : List UInt8) :
    ∀ (sections : List Grass.Target.Section)
      (bound : ∀ sec ∈ sections, sec.name.toList.length ≤ 8 ∧
        sec.bytes.length + fileAlign < 4294967296),
      (∃ pe ∈ mkSections base sections bound, pe.nameBytes = target) ↔
        ∃ sec ∈ sections, nameField sec.name = target := by
  intro sections
  induction sections with
  | nil => intro bound; simp [mkSections]
  | cons sec sections ih =>
      intro bound
      simp only [mkSections, List.mem_cons]
      constructor
      · rintro ⟨pe, hmem, heq⟩
        rcases hmem with heq2 | hmem
        · rw [heq2] at heq
          exact ⟨sec, Or.inl rfl, heq⟩
        · obtain ⟨s, hs, heq'⟩ := (ih (fun t m => bound t (List.mem_cons_of_mem _ m))).mp
            ⟨pe, hmem, heq⟩
          exact ⟨s, Or.inr hs, heq'⟩
      · rintro ⟨s, hmem, heq⟩
        rcases hmem with heq2 | hmem
        · rw [heq2] at heq
          exact ⟨toPeSection base sec (bound sec (List.mem_cons_self ..)).1
            (bound sec (List.mem_cons_self ..)).2, Or.inl rfl, heq⟩
        · obtain ⟨pe, hpe, heq'⟩ := (ih (fun t m => bound t (List.mem_cons_of_mem _ m))).mpr
            ⟨s, hmem, heq⟩
          exact ⟨pe, Or.inr hpe, heq'⟩

/-- An ASCII name that fits the eight-byte field spells `.pdata` exactly when
its field bytes equal `pdataNameField`. -/
theorem nameField_eq_pdataNameField_iff {s : String} (ascii : AsciiName s)
    (fits : s.toList.length ≤ 8) : nameField s = pdataNameField ↔ s = ".pdata" := by
  constructor
  · intro h
    have step : decodeNameField (nameField s) = s := decodeNameField_nameField ascii
    rw [h] at step
    have compute : decodeNameField pdataNameField = ".pdata" := by decide
    rw [compute] at step
    exact step.symm
  · intro h
    subst h
    decide

/-- `Artifact.hasUnwind` reports exactly whether the assembled program
supplied a `.pdata` section: the exception directory (`exceptionRvaOf`,
`exceptionSizeOf` in `assemble`) is populated on precisely this condition, and
downstream (the certificate's platform tier) can demand it for Win32 profiles
that require unwind metadata. -/
theorem assemble_hasUnwind (program : Sectioned) (artifact : Artifact) :
    assemble program = some artifact →
      (artifact.hasUnwind ↔ ∃ s ∈ program.sections, s.name = ".pdata") := by
  intro success
  unfold assemble at success
  split at success
  next elig =>
    obtain ⟨_wf, _ascending, placed, _importsPlaced, fits, ascii⟩ := elig
    obtain ⟨sectionFits, _idataBound, _directoryBound, _fileBound, _baseBound, _stackBound,
      _baseLe, _entryBound, _countBound⟩ := fits
    injection success with success
    subst success
    unfold Artifact.hasUnwind
    rw [decide_eq_true_eq]
    simp only [imageSections]
    constructor
    · rintro ⟨pe, member, eq⟩
      rw [List.mem_append, List.mem_singleton] at member
      rcases member with memberMk | heqIdata
      · obtain ⟨sec, memberSec, nameEq⟩ :=
          (mkSections_hasName (baseAddress program) pdataNameField program.sections _).mp
            ⟨pe, memberMk, eq⟩
        exact ⟨sec, memberSec,
          (nameField_eq_pdataNameField_iff (ascii sec memberSec)
            (sectionFits sec memberSec).1).mp nameEq⟩
      · rw [heqIdata] at eq
        simp only [idataSection] at eq
        exact absurd eq (by decide)
    · rintro ⟨sec, member, nameEq⟩
      have nameFieldEq : nameField sec.name = pdataNameField := by rw [nameEq]; decide
      obtain ⟨pe, memberPe, eq⟩ :=
        (mkSections_hasName (baseAddress program) pdataNameField program.sections _).mpr
          ⟨sec, member, nameFieldEq⟩
      exact ⟨pe, List.mem_append.mpr (Or.inl memberPe), eq⟩
  next => simp at success

/-- The PE32+ executable `Format`, parameterized by the COFF `Machine` field
(`0x8664` for `IMAGE_FILE_MACHINE_AMD64`, `0xAA64` for
`IMAGE_FILE_MACHINE_ARM64`). -/
def format (machine : UInt16) : Format Sectioned where
  Artifact := Artifact
  assemble := assemble
  write := write machine
  read := read machine
  read_write := read_write machine
  rawOf := rawOf
  rawOf_assemble := rawOf_assemble

end Grass.Artifact.PE.Target

namespace Grass.Artifact.PE

export Target (format)

end Grass.Artifact.PE
