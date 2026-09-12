import Grass.Artifact.Binary.LEB128
import Grass.Artifact.Binary.LittleEndian
import Grass.Target.Artifact

/-!
# The flat bare-metal boot image artifact format

The simplest instance of `Grass.Target.Format`: a self-describing header
(magic, entry, reserved stack size, section count, then one
(virtual address, size, permission flags) record per section) followed by
the concatenated section bytes, so `read` recovers the sections exactly.

Every numeric field is an unsigned LEB128 varint (`Grass.Artifact.Binary`),
which has no fixed bit width and so never truncates: `Artifact`'s `entry`,
`stackBytes` and per-section `virtualAddress` are plain `Nat`, and
`read_write` holds unconditionally, with no size-refusal case to prove. The
seam's own `assemble` still refuses a program by returning `none`, but here
only for reasons intrinsic to the format, not for numeric overflow: a program
that is not `Sectioned.WellFormed`, one with import slots (bare metal has no
loader to resolve them), or one whose section carries a non-empty name (this
header carries no name field).

This is deliberately the simplest format in the artifact seam, built first to
validate `Grass.Target.Format`'s shape before ELF, PE and Wasm.
-/

namespace Grass.Artifact.Flat

open Grass.Artifact.Binary Grass.Target

/-- A section as this format's header records it: no name (the header has no
name field), an address, contents, and the three permission bits. -/
structure FlatSection where
  virtualAddress : Nat
  bytes : List UInt8
  readable : Bool
  writable : Bool
  executable : Bool
deriving DecidableEq, Repr

/-- The flat image container: everything the header and payload together
carry. -/
structure Artifact where
  entry : Nat
  stackBytes : Nat
  sections : List FlatSection
deriving DecidableEq, Repr

/-- Four-byte constant identifying a flat boot image. -/
def MAGIC : List UInt8 := [0x47, 0x42, 0x46, 0x31]

@[simp] theorem length_MAGIC : MAGIC.length = 4 := rfl

/-- Pack the three permission bits into one byte. -/
def flagsByte (readable writable executable : Bool) : UInt8 :=
  UInt8.ofNat
    ((if readable then 1 else 0) + (if writable then 2 else 0) + (if executable then 4 else 0))

/-- Unpack the three permission bits from one byte. -/
def readFlags (b : UInt8) : Bool × Bool × Bool :=
  (b.toNat % 2 = 1, b.toNat / 2 % 2 = 1, b.toNat / 4 % 2 = 1)

/-- Packing and unpacking a permission byte round-trip exactly, for every
combination of the three bits. -/
theorem readFlags_flagsByte (r w x : Bool) :
    readFlags (flagsByte r w x) = (r, w, x) := by
  cases r <;> cases w <;> cases x <;> decide

/-- A section's header fields as the reader recovers them, before they are
repacked into a `FlatSection`. -/
def headerFields (sec : FlatSection) : Nat × Nat × Bool × Bool × Bool :=
  (sec.virtualAddress, sec.bytes.length, sec.readable, sec.writable, sec.executable)

/-- Serialize one section's header record: address, size, flags. -/
def writeSectionHeader (sec : FlatSection) : List UInt8 :=
  natToLEB128 sec.virtualAddress ++ natToLEB128 sec.bytes.length ++
    [flagsByte sec.readable sec.writable sec.executable]

/-- Serialize every section's header record, in order. -/
def writeSectionHeaders : List FlatSection → List UInt8
  | [] => []
  | sec :: rest => writeSectionHeader sec ++ writeSectionHeaders rest

/-- Serialize the concatenated section payloads, in order. -/
def writeSectionPayloads : List FlatSection → List UInt8
  | [] => []
  | sec :: rest => sec.bytes ++ writeSectionPayloads rest

/-- The complete flat image: header then payload. -/
def write (artifact : Artifact) : List UInt8 :=
  MAGIC ++ natToLEB128 artifact.entry ++ natToLEB128 artifact.stackBytes ++
    natToLEB128 artifact.sections.length ++
    writeSectionHeaders artifact.sections ++ writeSectionPayloads artifact.sections

/-- Read `count` section header records from the head of the list. -/
def readSectionHeaders : Nat → List UInt8 → Option (List (Nat × Nat × Bool × Bool × Bool) × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes =>
      match readLEB128 bytes with
      | none => none
      | some (vaddr, bytes) =>
      match readLEB128 bytes with
      | none => none
      | some (size, bytes) =>
      match bytes with
      | [] => none
      | flag :: bytes =>
          let (r, w, x) := readFlags flag
          match readSectionHeaders n bytes with
          | none => none
          | some (tail, rest) => some ((vaddr, size, r, w, x) :: tail, rest)

/-- Split the payload region into sections using the sizes the headers
declared. -/
def splitPayload : List (Nat × Nat × Bool × Bool × Bool) → List UInt8 → Option (List FlatSection)
  | [], _ => some []
  | (vaddr, size, r, w, x) :: tail, bytes =>
      match takeBytes size bytes with
      | none => none
      | some (secBytes, rest) =>
      match splitPayload tail rest with
      | none => none
      | some tailSecs => some (⟨vaddr, secBytes, r, w, x⟩ :: tailSecs)

/-- Recover a flat image from bytes. -/
def read (bytes : List UInt8) : Option Artifact :=
  match takeBytes 4 bytes with
  | none => none
  | some (magic, bytes) =>
      if magic = MAGIC then
        match readLEB128 bytes with
        | none => none
        | some (entry, bytes) =>
        match readLEB128 bytes with
        | none => none
        | some (stackBytes, bytes) =>
        match readLEB128 bytes with
        | none => none
        | some (count, bytes) =>
        match readSectionHeaders count bytes with
        | none => none
        | some (headers, bytes) =>
        match splitPayload headers bytes with
        | none => none
        | some sections => some { entry, stackBytes, sections }
      else none

/-- Section headers are recovered exactly, for the exact number written, with
the exact byte suffix. -/
theorem readSectionHeaders_write_append (sections : List FlatSection) (rest : List UInt8) :
    readSectionHeaders sections.length (writeSectionHeaders sections ++ rest) =
      some (sections.map headerFields,
        rest) := by
  induction sections with
  | nil => rfl
  | cons sec sections ih =>
      have shape : writeSectionHeaders (sec :: sections) ++ rest =
          natToLEB128 sec.virtualAddress ++ (natToLEB128 sec.bytes.length ++
            (flagsByte sec.readable sec.writable sec.executable ::
              (writeSectionHeaders sections ++ rest))) := by
        simp [writeSectionHeaders, writeSectionHeader, List.append_assoc]
      rw [List.length_cons, shape]
      simp only [readSectionHeaders, readLEB128_natToLEB128_append, readFlags_flagsByte, ih,
        List.map_cons, headerFields]

/-- Splitting the payload with the headers' own sizes recovers the exact
sections and the exact byte suffix. -/
theorem splitPayload_write_append (sections : List FlatSection) (rest : List UInt8) :
    splitPayload
      (sections.map headerFields)
      (writeSectionPayloads sections ++ rest) = some sections := by
  induction sections with
  | nil => rfl
  | cons sec sections ih =>
      have shape : writeSectionPayloads (sec :: sections) ++ rest =
          sec.bytes ++ (writeSectionPayloads sections ++ rest) := by
        simp [writeSectionPayloads, List.append_assoc]
      simp only [List.map_cons, headerFields, splitPayload]
      rw [shape, takeBytes_append]
      simp only [ih]

/-- The no-trailing-bytes instance of `splitPayload_write_append`, matching
exactly what `read` sees once the header has been consumed: the payload
region is precisely the written section bytes, with nothing after. -/
theorem splitPayload_write (sections : List FlatSection) :
    splitPayload
      (sections.map headerFields)
      (writeSectionPayloads sections) = some sections := by
  simpa using splitPayload_write_append sections []

/-- The reader inverts the writer exactly, for every artifact: no `Artifact`
field has a fixed bit width, so nothing here can overflow. -/
theorem read_write (artifact : Artifact) : read (write artifact) = some artifact := by
  have shape : write artifact =
      MAGIC ++ (natToLEB128 artifact.entry ++ (natToLEB128 artifact.stackBytes ++
        (natToLEB128 artifact.sections.length ++
          (writeSectionHeaders artifact.sections ++ writeSectionPayloads artifact.sections)))) := by
    simp [write, List.append_assoc]
  rw [shape]
  simp only [read, takeBytes_append_of_eq length_MAGIC, ↓reduceIte,
    readLEB128_natToLEB128_append, readSectionHeaders_write_append, splitPayload_write]

/-- Whether every section in a program carries no name: the flat header has
no name field, so only anonymous sections are representable. -/
def allSectionsAnonymous (program : Sectioned) : Prop := ∀ sec ∈ program.sections, sec.name = ""

instance : DecidablePred allSectionsAnonymous := fun program =>
  inferInstanceAs (Decidable (∀ sec ∈ program.sections, sec.name = ""))

/-- `Sectioned.Disjoint`, `.EntryExecutable` and `.ImportsReadable` are plain
`def`s over decidable shapes (`List.Pairwise` of a decidable relation, and
bounded quantifiers over decidable predicates), but instance search does not
unfold ordinary `def`s to find that, so each gets its instance spelled out
against the unfolded shape. -/
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

/-- `Sectioned.WellFormed` is a structure over three propositions, each
already decidable; this instance packages them as one decision procedure so
`assemble` can refuse an ill-formed program computably. -/
instance : DecidablePred Sectioned.WellFormed := fun program =>
  decidable_of_iff (program.Disjoint ∧ program.EntryExecutable ∧ program.ImportsReadable)
    (Iff.intro (fun ⟨disjoint, entryExecutable, importsReadable⟩ =>
        ⟨disjoint, entryExecutable, importsReadable⟩)
      (fun wf => ⟨wf.disjoint, wf.entryExecutable, wf.importsReadable⟩))

/-- What `assemble` accepts: a well-formed program with no import slots (bare
metal has no loader to resolve them against) and no named sections (this
header carries no name field). -/
def Eligible (program : Sectioned) : Prop :=
  program.WellFormed ∧ program.imports = [] ∧ allSectionsAnonymous program

instance : DecidablePred Eligible := fun _program =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A carried program's section, forgetting its (already-checked-empty)
name. -/
def toFlatSection (sec : Grass.Target.Section) : FlatSection :=
  { virtualAddress := sec.virtualAddress, bytes := sec.bytes, readable := sec.readable,
    writable := sec.writable, executable := sec.executable }

/-- A recovered section, regaining the empty name every carried program
already had. -/
def toSection (fs : FlatSection) : Grass.Target.Section :=
  { name := "", virtualAddress := fs.virtualAddress, bytes := fs.bytes,
    readable := fs.readable, writable := fs.writable, executable := fs.executable }

/-- Assemble a flat image, refusing a program that is not well-formed, that
carries import slots, or that names a section. -/
def assemble (program : Sectioned) : Option Artifact :=
  if _ : Eligible program then
    some
      { entry := program.entry
        stackBytes := program.stackBytes
        sections := program.sections.map toFlatSection }
  else none

/-- The program a flat image carries: sections regain the empty name every
assembled program already had, and there are no import slots. -/
def rawOf (artifact : Artifact) : Sectioned :=
  { sections := artifact.sections.map toSection
    entry := artifact.entry
    imports := []
    stackBytes := artifact.stackBytes }

/-- Reassembling every accepted section's forgotten name recovers it exactly,
because `Eligible` already required it to be empty. -/
theorem sections_rawOf_assemble (sections : List Grass.Target.Section)
    (anon : ∀ sec ∈ sections, sec.name = "") :
    (sections.map toFlatSection).map toSection = sections := by
  induction sections with
  | nil => rfl
  | cons sec sections ih =>
      have nameEq : sec.name = "" := anon sec (by simp)
      have tailAnon : ∀ s ∈ sections, s.name = "" := fun s member => anon s (by simp [member])
      simp only [List.map_cons, ih tailAnon, toFlatSection, toSection]
      rw [← nameEq]

/-- `rawOf_assemble` recovers the input program from the artifact after a successful `assemble`. -/
theorem rawOf_assemble (program : Sectioned) (artifact : Artifact) :
    assemble program = some artifact → rawOf artifact = program := by
  intro success
  unfold assemble at success
  split at success
  next elig =>
    obtain ⟨_wf, noImports, anon⟩ := elig
    injection success with success
    subst success
    unfold rawOf
    simp only
    rw [sections_rawOf_assemble program.sections anon, ← noImports]
  next => simp at success

/-- The flat bare-metal boot image `Format`. -/
def format : Format Sectioned where
  Artifact := Artifact
  assemble := assemble
  write := write
  read := read
  read_write := read_write
  rawOf := rawOf
  rawOf_assemble := rawOf_assemble

end Grass.Artifact.Flat
