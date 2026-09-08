import Grass.Platform.Win32.CoffLayout

/-!
# Auxiliary section-definition records

The eighteen bytes that follow a section symbol, and the reason they are derived
here rather than supplied.

Every section symbol `ml64` emits declares `numberOfAuxSymbols = 1` and is
followed by one of these -- five of the fifteen symbols in each object measured
for these modules. `CoffSymbol.lean` writes the count and nothing wrote the
record, so an object built from that model alone would tell a reader to skip a
record that was not there, mis-indexing every symbol after it.

## The duplication this exists to make safe

The record's first two fields are the section's size and its relocation count,
and both already appear in that section's *header*. The format states them
twice, and a writer that filled them in independently could state them
differently -- an object whose `.pdata` header says three relocations and whose
`.pdata` aux record says six is well-formed, and which number a tool believes is
not something the format decides.

So `AuxSectionDefinition.toBytes` takes the `Section` and computes both, and
the structure has no field for either -- there is nothing for a caller to fill
in wrongly. `aux_agrees_with_object_header` states the consequence against the
section table the object actually emits, which is the half that is not merely
definitional.

## What the remaining fields are

`checkSum` is zero, which is what `ml64` writes for every section in both
measured objects; it is only meaningful for COMDAT sections. `number` and
`selection` are the COMDAT section index and selection rule, both zero because
this profile emits no COMDAT. `numberOfLinenumbers` is zero because nothing here
emits line numbers, and three unused bytes pad the record to eighteen.

Those are five fields that are always zero, and writing them out rather than
collapsing them is deliberate: the record is eighteen bytes whatever they hold,
and a reader that finds seventeen is desynchronised from that point on.
-/

namespace Grass.Platform.Win32.Coff

open Grass.ISA.X86 (le16 le32)
open Grass.Std.Logical (Byte ByteSeq)

/--
The auxiliary record that defines a section.

No field for the length or the relocation count: both are read off the
`Section` when the record is written, so they cannot disagree with the header.
-/
structure AuxSectionDefinition where
  /-- COMDAT checksum. Zero outside COMDAT, which is all this profile emits. -/
  checkSum : BitVec 32
  /-- One-based index of the COMDAT section this one is associated with. -/
  number : BitVec 16
  /-- COMDAT selection rule. -/
  selection : Byte
deriving DecidableEq, Repr, Inhabited

/-- The record this profile writes: no COMDAT, so every field is zero. -/
def AuxSectionDefinition.plain : AuxSectionDefinition where
  checkSum := 0
  number := 0
  selection := 0

/--
The eighteen bytes, with the size and relocation count taken from the section.

`numberOfLinenumbers` is zero because nothing here emits line numbers, and the
last three bytes are the record's unused tail. -/
def AuxSectionDefinition.toBytes (a : AuxSectionDefinition) (s : Section) :
    ByteSeq :=
  le32 (BitVec.ofNat 32 s.data.length)
    ++ le16 (BitVec.ofNat 16 s.relocations.length)
    ++ le16 0
    ++ le32 a.checkSum
    ++ le16 a.number
    ++ [a.selection, 0, 0, 0]

/--
**An auxiliary record is exactly eighteen bytes.**

The same width as a symbol, which is what lets a reader skip
`numberOfAuxSymbols` of them by multiplying. Seventeen or nineteen would
desynchronise the table from that point on. -/
@[simp] theorem AuxSectionDefinition.length_toBytes
    (a : AuxSectionDefinition) (s : Section) :
    (a.toBytes s).length = 18 := by
  simp [toBytes]

/--
**The record restates the section's own size and relocation count.**

Definitional, and said so: `toBytes` reads both off the `Section`, so this is
what the type already guarantees rather than something a proof discovers. It is
here because the *statement* is what a reader needs -- the fields are the
section's, not a caller's.

An earlier version carried two bound hypotheses about the fields' widths. They
were never used, because both sides of this equation wrap identically, and a
hypothesis that does no work is a claim that the theorem is stronger than it
is. The real safety is one line above: `AuxSectionDefinition` has no length
field for anyone to fill in wrongly. -/
theorem aux_restates_section (a : AuxSectionDefinition) (s : Section) :
    ((a.toBytes s).take 4 = le32 (BitVec.ofNat 32 s.data.length))
    ∧ (((a.toBytes s).drop 4).take 2
        = le16 (BitVec.ofNat 16 s.relocations.length)) := by
  constructor <;>
    simp [AuxSectionDefinition.toBytes, Grass.ISA.X86.le32, Grass.ISA.X86.le16]

/--
**And those are the numbers the object's own section table carries.**

The statement that is not definitional. `Object.sectionHeaders` computes
`sizeOfRawData` and `numberOfRelocations` independently of this module, and
this says the auxiliary record agrees with the header the object actually
emits -- so the format's duplication cannot come apart.

Proved by the same decomposition `header_points_at_data` uses: name the section
by splitting the list at it, and the header for it falls out of how
`sectionHeaders` zips. -/
theorem aux_agrees_with_object_header (o : Object) (pre : List Section)
    (sec : Section) (post : List Section) (a : AuxSectionDefinition)
    (h : o.sections = pre ++ sec :: post) :
    ∃ hdr ∈ o.sectionHeaders,
      (a.toBytes sec).take 4 = le32 hdr.sizeOfRawData
      ∧ ((a.toBytes sec).drop 4).take 2 = le16 hdr.numberOfRelocations := by
  refine ⟨{ name := sec.name
            virtualSize := 0
            virtualAddress := 0
            sizeOfRawData := BitVec.ofNat 32 sec.data.length
            pointerToRawData :=
              BitVec.ofNat 32
                (o.headerSize + (pre.map (fun x => x.data.length)).sum)
            pointerToRelocations :=
              BitVec.ofNat 32
                (o.headerSize + o.dataSize
                  + (pre.map Section.relocationSize).sum)
            pointerToLinenumbers := 0
            numberOfRelocations := BitVec.ofNat 16 sec.relocations.length
            numberOfLinenumbers := 0
            characteristics := sec.characteristics }, ?_, ?_, ?_⟩
  · unfold Object.sectionHeaders
    rw [h, dataOffsets_append, relocOffsets_append,
        List.zip_append (by simp), List.zip_append (by simp)]
    simp [dataOffsets, relocOffsets]
  · exact (aux_restates_section a sec).1
  · exact (aux_restates_section a sec).2

/-- A section symbol and the auxiliary record that defines it. -/
def sectionSymbolBytes (sym : Symbol) (a : AuxSectionDefinition)
    (s : Section) : ByteSeq :=
  sym.toBytes ++ a.toBytes s

/--
**A section symbol with its auxiliary record is thirty-six bytes.**

Two entries, which is exactly what `numberOfAuxSymbols = 1` tells a reader to
expect. A symbol declaring one auxiliary record and emitting none is the defect
this module was added to remove. -/
@[simp] theorem length_sectionSymbolBytes (sym : Symbol)
    (a : AuxSectionDefinition) (s : Section) :
    (sectionSymbolBytes sym a s).length = 36 := by
  simp [sectionSymbolBytes]

end Grass.Platform.Win32.Coff
