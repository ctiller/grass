import Grass.Platform.Win32.CoffSymbol
import Grass.Platform.Win32.CoffStrings

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
definitional. It lives in `CoffLayout.lean`, because `Object` does and this
module deliberately sits below it -- a section's records do not need to know
how a file is laid out.

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

/-! ## Symbol table entries

## `NumberOfSymbols` counts records, not symbols

The file header's `numberOfSymbols` is the number of eighteen-byte *entries* in
the table, auxiliary records included. Both measured objects report fifteen:
ten symbols and five auxiliary records, not ten. A writer that reported the
symbol count would be wrong by the number of sections it defined.

That is not a cosmetic miscount. A relocation names its symbol by index into
this table, so every index past the first auxiliary record would shift -- and a
relocation pointing one entry early resolves against the previous symbol, which
in these objects is a *section* rather than a function. The object would link
and the call would go to the wrong place.

`SymbolEntry` is what makes both counts come from one structure.
-/

/--
A symbol together with the auxiliary record defining it, if it has one.

The pairing is the point. `Symbol.numberOfAuxSymbols` is a field a caller could
set to one while supplying no record, or to zero while supplying one; here the
field is *derived* from whether `aux` is present, so the two cannot disagree.
-/
structure SymbolEntry where
  /-- The symbol itself. Its `numberOfAuxSymbols` field is ignored and
  recomputed -- see `SymbolEntry.toBytes`. -/
  symbol : Symbol
  /-- The auxiliary section definition, and the section it describes. -/
  aux : Option (AuxSectionDefinition × Section)

/-- How many eighteen-byte table entries this contributes. -/
def SymbolEntry.count (e : SymbolEntry) : Nat :=
  match e.aux with
  | none => 1
  | some _ => 2

/--
The entry's bytes, with `numberOfAuxSymbols` recomputed from `aux`.

A caller cannot declare a record it does not supply, because the declaration is
not theirs to make. -/
def SymbolEntry.toBytes (e : SymbolEntry) : ByteSeq :=
  match e.aux with
  | none => { e.symbol with numberOfAuxSymbols := 0 }.toBytes
  | some (a, s) =>
      { e.symbol with numberOfAuxSymbols := 1 }.toBytes ++ a.toBytes s

/--
**An entry is eighteen bytes per record it claims.**

The statement tying `count` to the bytes, which is what makes
`numberOfSymbols` computable from the entry list without walking it twice. -/
@[simp] theorem SymbolEntry.length_toBytes (e : SymbolEntry) :
    e.toBytes.length = 18 * e.count := by
  unfold toBytes count
  cases e.aux <;> simp

/--
**A symbol with an auxiliary record declares exactly one.**

Half of the agreement; the other half is that a symbol without one declares
none. Together they say the field always describes what follows it. -/
theorem SymbolEntry.declares_its_aux (e : SymbolEntry)
    (a : AuxSectionDefinition) (s : Section) (h : e.aux = some (a, s)) :
    e.toBytes = { e.symbol with numberOfAuxSymbols := 1 }.toBytes
        ++ a.toBytes s := by
  unfold toBytes
  rw [h]

/-- **And a symbol without one declares none.** -/
theorem SymbolEntry.declares_no_aux (e : SymbolEntry) (h : e.aux = none) :
    e.toBytes = { e.symbol with numberOfAuxSymbols := 0 }.toBytes := by
  unfold toBytes
  rw [h]

/-- Every entry's bytes, in table order. -/
def symbolTableBytes (entries : List SymbolEntry) : ByteSeq :=
  (entries.map SymbolEntry.toBytes).flatten

/-- The number the file header must report: records, not symbols. -/
def symbolRecordCount (entries : List SymbolEntry) : Nat :=
  (entries.map SymbolEntry.count).sum

/--
**The table is eighteen bytes per reported record.**

The theorem a reader depends on: it takes `numberOfSymbols`, multiplies by
eighteen, and expects to land exactly on the string table. -/
theorem length_symbolTableBytes (entries : List SymbolEntry) :
    (symbolTableBytes entries).length = 18 * symbolRecordCount entries := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
      simp only [symbolTableBytes, symbolRecordCount, List.map_cons,
                 List.flatten_cons, List.length_append, List.sum_cons,
                 SymbolEntry.length_toBytes] at *
      omega

end Grass.Platform.Win32.Coff
