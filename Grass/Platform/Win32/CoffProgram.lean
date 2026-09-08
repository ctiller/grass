import Grass.Platform.Win32.CoffText
import Grass.Platform.Win32.CoffPdata
import Grass.Platform.Win32.CoffXdata
import Grass.Platform.Win32.CoffWellFormed

/-!
# Assembling a whole object from functions

Every module below this one makes one part right. This is where the parts have
to agree at once, and it is the first place where getting one of them wrong
shows up as a wrong *number* rather than a wrong record.

## Why the symbol indices are the hard part

A `.pdata` entry names its function and its unwind section by symbol index, and
those indices are into the table of eighteen-byte *records* -- so every
auxiliary record shifts everything after it. This profile emits a section
symbol with an auxiliary record for each of `.text`, `.pdata` and `.xdata`,
which is six records before the first function symbol appears.

Compute that wrongly by one and the object still links: the relocation resolves
against a section symbol instead of the function, and the unwinder is handed a
range starting at the section base. Nothing diagnoses it. `symbolIndexOf` is
the arithmetic, and `Object.WellFormed` is what checks the result rather than
the reasoning.

## What this does not do

It does not encode anything. A `FunctionUnit` arrives with its bytes already
produced -- `Grass/ISA/X86/Bytes.lean` makes those, and
`Grass/ABI/Win64/UnwindBytes.lean` makes the unwind block -- because the layout
question and the encoding question are separate, and mixing them would put x86
opcode knowledge in a file about file structure.

Nor does it emit `.data`, `.debug$S`, or the `@comp.id` and `@feat.00` symbols
`ml64` includes. An object from here is smaller than one from an assembler and
describes the same functions.
-/

namespace Grass.Platform.Win32.Coff

open Grass.Std.Logical (ByteSeq)

/--
One function, with everything the object needs to describe it.

The name is the symbol name without a terminator; the string table adds that.
-/
structure FunctionUnit where
  /-- The symbol name, which goes in the string table. -/
  name : ByteSeq
  /-- The encoded instructions. -/
  code : ByteSeq
  /-- The function's `UNWIND_INFO` block. -/
  unwind : ByteSeq
  /-- Displacement sites within `code`, offsets relative to the function. -/
  sites : List DisplacementSite

/-- How many table records precede the first function symbol.

Three section symbols, each with one auxiliary record. -/
def sectionSymbolRecords : Nat := 6

/--
The record index of the `n`-th function's symbol.

Six records of section symbols, then one record per function -- functions carry
no auxiliary records, so the index advances by one each time. -/
def symbolIndexOf (n : Nat) : Nat := sectionSymbolRecords + n

/-- The record index of the `.xdata` section symbol, which every `.pdata`
entry's `UnwindInfoAddress` resolves against. -/
def xdataSymbolIndex : Nat := 4

/-- **The first function's symbol comes after every section symbol.** -/
theorem symbolIndexOf_after_sections (n : Nat) :
    sectionSymbolRecords ≤ symbolIndexOf n := by
  simp [symbolIndexOf]

/-- **Distinct functions have distinct symbol indices.** -/
theorem symbolIndexOf_injective {m n : Nat} (h : symbolIndexOf m = symbolIndexOf n) :
    m = n := by
  simp [symbolIndexOf] at h
  exact h

/-- **The `.xdata` symbol is a section symbol, never a function's.**

Stated because both are record indices into one table, and a `.pdata` entry
carries one of each. If they could collide, an entry's `UnwindInfoAddress`
would resolve against a function and the unwinder would read code as unwind
data. -/
theorem xdataSymbolIndex_ne_function (n : Nat) :
    xdataSymbolIndex ≠ symbolIndexOf n := by
  simp only [xdataSymbolIndex, symbolIndexOf, sectionSymbolRecords]
  omega

/-- Where each function's code starts in `.text`. -/
def codeOffsets (start : Nat) : List FunctionUnit → List Nat
  | [] => []
  | u :: rest => start :: codeOffsets (start + u.code.length) rest

/-- Where each function's unwind block starts in `.xdata`. -/
def unwindOffsets (start : Nat) : List FunctionUnit → List Nat
  | [] => []
  | u :: rest => start :: unwindOffsets (start + (xdataBlock u.unwind).length) rest

/-- **There is one code offset per function.** -/
@[simp] theorem length_codeOffsets (start : Nat) (us : List FunctionUnit) :
    (codeOffsets start us).length = us.length := by
  induction us generalizing start with
  | nil => rfl
  | cons u rest ih => simp [codeOffsets, ih]

/-- **There is one unwind offset per function.** -/
@[simp] theorem length_unwindOffsets (start : Nat) (us : List FunctionUnit) :
    (unwindOffsets start us).length = us.length := by
  induction us generalizing start with
  | nil => rfl
  | cons u rest ih => simp [unwindOffsets, ih]

/-- All functions' code, concatenated. -/
def programCode (us : List FunctionUnit) : ByteSeq :=
  (us.map FunctionUnit.code).flatten

/-- All functions' unwind blocks, each padded. -/
def programUnwind (us : List FunctionUnit) : ByteSeq :=
  xdataBytes (us.map FunctionUnit.unwind)

/--
The `.pdata` entries, one per function, with indices and offsets filled in.

Every number here is computed: the function's symbol index from its position,
the unwind offset from the `.xdata` layout, and the length from the code
itself. -/
def programPdataEntries (us : List FunctionUnit) : List PdataEntry :=
  (us.zipIdx.zip (unwindOffsets 0 us)).map fun ((u, n), uoff) =>
    { functionSymbol := BitVec.ofNat 32 (symbolIndexOf n)
      unwindSymbol := BitVec.ofNat 32 xdataSymbolIndex
      functionLength := BitVec.ofNat 32 u.code.length
      unwindOffset := BitVec.ofNat 32 uoff }

/-- **There is one `.pdata` entry per function.** -/
@[simp] theorem length_programPdataEntries (us : List FunctionUnit) :
    (programPdataEntries us).length = us.length := by
  simp [programPdataEntries]

/-- **Every entry's unwind symbol is the `.xdata` section symbol.**

Not a per-function symbol: one `$xdatasym` shared by every entry, which is what
`ml64` emits and what the addend distinguishes. -/
theorem programPdataEntries_share_xdata_symbol (us : List FunctionUnit) :
    ∀ e ∈ programPdataEntries us,
      e.unwindSymbol = BitVec.ofNat 32 xdataSymbolIndex := by
  intro e he
  simp only [programPdataEntries, List.mem_map] at he
  obtain ⟨_, _, he⟩ := he
  subst he
  rfl

/-! ## The object -/

/-- `.text`, `.pdata` and `.xdata`, named. -/
def textName : SectionName := ⟨[0x2e, 0x74, 0x65, 0x78, 0x74], by decide⟩
/-- The `.pdata` section's name. -/
def pdataSectionName : SectionName :=
  ⟨[0x2e, 0x70, 0x64, 0x61, 0x74, 0x61], by decide⟩
/-- The `.xdata` section's name. -/
def xdataSectionName : SectionName :=
  ⟨[0x2e, 0x78, 0x64, 0x61, 0x74, 0x61], by decide⟩

/--
Every function's displacement sites, shifted to their place in `.text`.

A `FunctionUnit`'s sites are offsets within that function, because a function
does not know where it will be laid out. This is where it finds out. -/
def programSites (us : List FunctionUnit) : List DisplacementSite :=
  ((us.zip (codeOffsets 0 us)).map fun (u, base) =>
    u.sites.map fun d => { d with fieldOffset := base + d.fieldOffset }).flatten

/-- Where each function's name sits in the string table. -/
def nameOffsets (us : List FunctionUnit) : List Nat :=
  stringOffsets 4 (us.map FunctionUnit.name)

/-- **There is one name offset per function.** -/
@[simp] theorem length_nameOffsets (us : List FunctionUnit) :
    (nameOffsets us).length = us.length := by
  simp [nameOffsets]

/--
A section symbol and its auxiliary record.

The three of these are what makes `sectionSymbolRecords` six. -/
def sectionSymbolFor (nm : SectionName) (number : Nat) (s : Section) :
    SymbolEntry where
  symbol :=
    { name := .short nm, value := 0
      sectionNumber := .section_ number, type := 0
      storageClass := 3, numberOfAuxSymbols := 1 }
  aux := some (AuxSectionDefinition.plain, s)

/--
The whole object, or nothing if any displacement site cannot be placed.

Every index and offset is computed here and nowhere else: section numbers from
position, symbol record indices from `symbolIndexOf`, string offsets from
`nameOffsets`, code and unwind offsets from the layout. -/
def objectFor (us : List FunctionUnit) : Option Object :=
  match textSection? textName (programCode us) (programSites us) with
  | none => none
  | some text =>
      let pdata := pdataSection pdataSectionName (programPdataEntries us)
      let xdata := xdataSection xdataSectionName
        (us.map FunctionUnit.unwind) []
      some
        { machine := .amd64
          sections := [text, pdata, xdata]
          symbols :=
            [ sectionSymbolFor textName 1 text
            , sectionSymbolFor pdataSectionName 2 pdata
            , sectionSymbolFor xdataSectionName 3 xdata ]
            ++ ((us.zip (codeOffsets 0 us)).zip (nameOffsets us)).map
                 (fun ((_, base), noff) =>
                   { symbol :=
                       { name := .long (BitVec.ofNat 32 noff)
                         value := BitVec.ofNat 32 base
                         sectionNumber := .section_ 1
                         type := 0x0020, storageClass := 2
                         numberOfAuxSymbols := 0 }
                     aux := none })
          strings := us.map FunctionUnit.name }

/-- **An object with no functions still has its three sections.**

The base case. An empty program is not an empty file: a linker reading it finds
three sections and six symbol records describing nothing, which is what an
assembler produces for an empty source too. -/
theorem objectFor_empty_sections :
    (objectFor []).map (fun o => o.sections.length) = some 3 := by decide

/-- **And six symbol records, all of them section definitions.** -/
theorem objectFor_empty_records :
    (objectFor []).map (fun o => symbolRecordCount o.symbols)
      = some sectionSymbolRecords := by decide

/--
**Each function adds exactly one symbol record.**

Which is what `symbolIndexOf` assumes when it advances by one per function. A
function that carried an auxiliary record would break the arithmetic, and this
is where that assumption is stated rather than relied on. -/
theorem objectFor_records (us : List FunctionUnit) :
    (objectFor us).map (fun o => symbolRecordCount o.symbols)
      = (objectFor us).map (fun _ => sectionSymbolRecords + us.length) := by
  unfold objectFor
  split
  · rfl
  · simp only [Option.map_some]
    congr 1
    rw [symbolRecordCount_append, symbolRecordCount_map_none _ _ (fun _ => rfl)]
    simp [symbolRecordCount, sectionSymbolFor, SymbolEntry.count,
          sectionSymbolRecords]

end Grass.Platform.Win32.Coff
