import Grass.Platform.Win32.Coff
import Grass.Platform.Win32.CoffSymbol
import Grass.Platform.Win32.CoffPdata
import Grass.Platform.Win32.CoffXdata
import Grass.Platform.Win32.CoffAux
import Grass.Platform.Win32.CoffWellFormed
import Grass.Platform.Win32.CoffText

/-!
# COFF records, against a real object file

Every byte string below was read out of an object file `ml64` produced, once,
with a throwaway script that was not kept. The prologue was
`grassprobe PROC FRAME :grasshandler; push rbp; .pushreg rbp; push rbx;
.pushreg rbx; .endprolog; xor eax, eax; pop rbx; pop rbp; ret` -- seven bytes of
code, one handler, five sections.

## Why a fixture and not a differential

A differential re-runs the assembler on every build, which is what you want
against an oracle that moves. These records do not move: COFF has had these
field orders and widths since the format was published, and a build that
reproduced these bytes yesterday reproduces them tomorrow. What the model can
still get wrong is field order, field width and padding, and a recorded
measurement catches that exactly as well as a re-run would -- without a harness
for anyone to own.

So the measurement is kept and the script that made it is not. The prologue
above is enough to reproduce the object if these ever need re-measuring.

## What this establishes, and what it does not

It establishes that `FileHeader.toBytes`, `SectionHeader.toBytes`,
`Relocation.toBytes` and `Symbol.toBytes` agree with a real assembler on field
order, width and padding, which is the whole content of those definitions.

It does not establish that this profile can write a linkable object file.
`CoffLayout.lean` still emits no symbol table -- the records are modelled here,
but nothing places them in a file or fills in `pointerToSymbolTable`. There is
no string table either, so a `SymbolName.long` offset points into something that
does not exist yet. And nothing here says anything about `.pdata`'s *contents*:
the relocations are checked as records, not as a correct `RUNTIME_FUNCTION`
table.
-/

namespace Grass.Tests.Platform.Win32.Coff

open Grass.Platform.Win32.Coff
open Grass.Std.Logical (ByteSeq)

-- The whole-object theorems at the end evaluate a three-hundred-byte file by
-- `decide`, which walks the list. The default depth is not enough and the
-- alternative -- checking only fragments -- would defeat the point of
-- instantiating the layout theorems on a real file.
set_option maxRecDepth 8000

/-! ## The file header -/

/-- The header of the measured object: five sections, no optional header. -/
def measuredFileHeader : FileHeader where
  machine := .amd64
  numberOfSections := 5
  timeDateStamp := 0x6a9f7118
  pointerToSymbolTable := 0x224
  numberOfSymbols := 15
  sizeOfOptionalHeader := 0
  characteristics := 0

/--
**The twenty bytes `ml64` wrote.**

The machine code leads, little-endian, which is the field a reader checks first
to decide whether it is looking at an AMD64 object at all. -/
theorem measuredFileHeader_bytes :
    measuredFileHeader.toBytes =
      [0x64, 0x86, 0x05, 0x00, 0x18, 0x71, 0x9f, 0x6a, 0x24, 0x02, 0x00, 0x00,
       0x0f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by
  decide

/-- **An object file's section table starts at byte twenty.** -/
theorem measuredFileHeader_sectionTable :
    measuredFileHeader.sectionTableOffset = 20 := by decide

/-! ## The section name -/

/-- `.pdata`, six bytes, which the field pads to eight. -/
def pdataName : SectionName :=
  ⟨[0x2e, 0x70, 0x64, 0x61, 0x74, 0x61], by decide⟩

/-- **The name field `ml64` wrote: six bytes and two of padding.** -/
theorem pdataName_bytes :
    pdataName.toBytes = [0x2e, 0x70, 0x64, 0x61, 0x74, 0x61, 0x00, 0x00] := by
  decide

/--
**A nine-byte name is refused rather than truncated.**

`.debug$XX` is a real section name one byte too long for the field, which a real
toolchain stores in the string table. This profile does not, and refusing is
what makes that absence visible instead of silently writing `.debug$X`. -/
theorem long_name_refused :
    SectionName.mk? [0x2e, 0x64, 0x65, 0x62, 0x75, 0x67, 0x24, 0x58, 0x58]
      = none := by decide

/-! ## The section header -/

/-- The `.pdata` section header of the measured object. -/
def measuredPdataHeader : SectionHeader where
  name := pdataName
  virtualSize := 0
  virtualAddress := 0
  sizeOfRawData := 12
  pointerToRawData := 0xe3
  pointerToRelocations := 0xf0
  pointerToLinenumbers := 0
  numberOfRelocations := 3
  numberOfLinenumbers := 0
  characteristics := 0x40300040

/--
**The forty bytes `ml64` wrote for `.pdata`.**

`sizeOfRawData` is twelve: one `RUNTIME_FUNCTION`. `numberOfRelocations` is
three, which is the whole reason an unlinked object is readable at all -- the
twelve bytes it points at are entirely zero except the function length. -/
theorem measuredPdataHeader_bytes :
    measuredPdataHeader.toBytes =
      [0x2e, 0x70, 0x64, 0x61, 0x74, 0x61, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0x0c, 0x00, 0x00, 0x00, 0xe3, 0x00, 0x00, 0x00,
       0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0x03, 0x00, 0x00, 0x00, 0x40, 0x00, 0x30, 0x40] := by
  decide

/-! ## The relocations -/

/--
The three relocations `ml64` emitted into `.pdata`, in file order.

Symbol 13 is the function and symbol 14 is its `UNWIND_INFO`, so `BeginAddress`
and `EndAddress` name the same symbol and `UnwindInfoAddress` names a different
one. That is the shape a reader uses to pair an entry with its unwind data. -/
def measuredPdataRelocations : List Relocation :=
  [ ⟨0, 13, .addr32nb⟩
  , ⟨4, 13, .addr32nb⟩
  , ⟨8, 14, .addr32nb⟩ ]

/--
**The thirty bytes of `.pdata`'s relocation directory.**

Offsets 0, 4 and 8: the three `RUNTIME_FUNCTION` fields, each a four-byte RVA,
each relocated. This is the measurement that makes the field order checkable at
all, since the raw bytes those relocations point at are zero. -/
theorem measuredPdataRelocations_bytes :
    (measuredPdataRelocations.map Relocation.toBytes).flatten =
      [0x00, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x03, 0x00,
       0x04, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x03, 0x00,
       0x08, 0x00, 0x00, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x03, 0x00] := by
  decide

/--
**The directory is a fixed stride, so entry `n` starts at `10 * n`.**

Stated against the measured list rather than in general, because it is the
property a reader relies on and the one a wrong record size would break. -/
theorem measuredPdataRelocations_stride :
    (measuredPdataRelocations.map Relocation.toBytes).flatten.length
      = 10 * measuredPdataRelocations.length := by
  decide

/-! ## Symbols

The same object carried fifteen symbols. Three are recorded here, chosen because
between them they exercise both name forms and two of the three reserved section
numbers.

These check the eighteen-byte record only. Five of the object's symbols declare
`numberOfAuxSymbols = 1` and are followed by an auxiliary record this profile
does not model; the field is written so a reader skips correctly, but the
auxiliary record itself is absent, so a fixture over the following bytes would
fail and should.
-/

/-- The `.pdata` section symbol: inline name, a real section, one auxiliary
record following. -/
def measuredPdataSymbol : Symbol where
  name := .short pdataName
  value := 0
  sectionNumber := .section_ 3
  type := 0
  storageClass := 3
  numberOfAuxSymbols := 1

/-- **The eighteen bytes `ml64` wrote for the `.pdata` section symbol.** -/
theorem measuredPdataSymbol_bytes :
    measuredPdataSymbol.toBytes =
      [0x2e, 0x70, 0x64, 0x61, 0x74, 0x61, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x03, 0x01] := by
  decide

/--
`grasshandler`: the external the prologue named.

Its name is twelve bytes, so it takes the long form -- four zero bytes then an
offset of four into the string table. Its section number is zero, which is not
section zero but `undefined`: the symbol is resolved by another object, which is
what an `EXTERN` in the source becomes.

It is symbol 12, and it is *not* what the `.pdata` relocations point at -- those
name symbol 13, `grassprobe`, for both `BeginAddress` and `EndAddress`.
`grasshandler` is referenced from `.xdata` instead, by the handler field. An
earlier version of this sentence said symbol 13 and claimed the `.pdata`
relocations reached it, which was wrong twice over in a docstring written from
the same measurement that refutes it. -/
def measuredHandlerSymbol : Symbol where
  name := .long 4
  value := 0
  sectionNumber := .undefined
  type := 0
  storageClass := 2
  numberOfAuxSymbols := 0

/-- **The eighteen bytes `ml64` wrote for `grasshandler`.** -/
theorem measuredHandlerSymbol_bytes :
    measuredHandlerSymbol.toBytes =
      [0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x00] := by
  decide

/--
`grassprobe`: the function itself.

Long form again, offset seventeen. Section one, and a type of `0x0020`, which is
the complex type `DTYPE_FUNCTION` -- the field that tells a linker this symbol
is code rather than data. -/
def measuredProbeSymbol : Symbol where
  name := .long 17
  value := 0
  sectionNumber := .section_ 1
  type := 0x0020
  storageClass := 2
  numberOfAuxSymbols := 0

/-- **The eighteen bytes `ml64` wrote for `grassprobe`.** -/
theorem measuredProbeSymbol_bytes :
    measuredProbeSymbol.toBytes =
      [0x00, 0x00, 0x00, 0x00, 0x11, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x20, 0x00, 0x02, 0x00] := by
  decide

/--
**`grassprobe`'s name cannot be written inline, and the model refuses to try.**

Ten bytes, so `short?` turns it away and the long form is the only option --
which is why `ml64` used it. The refusal here is the length bound rather than
the leading-NUL rule. -/
theorem probe_name_too_long :
    SymbolName.short?
      [0x67, 0x72, 0x61, 0x73, 0x73, 0x70, 0x72, 0x6f, 0x62, 0x65] = none := by
  decide

/-! ## `.pdata` built rather than transcribed

The relocations above were written out as literals. These build the same section
from a description of the function -- which symbol it is, which symbol its
unwind data is, and how long it is -- and check that what comes out is what
`ml64` wrote. That is a stronger statement than the literal one: it says the
*constructor* agrees with the assembler, not just that a hand-copied list does.
-/

/-- The measured object's single `.pdata` entry: `grassprobe` is symbol 13, its
`UNWIND_INFO` is symbol 14, and the function is seven bytes long. -/
def measuredPdataEntry : PdataEntry where
  functionSymbol := 13
  unwindSymbol := 14
  functionLength := 7
  unwindOffset := 0

/--
**The twelve bytes `ml64` wrote into `.pdata`.**

Two zero addresses around the length. `BeginAddress` and `UnwindInfoAddress`
read zero because the linker has not run; `EndAddress` holds seven, which is
`push rbp; push rbx; xor eax, eax; pop rbx; pop rbp; ret`. -/
theorem measuredPdataEntry_bytes :
    pdataBytes [measuredPdataEntry] =
      [0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00] := by
  decide

/--
**The constructed relocations are the ones `ml64` emitted.**

Byte-for-byte the same thirty bytes as `measuredPdataRelocations_bytes` above,
but reached by building the section rather than by transcribing it. If
`PdataEntry.relocations` put a field at the wrong offset or named the wrong
symbol, this would differ and that would not. -/
theorem measuredPdataRelocations_constructed :
    ((pdataRelocations [measuredPdataEntry]).map Relocation.toBytes).flatten
      = (measuredPdataRelocations.map Relocation.toBytes).flatten := by
  decide

/-- **And the built section carries exactly what the measured header
described**: twelve bytes of data and three relocations. -/
theorem measuredPdataSection_shape :
    (pdataSection pdataName [measuredPdataEntry]).data.length = 12
    ∧ (pdataSection pdataName [measuredPdataEntry]).relocations.length = 3
    ∧ (pdataSection pdataName [measuredPdataEntry]).characteristics
        = measuredPdataHeader.characteristics := by
  decide

/-! ## Two functions, which is what pins the stride

A second object was assembled for this: `alpha`, five bytes with one pushed
register, and `beta`, seven bytes with two. One entry cannot show the stride --
at index zero, a twelve-byte stride and an eight-byte one give the same offsets,
and a mutation to that effect survived a fixture that had only `grassprobe`.

It also caught a real defect. `UnwindInfoAddress` is not zero for the second
function: both share one `.xdata` section, so the field carries the byte offset
of that function's own `UNWIND_INFO` within it. The model wrote zero there until
this object was measured.
-/

/-- `alpha`: five bytes, unwind data at the start of `.xdata`. -/
def alphaEntry : PdataEntry where
  functionSymbol := 12
  unwindSymbol := 13
  functionLength := 5
  unwindOffset := 0

/-- `beta`: seven bytes, unwind data eight bytes into the same `.xdata`. -/
def betaEntry : PdataEntry where
  functionSymbol := 14
  unwindSymbol := 13
  functionLength := 7
  unwindOffset := 8

/--
**The twenty-four bytes `ml64` wrote for two functions.**

The second entry's trailing eight is the defect this fixture exists to catch:
`beta`'s `UNWIND_INFO` is not at the start of `.xdata`, and a model that wrote
zero would aim every function after the first at the first one's unwind data. -/
theorem twoFunction_pdata_bytes :
    pdataBytes [alphaEntry, betaEntry] =
      [0x00, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00]
      := by decide

/--
**The six relocations, at offsets 0, 4, 8, 12, 16 and 20.**

The stride, measured rather than assumed. The second entry's three fields start
at twelve, which is what makes a twelve-byte `RUNTIME_FUNCTION` observable at
all; every one-entry fixture agrees with an eight-byte stride by accident.

Note that `alpha` and `beta` are symbols 12 and 14 while both unwind
relocations name 13: one `$xdatasym` shared between them, distinguished by the
addend rather than by the symbol. -/
theorem twoFunction_pdata_relocations :
    ((pdataRelocations [alphaEntry, betaEntry]).map Relocation.toBytes).flatten
      = [0x00, 0x00, 0x00, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x03, 0x00,
         0x04, 0x00, 0x00, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x03, 0x00,
         0x08, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x03, 0x00,
         0x0c, 0x00, 0x00, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x03, 0x00,
         0x10, 0x00, 0x00, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x03, 0x00,
         0x14, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x03, 0x00] := by
  decide

/-! ## `.xdata`, and the two sections agreeing

The same two-function object. Its `.xdata` is sixteen bytes: two eight-byte
`UNWIND_INFO` blocks at offsets zero and eight, with no relocations at all --
unwind data refers to nothing outside itself unless it carries a handler.
-/

/-- `alpha`'s `UNWIND_INFO`: version 1, no flags, one code pushing rbp, and a
padding slot. -/
def alphaUnwind : ByteSeq :=
  [0x01, 0x01, 0x01, 0x00, 0x01, 0x50, 0x00, 0x00]

/-- `beta`'s: two codes, so no padding slot is needed. -/
def betaUnwind : ByteSeq :=
  [0x01, 0x02, 0x02, 0x00, 0x02, 0x30, 0x01, 0x50]

/-- **The sixteen bytes `ml64` wrote into `.xdata`.** -/
theorem twoFunction_xdata_bytes :
    xdataBytes [alphaUnwind, betaUnwind] =
      [0x01, 0x01, 0x01, 0x00, 0x01, 0x50, 0x00, 0x00,
       0x01, 0x02, 0x02, 0x00, 0x02, 0x30, 0x01, 0x50] := by
  decide

/--
**Neither block needed padding.**

Both are eight bytes, which is already four-aligned, so `xdataBlock` is the
identity on them. This is what makes the padding path untested by the measured
object -- worth saying, since a mutation to the padding would survive these
bytes alone. -/
theorem twoFunction_xdata_unpadded :
    xdataBlock alphaUnwind = alphaUnwind ∧ xdataBlock betaUnwind = betaUnwind :=
  ⟨by decide, by decide⟩

/--
**A block of odd length is padded to the next boundary.**

The case the measured object cannot show, so it is stated on a made-up block
rather than left to the general theorem. Five bytes become eight. -/
theorem odd_block_padded :
    xdataBlock [0x01, 0x02, 0x03, 0x04, 0x05]
      = [0x01, 0x02, 0x03, 0x04, 0x05, 0x00, 0x00, 0x00] := by
  decide

/--
**`beta`'s entry points at `beta`'s unwind block, not `alpha`'s.**

The two sections agreeing, on the measured object. `betaEntry.unwindOffset` is
eight, and eight is where `xdataOffsets` puts the second block -- so reading
there returns `betaUnwind`.

This is the check that a hardcoded zero would fail, and it is the defect the
one-function fixture could not see. -/
theorem betaEntry_points_at_betaUnwind :
    ((xdataBytes [alphaUnwind, betaUnwind]).drop
        betaEntry.unwindOffset.toNat).take (xdataBlock betaUnwind).length
      = xdataBlock betaUnwind := by
  decide

/-- **And `alpha`'s points at `alpha`'s.** -/
theorem alphaEntry_points_at_alphaUnwind :
    ((xdataBytes [alphaUnwind, betaUnwind]).drop
        alphaEntry.unwindOffset.toNat).take (xdataBlock alphaUnwind).length
      = xdataBlock alphaUnwind := by
  decide

/--
**The two sections' flag words, as `ml64` wrote them.**

They differ, and the difference is the alignment field: `.pdata` carries
`ALIGN_4BYTES` and `.xdata` carries `ALIGN_8BYTES`. The model had `.pdata`'s
word in both places until this was measured -- a mistake invisible to every
block-offset theorem, because those are about alignment *within* the section
and this is alignment *of* it. -/
theorem section_characteristics_measured :
    pdataCharacteristics = 0x40300040
    ∧ xdataCharacteristics = 0x40400040
    ∧ pdataCharacteristics ≠ xdataCharacteristics := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-! ## A whole object, assembled

The layout theorems in `CoffLayout.lean` are quantified over any `Object`. This
builds one -- three sections, two symbols, one long name -- and instantiates
them, so that what they claim is visible as concrete numbers rather than only as
a statement about all files.

The object is the two-function shape measured throughout: `.text` holding
`alpha` and `beta`, `.pdata` with their two entries, `.xdata` with their two
unwind blocks. It is not byte-identical to what `ml64` produced and does not try
to be -- that object also carries `.data`, `.debug$S`, `@comp.id` and `@feat.00`,
and interleaves each section's relocations with its data. What is checked is
that every pointer in this file addresses what it claims to.
-/

/-- `.text`: alpha's five bytes then beta's seven. -/
def textSection : Section where
  name := ⟨[0x2e, 0x74, 0x65, 0x78, 0x74], by decide⟩
  data := [0x55, 0x33, 0xc0, 0x5d, 0xc3,
           0x55, 0x53, 0x33, 0xc0, 0x5b, 0x5d, 0xc3]
  relocations := []
  characteristics := 0x60500020

/--
The demo's own `.pdata` entries.

`alphaEntry` and `betaEntry` name symbols 12, 13 and 14, which are the indices
those functions have in the object `ml64` produced -- an object with fifteen
records. This file has five, so reusing them would describe relocations pointing
past the end of its own symbol table.

`Object.WellFormed` caught exactly that: the first version of `demoObject` did
reuse them, and it was not well formed. These are the same two functions
renumbered for the table this object actually has -- symbol 2 is the function,
symbol 3 is the `.xdata` section it unwinds through. -/
def demoPdataEntries : List PdataEntry :=
  [ { functionSymbol := 2, unwindSymbol := 3
      functionLength := 5, unwindOffset := 0 }
  , { functionSymbol := 2, unwindSymbol := 3
      functionLength := 7, unwindOffset := 8 } ]

/-- `.xdata`, named so the demo's symbol table can define it. -/
def demoXdataName : SectionName :=
  ⟨[0x2e, 0x78, 0x64, 0x61, 0x74, 0x61], by decide⟩

/-- The three sections in file order. -/
def demoSections : List Section :=
  [ textSection
  , pdataSection pdataName demoPdataEntries
  , xdataSection demoXdataName [alphaUnwind, betaUnwind] [] ]

/--
Three table entries from two symbols.

The `.text` section symbol carries an auxiliary record, so it occupies two
entries; the two function symbols occupy one each. That is what makes
`numberOfSymbols` three rather than two, and it is the arithmetic a relocation's
index depends on. -/
def demoSymbols : List SymbolEntry :=
  [ { symbol :=
        { name := .short ⟨[0x2e, 0x74, 0x65, 0x78, 0x74], by decide⟩
          value := 0, sectionNumber := .section_ 1, type := 0
          storageClass := 3, numberOfAuxSymbols := 1 }
      aux := some (AuxSectionDefinition.plain, textSection) }
  , { symbol :=
        { name := .long 4
          value := 5, sectionNumber := .section_ 1, type := 0x0020
          storageClass := 2, numberOfAuxSymbols := 0 }
      aux := none }
  , { symbol :=
        { name := .short demoXdataName
          value := 0, sectionNumber := .section_ 3, type := 0
          storageClass := 3, numberOfAuxSymbols := 1 }
      aux := some (AuxSectionDefinition.plain,
                   xdataSection demoXdataName [alphaUnwind, betaUnwind] []) } ]

/-- The whole object. -/
def demoObject : Object where
  machine := .amd64
  sections := demoSections
  symbols := demoSymbols
  strings := [[0x62, 0x65, 0x74, 0x61, 0x5f, 0x6c, 0x6f, 0x6e, 0x67]]

/--
**The file's size is exactly its parts.**

Twenty bytes of header, one hundred and twenty of section table, fifty-two of
data, sixty of relocations, ninety of symbol table -- five records for three
symbols -- and fourteen of string table. No padding and no slack, which is what makes every offset below mean
what it says. -/
theorem demoObject_length : demoObject.toBytes.length = 356 := by decide

/-- **The section table starts at byte twenty and holds three headers.** -/
theorem demoObject_sectionTable :
    demoObject.fileHeader.sectionTableOffset = 20
    ∧ demoObject.fileHeader.numberOfSections.toNat = 3 := by decide

/--
**Each section's data is at the offset its own header gives.**

`header_points_at_data` instantiated three times. These are the numbers a
reader would follow: `.text` at 140, `.pdata` at 152, `.xdata` at 176. -/
theorem demoObject_data_offsets :
    ((demoObject.toBytes.drop 140).take 12) = textSection.data
    ∧ ((demoObject.toBytes.drop 152).take 24)
        = (pdataSection pdataName demoPdataEntries).data
    ∧ ((demoObject.toBytes.drop 176).take 16)
        = xdataBytes [alphaUnwind, betaUnwind] := by
  decide

/--
**The symbol table is where the file header points, and reports three
records for two symbols.**

The count is the point. Three symbols are defined; two of them are section
symbols with auxiliary records, so the table holds five eighteen-byte entries
and the header must say five. A writer reporting three would leave every
relocation index past the first auxiliary record pointing two entries early --
at a section symbol rather than at the function it meant. -/
theorem demoObject_symbolTable :
    demoObject.fileHeader.pointerToSymbolTable.toNat = 252
    ∧ demoObject.fileHeader.numberOfSymbols.toNat = 5
    ∧ ((demoObject.toBytes.drop 252).take 90)
        = symbolTableBytes demoSymbols := by
  decide

/--
**The long symbol name resolves to a real string.**

The second symbol carries offset four, and offset four in this object's string
table is `beta_long`. That is the whole promise of a `SymbolName.long`, checked
on a concrete file rather than as a quantified statement. -/
theorem demoObject_long_name_resolves :
    ((stringTableBytes demoObject.strings).drop 4).take 9
      = [0x62, 0x65, 0x74, 0x61, 0x5f, 0x6c, 0x6f, 0x6e, 0x67] := by
  decide

/-! ## Auxiliary section records

Every section symbol in both measured objects declares one auxiliary record and
is followed by it. The records are almost entirely zero: only the section's
size and its relocation count are set, and both are copies of fields already in
that section's header.
-/

/--
**The auxiliary record `ml64` wrote for `.pdata`, in the two-function object.**

Twenty-four bytes of data and six relocations -- the same two numbers as that
section's header, which is the duplication `aux_agrees_with_object_header`
exists to keep consistent. -/
theorem measuredPdataAux_bytes :
    AuxSectionDefinition.plain.toBytes
        (pdataSection pdataName [alphaEntry, betaEntry]) =
      [0x18, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by
  decide

/--
**And for `.xdata`, which has no relocations at all.**

Sixteen bytes, zero relocations. In the *other* measured object `.xdata` had one
relocation, because that function carried a handler -- so this pair of fixtures
covers both the presence and the absence. -/
theorem measuredXdataAux_bytes :
    AuxSectionDefinition.plain.toBytes
        (xdataSection ⟨[0x2e, 0x78, 0x64, 0x61, 0x74, 0x61], by decide⟩
          [alphaUnwind, betaUnwind] []) =
      [0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by
  decide

/--
**A section symbol and its auxiliary record are two table entries.**

Thirty-six bytes, which is what `numberOfAuxSymbols = 1` promises a reader.
A symbol declaring an auxiliary record and emitting none leaves the table
desynchronised from that point on, and that was the state of these modules
before `CoffAux.lean`. -/
theorem sectionSymbol_with_aux_is_two_entries :
    ({ symbol := measuredPdataSymbol
       aux := some (AuxSectionDefinition.plain,
                    pdataSection pdataName [alphaEntry, betaEntry])
     } : SymbolEntry).count = 2
    ∧ ({ symbol := measuredPdataSymbol
         aux := some (AuxSectionDefinition.plain,
                      pdataSection pdataName [alphaEntry, betaEntry])
       } : SymbolEntry).toBytes.length = 36 := by
  decide

/--
**And the whole object is internally consistent.**

`Object.WellFormed` on a real file: every relocation names a record the table
has, every symbol names a section that exists, and every auxiliary record
describes a section of this object.

This is the theorem that failed first. `demoObject` originally reused
`alphaEntry` and `betaEntry`, whose symbol indices are 12, 13 and 14 -- correct
for the fifteen-record object `ml64` wrote and past the end of this one's
five. Nothing else in this file noticed: the lengths were right, every offset
resolved, and the bytes were exactly what the model said they should be. Only
the cross-record predicate saw it. -/
theorem demoObject_wellFormed : Object.WellFormed demoObject := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## RIP-relative relocations, and the family they come from

Two more objects were measured for this. The first calls an extern and reads a
global twice; the second writes immediates of three different widths through a
RIP-relative displacement. Between them they show what decides which member of
the `REL32` family an instruction needs.
-/

/--
**A call and two RIP-relative loads all take plain `REL32`.**

`call callee` puts its displacement at code offset 2, `mov rax, [rip+disp]` at
9, and `lea rcx, [rip+disp]` at 16 -- and in every case the field is the last
four bytes of the instruction, so nothing follows it and `REL32` is right. -/
theorem plain_rel32_relocations :
    (RelocationType.ripRelative? 0).map RelocationType.code
      = some 0x0004 := by
  decide

/--
**An immediate after the displacement changes the relocation.**

Measured: `mov DWORD PTR [rip+disp], imm32` gets `REL32_4`, `mov BYTE PTR
[rip+disp], imm8` gets `REL32_1`, and `mov WORD PTR [rip+disp], imm16` gets
`REL32_2`. The code is four plus the number of trailing bytes in each case.

This is the fact a writer gets wrong by reaching for `REL32` everywhere: the
linker computes the target relative to the byte after the *field*, so an
instruction that continues past it resolves short by exactly the bytes that
follow. -/
theorem trailing_immediates_pick_the_family :
    (RelocationType.ripRelative? 4).map RelocationType.code = some 0x0008
    ∧ (RelocationType.ripRelative? 1).map RelocationType.code = some 0x0005
    ∧ (RelocationType.ripRelative? 2).map RelocationType.code = some 0x0006 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/--
**Six trailing bytes is refused.**

No encoding exists past `REL32_5`, and no x86-64 instruction puts more than an
`imm32` after a RIP-relative displacement. Refusing rather than clamping is
what keeps a future caller from silently getting `REL32_5`. -/
theorem six_trailing_bytes_refused :
    RelocationType.ripRelative? 6 = none := by decide

/--
**The three fixed kinds still encode distinctly.**

`ADDR32NB` is 3 and `REL32` is 4, adjacent -- a transposition between them
gives a file that links with every address computed against the wrong base. -/
theorem fixed_kinds_distinct :
    RelocationType.addr64.code ≠ RelocationType.addr32nb.code
    ∧ RelocationType.addr32nb.code ≠ RelocationType.rel32.code := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## `.text` and its displacement sites

The measured call object: `push rbp; call callee; mov rax, [rip+globalWord];
lea rcx, [rip+globalWord]; pop rbp; ret` -- twenty-two bytes with three
displacement fields, at offsets 2, 9 and 16.
-/

/-- The twenty-two bytes `ml64` assembled, displacements left zero. -/
def callerCode : ByteSeq :=
  [0x55, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x05, 0x00, 0x00,
   0x00, 0x00, 0x48, 0x8d, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xc3]

/--
The three sites, as a writer knows them.

None has trailing bytes: in each instruction the displacement is the last four
bytes. `callee` is symbol 12 and `globalWord` is 13, which is what `ml64`
recorded. -/
def callerSites : List DisplacementSite :=
  [ ⟨2, 12, 0⟩, ⟨9, 13, 0⟩, ⟨16, 13, 0⟩ ]

/--
**The three relocations `ml64` emitted for those sites.**

Thirty bytes: offsets 2, 9 and 16, symbols 12, 13 and 13, all type 4. Built
from the sites rather than transcribed, so this says the constructor agrees
with the assembler. -/
theorem callerRelocations_bytes :
    (displacementRelocations? callerSites).map
        (fun rs => (rs.map Relocation.toBytes).flatten)
      = some
        [0x02, 0x00, 0x00, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x04, 0x00,
         0x09, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x04, 0x00,
         0x10, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x04, 0x00] := by
  decide

/--
**Every site fits, so the section is built.**

The last one is the tight case: its field is at 16 and the code is 22 bytes, so
the field ends exactly at 20 with the `pop rbp; ret` after it. A field two
bytes later would not fit and `textSection?` would refuse. -/
theorem callerSection_builds :
    (textSection? dotText callerCode callerSites).isSome := by decide

/--
**Moving the last site two bytes on makes it run off the end.**

22 bytes of code, a field at 18, and four bytes of field need through 21 --
which fits. At 19 it does not. This is the boundary, checked on the real
instruction stream rather than a made-up one. -/
theorem callerSection_boundary :
    (textSection? dotText callerCode [⟨18, 13, 0⟩]).isSome
    ∧ textSection? dotText callerCode [⟨19, 13, 0⟩] = none := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`.text`'s flag word, as `ml64` wrote it.** -/
theorem textCharacteristics_measured :
    textCharacteristics = 0x60500020 := by decide

/-! ## Sites with trailing bytes, which is what pins that term

Every site above has `trailing = 0`, so the `+ trailing` in
`DisplacementSite.InRange` was invisible: dropping it survived every check. The
second measured object has three sites with nonzero counts.

Its code is `mov DWORD PTR [rip+d], 5; mov BYTE PTR [rip+d], 7;
mov WORD PTR [rip+d], 9; ret` -- twenty-seven bytes, with displacement fields at
2, 12 and 20 followed by four, one and two bytes of immediate.
-/

/-- The twenty-seven bytes `ml64` assembled. -/
def immediateCode : ByteSeq :=
  [0xc7, 0x05, 0x00, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00,
   0xc6, 0x05, 0x00, 0x00, 0x00, 0x00, 0x07,
   0x66, 0xc7, 0x05, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0xc3]

/-- The three sites, with the trailing counts the immediates imply. -/
def immediateSites : List DisplacementSite :=
  [ ⟨2, 13, 4⟩, ⟨12, 13, 1⟩, ⟨20, 13, 2⟩ ]

/--
**The relocations `ml64` emitted: `REL32_4`, `REL32_1` and `REL32_2`.**

Types 8, 5 and 6 -- four plus the trailing count in each case. This is the
family being selected by the instruction, checked against the assembler that
selected it. -/
theorem immediateRelocations_bytes :
    (displacementRelocations? immediateSites).map
        (fun rs => (rs.map Relocation.toBytes).flatten)
      = some
        [0x02, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x08, 0x00,
         0x0c, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x05, 0x00,
         0x14, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x06, 0x00] := by
  decide

/-- **All three fit in the twenty-seven bytes.** -/
theorem immediateSection_builds :
    (textSection? dotText immediateCode immediateSites).isSome := by decide

/--
**A site whose field fits but whose immediate does not is refused.**

The case that pins the `+ trailing` term. In eight bytes of code a field at
offset two ends at six, so the field alone fits -- but four trailing bytes
carry the instruction through nine, which does not. A range check written
without the trailing term accepts this, and a mutation to that effect survived
every other theorem here. -/
theorem trailing_bytes_are_counted :
    (textSection? dotText (List.replicate 8 0x90) [⟨2, 0, 0⟩]).isSome
    ∧ textSection? dotText (List.replicate 8 0x90) [⟨2, 0, 4⟩] = none := by
  refine ⟨?_, ?_⟩ <;> decide

end Grass.Tests.Platform.Win32.Coff
