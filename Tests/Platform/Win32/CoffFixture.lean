import Grass.Platform.Win32.Coff
import Grass.Platform.Win32.CoffSymbol
import Grass.Platform.Win32.CoffPdata

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

end Grass.Tests.Platform.Win32.Coff
