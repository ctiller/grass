import Grass.Platform.Win32.Coff

/-!
# COFF records, against a real object file

Every byte string below was read out of an object file `ml64` produced, once,
with a throwaway script that was not kept. The prologue was
`grassprobe PROC FRAME :grasshandler; push rbp; .pushreg rbp; push rbx;
.pushreg rbx; .endprolog; xor eax, eax; pop rbx; pop rbp; ret` -- seven bytes of
code, one handler, five sections.

## Why a fixture and not a differential

A differential re-runs the assembler on every build, which is what you want
against an oracle that moves. These three records do not move: the COFF file
header has had this field order and this width since the format was published,
and a build that reproduced these bytes yesterday reproduces them tomorrow. What
the model can still get wrong is field order, field width and padding, and a
recorded measurement catches that exactly as well as a re-run would -- without a
harness for anyone to own.

So the measurement is kept and the script that made it is not. The prologue
above is enough to reproduce the object if these ever need re-measuring.

## What this establishes, and what it does not

It establishes that `FileHeader.toBytes`, `SectionHeader.toBytes` and
`Relocation.toBytes` agree with a real assembler on field order, width and
padding, which is the whole content of those three definitions.

It does not establish that this profile can write a linkable object file.
Nothing here emits a symbol table, and the section header below points at raw
data this model does not lay out. It also says nothing about `.pdata`'s
*contents*: the relocations are checked as records, not as a correct
`RUNTIME_FUNCTION` table.
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

end Grass.Tests.Platform.Win32.Coff
