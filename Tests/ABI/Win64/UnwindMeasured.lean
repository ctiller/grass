import Grass.ABI.Win64.UnwindBytes

/-!
# Unwind records measured against `ml64`, as fixtures

`UnwindCorpus.lean` is a differential: it emits a corpus that
`Tools/win64-unwind-differential.py` re-assembles. That tool is not this
agent's, and it needs `ml64.exe`, which exists only on Windows.

This file needs neither. Every byte string below was read out of an object
`ml64` produced, once, and is checked against the model by evaluation. It runs
wherever Lean does.

## What it covers that the corpus does not

`UnwindTail.flags`, `UnwindTail.handlerRva`, `UnwindTail.toBytes`,
`RuntimeFunction.toBytes` and `PdataSection.toBytes` were covered by nothing:
every corpus row uses `.noHandler` and none emits `.pdata`. Handler rows for
them existed briefly in the corpus and were deleted along with the differential
that checked them. The measurements survived; this is where they live now.

## Why a fixture is the right shape here and not everywhere

These records do not move. `UNWIND_INFO`'s field order and `RUNTIME_FUNCTION`'s
three-address layout have been fixed since Win64 shipped, so a recorded
measurement catches what a re-run would -- field order, width, padding -- and
catches it on any host.

That reasoning does not extend to the encoder differentials, where the corpus is
generated and the point is to re-run a moving corpus against a live assembler.
It applies here because the corpus is three records that a specification fixes.

## What `ml64` will and will not produce

`PROC FRAME:handler` sets *both* handler bits: the first byte is `0x19`, so
`Flags` reads 3, not `UNW_FLAG_EHANDLER` alone. There is no MASM syntax for a
termination-only handler, and `.handlerdata` is not a directive this assembler
build knows -- it is refused with the same `A2008 syntax error : .` as an
invented one, on a line where `.pushreg` assembles. So `.exceptionHandler`,
`.terminationHandler` and `.chained` have no oracle at all, and the
language-specific data is always one dword and always zero.
-/

namespace Grass.Tests.ABI.Win64.Measured

open Grass.ABI.Win64
open Grass.Std.Logical (ByteSeq)

/-! ## Handler tails -/

/-- The only tail `ml64` emits: both handler bits, a zero address, one zero
dword of language-specific data. -/
def ml64Tail : UnwindTail := .bothHandlers 0 [0]

/--
**`PROC FRAME:handler` sets `Flags` to 3, not 1.**

The measurement that makes `.exceptionHandler` untestable: there is no MASM
syntax that produces it, so a model emitting flags 1 would never be
contradicted by this assembler. -/
theorem ml64Tail_flags : ml64Tail.flags = 3 := by decide

/-- **The tail carries a handler address.** -/
theorem ml64Tail_hasHandler : ml64Tail.handlerRva = some 0 := by decide

/-- One push of `rbp`, which pads to two slots. -/
def onePush : Layout := ⟨[⟨.pushNonvolatile .rbp, 1⟩], 1⟩

/-- Two pushes: `rbp` then `rbx`, an even slot count with no padding. -/
def twoPush : Layout :=
  ⟨[⟨.pushNonvolatile .rbp, 1⟩, ⟨.pushNonvolatile .rbx, 2⟩], 2⟩

/-- Three pushes, which pads to four slots. -/
def threePush : Layout :=
  ⟨[⟨.pushNonvolatile .rbp, 1⟩, ⟨.pushNonvolatile .rbx, 2⟩,
    ⟨.pushNonvolatile .rsi, 3⟩], 3⟩

/-- No frame register. -/
def noFrame : FrameSpec := ⟨0, 0⟩

/--
**The sixteen bytes `ml64` wrote for one push with a handler.**

`19` is version 1 with flags 3; then `SizeOfProlog`, `CountOfCodes`, the frame
byte, one unwind code, a padding slot, then four zero bytes of handler address
and four of language-specific data. -/
theorem onePush_handler_bytes :
    (UnwindInfo.mk? onePush noFrame ml64Tail).map UnwindInfo.toBytes
      = some [0x19, 0x01, 0x01, 0x00, 0x01, 0x50, 0x00, 0x00,
              0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by
  decide

/-- **Two pushes: still sixteen bytes, because two codes fill the padding.** -/
theorem twoPush_handler_bytes :
    (UnwindInfo.mk? twoPush noFrame ml64Tail).map UnwindInfo.toBytes
      = some [0x19, 0x02, 0x02, 0x00, 0x02, 0x30, 0x01, 0x50,
              0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by
  decide

/--
**Three pushes: twenty bytes, because the code array pads to four slots.**

The parity case. One and two codes put the handler at byte 8; three and four
put it at byte 12. A model that forgot the padding agrees with `ml64` on the
even counts and disagrees on the odd ones, so measuring only `onePush` would
not have caught it. -/
theorem threePush_handler_bytes :
    (UnwindInfo.mk? threePush noFrame ml64Tail).map UnwindInfo.toBytes
      = some [0x19, 0x03, 0x03, 0x00, 0x03, 0x60, 0x02, 0x30,
              0x01, 0x50, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
              0x00, 0x00, 0x00, 0x00] := by
  decide

/--
**Without a handler the same prologue is eight bytes.**

The difference the tail makes, stated so the handler theorems above are not
just restating the header. -/
theorem onePush_noHandler_bytes :
    (UnwindInfo.mk? onePush noFrame .noHandler).map UnwindInfo.toBytes
      = some [0x01, 0x01, 0x01, 0x00, 0x01, 0x50, 0x00, 0x00] := by
  decide

/--
**The handler address comes before its language-specific data.**

Synthetic, and it has to be. In a real object the handler is an unresolved
relocation reading zero and the language-specific dword is zero too, so the
measured bytes are eight zeros either way -- a mutation swapping the two
survived every theorem above. The order is a fact about the format that this
oracle structurally cannot show, so it is stated on distinct values instead.

The same limitation that makes `.pdata`'s `BeginAddress` unmeasurable in an
object file: what a relocation supplies, the bytes do not. -/
theorem tail_handler_precedes_langData :
    (UnwindTail.bothHandlers 0x11223344 [0x55667788]).toBytes
      = [0x44, 0x33, 0x22, 0x11, 0x88, 0x77, 0x66, 0x55] := by
  decide

/-! ## `RUNTIME_FUNCTION` -/

/--
The single entry `ml64` wrote for a seven-byte function.

Every address is zero because they are unresolved relocations; only the
function length survives in the bytes, as `EndAddress`. -/
def measuredFunction : RuntimeFunction := ⟨0, 7, 0⟩

/-- **The twelve bytes, in file order.** -/
theorem measuredFunction_bytes :
    measuredFunction.toBytes =
      [0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00] := by
  decide

/-- The two entries of the two-function object: five bytes then seven. -/
def measuredTwoFunctions : PdataSection := ⟨[⟨0, 5, 0⟩, ⟨0, 7, 8⟩]⟩

/--
**The twenty-four bytes of a two-entry `.pdata`.**

The stride, which one entry cannot show: the second entry starts at byte
twelve. Its `UnwindInfoAddress` is eight rather than zero, because both
functions share one `.xdata` section and the addend is what tells their unwind
blocks apart. -/
theorem measuredTwoFunctions_bytes :
    measuredTwoFunctions.toBytes =
      [0x00, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00]
      := by decide

/--
**Twelve bytes per entry.**

Stated against the measured section rather than in general, because it is the
property a reader relies on to find entry `n`. -/
theorem measuredTwoFunctions_stride :
    measuredTwoFunctions.toBytes.length
      = 12 * measuredTwoFunctions.functions.length := by
  decide

/-! ## A linked table, which an object file cannot be

`SearchablePdata` demands `PdataSection.WellFormed`: consecutive ranges
disjoint, every range nonempty, every entry's unwind data outside the function
it describes. None of that can hold of a measured object, where every address
is an unresolved relocation reading zero -- the ranges are all empty and all
identical.

So this section is synthetic and says so. It is what the same two functions look
like *after* linking, with the addresses a linker would assign, and it is the
only way to exercise the searchability rules at all. The addresses are invented;
the rules they satisfy are not.
-/

/--
Three functions as a linker would lay them out.

`alpha` at 0x1000 for five bytes, `beta` at 0x1010 for seven, a third at
0x1020 -- ascending, disjoint, each with unwind data in `.xdata` at 0x2000 and
beyond, which is outside every function. -/
def linkedFunctions : List RuntimeFunction :=
  [ ⟨0x1000, 0x1005, 0x2000⟩
  , ⟨0x1010, 0x1017, 0x2008⟩
  , ⟨0x1020, 0x1030, 0x2010⟩ ]

/-- **A linked table is searchable.** -/
theorem linkedFunctions_searchable :
    (SearchablePdata.mk? linkedFunctions).isSome := by decide

/--
**Its bytes are twelve per entry, in ascending order.**

`SearchablePdata.toBytes` is the table's bytes and nothing more -- the
searchability is a property of the entries, not an extra field. -/
theorem linkedFunctions_bytes :
    (SearchablePdata.mk? linkedFunctions).map SearchablePdata.toBytes
      = some
        [0x00, 0x10, 0x00, 0x00, 0x05, 0x10, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00,
         0x10, 0x10, 0x00, 0x00, 0x17, 0x10, 0x00, 0x00, 0x08, 0x20, 0x00, 0x00,
         0x20, 0x10, 0x00, 0x00, 0x30, 0x10, 0x00, 0x00, 0x10, 0x20, 0x00, 0x00]
      := by decide

/--
**Overlapping functions are refused.**

The second entry begins before the first ends. A binary search over such a
table can return either, so the unwinder may be handed the wrong function's
prologue -- which is why `Separated` is a precondition rather than a warning. -/
theorem overlapping_refused :
    SearchablePdata.mk?
      [ ⟨0x1000, 0x1010, 0x2000⟩, ⟨0x1008, 0x1018, 0x2008⟩ ] = none := by
  decide

/--
**Descending entries are refused.**

Disjoint but out of order, which a binary search cannot handle either. The two
refusals are different: the one above overlaps, this one does not. -/
theorem descending_refused :
    SearchablePdata.mk?
      [ ⟨0x1010, 0x1017, 0x2008⟩, ⟨0x1000, 0x1005, 0x2000⟩ ] = none := by
  decide

/--
**An entry whose unwind data sits inside its own function is refused.**

`PointsOutside`. Unwind data inside the code it describes would be executed as
instructions, and read as unwind codes by the unwinder -- each interpretation
plausible and at most one right. -/
theorem unwindInsideFunction_refused :
    SearchablePdata.mk? [ ⟨0x1000, 0x1010, 0x1004⟩ ] = none := by decide

/--
**And a measured object's table is refused, which is the point.**

The two entries from the real two-function object have `BeginAddress` and
`EndAddress` both zero, so their ranges are empty and identical. That is not a
defect in the object -- it is what an unlinked file looks like -- and it is
exactly why the searchability rules need a synthetic table to be exercised at
all. -/
theorem measured_object_table_not_searchable :
    SearchablePdata.mk? measuredTwoFunctions.functions = none := by decide

end Grass.Tests.ABI.Win64.Measured
