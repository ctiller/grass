import Grass.ABI.Win64.Unwind
import Grass.ISA.X86.Bytes

/-!
# Win64 unwind metadata, as bytes

`Grass/ABI/Win64/Unwind.lean` models the unwind *language* — which prologues can
be described at all, and how many `UNWIND_CODE` slots each operation needs. It
stops short of bytes. This module writes them: `UNWIND_CODE`, `UNWIND_INFO` and
`RUNTIME_FUNCTION`, which are the contents of `.xdata` and `.pdata`.

## Authority

`docs/DECISIONS.md` 16 fixes the baseline at Win32 x64, and these three
structures are Microsoft's, not Intel's or AMD's. That matters for citation:
`Grass.ISA.X86.DualCitation` is closed over `Vendor` = intel | amd, so there is
no `DualCitation` for a Microsoft structure and none is faked here. No
declaration in this module carries a `Citation`, and the trust ledger's `owed`
bucket is the right place for them until a Microsoft `SourceDocument` is
registered.

What this module has instead is stronger than a citation and weaker than a
proof: some of the layouts are confirmed against bytes emitted by Microsoft's
own toolchain. `Tools/win64-unwind-differential.py` assembles MASM `PROC FRAME`
prologues with `ml64.exe`, reads the `.xdata` section straight out of the COFF
object, and compares it byte for byte against `UnwindInfo.toBytes`.

An earlier version of this paragraph described a different tool -- one that
compiled C with `cl.exe`, extracted `.pdata` as well, and decoded each
`UNWIND_INFO` to re-encode it. No such tool has ever existed here; `cl.exe` was
used once by hand while working out the field orders, and the paragraph
described that session rather than the check. A reviewer caught it.

The distinction matters because it changes what is covered. `UNWIND_INFO` for
all nine operations this profile models is covered by that differential, on 100
prologues, and every row of it uses `.noHandler`.

The handler tail and the `.pdata` records are covered a different way, in
`Tests/ABI/Win64/UnwindMeasured.lean`: recorded measurements rather than a
re-run. `UnwindTail.flags`, `UnwindTail.handlerRva`, `UnwindTail.toBytes`,
`RuntimeFunction.toBytes` and `PdataSection.toBytes` are checked there against
bytes `ml64` actually wrote, by evaluation, with no assembler involved.

That shape was chosen because it survives. Handler rows lived in the corpus
briefly and were deleted with the differential that read them, since that tool
belongs to another owner and runs only on Windows; the measurements outlived
both. It is the right shape here for a second reason too -- these records do
not move, so a recorded measurement catches what a re-run would. It is *not*
the right shape for the encoder differentials, where the corpus is generated
and the point is to re-run a moving corpus against a live assembler.

`SearchablePdata` is covered in the same file, but only synthetically, and the
distinction is worth keeping. It demands `PdataSection.WellFormed` -- disjoint,
nonempty, ascending ranges with unwind data outside each function -- and none of
that can hold of a measured object, where every address is an unresolved
relocation reading zero, so the ranges are all empty and all identical. A
theorem there states exactly that: the real object's table is refused. The
searchability rules are therefore exercised against a table with the addresses a
linker would assign, which is invented; what those addresses satisfy is not.

## What ml64 was measured to do, and why none of it is checked here

Handler tails and `.pdata` were briefly covered by seven added rows and a
relocation check. That work was deleted, because the differential that ran it
lives under `Tools/`, which `c-agent` owns and `c-x86` does not, and a corpus
whose checker belongs to another owner is a two-agent handshake on every column.
The measurements survive the deletion; they are recorded here because they were
expensive to obtain and are what a rebuilt checker should start from.

`ml64` will emit exactly one tail, and it is `.bothHandlers 0 [0]`.
`PROC FRAME:handler` sets *both* handler bits -- the first byte is `0x19`, so
`Flags` reads 3 -- rather than `UNW_FLAG_EHANDLER` alone, and there is no MASM
syntax for a termination-only handler. `.handlerdata`, which would supply
language-specific data, is not a directive this assembler build knows: it is
refused with the same `A2008 syntax error : .` as an invented directive, on a
line where `.pushreg` and `.savereg` assemble. So `.exceptionHandler`,
`.terminationHandler` and `.chained` have no oracle in this assembler at all,
and the language-specific data is always one dword and always zero.

The handler address sits after the code array *once that array is padded to an
even slot count*. Measured: one and two codes put it at byte 8, three and four
at byte 12. A model that forgot the padding agrees with `ml64` on the even
cases and disagrees on the odd ones, which is why a rebuilt corpus should vary
`CountOfCodes` rather than which register is pushed.

`.pdata` for one function is exactly twelve bytes carrying exactly three
`ADDR32NB` relocations, at offsets 0, 4 and 8 -- the field order and the stride.
The `BeginAddress` addend is zero and the `EndAddress` addend equals the size of
`.text`, which is where the check has teeth, since that size is a fact about the
object rather than anything a corpus predicted.

## Why bytes alone cannot check any of it

This is the part most easily lost, and it is the reason the deleted checker read
relocations rather than section contents. In an object file every address is an
unresolved relocation, so the handler field, the language-specific dword, the
padding and all three `RUNTIME_FUNCTION` fields read as zero. A model that
omitted the handler entirely, or emitted the three `.pdata` fields in any order,
produces bytes identical to one that placed them correctly. Comparing those
bytes establishes nothing. The relocation directory is what distinguishes them,
and it needs no linker.

What genuinely does need a linked image is `PdataSection.Separated` and the
ascending order `WellFormed` requires, because those are facts about several
entries laid out together and each object here holds one function.

The estimate in this section was wrong twice before it was measured -- first
"no oracle at all", then "field order only" -- both times because a zero was
read as an absence rather than as an unresolved reference.

Every field order below was read off `ml64` output rather than inferred,
including the two that a reader of the C struct declarations would most likely
get backwards:

* `Version : 3` then `Flags : 5` in one byte means version occupies bits 2:0 and
  flags bits 7:3, because MSVC packs the first-declared bitfield into the low
  bits. A real leaf-free function compiled at `/O2` starts its `.xdata` with
  `01`, which is version 1 and no flags -- not `08`.
* `FrameRegister : 4` then `FrameOffset : 4` likewise puts the register in bits
  3:0.

`UnwindCode.codeOffset` is the offset of the byte *after* the instruction, not
of its first byte. The same function settles it: `sub rsp, 520` assembles to
seven bytes at prologue offset 0, and its `UNWIND_CODE` carries `CodeOffset = 7`
with `SizeOfProlog = 7`.

## Custody note

`le32` and `le16` come from `Grass.ISA.X86.Bytes`. Little-endian byte order is a
property of the machine rather than of instruction encoding, so they would sit
better in `Grass.Std.Logical`; that module is not in this agent's trees, so the
import stands and the misplacement is recorded here rather than worked around.
-/

namespace Grass.ABI.Win64

open Grass.Core Grass.Std.Logical Grass.ISA.X86

/-! ## Strictly increasing byte sequences

Two of the well-formedness conditions below are "these numbers ascend", over
different widths. Stated once, as a `Bool` recursion so that `Decidable` needs
no instance of its own.
-/

/-- Whether a list of bit vectors strictly ascends, unsigned. -/
def ascends {n : Nat} : List (BitVec n) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a.ult b && ascends (b :: rest)

/-- A list of bit vectors strictly ascends, unsigned. -/
def Ascends {n : Nat} (l : List (BitVec n)) : Prop := ascends l = true

instance {n : Nat} (l : List (BitVec n)) : Decidable (Ascends l) :=
  inferInstanceAs (Decidable (_ = true))

/-- The empty sequence ascends, and so does a one-element sequence. -/
@[simp] theorem ascends_nil {n : Nat} : ascends ([] : List (BitVec n)) = true := rfl

@[simp] theorem ascends_singleton {n : Nat} (a : BitVec n) :
    ascends [a] = true := rfl

/-- Ascending is inherited by the tail, which is what makes it usable as an
invariant while walking a list. -/
theorem Ascends.tail {n : Nat} {a : BitVec n} {l : List (BitVec n)}
    (h : Ascends (a :: l)) : Ascends l := by
  match l with
  | [] => exact ascends_nil
  | b :: rest =>
      simp only [Ascends, ascends, Bool.and_eq_true] at h
      exact h.2

/-! ## `UNWIND_CODE` -/

/--
One unwind operation together with the prologue offset it is recorded at.

`codeOffset` is the offset of the first byte *past* the instruction that performs
the operation, not the offset of the instruction. Getting this backwards
produces metadata that unwinds from one instruction too early, which is only
observable when an exception arrives inside the prologue.
-/
structure PlacedOp where
  /-- The operation. -/
  op : UnwindOp
  /-- Prologue offset of the byte after the instruction performing it. -/
  codeOffset : Byte
deriving DecidableEq, Repr, Inhabited

namespace PlacedOp

/--
The slots this operation occupies, as bytes.

The first slot is always `CodeOffset` then the packed `UnwindOp`/`OpInfo` byte.
`allocLarge` with `OpInfo = 0` follows it with the size scaled by eight, as a
little-endian 16-bit value in the next slot. `saveNonvolatile` follows it with
its offset scaled by eight the same way, and `saveXmm128` with its offset scaled
by *sixteen* -- the divisor differs because the saved value is sixteen bytes
wide, and getting it wrong would place a restore at four times the intended
displacement.
-/
def toBytes : PlacedOp → ByteSeq
  | ⟨.allocLarge n, off⟩ =>
      [off, (UnwindOp.allocLarge n).opInfo ++ (UnwindOp.allocLarge n).opcode] ++
        (if n ≤ UnwindOp.largeAllocScaledMax then
          le16 (BitVec.ofNat 16 (n / 8))
        else
          le32 (BitVec.ofNat 32 n))
  | ⟨.saveNonvolatile r n, off⟩ =>
      [off, (UnwindOp.saveNonvolatile r n).opInfo ++
        (UnwindOp.saveNonvolatile r n).opcode] ++ le16 (BitVec.ofNat 16 (n / 8))
  | ⟨.saveXmm128 r n, off⟩ =>
      [off, (UnwindOp.saveXmm128 r n).opInfo ++
        (UnwindOp.saveXmm128 r n).opcode] ++ le16 (BitVec.ofNat 16 (n / 16))
  | ⟨.saveNonvolatileFar r n, off⟩ =>
      [off, (UnwindOp.saveNonvolatileFar r n).opInfo ++
        (UnwindOp.saveNonvolatileFar r n).opcode] ++ le32 (BitVec.ofNat 32 n)
  | ⟨.saveXmm128Far r n, off⟩ =>
      [off, (UnwindOp.saveXmm128Far r n).opInfo ++
        (UnwindOp.saveXmm128Far r n).opcode] ++ le32 (BitVec.ofNat 32 n)
  | ⟨op, off⟩ => [off, op.opInfo ++ op.opcode]

/--
Each operation writes exactly two bytes per slot it claims.

This is the agreement that `UNWIND_INFO.CountOfCodes` depends on. The header
reports slots; if `toBytes` and `UnwindOp.slots` ever disagreed, the header
would describe an array of a different length than the one written, and the
unwinder would read whatever follows `.xdata` as unwind codes.
-/
@[simp] theorem length_toBytes (p : PlacedOp) : p.toBytes.length = 2 * p.op.slots := by
  match p with
  | ⟨.allocLarge n, _⟩ =>
      by_cases h : n ≤ UnwindOp.largeAllocScaledMax <;>
        simp [toBytes, UnwindOp.slots, le16, le32, h]
  | ⟨.pushNonvolatile _, _⟩ => simp [toBytes, UnwindOp.slots]
  | ⟨.allocSmall _, _⟩ => simp [toBytes, UnwindOp.slots]
  | ⟨.setFramePointer _ _, _⟩ => simp [toBytes, UnwindOp.slots]
  | ⟨.saveNonvolatile _ _, _⟩ => simp [toBytes, UnwindOp.slots, le16]
  | ⟨.saveXmm128 _ _, _⟩ => simp [toBytes, UnwindOp.slots, le16]
  | ⟨.saveNonvolatileFar _ _, _⟩ =>
      simp [toBytes, UnwindOp.slots, le32]
  | ⟨.saveXmm128Far _ _, _⟩ => simp [toBytes, UnwindOp.slots, le32]
  | ⟨.pushMachineFrame _, _⟩ => simp [toBytes, UnwindOp.slots]

/-- The code offset is placed where the unwinder can act on it.

Every operation but one describes an instruction, and its unwind code takes
effect at the address *after* that instruction; an offset of zero would make the
code apply before the instruction had run, which is
`zero_codeOffset_not_wellFormed`.

`pushMachineFrame` is the exception and its offset must be zero. It describes
what the processor pushed before the function's first instruction, so there is
no preceding instruction for it to sit after -- `ml64` writes `00 0A`, and a
positive offset would claim the trap frame appeared partway through a prologue
that had already started running.

Stated per operation rather than as a blanket rule on offsets, because the two
cases are opposite and a single bound cannot express both. This cost five
corpus rows that vanished silently before it was noticed: `rowOf` returns an
`Option`, and a machine-frame row simply failed to build. -/
def OffsetPlaced (p : PlacedOp) : Prop :=
  match p.op with
  | .pushMachineFrame _ => p.codeOffset.toNat = 0
  | _ => 0 < p.codeOffset.toNat

instance (p : PlacedOp) : Decidable p.OffsetPlaced := by
  unfold OffsetPlaced
  split <;> infer_instance

/-- The first byte written is the code offset. -/
theorem toBytes_head (p : PlacedOp) : p.toBytes.head? = some p.codeOffset := by
  match p with
  | ⟨.allocLarge n, _⟩ =>
      by_cases h : n ≤ UnwindOp.largeAllocScaledMax <;>
        simp [toBytes, le16, le32, h]
  | ⟨.pushNonvolatile _, _⟩ => rfl
  | ⟨.allocSmall _, _⟩ => rfl
  | ⟨.setFramePointer _ _, _⟩ => rfl
  | ⟨.saveNonvolatile _ _, _⟩ => rfl
  | ⟨.saveXmm128 _ _, _⟩ => rfl
  | ⟨.saveNonvolatileFar _ _, _⟩ => rfl
  | ⟨.saveXmm128Far _ _, _⟩ => rfl
  | ⟨.pushMachineFrame _, _⟩ => rfl

end PlacedOp

/-! ## The placed prologue -/

/--
A prologue with each operation's offset, plus the total prologue size.

`Grass.ABI.Win64.Prologue` is the vocabulary check; this adds the positions,
which is everything the byte layout needs and the vocabulary does not have.
-/
structure Layout where
  /-- Operations in execution order, each with its offset. -/
  placed : List PlacedOp
  /-- `SizeOfProlog`: the length in bytes of the whole prologue. -/
  sizeOfProlog : Byte
deriving DecidableEq, Repr, Inhabited

namespace Layout

/-- The underlying vocabulary-level prologue. -/
def prologue (l : Layout) : Prologue := ⟨l.placed.map PlacedOp.op⟩

/-- The offsets, in execution order. -/
def offsets (l : Layout) : List Byte := l.placed.map PlacedOp.codeOffset

/--
A layout the unwinder will read correctly.

Three conditions, each of which a plausible generator gets wrong:

* every operation is in the unwind language (`Prologue.Encodable`);
* the offsets strictly ascend in execution order, since two operations cannot
  complete at the same byte and the array is a reversal of this order;
* no offset exceeds `SizeOfProlog`, because an offset past the prologue
  describes an instruction the unwinder will never be executing inside;
* no offset is zero. `RtlVirtualUnwind` skips a code while
  `PrologOffset < CodeOffset`, so a code at offset 0 is applied at the
  function's very first byte -- popping a register that has not been pushed
  yet. No real prologue produces one, because the first instruction ends at 1
  or later, and every offset in every `ml64` and `cl.exe` dump taken while
  building this module is at least 1. A reviewer noticed this is *not* inside
  the open obligation below: it needs no instruction encoder, only the
  observation that offsets count bytes already executed.

## The offsets, checked against instructions

These three conditions are internal. Nothing *here* relates `codeOffset` or
`SizeOfProlog` to the bytes an assembler would emit, so a layout claiming three
two-byte pushes end at 1, 2 and 3, or one claiming `SizeOfProlog = 255` for a
ten-byte prologue, satisfies `WellFormed`. Both mis-unwind: the second has
Windows treat every address below 255 as mid-prologue and restore nothing.

This was recorded as an open obligation, on the grounds that there was no
encoder for `push` or `sub rsp` to compare against. There is now:
`Grass.ISA.X86.pushR64` and `Grass.ISA.X86.subR64Imm8`/`subR64Imm32`, checked
byte-for-byte against the vendor encodings in
`Tests/ISA/X86/PrologueInsns.lean`. `Layout.Realizes` below is the recogniser,
and `Tests/ABI/Win64/PrologueRealization.lean` refutes both layouts above.

Three things are still true and worth stating plainly.

First, `Realizes` covers three of the nine operations -- the two allocation
forms and a nonvolatile push. The rest have no unambiguous instruction,
`UnwindOp.prologueInsns` returns `none` for them, and `Realizes` refuses rather
than guesses. A layout using `setFramePointer` is no better checked than
before.

Second, `WellFormed` does not require `Realizes`, and should not. `Realizes`
assumes the prologue is exactly its unwind-relevant instructions laid
contiguously from the function's first byte; a prologue that also moves an
argument into a saved register is well-formed and not realizable. The two are
separate predicates and a caller who wants both must ask for both.

Third, `Tests/ABI/Win64/UnwindCorpus.lean` still closes a different and
stronger thing for the prologues it builds: its offsets come from a length
model that `ml64` itself checks, so it is answerable to an assembler rather
than to this library's encoder. `Realizes` closes the case that corpus cannot
reach -- a `Layout` a caller writes directly -- and does not replace it.

What `docs/PLATFORM_ABI.md` section 3 asks for is the general recogniser over
all nine operations. That remains owed.
-/
def WellFormed (l : Layout) : Prop :=
  l.prologue.Encodable ∧ Ascends l.offsets ∧
    (∀ o ∈ l.offsets, o ≤ l.sizeOfProlog) ∧
    ∀ p ∈ l.placed, PlacedOp.OffsetPlaced p

instance (l : Layout) : Decidable l.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
A code offset of zero is refused for an operation describing an instruction.

The reviewer's case, kept as a theorem. The layout is internally consistent --
the offsets ascend and stay inside the prologue -- and it describes a `push`
whose unwind code applies before the `push` has run.

`UWOP_PUSH_MACHFRAME` is the exception, and `PlacedOp.OffsetPlaced` is where
that lives. See its docstring: the rule is about instructions, and a machine
frame is not one.
-/
theorem zero_codeOffset_not_wellFormed :
    ¬ (Layout.mk [⟨.pushNonvolatile .rbx, 0⟩, ⟨.allocSmall 32, 4⟩] 4).WellFormed := by
  decide

/-- A machine frame at a nonzero offset is refused, the mirror of
`zero_codeOffset_not_wellFormed`. The two together are why the rule is stated
per operation: neither bound alone admits both. -/
theorem machineFrame_nonzero_not_wellFormed :
    ¬ (Layout.mk [⟨.pushMachineFrame false, 4⟩] 4).WellFormed := by
  decide

/--
The `UNWIND_CODE` array, in the descending order `.xdata` stores it.

`Prologue.codes` reverses execution order for the same reason; this reverses the
placed list so the offsets descend too.
-/
def codeBytes (l : Layout) : ByteSeq :=
  (l.placed.reverse.map PlacedOp.toBytes).flatten

/--
The padding slot, present exactly when the slot count is odd.

Two zero bytes, so that whatever follows the code array stays 4-byte aligned.
The padding is *not* counted by `CountOfCodes` -- `Prologue.countOfCodes` reports
the unpadded slot count, and `Prologue.arraySlots` is the physical length that
includes this. `ml64` settled which of the two the header carries; see
`Prologue.countOfCodes`.
-/
def padding (l : Layout) : ByteSeq :=
  if l.prologue.slots % 2 = 1 then [0, 0] else []

/-- Flattening a list of placed operations writes two bytes per slot. -/
private theorem length_flatten_toBytes (ps : List PlacedOp) :
    ((ps.map PlacedOp.toBytes).flatten).length
      = 2 * ((ps.map PlacedOp.op).map UnwindOp.slots).sum := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append,
        PlacedOp.length_toBytes, ih, List.sum_cons]
      omega

/-- The code array is two bytes per slot, in either order. -/
@[simp] theorem length_codeBytes (l : Layout) :
    l.codeBytes.length = 2 * l.prologue.slots := by
  rw [codeBytes, length_flatten_toBytes]
  simp only [prologue, Prologue.slots, List.map_reverse, List.sum_reverse]

/--
**The array's physical length is exactly the slots the operations claim, rounded
up for alignment.**

Two bytes per slot, and `Prologue.arraySlots` is the slot count including the
padding entry.

Note this is `arraySlots`, not `countOfCodes`. The header reports the smaller
number and the section holds the larger; conflating the two is the bug `ml64`
caught here. `length_codeBytes_append_padding_ge` is the direction that keeps
the unwinder in bounds.
-/
theorem length_codeBytes_append_padding (l : Layout) :
    (l.codeBytes ++ l.padding).length = 2 * l.prologue.arraySlots := by
  have hmod : l.prologue.slots % 2 = 0 ∨ l.prologue.slots % 2 = 1 :=
    Nat.mod_two_eq_zero_or_one _
  simp only [List.length_append, length_codeBytes, padding, Prologue.arraySlots]
  rcases hmod with h | h <;> simp [h] <;> omega

/--
**The bytes written never fall short of what `CountOfCodes` promises.**

The unwinder walks `CountOfCodes` slots whatever was actually written, so this
is the direction that matters: an array shorter than its own header has the
unwinder reading past `.xdata`. A generator counting operations rather than
slots breaks exactly this.
-/
theorem length_codeBytes_append_padding_ge (l : Layout) :
    2 * l.prologue.countOfCodes ≤ (l.codeBytes ++ l.padding).length := by
  rw [length_codeBytes_append_padding]
  have := l.prologue.arraySlots_ge_countOfCodes
  omega

/-- The code array and its padding together are a multiple of four bytes long,
which is what keeps a following handler RVA aligned. -/
theorem codeBytes_padding_aligned (l : Layout) :
    (l.codeBytes ++ l.padding).length % 4 = 0 := by
  rw [length_codeBytes_append_padding]
  have := l.prologue.arraySlots_even
  omega

end Layout

/-! ## What follows the code array -/

/--
The data after the `UNWIND_CODE` array, and the flags that announce it.

One constructor per legal shape, each carrying its own payload. This is the
point of the type: `UNW_FLAG_EHANDLER` without a handler address, or
`UNW_FLAG_CHAININFO` set alongside a handler, are not values of this type. The
flags are derived by `flags` rather than stored, so a flag word cannot
contradict the data that follows it.

Chained info and a handler are mutually exclusive in the ABI, and making them
separate constructors is what enforces it; `chained_has_no_handler` states the
consequence.
-/
inductive UnwindTail where
  /-- No flags: nothing follows the code array. -/
  | noHandler
  /-- `UNW_FLAG_EHANDLER` (1): an exception handler, then its language-specific
  data. -/
  | exceptionHandler (handler : BitVec 32) (langData : List (BitVec 32))
  /-- `UNW_FLAG_UHANDLER` (2): a termination handler, then its data. -/
  | terminationHandler (handler : BitVec 32) (langData : List (BitVec 32))
  /-- Both handler flags (3), which share one routine and one data block. -/
  | bothHandlers (handler : BitVec 32) (langData : List (BitVec 32))
  /-- `UNW_FLAG_CHAININFO` (4): a `RUNTIME_FUNCTION` for the primary function.
  Never combined with a handler. -/
  | chained (begin_ end_ unwindInfo : BitVec 32)
deriving DecidableEq, Repr, Inhabited

namespace UnwindTail

/-- The `Flags` field, five bits. -/
def flags : UnwindTail → BitVec 5
  | .noHandler => 0
  | .exceptionHandler _ _ => 1
  | .terminationHandler _ _ => 2
  | .bothHandlers _ _ => 3
  | .chained _ _ _ => 4

/-- The handler address, when there is one. -/
def handlerRva : UnwindTail → Option (BitVec 32)
  | .noHandler => none
  | .exceptionHandler h _ => some h
  | .terminationHandler h _ => some h
  | .bothHandlers h _ => some h
  | .chained _ _ _ => none

/-- The bytes following the code array. -/
def toBytes : UnwindTail → ByteSeq
  | .noHandler => []
  | .exceptionHandler h d => le32 h ++ (d.map le32).flatten
  | .terminationHandler h d => le32 h ++ (d.map le32).flatten
  | .bothHandlers h d => le32 h ++ (d.map le32).flatten
  | .chained b e u => le32 b ++ le32 e ++ le32 u

/--
**A handler flag is set exactly when a handler address is present.**

The two are read off the same constructor, so there is no value of this type
where the flags promise a handler the bytes do not supply, or vice versa. Bit 0
is `UNW_FLAG_EHANDLER` and bit 1 is `UNW_FLAG_UHANDLER`.
-/
theorem handler_flag_iff_handler (t : UnwindTail) :
    (t.flags.getLsbD 0 = true ∨ t.flags.getLsbD 1 = true) ↔ t.handlerRva.isSome := by
  cases t <;> simp [flags, handlerRva]

/--
**Chained info never carries a handler.**

Bit 2 is `UNW_FLAG_CHAININFO`. An `UNWIND_INFO` that set it together with a
handler flag would have the unwinder read a `RUNTIME_FUNCTION` as a handler
address; that combination has no constructor here.
-/
theorem chained_has_no_handler (t : UnwindTail) (h : t.flags.getLsbD 2 = true) :
    t.flags.getLsbD 0 = false ∧ t.flags.getLsbD 1 = false ∧ t.handlerRva = none := by
  cases t <;> simp_all [flags, handlerRva]

/-- Everything after the code array is a whole number of 32-bit values, each
written by `le32`, so `UnwindTail.toBytes` cannot break the 4-byte alignment the
padding slot establishes. `UnwindInfo.length_toBytes_aligned` rests on this. -/
theorem length_toBytes_aligned (t : UnwindTail) : t.toBytes.length % 4 = 0 := by
  have hd : ∀ d : List (BitVec 32), ((d.map le32).flatten).length = 4 * d.length := by
    intro d
    induction d with
    | nil => simp
    | cons a rest ih =>
        simp only [List.map_cons, List.flatten_cons, List.length_append, ih, le32,
          List.length_cons, List.length_nil]
        omega
  cases t <;> simp [toBytes, le32, hd] <;> omega

/-- The default tail is the one that promises nothing. `Inhabited` picks the
first constructor, and `noHandler` is deliberately first so that a defaulted
`UnwindTail` cannot claim a handler that does not exist. -/
theorem default_eq_noHandler : (default : UnwindTail) = .noHandler := rfl

end UnwindTail

/-! ## `UNWIND_INFO` -/

/-- The `FrameRegister` and `FrameOffset` nibbles.

`reg = 0` means the function has no frame pointer. Register 0 is `RAX`, so a
frame pointer in `RAX` is not expressible -- an ABI quirk, not an omission
here; `framePointer_not_rax` derives it.

Both nibbles are pinned to the prologue by `UnwindInfo.framePointerAgrees`.
`offset` was unconstrained until a reviewer built an `UnwindInfo` declaring a
240-byte frame offset for a frame established at `RSP + 0`. -/
structure FrameSpec where
  /-- `FrameRegister`: a four-bit register number, 0 for none. -/
  reg : BitVec 4
  /-- `FrameOffset`: the offset from `RSP`, scaled by 16. -/
  offset : BitVec 4
deriving DecidableEq, Repr, Inhabited

/-- Whether a frame pointer is declared. -/
def FrameSpec.declared (f : FrameSpec) : Prop := f.reg ≠ 0

instance (f : FrameSpec) : Decidable f.declared :=
  inferInstanceAs (Decidable (_ ≠ _))

/--
An `UNWIND_INFO` that the Windows unwinder will read as intended.

The proof fields are the point. Each rules out a state that is
representable in the C struct, produces no error from any tool, and unwinds
wrongly:

* `layoutWellFormed` -- the offsets ascend and stay inside the prologue.
* `framePointerAgrees` -- *every* `UWOP_SET_FPREG` in the prologue matches
  both of the header's frame nibbles, register and offset. Quantified over the
  operations rather than checked against the first one, because a prologue
  holding two of them that disagree would otherwise match the header on one and
  diverge on the other.
* `framePointerDeclared` -- a nonzero `FrameRegister` and the presence of
  `UWOP_SET_FPREG` imply each other. The operation without the field leaves the
  unwinder computing the frame from `RSP` after the prologue moved it; the field
  without the operation points it at a register that was never established.
  Neither is detectable from the bytes alone, which is why both are hypotheses
  here rather than checks later.
* `noFrameOffsetWithoutFrame` -- with no frame pointer, `FrameOffset` is zero
  rather than arbitrary. The field is meaningless in that case, so nothing reads
  it; writing garbage there simply differs from what `ml64` emits.
* `countFits` -- `CountOfCodes` is one byte. A prologue needing 256 or more
  slots cannot be described, and truncating the count is the failure mode, so
  the field `countFits` is what a caller must discharge instead.

Two of them together have a consequence `framePointer_not_rax` derives rather
than states: `RAX` cannot be a frame register, because its register number is 0
and 0 is how `FrameRegister` spells "none".

`Version` is not a field: it is fixed at 1 by `toBytes`, since version 2
`UNWIND_INFO` has epilogue codes this module does not write.
-/
structure UnwindInfo where
  /-- The placed prologue. -/
  layout : Layout
  /-- The frame-pointer nibbles. -/
  frame : FrameSpec
  /-- What follows the code array. -/
  tail : UnwindTail
  /-- The layout is one the unwinder will read correctly. -/
  layoutWellFormed : layout.WellFormed
  /-- Every establishing operation matches both of the header's frame nibbles. -/
  framePointerAgrees :
    layout.prologue.frameSpecIs frame.reg frame.offset = true
  /-- A frame register is declared exactly when the prologue establishes one. -/
  framePointerDeclared :
    frame.declared ↔ layout.prologue.establishesFramePointer = true
  /-- With no frame pointer, `FrameOffset` is zero rather than arbitrary. -/
  noFrameOffsetWithoutFrame :
    layout.prologue.establishesFramePointer = false → frame.offset = 0#4
  /-- The slot count fits the one byte that reports it. -/
  countFits : layout.prologue.countOfCodes < 256

namespace UnwindInfo

/--
Build an `UNWIND_INFO`, or refuse.

The proof fields rule out metadata the unwinder would misread, which is only useful
if well-formed metadata can still be built without writing proofs by hand. All
conditions are decidable, so this discharges them and returns `none` when
they fail -- the same shape as the encoders in `Grass.ISA.X86.Bytes`, where
refusal is the answer for an operand the encoding cannot express.

`none` is a rejection, not an error to route around. A caller that wants
metadata for a prologue this returns `none` for has to change the prologue.
-/
def mk? (l : Layout) (f : FrameSpec) (t : UnwindTail) : Option UnwindInfo :=
  if hl : l.WellFormed then
    if ha : l.prologue.frameSpecIs f.reg f.offset = true then
      if hf : f.declared ↔ l.prologue.establishesFramePointer = true then
        if hz : l.prologue.establishesFramePointer = false → f.offset = 0#4 then
          if hc : l.prologue.countOfCodes < 256 then
            some { layout := l, frame := f, tail := t
                   layoutWellFormed := hl, framePointerAgrees := ha
                   framePointerDeclared := hf, noFrameOffsetWithoutFrame := hz
                   countFits := hc }
          else none
        else none
      else none
    else none
  else none

/-- `mk?` succeeds exactly when every condition holds, so a `none` is
informative rather than a signal that something else went wrong. -/
theorem mk?_isSome_iff (l : Layout) (f : FrameSpec) (t : UnwindTail) :
    (mk? l f t).isSome ↔
      l.WellFormed ∧ l.prologue.frameSpecIs f.reg f.offset = true ∧
        (f.declared ↔ l.prologue.establishesFramePointer = true) ∧
          (l.prologue.establishesFramePointer = false → f.offset = 0#4) ∧
            l.prologue.countOfCodes < 256 := by
  unfold mk?
  by_cases hl : l.WellFormed
  case neg => rw [dif_neg hl]; simp [hl]
  case pos =>
    rw [dif_pos hl]
    by_cases ha : l.prologue.frameSpecIs f.reg f.offset = true
    case neg => rw [dif_neg ha]; simp [ha]
    case pos =>
      rw [dif_pos ha]
      by_cases hf : f.declared ↔ l.prologue.establishesFramePointer = true
      case neg => rw [dif_neg hf]; simp [hf]
      case pos =>
        rw [dif_pos hf]
        by_cases hz : l.prologue.establishesFramePointer = false → f.offset = 0#4
        case neg => rw [dif_neg hz]; simp [hz]
        case pos =>
          rw [dif_pos hz]
          by_cases hc : l.prologue.countOfCodes < 256
          case neg => rw [dif_neg hc]; simp [hc]
          case pos =>
            rw [dif_pos hc]
            simp only [Option.isSome_some, true_iff]
            exact ⟨hl, ha, hf, hz, hc⟩

/-- `mk?` keeps what it was given, so the bytes it produces describe the layout
the caller asked about and not some adjusted version of it. -/
theorem mk?_eq_some {l : Layout} {f : FrameSpec} {t : UnwindTail} {u : UnwindInfo}
    (h : mk? l f t = some u) : u.layout = l ∧ u.frame = f ∧ u.tail = t := by
  unfold mk? at h
  by_cases hl : l.WellFormed
  case neg => rw [dif_neg hl] at h; exact absurd h (by simp)
  case pos =>
    rw [dif_pos hl] at h
    by_cases ha : l.prologue.frameSpecIs f.reg f.offset = true
    case neg => rw [dif_neg ha] at h; exact absurd h (by simp)
    case pos =>
      rw [dif_pos ha] at h
      by_cases hf : f.declared ↔ l.prologue.establishesFramePointer = true
      case neg => rw [dif_neg hf] at h; exact absurd h (by simp)
      case pos =>
        rw [dif_pos hf] at h
        by_cases hz : l.prologue.establishesFramePointer = false → f.offset = 0#4
        case neg => rw [dif_neg hz] at h; exact absurd h (by simp)
        case pos =>
          rw [dif_pos hz] at h
          by_cases hc : l.prologue.countOfCodes < 256
          case neg => rw [dif_neg hc] at h; exact absurd h (by simp)
          case pos =>
            rw [dif_pos hc] at h
            obtain rfl := Option.some.inj h
            exact ⟨rfl, rfl, rfl⟩

/-- The `Version` field. Fixed: this module writes version 1 only. -/
def version : BitVec 3 := 1

/--
The bytes of the `UNWIND_INFO` structure.

Four header bytes, then the code array, then its padding, then the tail. The two
packed bytes put the first-declared bitfield in the low bits, matching what
`cl.exe` emits.
-/
def toBytes (u : UnwindInfo) : ByteSeq :=
  [ u.tail.flags ++ version
  , u.layout.sizeOfProlog
  , BitVec.ofNat 8 u.layout.prologue.countOfCodes
  , u.frame.offset ++ u.frame.reg ]
    ++ u.layout.codeBytes ++ u.layout.padding ++ u.tail.toBytes

/-- The header is four bytes, then two per array slot, then the tail. -/
theorem length_toBytes (u : UnwindInfo) :
    u.toBytes.length = 4 + 2 * u.layout.prologue.arraySlots + u.tail.toBytes.length := by
  have h := u.layout.length_codeBytes_append_padding
  simp only [List.length_append] at h
  simp only [toBytes, List.length_append, List.length_cons, List.length_nil]
  omega

/--
**The structure is always a multiple of four bytes long.**

`.xdata` entries are 4-byte aligned and are packed one after another, so a
length that is not a multiple of four misaligns every entry after it. The
padding slot is what makes this true, and `Prologue.countOfCodes` is what makes
the padding slot appear.
-/
theorem length_toBytes_aligned (u : UnwindInfo) : u.toBytes.length % 4 = 0 := by
  rw [length_toBytes]
  have hc := u.layout.prologue.arraySlots_even
  have ht := u.tail.length_toBytes_aligned
  omega

/--
**`RAX` cannot be a frame register.**

Not a stated rule but a consequence of `framePointerAgrees` and
`framePointerDeclared` together.
`FrameRegister` spells "no frame pointer" as 0, and `RAX`'s register number is
0; `framePointerDeclared` forces the field nonzero whenever the prologue
establishes a frame pointer, and `framePointerAgrees` forces the field to equal
the establishing register's number. So no `UnwindInfo` establishes a frame
pointer in `RAX`.

`RAX` is volatile, so `UnwindOp.Encodable` excludes it independently. Two routes
to the same exclusion, which is why this is worth stating rather than leaving
implicit: if either route were removed the other would still hold.
-/
theorem framePointer_not_rax (u : UnwindInfo) {r : Gpr} {off : Nat}
    (h : UnwindOp.setFramePointer r off ∈ u.layout.prologue.ops) : r ≠ .rax := by
  intro hrax
  subst hrax
  have hagree : u.frame.reg = regNibble .rax :=
    ((Prologue.frameSpecIs_iff _ _ _).mp u.framePointerAgrees _ _ h).1
  have hest : u.layout.prologue.establishesFramePointer = true := by
    simp only [Prologue.establishesFramePointer, List.any_eq_true]
    exact ⟨_, h, rfl⟩
  exact u.framePointerDeclared.mpr hest (hagree.trans (by decide))

/--
**The header's frame offset is the one the prologue establishes.**

The consequence of `framePointerAgrees` that `FrameOffset` previously lacked
entirely: a declared offset must be the establishing operation's, scaled by
sixteen, and not an arbitrary nibble.
-/
theorem frameOffset_agrees (u : UnwindInfo) {r : Gpr} {off : Nat}
    (h : UnwindOp.setFramePointer r off ∈ u.layout.prologue.ops) :
    u.frame.offset = BitVec.ofNat 4 (off / 16) :=
  ((Prologue.frameSpecIs_iff _ _ _).mp u.framePointerAgrees _ _ h).2

/-- The version this module writes. -/
theorem version_eq_one : version = 1 := rfl

/-- The version occupies the low three bits of the first byte. -/
theorem version_byte (u : UnwindInfo) :
    (u.tail.flags ++ version).extractLsb' 0 3 = version := by
  ext i hi
  rw [BitVec.getElem_extractLsb' hi, BitVec.getLsbD_append]
  simp [hi]

/-- The flags occupy the high five bits, and read back unchanged. -/
theorem flags_byte (u : UnwindInfo) :
    (u.tail.flags ++ version).extractLsb' 3 5 = u.tail.flags := by
  ext i hi
  rw [BitVec.getElem_extractLsb' hi, BitVec.getLsbD_append]
  simp [show ¬(3 + i < 3) by omega, hi]

/-- The frame register reads back out of its shared byte unchanged, which is the
half that a reader who assumed C bitfields pack high-first gets wrong. -/
theorem frameRegister_byte (u : UnwindInfo) :
    (u.frame.offset ++ u.frame.reg).extractLsb' 0 4 = u.frame.reg := by
  ext i hi
  rw [BitVec.getElem_extractLsb' hi, BitVec.getLsbD_append]
  simp [hi]

/-- And the frame offset occupies the high nibble. -/
theorem frameOffset_byte (u : UnwindInfo) :
    (u.frame.offset ++ u.frame.reg).extractLsb' 4 4 = u.frame.offset := by
  ext i hi
  rw [BitVec.getElem_extractLsb' hi, BitVec.getLsbD_append]
  simp [show ¬(4 + i < 4) by omega, hi]

end UnwindInfo

/-! ## `RUNTIME_FUNCTION` and `.pdata` -/

/-- One `.pdata` entry: three image-relative addresses. -/
structure RuntimeFunction where
  /-- Start of the function, image-relative. -/
  begin_ : BitVec 32
  /-- One past the end of the function, image-relative. -/
  end_ : BitVec 32
  /-- The function's `UNWIND_INFO`, image-relative. -/
  unwindInfo : BitVec 32
deriving DecidableEq, Repr, Inhabited

namespace RuntimeFunction

/-- Three little-endian 32-bit values. -/
def toBytes (f : RuntimeFunction) : ByteSeq :=
  le32 f.begin_ ++ le32 f.end_ ++ le32 f.unwindInfo

@[simp] theorem length_toBytes (f : RuntimeFunction) : f.toBytes.length = 12 := by
  simp [toBytes, le32]

/-- The entry covers a nonempty range. -/
def Nonempty (f : RuntimeFunction) : Prop := f.begin_.ult f.end_ = true

instance (f : RuntimeFunction) : Decidable f.Nonempty :=
  inferInstanceAs (Decidable (_ = true))

/--
The entry points somewhere an `UNWIND_INFO` could be.

`unwindInfo` was unconstrained, which a reviewer noted is the critique this
module makes of the old `PdataSection.WellFormed` applied one level in: a
condition on the table said nothing about what its entries point at. Both
excluded values are impossible in a real image rather than merely unlikely.

RVA 0 is the DOS header, so no `UNWIND_INFO` is ever there -- and 0 is what an
uninitialised or unrelocated field holds, which is the realistic way to get it.
An RVA inside the function's own range is impossible because `.pdata` and
`.xdata` are sections distinct from `.text`; an entry pointing there would have
the unwinder read instruction bytes as a header.
-/
def PointsOutside (f : RuntimeFunction) : Prop :=
  f.unwindInfo ≠ 0 ∧ ¬ (f.begin_.ule f.unwindInfo = true ∧ f.unwindInfo.ult f.end_ = true)

instance (f : RuntimeFunction) : Decidable f.PointsOutside :=
  inferInstanceAs (Decidable (_ ∧ _))

end RuntimeFunction

/--
The `.pdata` section: the function table.

`RtlLookupFunctionEntry` binary-searches this table, so entry order is not
cosmetic. An unsorted table does not fail loudly; the search simply misses
entries, and the functions it misses unwind as if they were leaves.
-/
structure PdataSection where
  /-- The entries, in the order they appear in the section. -/
  functions : List RuntimeFunction
deriving DecidableEq, Repr, Inhabited

namespace PdataSection

/--
Whether consecutive entries are disjoint: each ends no later than the next
begins.

Ascending start addresses are *necessary* for the binary search but not
sufficient, and the gap is a real failure rather than a technicality. Entries
`[0x00, 0x100)` and `[0x10, 0x20)` have ascending starts. A search for `0x50`
lands on the second, finds `0x50` outside it, and reports nothing -- so the
function covering `0x00..0x100` unwinds as a leaf everywhere above `0x20`.
Requiring `end_ ≤ begin_` between neighbours rules that out, and together with
`RuntimeFunction.Nonempty` it implies the ascending order rather than needing it
separately; `WellFormed.ascends` derives that.

An earlier version of this definition asked only for ascending starts, and
`enclosing_not_wellFormed` is the table it wrongly accepted.
-/
def separated : List RuntimeFunction → Bool
  | [] => true
  | [_] => true
  | f :: g :: rest => f.end_.ule g.begin_ && separated (g :: rest)

/-- Consecutive entries are disjoint. -/
def Separated (l : List RuntimeFunction) : Prop := separated l = true

instance (l : List RuntimeFunction) : Decidable (Separated l) :=
  inferInstanceAs (Decidable (_ = true))

/--
The table is searchable and its entries are sane.

Disjoint consecutive ranges are what the binary search needs; nonempty ranges
rule out the degenerate entry that matches no address at all. Ascending starts
follow rather than being assumed -- see `WellFormed.ascends`.
-/
def WellFormed (s : PdataSection) : Prop :=
  Separated s.functions ∧ (∀ f ∈ s.functions, f.Nonempty) ∧
    ∀ f ∈ s.functions, f.PointsOutside

instance (s : PdataSection) : Decidable s.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- An entry whose unwind information is at RVA 0, or inside the function it
describes, is refused. Both are the reviewer's cases. -/
theorem bad_unwindInfo_refused :
    ¬ (PdataSection.mk
        [{ begin_ := 0x1000, end_ := 0x1020, unwindInfo := 0 }]).WellFormed ∧
      ¬ (PdataSection.mk
        [{ begin_ := 0x1000, end_ := 0x1020, unwindInfo := 0x1008 }]).WellFormed := by
  constructor <;> decide

private theorem ascends_of_separated :
    ∀ l : List RuntimeFunction, Separated l → (∀ f ∈ l, f.Nonempty) →
      Ascends (l.map RuntimeFunction.begin_)
  | [], _, _ => ascends_nil
  | [_], _, _ => ascends_singleton _
  | f :: g :: rest, hsep, hne => by
      simp only [Separated, separated, Bool.and_eq_true] at hsep
      have hfne : f.Nonempty := hne f (by simp)
      have htail := ascends_of_separated (g :: rest) hsep.2
        (fun x hx => hne x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, Ascends, ascends, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · have hfg := hsep.1
        simp only [RuntimeFunction.Nonempty, BitVec.ult, BitVec.ule,
          decide_eq_true_eq] at hfne hfg ⊢
        omega
      · simpa [Ascends, List.map_cons] using htail

/--
**Start addresses ascend.**

The property `RtlLookupFunctionEntry`'s binary search is usually stated in terms
of, here derived from disjointness rather than assumed alongside it. That is the
point: assuming it alone is exactly what let an enclosing entry hide a later
one.
-/
theorem WellFormed.ascends {s : PdataSection} (h : s.WellFormed) :
    Ascends (s.functions.map RuntimeFunction.begin_) :=
  ascends_of_separated s.functions h.1 h.2.1

/-- The section bytes. -/
def toBytes (s : PdataSection) : ByteSeq :=
  (s.functions.map RuntimeFunction.toBytes).flatten

/-- Twelve bytes per entry. -/
@[simp] theorem length_toBytes (s : PdataSection) :
    s.toBytes.length = 12 * s.functions.length := by
  simp only [toBytes]
  induction s.functions with
  | nil => simp
  | cons f rest ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append,
        RuntimeFunction.length_toBytes, ih, List.length_cons]
      omega

/-- Dropping the first entry leaves a well-formed table, so the search
invariant survives the recursion the search performs. -/
theorem WellFormed.tail {f : RuntimeFunction} {rest : List RuntimeFunction}
    (h : (PdataSection.mk (f :: rest)).WellFormed) :
    (PdataSection.mk rest).WellFormed := by
  obtain ⟨hsep, hne, hpt⟩ := h
  refine ⟨?_, fun g hg => hne g (List.mem_cons_of_mem _ hg),
    fun g hg => hpt g (List.mem_cons_of_mem _ hg)⟩
  match rest with
  | [] => exact rfl
  | g :: more =>
      simp only [Separated, separated, Bool.and_eq_true] at hsep
      exact hsep.2

/--
An entry enclosing a later one is rejected.

Kept as a theorem rather than a comment because it is the table the previous
definition accepted. Both entries begin in ascending order; the second lies
entirely inside the first, and every address in `0x20..0x100` is unreachable for
a search that has already passed the second entry's start.
-/
theorem enclosing_not_wellFormed :
    ¬ (PdataSection.mk
        [ { begin_ := 0x00, end_ := 0x100, unwindInfo := 0x1000 }
        , { begin_ := 0x10, end_ := 0x020, unwindInfo := 0x1010 } ]).WellFormed := by
  decide

/-- The same two functions laid out without overlap are accepted, so the
rejection above is about the enclosure and not about the addresses. -/
theorem adjacent_wellFormed :
    (PdataSection.mk
      [ { begin_ := 0x00, end_ := 0x100, unwindInfo := 0x1000 }
      , { begin_ := 0x100, end_ := 0x120, unwindInfo := 0x1010 } ]).WellFormed := by
  decide

/-- A descending table is rejected, which is the weaker condition the previous
definition did check. -/
theorem descending_not_wellFormed :
    ¬ (PdataSection.mk
        [ { begin_ := 0x100, end_ := 0x120, unwindInfo := 0x1000 }
        , { begin_ := 0x000, end_ := 0x010, unwindInfo := 0x1010 } ]).WellFormed := by
  decide

end PdataSection

/--
A `.pdata` section carrying the proof that the runtime can search it.

`PdataSection.WellFormed` was a predicate nobody had to satisfy:
`PdataSection.toBytes` serialises any list of entries, so a table that is
descending, overlapping or degenerate produces bytes exactly as readily as a
good one. A reviewer made the point that a condition stated where the bytes are
*not* produced constrains nothing.

This is the same shape as `UnwindInfo`: the obligation is a field, so the value
cannot exist without it, and `mk?` discharges it for a caller who has a concrete
list. `toBytes` here delegates to the section's, so the only way to reach it
through this type is with the proof in hand.
-/
structure SearchablePdata where
  /-- The section. -/
  table : PdataSection
  /-- `RtlLookupFunctionEntry` can find every entry in it. -/
  searchable : table.WellFormed

namespace SearchablePdata

/-- Build a searchable section from entries, or refuse. -/
def mk? (functions : List RuntimeFunction) : Option SearchablePdata :=
  if h : (PdataSection.mk functions).WellFormed then some ⟨_, h⟩ else none

/-- `mk?` succeeds exactly on the tables the runtime can search. -/
theorem mk?_isSome_iff (functions : List RuntimeFunction) :
    (mk? functions).isSome ↔ (PdataSection.mk functions).WellFormed := by
  unfold mk?
  by_cases h : (PdataSection.mk functions).WellFormed
  case pos => rw [dif_pos h]; simp [h]
  case neg => rw [dif_neg h]; simp [h]

/-- The bytes of the underlying section. -/
def toBytes (s : SearchablePdata) : ByteSeq := s.table.toBytes

/-- Twelve bytes per entry, as for the section itself. -/
@[simp] theorem length_toBytes (s : SearchablePdata) :
    s.toBytes.length = 12 * s.table.functions.length :=
  s.table.length_toBytes

/-- The enclosing table has no `SearchablePdata`, so no bytes can be produced
for it through this type. -/
theorem enclosing_refused :
    mk? [ { begin_ := 0x00, end_ := 0x100, unwindInfo := 0x1000 }
        , { begin_ := 0x10, end_ := 0x020, unwindInfo := 0x1010 } ] = none := by
  decide

end SearchablePdata

/-! ## Spike 1

The prologue `Grass/ABI/Win64/Unwind.lean` already checks at the vocabulary
level, now placed and serialised.

The offsets follow from the encodings. Spike 1 pushes `r12`, `r13` and `r14`,
all of which need `REX.B`, so each `push` is *two* bytes rather than the one a
push of `rbx` would take -- the offsets are 2, 4 and 6, not 1, 2 and 3. Then
`sub rsp, 32` is `48 83 EC 20`, four bytes, ending at 10.
-/

/-- Spike 1's prologue with offsets: three two-byte pushes ending at 2, 4 and 6,
and the allocation ending at 10. -/
def spike1Layout : Layout :=
  { placed :=
      [ ⟨.pushNonvolatile .r12, 2⟩
      , ⟨.pushNonvolatile .r13, 4⟩
      , ⟨.pushNonvolatile .r14, 6⟩
      , ⟨.allocSmall 32, 10⟩ ]
    sizeOfProlog := 10 }

/-- It satisfies every layout condition. -/
theorem spike1Layout_wellFormed : spike1Layout.WellFormed := by decide

/-- Its vocabulary-level prologue is the one already checked. -/
theorem spike1Layout_prologue : spike1Layout.prologue = spike1Prologue := by decide

/-- Four slots, so no padding slot. -/
theorem spike1Layout_padding : spike1Layout.padding = [] := by decide

/-- Spike 1's `UNWIND_INFO`: no handler, no frame pointer. -/
def spike1UnwindInfo : UnwindInfo :=
  { layout := spike1Layout
    frame := ⟨0, 0⟩
    tail := .noHandler
    layoutWellFormed := spike1Layout_wellFormed
    framePointerAgrees := by decide
    framePointerDeclared := by decide
    noFrameOffsetWithoutFrame := by decide
    countFits := by decide }

/-!
### A frame-pointer layout, and the metadata it refuses

`spike1Layout` establishes no frame pointer, so it exercises none of the frame
invariants. These do.
-/

/-- `push r13`, then establish `r13` as the frame register at `RSP + 0`. -/
def framePointerLayout : Layout :=
  { placed := [⟨.pushNonvolatile .r13, 2⟩, ⟨.setFramePointer .r13 0, 5⟩]
    sizeOfProlog := 5 }

/-- Declaring `r13` at offset 0, which is what the prologue does, is accepted. -/
theorem framePointerLayout_accepted :
    (UnwindInfo.mk? framePointerLayout ⟨regNibble .r13, 0⟩ .noHandler).isSome := by
  decide

/--
A frame offset the prologue does not establish is refused.

The reviewer's counterexample, kept as a theorem. `FrameOffset = 15` claims the
frame sits 240 bytes above the establishing `RSP`, for a prologue that
established it at `RSP + 0`; the unwinder would compute every restore location
240 bytes off. Before `setFramePointer` carried its offset there was nothing in
the model for this to contradict, and `mk?` returned `some`.
-/
theorem bogus_frameOffset_refused :
    UnwindInfo.mk? framePointerLayout ⟨regNibble .r13, 15⟩ .noHandler = none := by
  decide

/-- A frame register the prologue does not establish is refused too, which was
already true and stays true. -/
theorem bogus_frameRegister_refused :
    UnwindInfo.mk? framePointerLayout ⟨regNibble .r14, 0⟩ .noHandler = none := by
  decide

/--
The exact `.xdata` bytes for Spike 1.

Version 1 and no flags (`01`); a ten-byte prologue; four slots; no frame
register. Then the four codes in descending order: the allocation ending at 10
with `OpInfo = 3` for 32 bytes (`32`), then the three pushes ending at 6, 4 and
2 carrying register numbers 14, 13 and 12 in `OpInfo` (`E0`, `D0`, `C0`) -- the
four-bit numbers, so the `REX.B` bit is part of them.

`Tools/win64-unwind-differential.py` checks this shape against `.xdata` that
Microsoft's own assembler generates from the same prologue written with MASM's
`.pushreg`/`.allocstack` directives.
-/
theorem spike1UnwindInfo_toBytes :
    spike1UnwindInfo.toBytes =
      [ 0x01, 0x0A, 0x04, 0x00
      , 0x0A, 0x32
      , 0x06, 0xE0
      , 0x04, 0xD0
      , 0x02, 0xC0 ] := by
  decide

/-- Twelve bytes, which is a multiple of four. -/
theorem spike1UnwindInfo_length : spike1UnwindInfo.toBytes.length = 12 := by decide


/-!
## Relating code offsets to encoded instructions

`Layout.WellFormed` records an open obligation above: its three conditions are
internal, so a layout claiming three two-byte pushes end at 1, 2 and 3, or
claiming `SizeOfProlog = 255` for a ten-byte prologue, satisfies it. Both
mis-unwind.

`Grass.ISA.X86.pushR64` and `Grass.ISA.X86.subR64Imm8`/`subR64Imm32` now exist,
so the comparison the obligation asked for can be made. `Realizes` makes it:
it encodes the operations, lays them end to end from the function's first byte,
and requires every `CodeOffset` to be the offset the encoding actually puts the
operation at.
-/

namespace UnwindOp

/--
The instructions that perform a prologue operation, when this library can
encode them.

`Option`, and deliberately partial. Three operations have an unambiguous
instruction: a nonvolatile push is `PUSH r64`, and both allocation forms are
`SUB RSP, imm`. The rest do not, and inventing one would be worse than
returning `none` here -- `setFramePointer` is a `LEA` or a `MOV` whose operands
depend on the frame offset, `saveNonvolatile` is a `MOV` to a stack slot whose
`ModR/M` form depends on the offset's magnitude, and `pushMachineFrame`
describes what the processor pushed before the function existed, so there is no
instruction at all.

Which of the two `SUB` forms an allocation uses is the interesting part, because
it is where the byte count stops being a fixed stride. The `imm8` form is
sign-extended, so it reaches 127; `allocSmall 128` is legal as an unwind
operation and needs the seven-byte `imm32` form.
-/
def prologueInsns : UnwindOp → Option (List InsnEncoding)
  | .pushNonvolatile r => some [pushR64 r]
  | .allocSmall n =>
      if n ≤ 127 then some [subR64Imm8 .rsp (BitVec.ofNat 8 n)]
      else some [subR64Imm32 .rsp (BitVec.ofNat 32 n)]
  | .allocLarge n => some [subR64Imm32 .rsp (BitVec.ofNat 32 n)]
  | _ => Option.none

/-- Bytes those instructions occupy. -/
def prologueSize (op : UnwindOp) : Option Nat :=
  op.prologueInsns.map fun is => (is.map InsnEncoding.size).sum

/--
An operation this module can encode occupies at least one byte.

This is the byte-level reason `PlacedOp.OffsetPlaced` refuses offset zero for an
instruction. That condition was justified above by an observation about
`RtlVirtualUnwind` plus the remark that "the first instruction ends at 1 or
later"; with an encoder present, the remark is a consequence of
`InsnEncoding.size_pos` rather than a claim about assemblers.
-/
theorem prologueSize_pos {op : UnwindOp} {k : Nat}
    (h : op.prologueSize = some k) : 0 < k := by
  have one : ∀ i : InsnEncoding,
      0 < (([i] : List InsnEncoding).map InsnEncoding.size).sum := by
    intro i; simpa using InsnEncoding.size_pos i
  cases op
  case pushNonvolatile r =>
    simp only [prologueSize, prologueInsns] at h
    first | (have hk := Option.some.inj h; subst hk; exact one _) | (subst h; exact one _)
  case allocSmall n =>
    simp only [prologueSize, prologueInsns] at h
    split at h <;> (first | (have hk := Option.some.inj h; subst hk; exact one _) | (subst h; exact one _))
  case allocLarge n =>
    simp only [prologueSize, prologueInsns] at h
    first | (have hk := Option.some.inj h; subst hk; exact one _) | (subst h; exact one _)
  all_goals simp [prologueSize, prologueInsns] at h

end UnwindOp

namespace Layout

/--
Where each operation ends, laying the encodings end to end from `start`.

`none` as soon as any operation has no encoding, so a layout using
`setFramePointer` is not judged rather than being judged wrongly.
-/
def endOffsetsFrom : Nat → List UnwindOp → Option (List Nat)
  | _, [] => some []
  | start, op :: rest =>
      match op.prologueSize with
      | Option.none => Option.none
      | some k => (endOffsetsFrom (start + k) rest).map fun tl => (start + k) :: tl

/--
Every code offset is the offset the encoded prologue actually puts it at, and
`SizeOfProlog` is the encoded length.

This is what `WellFormed` could not say. `WellFormed` relates the offsets to
each other; this relates them to bytes. The two are independent: a layout can
satisfy either without the other, and the theorems below are the docstring's own
counterexamples, now refuted.

The prologue is taken to consist of exactly these instructions, contiguously,
from the function's first byte. That is what `ml64` emits for a prologue built
only from unwind-relevant instructions, and it is the case the corpus covers. A
prologue interleaving instructions that generate no unwind code -- a `mov` of an
argument into a saved register, say -- has a larger `SizeOfProlog` than this
computes, and `Realizes` will refuse it. Refusing is the right failure: this
predicate under-approximates, and nothing depends on it holding.
-/
def Realizes (l : Layout) : Prop :=
  endOffsetsFrom 0 l.prologue.ops = some (l.offsets.map BitVec.toNat) ∧
    l.sizeOfProlog.toNat = ((l.offsets.map BitVec.toNat).getLast?).getD 0

instance (l : Layout) : Decidable l.Realizes :=
  inferInstanceAs (Decidable (_ ∧ _))

end Layout

end Grass.ABI.Win64
