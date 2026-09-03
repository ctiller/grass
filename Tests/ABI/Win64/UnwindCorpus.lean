import Grass.ABI.Win64.UnwindBytes
import Tests.ISA.X86.CorpusCommon

/-!
# Win64 unwind metadata corpus, for differential checking against `ml64`

`docs/VALIDATION.md` section 2 layer 2 asks for comparison against independent
tools where they exist. For `.xdata` the independent tool is Microsoft's own
assembler: MASM's `PROC FRAME` and its `.pushreg`/`.allocstack`/`.setframe`
directives make `ml64.exe` generate `UNWIND_INFO` from a prologue, and that is
the same artifact `Grass.ABI.Win64.UnwindInfo.toBytes` produces.

This is a better oracle than the NASM one used for instruction encodings. NASM
is a third-party assembler agreeing with Grass about Intel's format; `ml64` is
the vendor of the format, so a disagreement here is much more likely to be a
Grass defect than an oracle defect. It is still not authority --
`docs/VALIDATION.md` section 2: "Tools and hardware are fallible oracles."

## What a row checks

Each row carries a MASM prologue and the bytes this model says its `.xdata`
should be. `Tools/win64-unwind-differential.py` assembles the prologue and
compares. That catches more than the byte layout, because the model's
`PlacedOp.codeOffset` values are computed here from instruction *lengths*:

* a `push` of `r12`-`r15` needs `REX.B` and is two bytes, while a push of
  `rbx`, `rbp`, `rsi` or `rdi` is one;
* `sub rsp, imm8` is four bytes and `sub rsp, imm32` is seven.

If either belief is wrong, `ml64` computes different offsets from the same
instructions and the row fails. So the corpus checks the encoder's length model
against the assembler even though this module never encodes an instruction.

## Coverage, and what is deliberately missing

Single-operation prologues are included specifically because they need one slot,
which is odd, which forces the padding slot. They earned their place: they are
the rows that caught `Prologue.countOfCodes` folding the padding slot into the
reported count, a mistake invisible on every even-slot prologue including Spike
1's. `Prologue.arraySlots` is now the padded length and `countOfCodes` the
reported one.

Not covered: `UWOP_SAVE_NONVOL`, `UWOP_SAVE_XMM128` and their `_FAR` forms, and
`UWOP_PUSH_MACHFRAME`. `Grass.ABI.Win64.UnwindOp` has no constructors for them,
so no row can be built and none is faked. Allocations of 512 KiB and above are
also absent: they need `UWOP_ALLOC_LARGE` with `OpInfo = 1` and a 32-bit size,
which `UnwindOp.LargeAllocEncodable` excludes. Both gaps belong in the trust
ledger's owed column rather than in a comment claiming coverage.
-/

namespace Grass.Tests.ABI.Win64.Unwind

open Grass.ISA.X86 Grass.ABI.Win64 Grass.Std.Logical
open Grass.Tests.ISA.X86.Corpus (hexBytes nasmName)

/--
One step of a prologue: an instruction plus the unwind directive describing it.

Deliberately not `UnwindOp`. An `UnwindOp` says what to undo; a `Step` also
carries the instruction that did it and therefore its length, which is what
positions the following operations.
-/
inductive Step where
  /-- `push r`, with `.pushreg r`. -/
  | push (r : Gpr)
  /-- `sub rsp, n`, with `.allocstack n`. -/
  | alloc (n : Nat)
  /-- Establish a frame register at `rsp + off`, with `.setframe r, off`. -/
  | setFrame (r : Gpr) (off : Nat)
deriving Repr

namespace Step

/-- The instruction MASM will assemble. -/
def instr : Step → String
  | .push r => "push " ++ nasmName r
  | .alloc n => "sub rsp, " ++ toString n
  | .setFrame r 0 => "mov " ++ nasmName r ++ ", rsp"
  | .setFrame r off => "lea " ++ nasmName r ++ ", [rsp+" ++ toString off ++ "]"

/-- The unwind directive that must follow it. -/
def directive : Step → String
  | .push r => ".pushreg " ++ nasmName r
  | .alloc n => ".allocstack " ++ toString n
  | .setFrame r off => ".setframe " ++ nasmName r ++ ", " ++ toString off

/--
The instruction's length in bytes.

This is a claim about encodings, and the differential is what checks it. A push
of `r12`-`r15` carries `REX.B`; `sub rsp, imm8` reaches 127; `mov r, rsp` is
`REX.W` plus opcode plus ModRM; `lea r, [rsp+off]` adds a SIB byte because the
base is `rsp`, plus a one-byte displacement.
-/
def length : Step → Nat
  | .push r => if r.rexBit then 2 else 1
  | .alloc n => if n ≤ 127 then 4 else 7
  | .setFrame _ 0 => 3
  | .setFrame _ _ => 5

/-- The unwind operation the directive records. `ml64` picks the small form up
to 128 bytes, which is exactly `UnwindOp.SmallAllocEncodable`'s range. -/
def op : Step → UnwindOp
  | .push r => .pushNonvolatile r
  | .alloc n => if n ≤ 128 then .allocSmall n else .allocLarge n
  | .setFrame r off => .setFramePointer r off

/-- The header nibbles this step establishes, if any. `FrameOffset` is scaled by
sixteen. -/
def frame : Step → Option FrameSpec
  | .setFrame r off => some ⟨regNibble r, BitVec.ofNat 4 (off / 16)⟩
  | _ => none

end Step

/--
Walk the steps, assigning each its offset.

`PlacedOp.codeOffset` is the offset of the byte *after* the instruction, so the
running total is advanced before the offset is recorded rather than after.
-/
def placeSteps (steps : List Step) : List PlacedOp × Nat × FrameSpec :=
  steps.foldl
    (fun acc st =>
      let off := acc.2.1 + st.length
      (acc.1 ++ [⟨st.op, BitVec.ofNat 8 off⟩], off, st.frame.getD acc.2.2))
    ([], 0, ⟨0, 0⟩)

/-- A corpus row: a MASM prologue and the `.xdata` this model predicts for it. -/
structure Row where
  /-- A label, for the tool's report. -/
  name : String
  /-- The prologue: instructions and directives, alternating, `" | "`
  separated so a row stays one line. -/
  masm : String
  /-- The predicted `.xdata` bytes, lowercase hex. -/
  xdata : String

/--
Build a row, or nothing.

`UnwindInfo.mk?` refuses a prologue outside the unwind language, so a `Step`
list naming a volatile register or an unencodable allocation produces no row.
That is why the corpus is a `filterMap`: the model's refusals silently shrink
the corpus rather than emitting rows it cannot justify, and the tool reports the
row count it actually received.
-/
def rowOf (name : String) (steps : List Step) : Option Row :=
  let placed := placeSteps steps
  let layout : Layout := ⟨placed.1, BitVec.ofNat 8 placed.2.1⟩
  (UnwindInfo.mk? layout placed.2.2 .noHandler).map fun u =>
    { name := name
      masm := String.intercalate " | " (steps.flatMap fun st => [st.instr, st.directive])
      xdata := hexBytes u.toBytes }

/-- The registers a prologue may push: nonvolatile and not `rsp`. -/
def pushable : List Gpr :=
  Gpr.all.filter fun r => volatility r == .nonvolatile && r != .rsp

/-- One push on its own. One slot, so every row here carries a padding slot. -/
def singlePushRows : List Row :=
  pushable.filterMap fun r => rowOf ("push-" ++ nasmName r) [.push r]

/-- Two pushes: an even slot count, and the descending store order becomes
observable because the two offsets differ. -/
def pairPushRows : List Row :=
  pushable.filterMap fun r =>
    rowOf ("push-rbx-" ++ nasmName r) [.push .rbx, .push r]

/-- Every allocation `UWOP_ALLOC_SMALL` can encode: 8 to 128 in steps of 8.
Alone, so each is an odd slot count. -/
def smallAllocRows : List Row :=
  (List.range 16).filterMap fun i =>
    let n := (i + 1) * 8
    rowOf ("alloc-small-" ++ toString n) [.alloc n]

/-- Allocations needing `UWOP_ALLOC_LARGE`: two slots, so no padding, and the
size is scaled by eight into the second slot. `136` is the first size too large
for the small form; `524280` is the last the 16-bit scaled field reaches. -/
def largeAllocRows : List Row :=
  [136, 256, 1024, 4096, 65536, 262144, 524280].filterMap fun n =>
    rowOf ("alloc-large-" ++ toString n) [.alloc n]

/-- A push and an allocation together, over the alloc forms, so that a
`REX`-prefixed push and a seven-byte `sub` have to agree on offsets. -/
def pushAllocRows : List Row :=
  [32, 136, 4096].flatMap fun n =>
    [Gpr.rbx, Gpr.r12].filterMap fun r =>
      rowOf ("push-" ++ nasmName r ++ "-alloc-" ++ toString n) [.push r, .alloc n]

/-- Frame-pointer prologues. `FrameRegister` is nonzero here, which is the case
`UnwindInfo.framePointerAgrees` couples to the presence of the operation. -/
def frameRows : List Row :=
  [ rowOf "frame-rbp-0" [.push .rbp, .alloc 32, .setFrame .rbp 0]
  , rowOf "frame-rbp-32" [.push .rbp, .alloc 48, .setFrame .rbp 32]
  , rowOf "frame-r13-16" [.push .r13, .alloc 64, .setFrame .r13 16]
  , rowOf "frame-rsi-0" [.push .rsi, .alloc 8, .setFrame .rsi 0] ].reduceOption

/-- Spike 1's prologue, as the differential sees it. -/
def spike1Rows : List Row :=
  [ rowOf "spike1"
      [.push .r12, .push .r13, .push .r14, .alloc 32] ].reduceOption

/-- The whole corpus. -/
def corpus : List Row :=
  singlePushRows ++ pairPushRows ++ smallAllocRows ++ largeAllocRows ++
    pushAllocRows ++ frameRows ++ spike1Rows

/-- The Spike 1 row agrees with the theorem in `UnwindBytes.lean`, so the
differential and the proof are checking the same bytes rather than two
independently-computed ones. -/
theorem spike1Row_matches_theorem :
    (spike1Rows.map Row.xdata) = ["010a04000a3206e004d002c0"] := by
  decide

end Grass.Tests.ABI.Win64.Unwind

/-- Print the corpus as tab-separated `xdata<TAB>name<TAB>masm` lines.

Top level rather than in the namespace because `lake env lean --run` looks for
`main` there. -/
def main : IO Unit := do
  for r in Grass.Tests.ABI.Win64.Unwind.corpus do
    IO.println (r.xdata ++ "\t" ++ r.name ++ "\t" ++ r.masm)
