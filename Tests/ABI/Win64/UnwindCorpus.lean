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

`UWOP_SAVE_NONVOL` and `UWOP_SAVE_XMM128` are covered by `saveRegRows` and
`saveXmmRows` below, over every nonvolatile register, every displacement form,
and mixed with pushes, frames and large allocations.

Not covered: the `_FAR` save forms and `UWOP_PUSH_MACHFRAME`, which have no
constructors, so no row can be built and none is faked. Allocations of 512 KiB
and above are also absent: they need `UWOP_ALLOC_LARGE` with `OpInfo = 1` and a
32-bit size, which `UnwindOp.LargeAllocEncodable` excludes.

Save offsets stop well below 64504 on purpose. `Encodable` permits up to 524280
and the ABI encodes it, but `ml64` switches to the far form at 64504 -- a
hard-coded `cmp edi, 0FBF8h` in the assembler, applied to the raw offset before
it is scaled. A row above that threshold would be correct and would still fail
this differential. `Grass/ABI/Win64/Unwind.lean` records the cause.
-/

namespace Grass.Tests.ABI.Win64.Unwind

open Grass.ISA.X86 Grass.ABI.Win64 Grass.Std.Logical
open Grass.Tests.ISA.X86.Corpus (hexBytes nasmName xmmName)

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
  /-- `mov [rsp+off], r`, with `.savereg r, off`. -/
  | saveReg (r : Gpr) (off : Nat)
  /-- `movaps [rsp+off], xmm`, with `.savexmm128 xmm, off`. -/
  | saveXmm (r : Xmm) (off : Nat)
  /-- `.pushframe`, with no instruction at all: the processor pushed the trap
  frame before the function's first instruction ran. The only step here that
  contributes nothing to `SizeOfProlog`. -/
  | pushFrame (withErrorCode : Bool)
deriving Repr

namespace Step

/-- The instruction MASM will assemble. -/
def instr : Step → String
  | .push r => "push " ++ nasmName r
  | .alloc n => "sub rsp, " ++ toString n
  | .setFrame r 0 => "mov " ++ nasmName r ++ ", rsp"
  | .setFrame r off => "lea " ++ nasmName r ++ ", [rsp+" ++ toString off ++ "]"
  | .saveReg r off =>
      "mov QWORD PTR [rsp+" ++ toString off ++ "], " ++ nasmName r
  | .saveXmm r off =>
      "movaps XMMWORD PTR [rsp+" ++ toString off ++ "], " ++ xmmName r
  -- No instruction. The row builder drops the empty string rather than
  -- emitting a blank line, because the differential counts non-directive
  -- parts to decide what epilogue the test function needs.
  | .pushFrame _ => ""

/-- The unwind directive that must follow it. -/
def directive : Step → String
  | .push r => ".pushreg " ++ nasmName r
  | .alloc n => ".allocstack " ++ toString n
  | .setFrame r off => ".setframe " ++ nasmName r ++ ", " ++ toString off
  | .saveReg r off => ".savereg " ++ nasmName r ++ ", " ++ toString off
  | .saveXmm r off => ".savexmm128 " ++ xmmName r ++ ", " ++ toString off
  | .pushFrame true => ".pushframe code"
  | .pushFrame false => ".pushframe"

/--
The instruction's length in bytes.

This is a claim about encodings, and the differential is what checks it. A push
of `r12`-`r15` carries `REX.B`; `sub rsp, imm8` reaches 127; `mov r, rsp` is
`REX.W` plus opcode plus ModRM; `lea r, [rsp+off]` adds a SIB byte because the
base is `rsp`, plus a displacement.

That displacement is one byte only up to 127. `.setframe` permits offsets to
240, and `lea rbp, [rsp+240]` needs a `disp32` and is eight bytes. The model
said five for every nonzero offset, which a reviewer measured against `ml64`
for `push rbp; sub rsp, 240; .setframe rbp, 240`: `SizeOfProlog` 16 against
Grass's 13. No corpus row exceeded 32, so nothing caught it -- and it would
have blocked extending the corpus to the top of the `off ≤ 240` bound that
`UnwindOp.Encodable` now permits.
-/
def length : Step → Nat
  | .push r => if r.rexBit then 2 else 1
  | .alloc n => if n ≤ 127 then 4 else 7
  | .setFrame _ 0 => 3
  | .setFrame _ off => if off ≤ 127 then 5 else 8
  -- Both save lengths are read off `ml64`'s own `SizeOfProlog` rather than
  -- counted from a manual, and the differential is what keeps them honest.
  --
  -- `mov [rsp+off], r64` is `REX.W` plus opcode plus ModRM plus SIB -- the SIB
  -- is forced because the base is `rsp` -- and then a displacement, which is
  -- absent at zero, one byte to 127, and four beyond. `REX` is already present
  -- for the operand size, so `r8`-`r15` cost nothing extra.
  | .saveReg _ off => 4 + (if off = 0 then 0 else if off ≤ 127 then 1 else 4)
  -- `movaps [rsp+off], xmm` has no `REX` unless the register needs `REX.R`,
  -- and is otherwise `0F 29` plus ModRM plus the forced SIB.
  | .saveXmm r off =>
      (if 8 ≤ r.index.val then 5 else 4)
        + (if off = 0 then 0 else if off ≤ 127 then 1 else 4)
  -- Zero: there is no instruction to measure, which is what makes the
  -- machine frame's code offset zero however many operations follow it.
  | .pushFrame _ => 0


/-- The largest save offset for which `ml64` writes the near form.

Measured, not derived: a binary search with the allocation held constant, so it
is a property of the offset alone, confirmed identical for general-purpose and
XMM saves even though their scaled fields differ by a factor of two. A reviewer
then found the constant in the assembler itself. -/
def ml64LastNearSave : Nat := 64496

/-- The unwind operation the directive records. `ml64` picks the small form up
to 128 bytes, which is exactly `UnwindOp.SmallAllocEncodable`'s range. -/
def op : Step → UnwindOp
  | .push r => .pushNonvolatile r
  | .alloc n => if n ≤ 128 then .allocSmall n else .allocLarge n
  | .setFrame r off => .setFramePointer r off
  -- Which save form `ml64` writes, which is not the same question as which
  -- forms the ABI permits. Both encode every offset the near form reaches, so
  -- `UnwindOp.Encodable` allows either; `ml64` picks the far one from 64504
  -- upward because of a hard-coded `cmp edi, 0FBF8h` applied before the shift
  -- that scales the offset -- the same literal in both save paths, which is
  -- why the threshold is the same byte value despite the divisors differing.
  -- `Grass/ABI/Win64/Unwind.lean` records the cause.
  --
  -- The model must not adopt that rule; this corpus must, because its job is
  -- to predict what `ml64` emits.
  | .saveReg r off =>
      if off ≤ ml64LastNearSave then .saveNonvolatile r off
      else .saveNonvolatileFar r off
  | .saveXmm r off =>
      if off ≤ ml64LastNearSave then .saveXmm128 r off
      else .saveXmm128Far r off
  | .pushFrame withErrorCode => .pushMachineFrame withErrorCode

/-! ### The gap between what `ml64` writes and what this library can build

`Grass/ABI/Win64/UnwindBytes.lean` records why `Realizes` covers three unwind
operations and not the rest. The reason is not ambiguity -- `length` above says
exactly what `ml64` emits for all six -- but that `Grass.ISA.X86.encodeMem` is a
*canonical* encoder: every memory form it builds carries `mod=10` and a
`disp32`, and no shorter displacement is ever chosen.

These pin the size of that gap. They are the numbers that obligation quotes, and
they exist so it cannot go stale silently: an `encodeMem` that learned to
minimise displacements would falsify the first three, and whoever writes it has
to come back here and to that header rather than leaving both describing a
library that no longer behaves that way. -/

/-- `lea rbp, [rsp+0]`: eight bytes canonically. `ml64` writes `mov rbp, rsp`,
which is three, and is a different instruction rather than a shorter encoding of
the same one. -/
example : (leaR64 .rbp (.base .rsp 0)).map InsnEncoding.size = some 8 := rfl
example : Step.length (.setFrame .rbp 0) = 3 := rfl

/-- `lea rbp, [rsp+32]`: eight canonically, five from `ml64`, and here the
instruction *is* the same one -- only the displacement width differs. -/
example : (leaR64 .rbp (.base .rsp 32)).map InsnEncoding.size = some 8 := rfl
example : Step.length (.setFrame .rbp 32) = 5 := rfl

/-- `mov [rsp+8], rbx`: the same three-byte difference, for the operation
`UWOP_SAVE_NONVOL` describes. -/
example : (encodeMemInsn false 0x89 true (.reg .rbx) (.base .rsp 8)).map
    InsnEncoding.size = some 8 := rfl
example : Step.length (.saveReg .rbx 8) = 5 := rfl

/-- The gap is not constant, which is why `prologueInsns` cannot correct for it
with an offset: it is three bytes for a `disp8` operand and five for the
zero-displacement frame pointer, and it would be zero for an offset past 127
where `disp32` is what `ml64` writes too. -/
example : Step.length (.setFrame .rbp 240) = 8 := rfl
example : (leaR64 .rbp (.base .rsp 240)).map InsnEncoding.size = some 8 := rfl

/-! ### The small/large boundary

`op` puts the boundary at 128, which its docstring says is exactly
`UnwindOp.SmallAllocEncodable`'s range. Nothing in Lean held it there: a
mutation moving it to 127 left every theorem in this file green, including the
agreement theorem below, because that theorem compares *lengths* and both
allocation operations encode from the immediate's magnitude -- so which unwind
opcode `op` picks is invisible to it.

Only `Tools/win64-unwind-differential.py` would have noticed, and that needs an
assembler this build does not have. These pin it here so a host without `ml64`
still catches the boundary moving. -/

/-- 128 is the last small allocation, and it is `SmallAllocEncodable`'s bound
rather than a constant of this corpus's own. -/
example : Step.op (.alloc 128) = .allocSmall 128 := rfl
example : UnwindOp.SmallAllocEncodable 128 := by decide

/-- One above it is the large form, and is not small-encodable. -/
example : Step.op (.alloc 136) = .allocLarge 136 := rfl
example : ¬ UnwindOp.SmallAllocEncodable 136 := by decide

/-- The bottom of the range is the small form too, so the boundary is an upper
bound and not a window. -/
example : Step.op (.alloc 8) = .allocSmall 8 := rfl

/--
**The encoder-derived lengths agree with the ones `ml64` validated.**

`length` above is a hand-written claim about encodings, kept honest by the
differential against `ml64`'s own `SizeOfProlog`.
`Grass.ABI.Win64.UnwindOp.prologueSize` computes the same quantity a different
way, from the instruction encoders in `Grass.ISA.X86`. Two models of one fact,
and nothing related them until this.

That is the arrangement `Grass/ABI/Win64/Convention.lean` complains about
elsewhere -- a number spelled twice in two places that had to agree by hand --
and the cost here would have been higher, because only one of the two is
answerable to an assembler. The encoder model has no oracle of its own on this
host; the corpus does. Relating them points `ml64`'s authority at the encoders.

Stated in the direction that holds. Wherever the encoder model gives an answer
it is `ml64`'s answer; the converse is false and should be, since `length`
covers all six step kinds and `prologueSize` refuses four of them. The corpus
stays the wider model, and this makes it the authority over the overlap rather
than a second opinion beside it.

Why the overlap is exactly these two is worth stating, because it looks like
luck and is not. `Grass.ISA.X86.encodeMem` is canonical rather than minimal --
every memory form it builds carries a `disp32` -- so the two models agree on
precisely the operations whose instructions have no displacement to shorten.
`push` has none, and `sub rsp, imm` chooses its immediate width from the
value rather than from an addressing mode. The four operations this theorem
does not reach are the four that address memory, and the section above
measures what that costs.

So the theorem cannot be extended by adding cases. It would have to wait on
displacement minimisation, which `Grass/ABI/Win64/UnwindBytes.lean` explains
is neither required for correctness nor free.

Finding the disagreement is what prompted the theorem. `prologueSize` gave
`allocLarge` the `imm32` form unconditionally, which is right for every
allocation `ml64` describes that way but wrong for the operation, since
`LargeAllocEncodable` permits `n` from 8 -- it reported seven bytes for
`sub rsp, 8`. The corpus, which derives the form from the immediate, was right.
-/
theorem prologueSize_agrees_with_length (s : Step) (k : Nat)
    (h : (Step.op s).prologueSize = some k) : k = s.length := by
  cases s
  case push r =>
    simp only [Step.op, UnwindOp.prologueSize, UnwindOp.prologueInsns,
      Option.map_eq_some_iff] at h
    obtain ⟨_, hi, rfl⟩ := h
    cases hi
    cases r <;> rfl
  case alloc n =>
    simp only [Step.op] at h
    split at h <;>
      (simp only [UnwindOp.prologueSize, UnwindOp.prologueInsns,
         Option.map_eq_some_iff] at h
       split at h <;>
         (obtain ⟨_, hi, rfl⟩ := h
          cases hi
          simp only [Step.length]
          first
            | (rw [if_pos (by omega : n ≤ 127)]; rfl)
            | (rw [if_neg (by omega : ¬ n ≤ 127)]; rfl)))
  all_goals
    simp only [Step.op] at h
    first
      | (split at h <;>
          simp [UnwindOp.prologueSize, UnwindOp.prologueInsns] at h)
      | simp [UnwindOp.prologueSize, UnwindOp.prologueInsns] at h

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
  /-- The unwind operations this row's prologue records.

  Not emitted: the differential reads three tab-separated fields and this is
  the fourth, so adding it changes no tool input. It is kept so that what the
  corpus covers is checkable in Lean rather than only by reading the row
  groups and trusting their names. -/
  ops : List UnwindOp

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
      -- An empty instruction is dropped rather than joined: `.pushframe`
      -- describes what the processor did, so there is nothing to assemble,
      -- and the differential decides the test function's epilogue by counting
      -- the parts that are not directives.
      masm := String.intercalate " | " (steps.flatMap fun st =>
        (if st.instr = "" then [] else [st.instr]) ++ [st.directive])
      xdata := hexBytes u.toBytes
      ops := steps.map Step.op }

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

/-- Allocations needing `UWOP_ALLOC_LARGE` with `OpInfo = 1`: three slots, and
the size stored unscaled in the two that follow. `524288` is the first size the
scaled field cannot reach, and `char buf[600000]` is what MSVC emits it for at
both optimisation levels, which is why this form is worth covering rather than
merely permitting.

Well below `UnwindOp.largeAllocRawMax`. At the very top of that range `ml64`
assembles `sub rsp, 4294967288` as a four-byte `sub rsp, -8`, because the
constant is its own two's complement, while still recording an unwind code
claiming the full allocation. `Step.length` says seven for every allocation
above 127, so a row up there would fail the differential on the instruction
length rather than on the unwind bytes -- a real disagreement about a
pathological input, and not the one this family is for. -/
def hugeAllocRows : List Row :=
  [524288, 600000, 1048576, 16777216].filterMap fun n =>
    rowOf ("alloc-huge-" ++ toString n) [.alloc n]

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
  , rowOf "frame-rsi-0" [.push .rsi, .alloc 8, .setFrame .rsi 0]
  -- The top of the `off <= 240` bound `UnwindOp.Encodable` permits, where the
  -- establishing `lea` needs a disp32 and is eight bytes rather than five.
  -- `Step.length` said five for every nonzero offset until a reviewer measured
  -- this shape against `ml64`; no row reached past 32, so nothing caught it.
  , rowOf "frame-rbp-240" [.push .rbp, .alloc 256, .setFrame .rbp 240]
  , rowOf "frame-r14-128" [.push .r14, .alloc 144, .setFrame .r14 128] ].reduceOption

/-- `UWOP_SAVE_NONVOL`: a register saved with a `mov` after the frame is
allocated, rather than pushed before it. Roughly what an optimising compiler
emits, and the reason this family exists: the corpus previously covered only
prologues built from pushes.

Every nonvolatile register at a fixed offset, then `rbx` across the
displacement forms, because `Step.length` claims the `mov` is four bytes at
offset zero, five to 127 and eight beyond -- three different encodings whose
lengths position everything after them. -/
def saveRegRows : List Row :=
  (pushable.filterMap fun r =>
    rowOf ("savereg-" ++ nasmName r) [.alloc 64, .saveReg r 8])
  ++ ([0, 8, 120, 128, 4096].filterMap fun off =>
    rowOf ("savereg-rbx-at-" ++ toString off)
      [.alloc (off + 4096), .saveReg .rbx off])

/-- `UWOP_SAVE_XMM128`: an XMM register saved with `movaps`. The offset is
scaled by *sixteen* in the extra slot rather than eight, and `xmm8`-`xmm15`
carry a `REX.R` that lengthens the instruction, so both the scaling and the
length claim are exercised.

Only `xmm6`-`xmm15` appear: `xmm0`-`xmm5` are volatile under Win64, and
`UnwindOp.Encodable` refuses them because unwind data naming one describes a
restore the unwinder must not perform. -/
def saveXmmRows : List Row :=
  (Xmm.all.filter (fun r => 6 ≤ r.index.val)).filterMap (fun r =>
    rowOf ("savexmm-" ++ xmmName r) [.alloc 64, .saveXmm r 16])
  ++ ([0, 16, 112, 128, 4096].filterMap fun off =>
    rowOf ("savexmm-xmm6-at-" ++ toString off)
      [.alloc (off + 4096), .saveXmm .xmm6 off])

/-- The far save forms, at offsets where `ml64` writes them.

These rows are the only ones that exercise `UWOP_SAVE_NONVOL_FAR` and
`UWOP_SAVE_XMM128_FAR`, and they exist because the threshold above is now
understood. Before that it was a measurement without a cause, and writing rows
against a rule nobody could explain would have been encoding a coincidence.

`64504` is the first offset past the threshold, so it checks the boundary from
the far side; `Step.op` selects the near form one step below it. -/
def farSaveRows : List Row :=
  ([64504, 100000, 524288].filterMap fun off =>
    rowOf ("savereg-far-rbx-at-" ++ toString off)
      [.alloc (off + 8), .saveReg .rbx off])
  ++ ([64512, 1048576].filterMap fun off =>
    rowOf ("savexmm-far-xmm6-at-" ++ toString off)
      [.alloc (off + 16), .saveXmm .xmm6 off])
  ++ [ rowOf "savereg-far-r15-boundary"
         [.alloc 64512, .saveReg .r15 64504]
     , rowOf "savereg-near-rbx-boundary"
         [.alloc 64504, .saveReg .rbx 64496] ].reduceOption

/-- `UWOP_PUSH_MACHFRAME`, the trap frame an interrupt or exception pushed
before the function began.

Both shapes: `OpInfo = 0` without an error code and `1` with one. `ml64` writes
`0A` and `1A` for them, and the operation's code offset is zero because no
instruction precedes it -- which the rows with operations after the frame check,
since those operations' offsets have to start from zero rather than from a
prologue that had already begun. -/
def machineFrameRows : List Row :=
  [ rowOf "machframe" [.pushFrame false]
  , rowOf "machframe-code" [.pushFrame true]
  , rowOf "machframe-push-rbp" [.pushFrame false, .push .rbp]
  , rowOf "machframe-code-alloc" [.pushFrame true, .alloc 32]
  , rowOf "machframe-push-alloc-save"
      [.pushFrame false, .push .rbx, .alloc 64, .saveReg .rsi 8] ].reduceOption

/-- Saves mixed with the forms that already had coverage, so that a two-slot
save has to agree on offsets with a push and an allocation on either side. -/
def mixedSaveRows : List Row :=
  [ rowOf "push-rbx-alloc-save-rsi"
      [.push .rbx, .alloc 64, .saveReg .rsi 8]
  , rowOf "push-rbp-frame-save-xmm6"
      [.push .rbp, .alloc 96, .setFrame .rbp 0, .saveXmm .xmm6 32]
  , rowOf "save-both-kinds"
      [.alloc 128, .saveReg .r12 8, .saveXmm .xmm7 32]
  , rowOf "push-r15-alloc-large-save-r14"
      [.push .r15, .alloc 4096, .saveReg .r14 24] ].reduceOption

/-- Spike 1's prologue, as the differential sees it. -/
def spike1Rows : List Row :=
  [ rowOf "spike1"
      [.push .r12, .push .r13, .push .r14, .alloc 32] ].reduceOption

/-- The whole corpus. -/
def corpus : List Row :=
  singlePushRows ++ pairPushRows ++ smallAllocRows ++ largeAllocRows ++
    pushAllocRows ++ frameRows ++ hugeAllocRows ++ saveRegRows ++
    saveXmmRows ++ farSaveRows ++ machineFrameRows ++ mixedSaveRows ++
    spike1Rows

-- Evaluating a hundred rows to a length outruns the default depth.
set_option maxRecDepth 8000

/-- Every family contributes the rows it was written to contribute.

`rowOf` returns an `Option`: a prologue `UnwindInfo.mk?` refuses produces no row
at all, and `filterMap` drops it without a word. That is the right behaviour --
a corpus must not contain a prologue the model calls unencodable -- but it means
a family can silently contribute nothing.

It already did. All five `machineFrameRows` vanished on their first run, because
`Layout.WellFormed` required every code offset to be positive and a machine
frame's is zero. The differential then reported "95 prologues, byte-identical",
which was true and told me nothing about the operation I had just added. The
count is pinned here so that the next silent drop is a failed build rather than
a satisfying green line.

Raising this number is the ordinary way to add rows; lowering it means
something stopped building and should be explained rather than accommodated. -/
theorem corpus_length : corpus.length = 100 := by rfl

/-! ### What the corpus covers

`Grass/ABI/Win64/UnwindBytes.lean`'s header says `UNWIND_INFO` for all nine
operations this profile models is covered by this differential, on 100
prologues. The second half has always been a theorem -- `corpus_length` --
and the first half was prose, checkable only by reading thirteen row groups
and trusting their names.

These make it mechanical. The membership form is deliberate: asserting the
deduplicated list equals a literal would pin first-occurrence order too, so
reordering the row groups would fail a test about coverage without coverage
having changed. -/

/-- Every opcode the encoding uses appears somewhere in the corpus. -/
theorem corpus_covers_every_opcode :
    ∀ c ∈ ([0, 1, 2, 3, 4, 5, 8, 9, 10] : List Nat),
      c ∈ ((corpus.flatMap Row.ops).map (fun o => o.opcode.toNat)) := by
  decide

/-- And exactly those nine, so a tenth operation added without a row would fail
here rather than quietly going untested. -/
theorem corpus_covers_no_others :
    (((corpus.flatMap Row.ops).map (fun o => o.opcode.toNat)).eraseDups).length
      = 9 := by
  rfl

/-- Both `allocLarge` forms are exercised, which the opcode alone cannot show:
the scaled and unscaled forms share opcode 1 and differ in slot count. Without
this the corpus could cover the opcode and never the three-slot encoding. -/
theorem corpus_covers_both_allocLarge_forms :
    ((((corpus.flatMap Row.ops).filter (fun o => o.opcode = 1)).map
      UnwindOp.slots).eraseDups) = [2, 3] := by
  rfl


/-- The Spike 1 row agrees with the theorem in `UnwindBytes.lean`, so the
differential and the proof are checking the same bytes rather than two
independently-computed ones. -/
theorem spike1Row_matches_theorem :
    (spike1Rows.map Row.xdata) = ["010a04000a3206e004d002c0"] := by
  decide

end Grass.Tests.ABI.Win64.Unwind

/-- Print the corpus as tab-separated `xdata<TAB>name<TAB>masm` lines.

Top level, and named for its corpus rather than `main`. Six of these
modules declared a root `main`, so importing any two into one environment
collided on it -- which is what `audit-trust.ps1` does, and `g-construct:58`
reported the gate failing before it could audit anything. `Tests/Emit.lean`
holds the single `main` that `lake env lean --run` needs and dispatches to
these by name. -/
def emitUnwindCorpus : IO Unit := do
  for r in Grass.Tests.ABI.Win64.Unwind.corpus do
    IO.println (r.xdata ++ "\t" ++ r.name ++ "\t" ++ r.masm)
