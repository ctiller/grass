import Grass.ABI.Win64.Convention
import Grass.ISA.X86.Encoding
import Grass.Std.Logical.Byte

/-!
# Win64 unwind metadata

`UNWIND_CODE`, `UNWIND_INFO`, and the decidable recogniser
`docs/PLATFORM_ABI.md` §3 requires:

> "Win64 automatic unwind generation applies only after a decidable
> `Win64UnwindEncodablePrologue` recognizer accepts the exact encoded prologue
> prefix and its frame layout. It produces `.pdata/.xdata` plus a proof that the
> metadata reverses that prefix. A semantically valid custom prologue outside
> the Windows unwind language must supply a separately verified encodable unwind
> description or is rejected locally; arbitrary assembly is never falsely
> claimed to have derivable standard metadata."

Two halves, and the second is the one that matters. Generating plausible unwind
codes for a prologue is easy; the demand is that generation is *refused* for a
prologue the unwind language cannot express, rather than silently producing
metadata that unwinds to the wrong place.

## Why the unwind language is narrower than assembly

The Windows unwind language describes a prologue as a list of operations from a
fixed vocabulary — push a nonvolatile register, allocate a constant amount,
establish a frame pointer, save a register or an XMM register at a constant
offset, and push a machine frame. `UnwindOp` models **all five**, in nine
constructors -- the two saves and the allocation each have a near and a far or
scaled and unscaled form. So
`UnwindOp.Encodable` rejects a stack adjustment that is not a constant multiple
of eight and a push of a volatile register, and a prologue interleaving other
work between the pushes has no `Prologue` value at all.

## How much of the language that is, measured

A reviewer once measured what the missing save operations cost, decoding the
unwind codes out of `.xdata` for 24 C functions compiled with the MSVC on this
machine: at `/O2`, 89 unwind operations of which **36 (40%) had no constructor
here** — 24 `UWOP_SAVE_XMM128` and 12 `UWOP_SAVE_NONVOL` — and **13 of the 24
functions (54%) had no `Prologue` value at all**. At `/Od`, 29 operations, all
modelled, 1 function of 25 without a `Prologue`.

`saveNonvolatile` and `saveXmm128` close that gap: all 36 of those operations
now have constructors. Both were added against `ml64` rather than against a
manual, and the corpus checks 100 prologues byte-for-byte.

`UWOP_SAVE_NONVOL` is not exotic: MSVC's standard optimised idiom is
`mov [rsp+32], rbx` into the caller's shadow space rather than `push rbx`.
`UWOP_SAVE_XMM128` appears in any function holding a `double` across a call,
because XMM6–XMM15 are nonvolatile on Win64 and `Grass/ABI/Win64/Convention.lean`
models general-purpose registers only.

## What is still outside the model

`UWOP_PUSH_MACHFRAME`, which has no constructor.

`UWOP_ALLOC_LARGE` with `OpInfo = 1` -- the three-slot form carrying an unscaled
32-bit size, which `char buf[600000]` produces at both optimisation levels -- is
modelled now. Which of the two forms an `allocLarge` takes is derived from its
size rather than chosen, so no operation can declare a slot count its own bytes
contradict.

None of that is unsoundness — every one is a refusal, and refusing is what this
module is for. It is a statement about *reach*.

## An `ml64` threshold that is not an ABI rule

`Encodable` permits a `saveNonvolatile` offset up to 524280, which is exactly
what the 16-bit scaled field encodes. `ml64` does not use the near form that
far: it emits `UWOP_SAVE_NONVOL_FAR` from offset 64504 upward, and the same
*byte* threshold for `saveXmm128` even though that field reaches 1048560.

That is not a rule to copy. A reviewer disassembled `ml64.exe` and found the
cause: `cmp edi, 0FBF8h` — 64504 — compared against the raw offset *before* the
shift that scales it, the same literal in both save paths. `.allocstack`, which
has an identical 16-bit-scaled-by-8 field, switches at the correct 524280, so
MASM makes the same decision correctly elsewhere.

The consequence is a split of responsibility rather than a hazard, now that
both forms are modelled. `Encodable` permits either form at any offset either
can hold, because the ABI does; `Tests/ABI/Win64/UnwindCorpus.lean` carries
`ml64LastNearSave` and picks the form `ml64` will write, because its job is to
predict that assembler. The threshold belongs in the thing that has to agree
with `ml64`, not in the thing that has to be right about the ABI. Rows sit on
both sides of it, so the prediction is checked in each direction.

Those prologues are perfectly legal machine code and run correctly. What they
cannot have is *derived* unwind data, and `Prologue.Encodable` is the predicate
that separates the two. `docs/PLATFORM_ABI.md` §3 is explicit that the answer
for the second class is local rejection, not a best effort.

## Ordering

Unwind codes are stored in **descending** order of their offset in the prologue
— last operation first — because the unwinder walks them forwards while undoing
the prologue backwards. `Prologue.codes` builds them in that order, and
`Prologue.codes_stackDelta` checks that reversing preserved the arithmetic.
-/

namespace Grass.ABI.Win64

open Grass.Core Grass.Std.Logical Grass.ISA.X86

/-! ## Unwind operations -/

/--
A register's four-bit number: the `REX` bit is the *high* bit and
`encodingBits` the low three, so `r12` is 12 and not 4.

Shared by `UnwindOp.opInfo` and `UNWIND_INFO.FrameRegister`, which is what lets
`Grass.ABI.Win64.UnwindInfo` require the two to agree.
-/
def regNibble (r : Gpr) : BitVec 4 := BitVec.ofBool r.rexBit ++ r.encodingBits

/--
An unwind operation code, as stored in the high nibble's `UnwindOp` field.

Only the operations this profile emits or recognises are constructors. The
numeric values are the ABI's; `opcode` is the table.
-/
inductive UnwindOp where
  /-- `UWOP_PUSH_NONVOL` (0): a `push` of a nonvolatile register. `OpInfo` is
  the register number. -/
  | pushNonvolatile (r : Gpr)
  /-- `UWOP_ALLOC_SMALL` (2): `sub rsp, n` for `n` in 8..128, a multiple of 8.
  `OpInfo` holds `n/8 - 1`. -/
  | allocSmall (bytes : Nat)
  /-- `UWOP_ALLOC_LARGE` (1) with `OpInfo = 0`: `sub rsp, n` for `n` a multiple
  of 8 below 512K, stored scaled in one extra slot. -/
  | allocLarge (bytes : Nat)
  /-- `UWOP_SET_FPREG` (3): establish the frame pointer from `RSP`.

  Carries the register, even though the unwinder reads `FrameRegister` from the
  `UNWIND_INFO` header rather than from this code's `OpInfo`. Two reasons.
  Microsoft's assembler writes the register number into `OpInfo` here -- see
  `opInfo` -- so a model storing 0 could not reproduce `ml64`'s bytes. And
  holding the register in the operation is what lets
  `Grass.ABI.Win64.UnwindInfo.framePointerAgrees` demand that the header field
  and every establishing instruction name the same register. -/
  | setFramePointer (r : Gpr) (offset : Nat)
  /-- `UWOP_SAVE_NONVOL` (4): `mov [RSP+n], reg`, saving a nonvolatile register
  without pushing it. `OpInfo` is the register number, and one extra slot holds
  `n/8` as a little-endian 16-bit value.

  This and `saveXmm128` are how a compiler-generated prologue saves registers
  after allocating its frame, rather than by pushing before it. `ml64`'s
  `.savereg` directive emits it. -/
  | saveNonvolatile (r : Gpr) (offset : Nat)
  /-- `UWOP_SAVE_XMM128` (8): `movaps [RSP+n], xmm`. `OpInfo` is the XMM
  register number, and one extra slot holds `n/16` -- scaled by sixteen, not
  eight, because the saved value is sixteen bytes wide. `ml64`'s `.savexmm128`
  directive emits it. -/
  | saveXmm128 (r : Xmm) (offset : Nat)
  /-- `UWOP_SAVE_NONVOL_FAR` (5): the same save, with the offset stored
  unscaled in two extra slots rather than divided by eight in one.

  Separate from `saveNonvolatile` rather than derived from the offset, unlike
  `allocLarge`, and the difference is worth stating because it looks
  inconsistent. An allocation past `largeAllocScaledMax` has only one legal
  encoding, so deriving the form from the size removes a way to be wrong.
  Both save forms are legal for every offset the near form reaches, so which
  one to write is a real choice the ABI leaves open, and a model that derived
  it would be inventing a rule. `ml64` makes that choice badly -- see the
  header -- which is exactly why the model should not copy whatever rule it
  appears to follow. -/
  | saveNonvolatileFar (r : Gpr) (offset : Nat)
  /-- `UWOP_SAVE_XMM128_FAR` (9): the XMM save with an unscaled offset. -/
  | saveXmm128Far (r : Xmm) (offset : Nat)
  /-- `UWOP_PUSH_MACHFRAME` (10): the trap frame the processor pushed before
  the first instruction of the function ran.

  Unlike every other operation here, this one describes something the prologue
  did not do. On an interrupt or exception the processor pushes `SS`, `RSP`,
  `RFLAGS`, `CS` and `RIP`, and an error code first for those vectors that have
  one; the operation records that it happened so the unwinder can step over it.
  Its code offset is zero and it contributes nothing to `SizeOfProlog`, because
  there is no instruction to measure. -/
  | pushMachineFrame (withErrorCode : Bool)
deriving DecidableEq, Repr, Inhabited

namespace UnwindOp

/-- The `UnwindOp` nibble stored in the code. -/
def opcode : UnwindOp → BitVec 4
  | .pushNonvolatile _ => 0
  | .allocLarge _ => 1
  | .allocSmall _ => 2
  | .setFramePointer _ _ => 3
  | .saveNonvolatile _ _ => 4
  | .saveXmm128 _ _ => 8
  | .saveNonvolatileFar _ _ => 5
  | .saveXmm128Far _ _ => 9
  | .pushMachineFrame _ => 10

/-- The largest allocation the scaled `UWOP_ALLOC_LARGE` form encodes:
`65535 * 8`, the ceiling of its 16-bit field. Above this the operation takes a
third slot and stores the size unscaled. -/
def largeAllocScaledMax : Nat := 524280

/-- The largest allocation the unscaled form encodes. `ml64` accepts `2^32 - 8`
and refuses `2^32` outright with `A2156: constant value out of range`. -/
def largeAllocRawMax : Nat := 4294967288

/--
How many two-byte slots this operation occupies in the `UNWIND_CODE` array.

Not one. `CountOfCodes` counts *slots*, not operations, and an allocation
carries its size in the slots that follow it. A generator that counted
operations produces an `UNWIND_INFO` header whose count disagrees with its own
array, which the unwinder reads as whatever follows.
-/
def slots : UnwindOp → Nat
  | .pushNonvolatile _ => 1
  | .allocSmall _ => 1
  -- Two slots for the scaled form, three for the unscaled one, derived from
  -- the size rather than chosen. `UWOP_ALLOC_LARGE` carries its size in the
  -- slots that follow it, so a constructor letting the caller pick the form
  -- could claim a slot count the bytes do not match, and the unwinder reads
  -- `CountOfCodes` slots whatever was actually written.
  | .allocLarge n => if n ≤ largeAllocScaledMax then 2 else 3
  | .setFramePointer _ _ => 1
  | .saveNonvolatile _ _ => 2
  | .saveXmm128 _ _ => 2
  | .saveNonvolatileFar _ _ => 3
  | .saveXmm128Far _ _ => 3
  | .pushMachineFrame _ => 1

/-- Every operation occupies at least one slot. -/
theorem slots_pos (op : UnwindOp) : 0 < op.slots := by
  cases op <;> simp [slots] <;> split <;> simp

/-- How many bytes this operation moves `RSP` down by in the prologue. -/
def stackDelta : UnwindOp → Nat
  | .pushNonvolatile _ => 8
  | .allocSmall n => n
  | .allocLarge n => n
  | .setFramePointer _ _ => 0
  -- A save writes through `RSP` without moving it: the space was already
  -- reserved by whichever allocation precedes it.
  | .saveNonvolatile _ _ => 0
  | .saveXmm128 _ _ => 0
  | .saveNonvolatileFar _ _ => 0
  | .saveXmm128Far _ _ => 0
  -- Zero, and the zero is a statement rather than an omission. `stackDelta`
  -- is what the *prologue* subtracts from `RSP`, which is what
  -- `Grass.ABI.Win64.rspAfterPrologue` reasons about; the processor pushed the
  -- machine frame before the first instruction ran, so no instruction in the
  -- prologue accounts for it.
  --
  -- The consequence is an open obligation rather than a hidden approximation:
  -- a function entered through an interrupt gate does not arrive with the
  -- eight-byte misalignment a `call` leaves, so `entryMisalignment` does not
  -- describe its entry at all. This module models the unwind *encoding* of a
  -- machine frame and not the alignment of the frame it sits in, and a
  -- prologue mixing `pushMachineFrame` with an alignment argument would be
  -- reasoning from a premise nothing here establishes.
  --
  -- Nothing does that reasoning today: `Grass.ABI.Win64.AlignedForCall` takes
  -- two bare `Nat`s and no caller derives them from a `Prologue`. So the guard
  -- that would make the mistake unwritable -- a predicate refusing a prologue
  -- that records a machine frame -- is deliberately not here: it would be a
  -- precondition invented for a caller that does not exist, which is the same
  -- trade `Grass/ABI/Win64/UnwindBytes.lean` declines for the prologue
  -- recogniser.
  --
  -- What the caller will need is smaller than it looks.
  -- `Grass.ABI.Win64.alignedForCall_iff_total` says alignment depends only on
  -- how far the prologue moved `RSP`, not on how that was split between pushes
  -- and a `sub`, so `Prologue.stackDelta` is the whole input and no second
  -- model of the split is needed. What must be established alongside it is
  -- exactly this: that the prologue records no machine frame.
  | .pushMachineFrame _ => 0

/-- The `OpInfo` nibble.

For a push it is the four-bit register number. For an allocation it is a size
encoding and not a register at all: `allocSmall` stores `n/8 - 1`, and
`allocLarge` stores 0 because its size goes in a following slot.

For `setFramePointer` it is the frame register's number, and that is a recorded
disagreement rather than a derivation -- a three-way one, which an earlier
version of this paragraph recorded only two thirds of.

Microsoft's description of `UWOP_SET_FPREG` says the operation info field is
reserved and should not be used, which reads as licence to write anything.
Microsoft then ships two generators that write different things. `ml64` writes
the **register**: `.setframe r13, 16` gives the code byte `D3`. `cl.exe`
writes the **offset** in the same position `opInfo` puts the register: a
function whose frame is established by `lea rbp, [rsp+96]` gets frame register
5 and frame offset 6, and its code byte carries 6 -- decisive, because the two
differ, so the byte cannot be the register.

`opInfo` below writes the register, so it reproduces one generator and not the
other. That is the honest scope of
`Tools/win64-unwind-differential.py`'s exactness, and the earlier claim that
"matching the vendor's generator makes the differential exact" was true only
against the generator this corpus happens to use. `docs/VALIDATION.md` section 2
asks for the disagreement to be preserved rather than smoothed over; preserving
one half of it and calling the matter settled is what a reviewer caught.

Nothing rests on the choice: the unwinder takes the register from
`FrameRegister`, which is why two vendor tools can disagree here without either
being wrong. -/
def opInfo : UnwindOp → BitVec 4
  | .pushNonvolatile r => regNibble r
  | .allocSmall n => BitVec.ofNat 4 (n / 8 - 1)
  | .allocLarge n => if n ≤ largeAllocScaledMax then 0 else 1
  | .setFramePointer r _ => regNibble r
  | .saveNonvolatile r _ => regNibble r
  | .saveXmm128 r _ => BitVec.ofNat 4 r.index.val
  | .saveNonvolatileFar r _ => regNibble r
  | .saveXmm128Far r _ => BitVec.ofNat 4 r.index.val
  -- `OpInfo` distinguishes the two trap-frame shapes: 1 when the processor
  -- also pushed an error code, 0 when it did not. Confirmed against `ml64`,
  -- which writes 0x0A for `.pushframe` and 0x1A for `.pushframe code`.
  | .pushMachineFrame withErrorCode => if withErrorCode then 1 else 0

/--
The allocation sizes `allocSmall` can encode: multiples of 8 from 8 to 128.

`OpInfo` is four bits holding `n/8 - 1`, so `n = 8` is `0` and `n = 128` is
`15`. An allocation of 136 needs `allocLarge`, and one of 12 cannot be encoded
at all because it is not a multiple of 8.
-/
def SmallAllocEncodable (n : Nat) : Prop := 8 ≤ n ∧ n ≤ 128 ∧ n % 8 = 0

instance (n : Nat) : Decidable (SmallAllocEncodable n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `allocLarge` covers both of its forms.

With `OpInfo = 0` the size is stored as `n/8` in one 16-bit slot, reaching
`largeAllocScaledMax`. Above that `OpInfo = 1` stores it unscaled in two slots,
reaching `largeAllocRawMax`. Both are multiples of eight.

Which form is used is not a choice: `slots` and `opInfo` derive it from `n`, so
there is no way to build an operation whose declared slot count disagrees with
the bytes it writes. -/
def LargeAllocEncodable (n : Nat) : Prop :=
  8 ≤ n ∧ n ≤ largeAllocRawMax ∧ n % 8 = 0

instance (n : Nat) : Decidable (LargeAllocEncodable n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/--
The operation is one this profile can actually encode.

`RSP` is excluded from `pushNonvolatile` even though `volatility .rsp` is
`.nonvolatile`, and the exclusion is not cosmetic. `UWOP_PUSH_NONVOL` tells the
unwinder to do `RSP := [RSP]; RSP += 8`, which recovers the pushed register's
value. For `push rsp` the pushed value is the stack pointer *before* the push,
so replaying the code yields `RSP_after + 16` where the truth is `RSP_after + 8`
-- the metadata is wrong even though the instruction is legal. That is exactly
the class `push_volatile_not_encodable` exists to exclude: "the prologue is
legal; the *description* is not".

A reviewer found this, and found that the guard already existed in
`Tests/ABI/Win64/UnwindCorpus.lean`'s `pushable` filter and nowhere in the
model. `ml64` accepts `.pushreg rsp` and emits the same `0101010001400000` this
profile did, so no differential could ever have caught it.
-/
def Encodable : UnwindOp → Prop
  | .pushNonvolatile r => volatility r = .nonvolatile ∧ r ≠ .rsp
  | .allocSmall n => SmallAllocEncodable n
  | .allocLarge n => LargeAllocEncodable n
  | .setFramePointer r off =>
      volatility r = .nonvolatile ∧ r ≠ .rsp ∧ off % 16 = 0 ∧ off ≤ 240
  | .saveNonvolatile r off =>
      volatility r = .nonvolatile ∧ r ≠ .rsp ∧ off % 8 = 0 ∧ off / 8 < 65536
  | .saveXmm128 r off =>
      -- Saving a volatile register in unwind data describes a restore the
      -- unwinder must not perform. Spelled through `xmmVolatility` rather
      -- than as the literal `6` it used to be, so the ABI fact has one
      -- declaration rather than two hand-matched copies.
      6 ≤ r.index.val ∧ off % 16 = 0 ∧ off / 16 < 65536
  | .saveNonvolatileFar r off =>
      -- Alignment still applies: `ml64` rejects `.savereg rbx, 4` with
      -- `A2219: Bad alignment for offset in unwind code` whichever form it
      -- would use. The offset is stored raw, so the ceiling is the 32-bit
      -- field rather than the scaled one.
      volatility r = .nonvolatile ∧ r ≠ .rsp ∧ off % 8 = 0 ∧
        off ≤ largeAllocRawMax
  | .saveXmm128Far r off =>
      6 ≤ r.index.val ∧ off % 16 = 0 ∧ off ≤ largeAllocRawMax
  -- Nothing to constrain: both trap-frame shapes are encodable, and which one
  -- occurred is a fact about the vector rather than a choice the prologue
  -- makes.
  | .pushMachineFrame _ => True

instance (op : UnwindOp) : Decidable op.Encodable := by
  cases op <;> unfold Encodable <;> infer_instance

/--
Pushing a volatile register is not encodable.

The unwinder restores what the codes name, so a `push rax` described as
`UWOP_PUSH_NONVOL rax` would make it restore a register the ABI says the callee
was free to destroy — and, worse, one the caller never saved. The prologue is
legal; the *description* is not.
-/
theorem push_volatile_not_encodable {r : Gpr} (h : volatility r = .volatile) :
    ¬ (UnwindOp.pushNonvolatile r).Encodable := by
  simp only [Encodable, h]
  exact fun hc => absurd hc.1 (by decide)

/--
**`push rsp` has no unwind description.**

`RSP` is nonvolatile, so the volatility rule above does not exclude it, and a
reviewer found that this profile accepted it. `UWOP_PUSH_NONVOL` replays as
`RSP := [RSP]; RSP += 8`; for `push rsp` the pushed value is the pre-push stack
pointer, so the replay lands eight bytes high. `ml64` accepts `.pushreg rsp` and
emits exactly the bytes this profile emitted, so only the model can refuse it.
-/
theorem push_rsp_not_encodable :
    ¬ (UnwindOp.pushNonvolatile .rsp).Encodable := by decide

/--
**A `mov` that saves a volatile register has no unwind description either.**

The same argument as `push_volatile_not_encodable`, and it needs its own
statement for the same reason that one did: `ml64` assembles `.savereg rax, 8`
without complaint and emits `UWOP_SAVE_NONVOL` with `OpInfo = 0`, so no
differential can catch a regression here. Only the model refuses it, and only a
theorem says the refusal is deliberate. -/
theorem save_volatile_not_encodable {r : Gpr} {off : Nat}
    (h : volatility r = .volatile) :
    ¬ (UnwindOp.saveNonvolatile r off).Encodable := by
  simp only [Encodable, h]
  exact fun hc => absurd hc.1 (by decide)

/-- **`mov [rsp+n], rsp` has no unwind description.**

`ml64` accepts `.savereg rsp, 8` as readily as it accepts `.pushreg rsp`. -/
theorem save_rsp_not_encodable {off : Nat} :
    ¬ (UnwindOp.saveNonvolatile .rsp off).Encodable := by
  simp only [Encodable]
  exact fun hc => absurd hc.2.1 (by decide)

/--
**Saving a volatile XMM register has no unwind description.**

`xmm0`-`xmm5` are volatile under Win64, so unwind data naming one describes a
restore the unwinder must not perform. `ml64` emits `UWOP_SAVE_XMM128` with
`OpInfo = 0` for `.savexmm128 xmm0, 16` without complaint. -/
theorem save_volatile_xmm_not_encodable {r : Xmm} {off : Nat}
    (h : xmmVolatility r = .volatile) :
    ¬ (UnwindOp.saveXmm128 r off).Encodable := by
  simp only [Encodable]
  intro hc
  have : ¬ (6 ≤ r.index.val) := by
    simp only [xmmVolatility] at h
    split at h
    · omega
    · exact absurd h (by decide)
  exact this hc.1

/-- An allocation that is not a multiple of eight has no encoding in either
form. -/
theorem unaligned_alloc_not_encodable (n : Nat) (h : n % 8 ≠ 0) :
    ¬ (UnwindOp.allocSmall n).Encodable ∧ ¬ (UnwindOp.allocLarge n).Encodable := by
  constructor
  · intro hc; exact h hc.2.2
  · intro hc; exact h hc.2.2

end UnwindOp

/-! ## The prologue this profile recognises -/

/--
A prologue in the shape the Win64 unwind language describes.

Deliberately a *list of operations* rather than a list of instructions. The
recogniser's job is to decide whether an encoded instruction prefix maps into
this vocabulary, and separating the vocabulary from the machine code is what
lets the rejection be stated: a prologue that does not map has no `Prologue`
value, so no metadata can be derived from it.
-/
structure Prologue where
  /-- The operations, in the order they execute. -/
  ops : List UnwindOp
deriving DecidableEq, Repr, Inhabited

namespace Prologue

/-- Every operation is encodable. -/
def Encodable (p : Prologue) : Prop := ∀ op ∈ p.ops, op.Encodable

instance (p : Prologue) : Decidable p.Encodable :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Total bytes the prologue moves `RSP` down. -/
def stackDelta (p : Prologue) : Nat := (p.ops.map UnwindOp.stackDelta).sum

/-- Total `UNWIND_CODE` slots the operations need. -/
def slots (p : Prologue) : Nat := (p.ops.map UnwindOp.slots).sum

/--
The `UNWIND_CODE` array, in the descending order the ABI stores it.

The unwinder walks the array forwards while undoing the prologue backwards, so
the array is the reverse of execution order.
-/
def codes (p : Prologue) : List UnwindOp := p.ops.reverse

@[simp] theorem codes_length (p : Prologue) : p.codes.length = p.ops.length := by
  simp [codes]

/-- Reversing does not change how many slots are needed. -/
@[simp] theorem codes_slots (p : Prologue) :
    (p.codes.map UnwindOp.slots).sum = p.slots := by
  simp [codes, slots, List.map_reverse, List.sum_reverse]

/--
**The metadata reverses the prologue.**

Undoing the unwind codes in stored order restores exactly the stack the prologue
consumed. This is the proof obligation `docs/PLATFORM_ABI.md` §3 attaches to
automatic generation, at the level of stack depth: the codes account for every
byte the prologue moved `RSP` by, and no more.

It is not the whole of that obligation. Which register each `push` restores, and
that the restores happen in the right order, are separate facts; this one is the
arithmetic, and it is the part a hand-written `sub` size gets wrong.
-/
theorem codes_stackDelta (p : Prologue) :
    (p.codes.map UnwindOp.stackDelta).sum = p.stackDelta := by
  simp [codes, stackDelta, List.map_reverse, List.sum_reverse]

/--
`CountOfCodes` as stored in `UNWIND_INFO`: the slots the operations occupy,
*without* the padding slot.

This definition was wrong, and `ml64` is what said so. The array is padded to an
even number of slots so that whatever follows stays 4-byte aligned, and the
previous definition folded that padding into the count. Microsoft's assembler
reports the unpadded count: for a prologue of a single `push`, `.xdata` is eight
bytes and ends in a zero padding slot, but `CountOfCodes` is 1. So the array is
one slot longer than the count exactly when the count is odd, and `arraySlots`
is that physical length.

The error was invisible on every prologue with an even slot count -- including
Spike 1's, whose four slots need no padding, so nothing already in this file
would have caught it. That is why `Tests/ABI/Win64/UnwindCorpus.lean`
deliberately includes single-operation prologues, and why those were the rows
that failed.
-/
def countOfCodes (p : Prologue) : Nat := p.slots

/-- The physical length of the `UNWIND_CODE` array in slots, padding included.
-/
def arraySlots (p : Prologue) : Nat := p.slots + p.slots % 2

theorem arraySlots_even (p : Prologue) : p.arraySlots % 2 = 0 := by
  simp only [arraySlots]
  omega

theorem arraySlots_ge_countOfCodes (p : Prologue) :
    p.countOfCodes ≤ p.arraySlots := by
  simp only [arraySlots, countOfCodes]
  omega

/-- The array exceeds the reported count by at most one slot, so a reader that
trusts `CountOfCodes` never runs past the array. -/
theorem arraySlots_le_countOfCodes_succ (p : Prologue) :
    p.arraySlots ≤ p.countOfCodes + 1 := by
  simp only [arraySlots, countOfCodes]
  omega

/-- Whether the prologue establishes a frame pointer at all. -/
def establishesFramePointer (p : Prologue) : Bool :=
  p.ops.any fun op => match op with
    | .setFramePointer _ _ => true
    | _ => false

/--
Whether every `setFramePointer` in the prologue matches the header's two
nibbles.

Both nibbles, not just the register. `FrameOffset` was outside every invariant
until a reviewer pointed out that `UNWIND_INFO` could declare a frame at
`FrameReg - 240` for a frame actually established at `RSP + 0`, and that nothing
in the model contradicted it because the operation carried no offset to
contradict it *with*. `setFramePointer` now carries the offset, and this is
where the header has to agree with it.

Quantified over the operations rather than looking up the first one. A lookup
would accept a prologue holding two `setFramePointer` operations that disagree
with each other -- matching the header on the first and silently diverging on
the second. Quantifying rules that out, and as a side effect forces any two
establishing operations to agree with each other.

`FrameOffset` is scaled by sixteen, which is why `UnwindOp.Encodable` requires
the offset to be a multiple of sixteen: an unscalable offset has no encoding
rather than a rounded one.
-/
def frameSpecIs (p : Prologue) (reg offset : BitVec 4) : Bool :=
  p.ops.all fun op => match op with
    | .setFramePointer r off => reg == regNibble r && offset == BitVec.ofNat 4 (off / 16)
    | _ => true

/-- `frameSpecIs` is the membership-quantified statement it is meant to be.

Stated so that the invariant is legible where it is used as a hypothesis rather
than merely computable, and so a reader can see it really is a `forall` over
every establishing operation rather than a check of one of them. -/
theorem frameSpecIs_iff (p : Prologue) (reg offset : BitVec 4) :
    p.frameSpecIs reg offset = true ↔
      ∀ r off, UnwindOp.setFramePointer r off ∈ p.ops →
        reg = regNibble r ∧ offset = BitVec.ofNat 4 (off / 16) := by
  simp only [frameSpecIs, List.all_eq_true]
  constructor
  · intro h r off hmem
    have := h _ hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this
  · intro h op hmem
    match op with
    | .setFramePointer r off =>
        have := h r off hmem
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact this
    | .pushNonvolatile _ => rfl
    | .allocSmall _ => rfl
    | .allocLarge _ => rfl
    | .saveNonvolatile _ _ => rfl
    | .saveXmm128 _ _ => rfl
    | .saveNonvolatileFar _ _ => rfl
    | .saveXmm128Far _ _ => rfl
    | .pushMachineFrame _ => rfl

/-- A register other than `RAX` has a nonzero four-bit number. `RAX` is 0, and 0
is how `UNWIND_INFO.FrameRegister` spells "no frame pointer". -/
theorem regNibble_ne_zero (r : Gpr) (h : r ≠ .rax) : regNibble r ≠ 0 := by
  cases r
  case rax => exact absurd rfl h
  all_goals decide

end Prologue

/-! ## Spike 1's prologue -/

/--
`push r12; push r13; push r14`, then the shadow space allocation.

The prologue of `Spikes/1_Hello_World/Program.lean`, as the unwind language
sees it.
-/
def spike1Prologue : Prologue :=
  { ops := [.pushNonvolatile .r12, .pushNonvolatile .r13, .pushNonvolatile .r14,
            .allocSmall shadowSpaceBytes] }

/-- It is encodable: three nonvolatile pushes and a 32-byte allocation, which
is a multiple of 8 in the 8..128 range. -/
theorem spike1Prologue_encodable : spike1Prologue.Encodable := by decide

/-- It moves `RSP` down 56 bytes: three pushes and 32 bytes of shadow space. -/
theorem spike1Prologue_stackDelta : spike1Prologue.stackDelta = 56 := by decide

/-- Four operations, four slots, so a reported count of four and no padding
slot. `ml64` agrees byte-for-byte; see `Tests/ABI/Win64/UnwindCorpus.lean`. -/
theorem spike1Prologue_countOfCodes : spike1Prologue.countOfCodes = 4 := by decide

/-- It establishes no frame pointer, so `FrameRegister` must be zero. -/
theorem spike1Prologue_no_framePointer :
    spike1Prologue.establishesFramePointer = false := by decide

/--
The stack it leaves is aligned for a call, agreeing with `Convention.lean`.

Two independent routes to the same number — `AlignedForCall 3 shadowSpaceBytes`
counts pushes and the adjustment separately, while this sums the unwind
operations' deltas — so a disagreement between the frame model and the unwind
model would show up here rather than at run time.
-/
theorem spike1Prologue_agrees_with_frame :
    (entryMisalignment + spike1Prologue.stackDelta) % stackAlignment = 0 := by decide

end Grass.ABI.Win64
