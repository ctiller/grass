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
establish a frame pointer, save a register at a constant offset. So
`UnwindOp.Encodable` rejects a stack adjustment that is not a constant multiple
of eight and a push of a volatile register, and a prologue interleaving other
work between the pushes has no `Prologue` value at all.

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
deriving DecidableEq, Repr, Inhabited

namespace UnwindOp

/-- The `UnwindOp` nibble stored in the code. -/
def opcode : UnwindOp → BitVec 4
  | .pushNonvolatile _ => 0
  | .allocLarge _ => 1
  | .allocSmall _ => 2
  | .setFramePointer _ _ => 3

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
  | .allocLarge _ => 2
  | .setFramePointer _ _ => 1

/-- Every operation occupies at least one slot. -/
theorem slots_pos (op : UnwindOp) : 0 < op.slots := by
  cases op <;> simp [slots]

/-- How many bytes this operation moves `RSP` down by in the prologue. -/
def stackDelta : UnwindOp → Nat
  | .pushNonvolatile _ => 8
  | .allocSmall n => n
  | .allocLarge n => n
  | .setFramePointer _ _ => 0

/-- The `OpInfo` nibble.

For a push it is the four-bit register number. For an allocation it is a size
encoding and not a register at all: `allocSmall` stores `n/8 - 1`, and
`allocLarge` stores 0 because its size goes in a following slot.

For `setFramePointer` it is the frame register's number, and that is a recorded
disagreement rather than a derivation. Microsoft's description of
`UWOP_SET_FPREG` says the operation info field is reserved and should not be
used, which reads as licence to write anything, including zero. `ml64` writes
the register: `.setframe r13, 16` produces the code byte `D3`, not `03`, as
`Tools/win64-unwind-differential.py` measured on this machine. Grass follows the
vendor's generator over the vendor's prose, because matching it byte-for-byte
makes the differential exact -- and `docs/VALIDATION.md` section 2 asks for such
a conflict to be preserved rather than smoothed over, which is what this
paragraph is. Nothing rests on the choice: the unwinder takes the register from
`FrameRegister`. -/
def opInfo : UnwindOp → BitVec 4
  | .pushNonvolatile r => regNibble r
  | .allocSmall n => BitVec.ofNat 4 (n / 8 - 1)
  | .allocLarge _ => 0
  | .setFramePointer r _ => regNibble r

/--
The allocation sizes `allocSmall` can encode: multiples of 8 from 8 to 128.

`OpInfo` is four bits holding `n/8 - 1`, so `n = 8` is `0` and `n = 128` is
`15`. An allocation of 136 needs `allocLarge`, and one of 12 cannot be encoded
at all because it is not a multiple of 8.
-/
def SmallAllocEncodable (n : Nat) : Prop := 8 ≤ n ∧ n ≤ 128 ∧ n % 8 = 0

instance (n : Nat) : Decidable (SmallAllocEncodable n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `allocLarge` with `OpInfo = 0` stores `n/8` in one 16-bit slot, so it
reaches 8 to 512K-8, and still only multiples of 8. -/
def LargeAllocEncodable (n : Nat) : Prop := 8 ≤ n ∧ n < 524288 ∧ n % 8 = 0

instance (n : Nat) : Decidable (LargeAllocEncodable n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The operation is one this profile can actually encode. -/
def Encodable : UnwindOp → Prop
  | .pushNonvolatile r => volatility r = .nonvolatile
  | .allocSmall n => SmallAllocEncodable n
  | .allocLarge n => LargeAllocEncodable n
  | .setFramePointer r off =>
      volatility r = .nonvolatile ∧ r ≠ .rsp ∧ off % 16 = 0 ∧ off ≤ 240

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
  exact fun hc => absurd hc (by decide)

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
