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
  /-- `UWOP_SET_FPREG` (3): establish the frame pointer from `RSP`. -/
  | setFramePointer
deriving DecidableEq, Repr, Inhabited

namespace UnwindOp

/-- The `UnwindOp` nibble stored in the code. -/
def opcode : UnwindOp → BitVec 4
  | .pushNonvolatile _ => 0
  | .allocLarge _ => 1
  | .allocSmall _ => 2
  | .setFramePointer => 3

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
  | .setFramePointer => 1

/-- Every operation occupies at least one slot. -/
theorem slots_pos (op : UnwindOp) : 0 < op.slots := by
  cases op <;> simp [slots]

/-- How many bytes this operation moves `RSP` down by in the prologue. -/
def stackDelta : UnwindOp → Nat
  | .pushNonvolatile _ => 8
  | .allocSmall n => n
  | .allocLarge n => n
  | .setFramePointer => 0

/-- The `OpInfo` nibble.

For a push it is the four-bit register number: the REX bit is the *high* bit and
`encodingBits` the low three, so `r12` is 12 and not 4. For an allocation it is
a size encoding and not a register at all. -/
def opInfo : UnwindOp → BitVec 4
  | .pushNonvolatile r => BitVec.ofBool r.rexBit ++ r.encodingBits
  | .allocSmall n => BitVec.ofNat 4 (n / 8 - 1)
  | .allocLarge _ => 0
  | .setFramePointer => 0

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
  | .setFramePointer => True

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
`CountOfCodes` as stored in `UNWIND_INFO`.

The array is padded to an even number of slots so the structure that follows it
stays 4-byte aligned. The padding slot is part of the count, so a generator that
reported the unpadded count would describe an array one slot shorter than the
one it wrote.
-/
def countOfCodes (p : Prologue) : Nat := p.slots + p.slots % 2

theorem countOfCodes_even (p : Prologue) : p.countOfCodes % 2 = 0 := by
  simp only [countOfCodes]
  omega

theorem countOfCodes_ge_slots (p : Prologue) : p.slots ≤ p.countOfCodes := by
  simp only [countOfCodes]
  omega

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

/-- Four operations, four slots, and the count pads to four because four is
already even. -/
theorem spike1Prologue_countOfCodes : spike1Prologue.countOfCodes = 4 := by decide

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
