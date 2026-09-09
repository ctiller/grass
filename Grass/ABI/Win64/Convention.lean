import Grass.ISA.X86.Register

/-!
# The Microsoft x64 calling convention

Register classification, argument placement, shadow space and stack alignment
for the Win64 ABI that `docs/DECISIONS.md` 16 selects.

## One authority, not two

`docs/DECISIONS.md` 15 makes the *ISA* the dual-cited intersection of Intel and
AMD, and `Grass/ISA/X86/DualCitation.lean` enforces that. None of it applies
here. A calling convention is not an architectural fact that two vendors
independently guarantee; it is a contract Microsoft defines for its platform,
and Intel and AMD have nothing to say about it. So the citations below are
single-sourced by construction, and using `DualCitation` for them would be
performing a rigour the subject does not have.

`docs/VALIDATION.md` §1 still applies in full: stable identity, revision,
retrieval location, exact anchor, and a locator.

## What makes this ABI easy to get wrong

Four things, and Spike 1 touches all four.

- **Shadow space is the caller's job and is always present.** Every call site
  reserves 32 bytes above the return address, even for a function taking no
  arguments, and even though the arguments were passed in registers. A callee
  may write its register arguments there. Omitting it does not fail at the call;
  it corrupts whatever was below.

- **Argument registers are assigned by position, not by type.** The fourth
  argument goes in `R9` whether or not the first three were integers, and a
  floating-point argument in position 2 uses `XMM1` while `RDX` is *reserved and
  skipped* rather than reused. `argumentRegister` is therefore a function of the
  index alone.

- **Alignment is stated at the wrong place to be convenient.** `RSP` is 16-byte
  aligned *before* the `CALL`, so at the callee's first instruction it is
  congruent to 8 — the return address is in the way. Every prologue that fails
  to account for the odd 8 bytes misaligns everything below it.

- **`RDI` and `RSI` are nonvolatile here** and volatile in the System V
  convention. Code ported between the two, or a model reused between them,
  silently loses their contents.
-/

namespace Grass.ABI.Win64

open Grass.Core Grass.Cite Grass.ISA.X86

/-! ## Register classification -/

/--
Whether a call preserves a register, as `volatility` classifies it.

`docs/PLATFORM_ABI.md` §3: "Over-approximating clobbers or resource use is
acceptable. Omitting a permitted behavior is unsound." So the asymmetry matters:
classifying a nonvolatile register as volatile costs a spill, while classifying
a volatile one as nonvolatile is a wrong theorem about what survives a call.
-/
inductive Volatility where
  /-- The callee may destroy it. The caller saves it if it cares. -/
  | volatile
  /-- The callee must restore it before returning. -/
  | nonvolatile
deriving DecidableEq, Repr, Inhabited

/--
How the Win64 convention classifies each general-purpose register.

Written as a table because that is what it is. `RDI` and `RSI` are the entries
to check against a System V habit: they are **nonvolatile** here.

`RSP` is listed nonvolatile, which is true but understates the contract — it is
not merely preserved, it is the stack pointer, and a callee that restored a
different value than it received would break unwinding as well as the caller.
-/
def volatility : Gpr → Volatility
  | .rax => .volatile
  | .rcx => .volatile
  | .rdx => .volatile
  | .rbx => .nonvolatile
  | .rsp => .nonvolatile
  | .rbp => .nonvolatile
  | .rsi => .nonvolatile
  | .rdi => .nonvolatile
  | .r8 => .volatile
  | .r9 => .volatile
  | .r10 => .volatile
  | .r11 => .volatile
  | .r12 => .nonvolatile
  | .r13 => .nonvolatile
  | .r14 => .nonvolatile
  | .r15 => .nonvolatile

/-!
### What this table does not cover

General-purpose registers only. XMM6-XMM15 are nonvolatile on Win64 and MSVC
saves them in ordinary mixed integer/float code -- a reviewer found 24
`UWOP_SAVE_XMM128` codes across 24 optimised C functions, and
`int mixed(int, double, int, double)` emits `movaps [rsp+48], xmm6`. Nothing
here names the XMM class, `MXCSR`, the x87 control word, or the direction-flag
rule, and `docs/PLATFORM_ABI.md` section 3's "omitting a permitted behavior is
unsound" applies to a caller reasoning from this table about a callee that
touches them.

That is an open obligation rather than a claim of coverage. It is the same gap
`Grass.ABI.Win64.UnwindOp` measures from the other side: its four constructors
have no `UWOP_SAVE_XMM128`, and that omission accounts for most of what this
profile cannot describe.
-/

/-- The registers a call may destroy. -/
def volatileRegisters : List Gpr := Gpr.all.filter (fun r => volatility r == .volatile)

/-- The registers a call must preserve. -/
def nonvolatileRegisters : List Gpr :=
  Gpr.all.filter (fun r => volatility r == .nonvolatile)

/-- Every register is classified exactly one way. -/
theorem volatility_total (r : Gpr) :
    (volatility r = .volatile) ∨ (volatility r = .nonvolatile) := by
  cases r <;> simp [volatility]

/-- The two classes are disjoint. -/
theorem volatile_not_nonvolatile (r : Gpr) :
    r ∈ volatileRegisters → r ∉ nonvolatileRegisters := by
  cases r <;> decide

/-- Together they account for all sixteen registers, so no register is
unclassified. `docs/INSTRUCTIONS.md` §1: missing metadata is rejection, not a
default. -/
theorem classification_covers_all :
    volatileRegisters.length + nonvolatileRegisters.length = 16 := by decide

/-- `rsi` and `rdi` are preserved, unlike System V. Stated as a theorem because
it is the difference a reader is most likely to carry in wrong. -/
theorem rsi_rdi_nonvolatile :
    volatility .rsi = .nonvolatile ∧ volatility .rdi = .nonvolatile :=
  ⟨rfl, rfl⟩

/-! ## Argument placement -/

/--
The register carrying integer argument `index`, counting from zero.

`none` for index 4 and beyond: those arguments are on the stack.

A function of the index alone, because that is how the convention works. A
floating-point argument at index 1 uses `XMM1` and *reserves* `RDX` rather than
letting the next integer argument use it, so there is no "next available
register" to track. Modeling it as an allocator would be both more complex and
wrong.
-/
def argumentRegister (index : Nat) : Option Gpr :=
  match index with
  | 0 => some .rcx
  | 1 => some .rdx
  | 2 => some .r8
  | 3 => some .r9
  | _ => Option.none

/-- The registers used for integer arguments, in order. -/
def argumentRegisters : List Gpr := [.rcx, .rdx, .r8, .r9]

/-- How many arguments are passed in registers. -/
def registerArgumentCount : Nat := 4

@[simp] theorem argumentRegister_beyond (index : Nat)
    (h : registerArgumentCount ≤ index) : argumentRegister index = Option.none := by
  match index, h with
  | 0, h => exact absurd h (by decide)
  | 1, h => exact absurd h (by decide)
  | 2, h => exact absurd h (by decide)
  | 3, h => exact absurd h (by decide)
  | (_ + 4), _ => rfl

/-- Every argument register is volatile, so a callee may use them freely and a
caller may not expect an argument to survive the call it passed it to. -/
theorem argumentRegisters_volatile (r : Gpr) (h : r ∈ argumentRegisters) :
    volatility r = .volatile := by
  revert h; cases r <;> decide

/-- Distinct argument positions use distinct registers. -/
theorem argumentRegister_injective {i j : Nat} {r : Gpr}
    (hi : argumentRegister i = some r) (hj : argumentRegister j = some r) : i = j := by
  match i, j with
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 => rfl
  | 0, 1 | 0, 2 | 0, 3 | 1, 0 | 1, 2 | 1, 3
  | 2, 0 | 2, 1 | 2, 3 | 3, 0 | 3, 1 | 3, 2 =>
      simp only [argumentRegister, Option.some.injEq] at hi hj
      exact absurd (hi.trans hj.symm) (by decide)
  | 0, (_ + 4) | 1, (_ + 4) | 2, (_ + 4) | 3, (_ + 4) => exact absurd hj (by simp [argumentRegister])
  | (_ + 4), _ => exact absurd hi (by simp [argumentRegister])

/-! ## The stack frame at a call -/

/--
Bytes the caller reserves above the return address for the callee to spill its
register arguments into.

Always present, always this size, and always the caller's responsibility — even
when the callee takes no arguments at all, and even though the arguments were
passed in registers. A callee is entitled to write here without allocating
anything.
-/
def shadowSpaceBytes : Nat := 32

/-- Shadow space holds exactly one 8-byte slot per register argument. -/
theorem shadowSpace_matches_argumentRegisters :
    shadowSpaceBytes = registerArgumentCount * 8 := rfl

/-- The required stack alignment at a call site, in bytes. -/
def stackAlignment : Nat := 16

/--
`RSP` modulo `stackAlignment` at the callee's first instruction.

Not zero. The convention requires `RSP` to be 16-byte aligned *before* the
`CALL`; the call then pushes an 8-byte return address, so the callee begins with
`RSP ≡ 8 (mod 16)`. Every prologue has to account for that odd 8 bytes, and a
frame computed as though entry were aligned is misaligned everywhere below.
-/
def entryMisalignment : Nat := 8

theorem entryMisalignment_lt_alignment : entryMisalignment < stackAlignment := by decide

/--
`RSP` modulo 16 after a prologue that pushes `pushes` registers and then
subtracts `subtracted` bytes, starting from function entry.

Each push moves `RSP` down 8. The caller wants this to be `0` at any `CALL` it
makes.
-/
def rspAfterPrologue (pushes subtracted : Nat) : Nat :=
  (entryMisalignment + stackAlignment * (pushes + subtracted)
    - (pushes * 8 + subtracted)) % stackAlignment

/-- The prologue leaves the stack aligned for a call. -/
def AlignedForCall (pushes subtracted : Nat) : Prop :=
  rspAfterPrologue pushes subtracted = 0

instance (pushes subtracted : Nat) : Decidable (AlignedForCall pushes subtracted) :=
  inferInstanceAs (Decidable (_ = _))

/--
An odd number of pushes with no adjustment leaves the stack aligned.

The entry misalignment and one push cancel, which is why a leaf-ish function
that pushes three nonvolatile registers and calls something needs no `sub rsp`
for alignment — only for shadow space.
-/
theorem odd_pushes_align (k : Nat) : AlignedForCall (2 * k + 1) 0 := by
  simp only [AlignedForCall, rspAfterPrologue, entryMisalignment, stackAlignment]
  omega

/-- An even number of pushes with no adjustment does not. -/
theorem even_pushes_misalign (k : Nat) : ¬ AlignedForCall (2 * k) 0 := by
  simp only [AlignedForCall, rspAfterPrologue, entryMisalignment, stackAlignment]
  omega

/-! ## Computed call-frame layouts -/
/-- Inputs to the bounded Win64 call-frame calculation.  Argument and local
descriptions are supplied by the caller; this type does not extract them from a
typed signature or generate machine instructions. -/
structure CallFrameLayout where
  argumentCount : Nat
  localBytes : Nat
  localAlignment : Nat
  savedRegisters : List Gpr

namespace CallFrameLayout

/-- Valid local alignments are positive divisors of the ABI stack alignment. -/
def Admissible (layout : CallFrameLayout) : Prop :=
  0 < layout.localAlignment ∧ stackAlignment % layout.localAlignment = 0

instance (layout : CallFrameLayout) : Decidable layout.Admissible :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Round an offset upward to the requested alignment. -/
def alignUp (value alignment : Nat) : Nat :=
  value + (alignment - value % alignment) % alignment

/-- Stack-passed arguments beyond the four register positions. -/
def stackArgumentBytes (layout : CallFrameLayout) : Nat :=
  (layout.argumentCount - registerArgumentCount) * 8

/-- The local begins after shadow space and all stack argument slots. -/
def localOffset (layout : CallFrameLayout) : Nat :=
  alignUp (shadowSpaceBytes + layout.stackArgumentBytes) layout.localAlignment

/-- Bytes occupied before final call-alignment padding. -/
def usedCallAllocationBytes (layout : CallFrameLayout) : Nat :=
  layout.localOffset + layout.localBytes

/-- The least adjustment represented by this calculation: occupied bytes plus
the current `RSP` residue that must also be subtracted before a call. -/
def callAllocationBytes (layout : CallFrameLayout) : Nat :=
  let used := layout.usedCallAllocationBytes
  used + (entryMisalignment + stackAlignment -
    (layout.savedRegisters.length * 8 + used) % stackAlignment) % stackAlignment

/-- Saved-register pushes plus the outgoing call allocation. -/
def totalFrameBytes (layout : CallFrameLayout) : Nat :=
  layout.savedRegisters.length * 8 + layout.callAllocationBytes

/-- Offset from post-prologue `RSP` to a saved register, indexed in push order.
The last register pushed is nearest the allocation. -/
def savedRegisterOffset (layout : CallFrameLayout) (index : Nat) : Nat :=
  layout.callAllocationBytes + 8 * (layout.savedRegisters.length - 1 - index)

theorem stackArguments_end_before_local (layout : CallFrameLayout) :
    shadowSpaceBytes + layout.stackArgumentBytes ≤ layout.localOffset := by
  simp only [localOffset, alignUp]
  omega

theorem localOffset_aligned (layout : CallFrameLayout) (valid : layout.Admissible) :
    layout.localOffset % layout.localAlignment = 0 := by
  rcases valid with ⟨positive, _⟩
  simp only [localOffset, alignUp]
  let value := shadowSpaceBytes + layout.stackArgumentBytes
  let remainder := value % layout.localAlignment
  have remainder_lt : remainder < layout.localAlignment := Nat.mod_lt _ positive
  by_cases zero : remainder = 0
  · simp [value, remainder, zero]
  · have padding_lt : layout.localAlignment - remainder < layout.localAlignment := by omega
    have padding_mod :
        (layout.localAlignment - remainder) % layout.localAlignment =
          layout.localAlignment - remainder := Nat.mod_eq_of_lt padding_lt
    change (value + (layout.localAlignment - remainder) %
      layout.localAlignment) % layout.localAlignment = 0
    rw [padding_mod]
    have fills : remainder + (layout.localAlignment - remainder) =
        layout.localAlignment := Nat.add_sub_of_le (Nat.le_of_lt remainder_lt)
    have fillsMod : remainder +
        (layout.localAlignment - remainder) % layout.localAlignment =
        layout.localAlignment := by rw [padding_mod, fills]
    rw [Nat.add_mod, show value % layout.localAlignment = remainder from rfl,
      fillsMod, Nat.mod_self]

theorem allocation_contains_local (layout : CallFrameLayout) :
    layout.localOffset + layout.localBytes ≤ layout.callAllocationBytes := by
  simp only [callAllocationBytes, usedCallAllocationBytes]
  omega

theorem callAllocation_aligned (layout : CallFrameLayout) :
    AlignedForCall layout.savedRegisters.length layout.callAllocationBytes := by
  simp only [AlignedForCall, callAllocationBytes, rspAfterPrologue,
    entryMisalignment, stackAlignment]
  omega

theorem savedRegisterOffset_at_or_above_allocation (layout : CallFrameLayout)
    (index : Nat) (_inRange : index < layout.savedRegisters.length) :
    layout.callAllocationBytes ≤ layout.savedRegisterOffset index := by
  simp only [savedRegisterOffset]
  omega

/-- Every in-range saved-register slot fits inside the computed total frame. -/
theorem savedRegisterSlot_fits (layout : CallFrameLayout) (index : Nat)
    (inRange : index < layout.savedRegisters.length) :
    layout.savedRegisterOffset index + 8 ≤ layout.totalFrameBytes := by
  simp only [savedRegisterOffset, totalFrameBytes]
  omega

/-- Later pushes occupy lower addresses than earlier pushes, with disjoint
eight-byte slots. -/
theorem savedRegisterSlots_ordered (layout : CallFrameLayout) {earlier later : Nat}
    (ordered : earlier < later) (inRange : later < layout.savedRegisters.length) :
    layout.savedRegisterOffset later + 8 ≤ layout.savedRegisterOffset earlier := by
  simp only [savedRegisterOffset]
  omega

/-- Distinct in-range saved-register indices denote disjoint byte intervals. -/
theorem savedRegisterSlots_disjoint (layout : CallFrameLayout) {left right : Nat}
    (leftInRange : left < layout.savedRegisters.length)
    (rightInRange : right < layout.savedRegisters.length) (distinct : left ≠ right) :
    layout.savedRegisterOffset left + 8 ≤ layout.savedRegisterOffset right ∨
      layout.savedRegisterOffset right + 8 ≤ layout.savedRegisterOffset left := by
  rcases Nat.lt_or_gt_of_ne distinct with ordered | ordered
  · exact Or.inr (layout.savedRegisterSlots_ordered ordered rightInRange)
  · exact Or.inl (layout.savedRegisterSlots_ordered ordered leftInRange)

end CallFrameLayout

/-- Spike 1's saved registers, in machine push order. -/
def spike1SavedRegisters : List Gpr := [.r12, .r13, .r14]

/-- The manually supplied Spike 1 inputs to the generic frame calculation. -/
def spike1FrameLayout : CallFrameLayout where
  argumentCount := 5
  localBytes := 4
  localAlignment := 4
  savedRegisters := spike1SavedRegisters

theorem spike1FrameLayout_admissible : spike1FrameLayout.Admissible := by decide

/-- The computed call allocation: shadow space, fifth-argument slot, separate
four-byte local, and whatever final alignment the calculation requires. -/
def spike1CallAllocationBytes : Nat := spike1FrameLayout.callAllocationBytes

theorem spike1_stackArgumentBytes : spike1FrameLayout.stackArgumentBytes = 8 := by decide
theorem spike1_localOffset : spike1FrameLayout.localOffset = 40 := by decide
theorem spike1_callAllocationBytes : spike1CallAllocationBytes = 48 := by decide
theorem spike1_totalFrameBytes : spike1FrameLayout.totalFrameBytes = 72 := by decide

theorem spike1_savedRegisterOffsets :
    spike1FrameLayout.savedRegisterOffset 0 = 64 ∧
    spike1FrameLayout.savedRegisterOffset 1 = 56 ∧
    spike1FrameLayout.savedRegisterOffset 2 = 48 := by decide

/-- Spike 1's call alignment is an instance of the generic layout contract. -/
theorem spike1_prologue_aligned : AlignedForCall 3 spike1CallAllocationBytes := by
  simpa [spike1FrameLayout, spike1SavedRegisters, spike1CallAllocationBytes] using
    spike1FrameLayout.callAllocation_aligned

/-- The same prologue without the shadow space is still aligned, which is why
the two concerns must be checked separately: alignment does not imply the
shadow space is there. -/
theorem spike1_prologue_aligned_without_shadow : AlignedForCall 3 0 := by decide

end Grass.ABI.Win64
