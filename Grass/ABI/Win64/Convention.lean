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

That is an open obligation rather than a claim of coverage, and what remains
open has narrowed since it was written.

The XMM half is closed. `Grass.ABI.Win64.UnwindOp` gained `saveXmm128`, so the
unwind language can describe an XMM save, and `xmmVolatility` below now says
which registers a callee must preserve -- `xmm0`-`xmm5` volatile,
`xmm6`-`xmm15` not. An earlier version of this paragraph said this table
"still cannot say" that, and went on saying it after `xmmVolatility` was added
twelve lines further down. It was a false claim about the file it was written
in.

`MXCSR`, the x87 control word and the direction-flag rule are still not named
anywhere here, and that is the obligation that survives. Those are not register
classes but *mode* state, which a caller reasoning from this table would
assume unchanged across a call and which the convention constrains
independently of any register's volatility.
-/

/-- Which XMM registers a callee must preserve.

`xmm0`-`xmm5` are volatile and `xmm6`-`xmm15` are nonvolatile under the Windows
x64 convention. Stated here rather than left as the literal `6` it was written
as inside `Grass.ABI.Win64.UnwindOp.Encodable`: a bare bound in a predicate is
an external ABI fact with no declaration to cite, no ledger row and no way for a
reader to find it, and a reviewer pointed out the same number was also spelled
independently in the corpus filter, so two copies of an unnamed fact had to
agree by hand. -/
def xmmVolatility (r : Xmm) : Volatility :=
  if r.index.val < 6 then .volatile else .nonvolatile

/-- `xmm6` onward are the preserved ones, which is the fact
`Grass.ABI.Win64.UnwindOp.Encodable` relies on when it refuses to describe a
save of a volatile XMM register. -/
theorem xmmVolatility_nonvolatile_iff (r : Xmm) :
    xmmVolatility r = .nonvolatile ↔ 6 ≤ r.index.val := by
  simp only [xmmVolatility]
  split <;> simp_all <;> omega

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

/--
Spike 1's prologue pushes `r12`, `r13` and `r14` — three registers — and then
needs shadow space for its calls.

Three pushes align the stack, so the 32 bytes of shadow space are all that the
`sub` has to provide, and they preserve alignment because 32 is a multiple of
16.
-/
theorem spike1_prologue_aligned : AlignedForCall 3 shadowSpaceBytes := by decide

/-- The same prologue without the shadow space is still aligned, which is why
the two concerns must be checked separately: alignment does not imply the
shadow space is there. -/
theorem spike1_prologue_aligned_without_shadow : AlignedForCall 3 0 := by decide

end Grass.ABI.Win64
