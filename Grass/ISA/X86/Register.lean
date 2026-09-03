import Grass.ISA.X86.Sources

/-!
# General-purpose registers and operand-size write behaviour

The 16 general-purpose registers of 64-bit mode, their encoding numbers, and the
rule that decides what a write of less than 64 bits does to the rest of the
register.

## Why the write rule is the first thing modeled

x86-64 has three different answers for one question, and Spike 1 depends on all
three in a single loop:

- a 64-bit write replaces the register (`writeBack.w64_independent`);
- a **32-bit write zero-extends**, discarding bits 63:32
  (`writeBack.w32_clears_high`);
- an 8- or 16-bit write **preserves** the upper bits
  (`writeBack.w8_preserves_high`, `writeBack.w16_preserves_high`).

`Spikes/1_Hello_World/Program.lean` writes `r14d` and then uses `r13`/`r14` as
64-bit quantities across a call. If the 32-bit rule were modeled as
preserve-upper, `sub r14d, eax` would appear to leave stale high bits and the
remaining-length measure could not be proved to decrease; if the 8/16-bit rule
were modeled as zero-extend, a program that relies on preservation would be
proved safe when it is not. Neither error is visible in the assembly text, so
the rule is stated here once, dual-cited, with theorems that pin all three
cases.

## Why the rule is stated as a concatenation

`writeBack` builds the new register value by joining the preserved high bits to
the written low bits:

```lean
| .w16, old, v => BitVec.extractLsb' 16 48 old ++ v
```

That is what "preserves the upper bits" means, said in one line. The
alternative — masking with `old &&& 0xFFFFFFFFFFFF0000` and OR-ing — encodes the
same rule in a hexadecimal literal that has to be counted to be checked, and
whose four variants differ only in how many `F`s they have.

## Exactly how much of this the type enforces

Less than an earlier version of this section implied, and the distinction is
worth stating because it decides where to look when something changes.

The dependent type `BitVec w.bits` forces each arm's two slices to sum to 64.
That rules out three mistakes outright, as *type* errors: swapping the `.w16`
and `.w8` arms, and mis-sizing either preserved slice — `extractLsb' 8 56` in
the `.w16` arm gives `BitVec (56 + 16)`, which is not `BitVec 64`.

It does not pin where a preserved slice *starts*, and it does not distinguish
preserving from zero-extending at all. A reviewer wrote six further mutations
that all typecheck cleanly: `.w32` preserving the high bits instead of clearing
them, `.w32` emitting `v ++ 0#32`, `.w16` reading from offset 0 instead of 16,
`.w8` from offset 0 instead of 8, `.w8` writing into bits 15:8, and `.w64`
ignoring its argument. Every one is caught, but by the theorems below rather
than by the type: `read_back` pins the low `w.bits`, and `w32_clears_high`,
`w32_independent`, `w16_preserves_high`, `w8_preserves_high` and
`read_back_w64` pin the rest, so between them all 64 bits of all four cases are
determined and no semantically different definition survives `lake build`.

The one worth naming is `.w32` preserving instead of clearing, because it is the
mutation this module exists to prevent and it is *not* type-prevented. Two of
the mutations also fail as `maximum number of heartbeats` timeouts rather than
as clean refutations, which is a fragile way to be caught — a raised
`maxHeartbeats` would turn them green. `w32_clears_high` is the theorem that
catches it semantically, and `Tests/ISA/X86/MachineProbes.lean` catches it on
silicon.

## Why not `bv_decide`

`docs/DECISIONS.md` 23 permits universally quantified `bv_decide`, and these
theorems were first proved with it. An axiom audit under
`docs/DECISIONS.md` 31 rejected two of them:

```text
'writeBack.w16_preserves_high' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   writeBack.w16_preserves_high._native.bv_decide.ax_1_5]
```

That generated constant is `verifyBVExpr expr cert = true` asserted as an axiom:
`bv_decide` ran its LRAT checker natively and admitted the result rather than
having the kernel reduce it. `docs/DECISIONS.md` 23 prohibits `native_decide`
and says "execution is not a proof", and 31 requires "rejection of every
dependency-defined axiom" — so the tactic's own permission does not survive its
own audit in this case.

The concatenation form removes the need. Every theorem below is closed by
`simp`, `rw` or `decide`, and the module no longer imports the tactic at all.
Audited, they depend on `propext` and `Quot.sound` only.

This is not a claim that `bv_decide` is unusable here. It is kernel-checked when
its normalizer closes the goal without calling the solver, and it was on four of
the six theorems. The point is that which path it takes is not visible in the
source, so the audit — not the tactic's documentation — decides.
-/

namespace Grass.ISA.X86

open Grass.Core Grass.Cite

/--
A general-purpose register of 64-bit mode.

Sixteen constructors rather than `Fin 16` so that `rsp` and `rbp` can be named
in the encoding rules that treat their numbers specially, and so a register
cannot be confused with an arbitrary index. `Gpr.index` supplies the number when
encoding needs it.
-/
inductive Gpr where
  /-- Register 0. -/ | rax
  /-- Register 1. -/ | rcx
  /-- Register 2. -/ | rdx
  /-- Register 3. -/ | rbx
  /-- Register 4. Its number selects a SIB byte in most memory encodings. -/
  | rsp
  /-- Register 5. Its number selects RIP-relative or no-base forms. -/
  | rbp
  /-- Register 6. -/ | rsi
  /-- Register 7. -/ | rdi
  /-- Register 8. Requires a REX extension bit to name. -/ | r8
  /-- Register 9. -/ | r9
  /-- Register 10. -/ | r10
  /-- Register 11. -/ | r11
  /-- Register 12. Shares `rsp`'s low three bits, and its SIB behaviour. -/
  | r12
  /-- Register 13. Shares `rbp`'s low three bits, and its displacement
  behaviour. -/
  | r13
  /-- Register 14. -/ | r14
  /-- Register 15. -/ | r15
deriving DecidableEq, Repr, Inhabited

namespace Gpr

/-- Every general-purpose register, in encoding order. -/
def all : List Gpr :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
   .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The register's architectural encoding number, 0-15. -/
def index : Gpr → Fin 16
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3
  | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

/-- `all` lists each register exactly once, so indexing it is total. -/
@[simp] theorem length_all : all.length = 16 := rfl

/-- The register with a given encoding number.

Read out of `all` rather than written as sixteen `Fin` patterns, because Lean
cannot see that such a match is exhaustive and would demand an unreachable
default case — a case that would then be the only place a wrong answer could
hide. `length_all` is what makes the fallback unreachable. -/
def ofIndex (i : Fin 16) : Gpr := all.getD i.val .rax

@[simp] theorem ofIndex_index (r : Gpr) : ofIndex r.index = r := by
  cases r <;> rfl

@[simp] theorem index_ofIndex (i : Fin 16) : (ofIndex i).index = i := by
  revert i; decide

theorem index_injective {a b : Gpr} (h : a.index = b.index) : a = b := by
  rw [← ofIndex_index a, ← ofIndex_index b, h]

theorem mem_all (r : Gpr) : r ∈ all := by cases r <;> decide

/--
The register needs a REX extension bit to be named.

Registers 8-15 are reachable only through `REX.R`, `REX.X` or `REX.B` depending
on the field they appear in. This is a property of the number, so `r12` needs
one and `rsp` — which shares its low three bits — does not.
-/
def isExtended (r : Gpr) : Bool := decide (8 ≤ r.index.val)

/-- The low three bits actually written into a ModRM or SIB field. -/
def lowBits (r : Gpr) : Fin 8 := ⟨r.index.val % 8, Nat.mod_lt _ (by decide)⟩

/--
Two registers sharing low three bits are distinguished only by the REX bit.

This is the fact behind every "why does `r12` behave like `rsp` here" question
in the encoding tables: the special cases in ModRM and SIB are selected by
`lowBits`, which cannot tell them apart, so the special case applies to both.
-/
theorem lowBits_eq_iff_isExtended_ne {a b : Gpr}
    (h : a.lowBits = b.lowBits) (hne : a ≠ b) : a.isExtended ≠ b.isExtended := by
  revert h hne; cases a <;> cases b <;> decide

end Gpr

/-- An operand size, in the four widths 64-bit mode gives general-purpose
integer operations. -/
inductive Width where
  /-- 8-bit. Leaves bits 63:8 as they were; see `writeBack.w8_preserves_high`. -/
  | w8
  /-- 16-bit. Leaves bits 63:16 as they were; see
  `writeBack.w16_preserves_high`. -/
  | w16
  /-- 32-bit. Zero-extends: bits 63:32 become zero. -/ | w32
  /-- 64-bit. Replaces the register. -/ | w64
deriving DecidableEq, Repr, Inhabited

namespace Width

/-- The width in bits. -/
def bits : Width → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

/-- Every operand width. -/
def all : List Width := [.w8, .w16, .w32, .w64]

/--
The default operand size for the instructions that have one, when no size
prefix or `REX.W` is present.

64-bit mode defaults to 32-bit operands, which is why `mov ecx, 3` is the short
encoding and `mov rcx, 3` needs `REX.W`. Address size defaults to 64 bits, which
is a separate axis and belongs to the addressing rules.

**Two groups of instructions do not follow this**, and for them a 32-bit form is
not encodable at all. Intel SDM Vol. 2A §2.2.1.7 "Default 64-Bit Operand Size"
names them exactly: near branches, and "all instructions, except far branches,
that implicitly reference the RSP". Those need no `REX.W` for a 64-bit operand,
and `66` gives them 16 bits rather than 32.

That is not a detail. `Grass/ISA/X86/Bytes.lean`'s `callMem64` sets `w := false`
because `FF /2` is a near branch, and `Spikes/1_Hello_World/Program.lean` opens
with three `push` instructions, which reference RSP implicitly. Both are in the
second group, and neither fact is derivable from this constant — which is why
this is a `Width` and not a function of the opcode. Making it opcode-indexed is
an **open obligation**; the anchor above is confirmed, the model is not yet
built. -/
def default64BitMode : Width := .w32

end Width

/--
What a write of `w` bits leaves in the rest of the 64-bit register.

This is the whole operand-size rule of 64-bit mode in one function. Both vendors
state it; see `Rules.registerWriteExtension`.
-/
def writeBack : (w : Width) → BitVec 64 → BitVec w.bits → BitVec 64
  | .w64, _, v => v
  | .w32, _, v => 0#32 ++ v
  | .w16, old, v => BitVec.extractLsb' 16 48 old ++ v
  | .w8, old, v => BitVec.extractLsb' 8 56 old ++ v

namespace writeBack

/-! The `show` in each proof below spells out the reduced definition rather than
letting `simp` find it, so the fact being proved sits next to the concatenation
it depends on. -/

theorem read_back_w8 (old : BitVec 64) (v : BitVec 8) :
    BitVec.setWidth 8 (writeBack .w8 old v) = v := by
  show BitVec.setWidth 8 (BitVec.extractLsb' 8 56 old ++ v) = v
  rw [BitVec.setWidth_append, dif_pos (by omega)]
  simp

theorem read_back_w16 (old : BitVec 64) (v : BitVec 16) :
    BitVec.setWidth 16 (writeBack .w16 old v) = v := by
  show BitVec.setWidth 16 (BitVec.extractLsb' 16 48 old ++ v) = v
  rw [BitVec.setWidth_append, dif_pos (by omega)]
  simp

theorem read_back_w32 (old : BitVec 64) (v : BitVec 32) :
    BitVec.setWidth 32 (writeBack .w32 old v) = v := by
  show BitVec.setWidth 32 (0#32 ++ v) = v
  rw [BitVec.setWidth_append, dif_pos (by omega)]
  simp

theorem read_back_w64 (old : BitVec 64) (v : BitVec 64) :
    BitVec.setWidth 64 (writeBack .w64 old v) = v := by
  show BitVec.setWidth 64 v = v
  simp

/-- A write of any width lands: reading back `w` bits returns what was written.

The property every one of the four cases must have, and the one a mistake in the
masks would break. -/
@[simp] theorem read_back (w : Width) (old : BitVec 64) (v : BitVec w.bits) :
    BitVec.setWidth w.bits (writeBack w old v) = v := by
  cases w
  · exact read_back_w8 old v
  · exact read_back_w16 old v
  · exact read_back_w32 old v
  · exact read_back_w64 old v

/-- A 64-bit write ignores the previous contents. -/
theorem w64_independent (a b : BitVec 64) (v : BitVec 64) :
    writeBack .w64 a v = writeBack .w64 b v := rfl

/-- A 32-bit write ignores the previous contents.

This is the zero-extension rule stated as *independence*, which is the form a
proof about `sub r14d, eax` actually needs: the resulting 64-bit value is a
function of the 32-bit result alone, so no reasoning about what was in the
register beforehand is required. -/
theorem w32_independent (a b : BitVec 64) (v : BitVec 32) :
    writeBack .w32 a v = writeBack .w32 b v := rfl

/-- A 32-bit write clears bits 63:32. -/
theorem w32_clears_high (old : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 32 32 (writeBack .w32 old v) = 0 := by
  show BitVec.extractLsb' 32 32 (0#32 ++ v) = 0
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  simp

/-- A 16-bit write preserves bits 63:16, which is what `w16_preserves_high`
states. -/
theorem w16_preserves_high (old : BitVec 64) (v : BitVec 16) :
    BitVec.extractLsb' 16 48 (writeBack .w16 old v) =
      BitVec.extractLsb' 16 48 old := by
  show BitVec.extractLsb' 16 48 (BitVec.extractLsb' 16 48 old ++ v) = _
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  simp

/-- An 8-bit write preserves bits 63:8, which is what `w8_preserves_high`
states. -/
theorem w8_preserves_high (old : BitVec 64) (v : BitVec 8) :
    BitVec.extractLsb' 8 56 (writeBack .w8 old v) =
      BitVec.extractLsb' 8 56 old := by
  show BitVec.extractLsb' 8 56 (BitVec.extractLsb' 8 56 old ++ v) = _
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  simp

/--
A 16-bit write is genuinely not independent of the previous contents.

Stated as a witness rather than left implicit. `w32_independent` above is `rfl`,
so it would be easy to assume every narrow write behaves that way and model
`w16` the same; this exhibits the pair of prior values that distinguishes them,
and fails if `writeBack .w16` is ever "simplified" to a zero-extension. -/
theorem w16_not_independent :
    writeBack .w16 (0xFFFF000000000000 : BitVec 64) 0 ≠
      writeBack .w16 (0 : BitVec 64) 0 := by
  decide

/-- An 8-bit write is genuinely not independent of the previous contents. -/
theorem w8_not_independent :
    writeBack .w8 (0xFF00000000000000 : BitVec 64) 0 ≠
      writeBack .w8 (0 : BitVec 64) 0 := by
  decide

end writeBack

/--
An 8-bit register operand.

The two constructors are not two spellings of one thing. `low` names the low
byte of one of the sixteen registers; `high` names bits 15:8 of one of the first
four, an encoding inherited from the 8086 that survives only in the absence of a
REX prefix. They collide in the encoding: with no REX, register numbers 4-7 in
an 8-bit operand mean `AH`, `CH`, `DH`, `BH`; with any REX, the same numbers mean
`SPL`, `BPL`, `SIL`, `DIL`.

Modeling both as `Gpr` plus a flag would make the collision invisible, and the
resulting encoder would silently emit `AH` where the author wrote `SPL`.
-/
inductive ByteReg where
  /-- The low 8 bits of a general-purpose register. -/
  | low (r : Gpr)
  /-- Bits 15:8 of `rax`, `rcx`, `rdx` or `rbx`, selected by index 0-3. Not
  encodable in the presence of a REX prefix. -/
  | high (r : Gpr)
deriving DecidableEq, Repr, Inhabited

namespace ByteReg

/-- The registers that have a legacy high-byte form: `ah`, `ch`, `dh`, `bh`. -/
def highCapable : List Gpr := [.rax, .rcx, .rdx, .rbx]

/-- The low-byte forms `ByteReg.Encodable` rejects without a REX prefix.

Without REX, encoding numbers 4-7 in an 8-bit operand denote the high-byte
registers, so `spl`, `bpl`, `sil` and `dil` are unreachable. A REX prefix with
no set bits (`0x40`) is the usual way to reach them. -/
def requiresRex : List Gpr := [.rsp, .rbp, .rsi, .rdi]

/--
Whether this operand is encodable given whether a REX prefix is present.

Both directions matter and they point opposite ways, which is why this is one
predicate rather than two independent checks:

- `high` requires *no* REX;
- `low` of `rsp`/`rbp`/`rsi`/`rdi` requires *a* REX;
- `low` of an extended register requires a REX to supply its high bit.

An instruction mixing `ah` with `r8` in one encoding is therefore rejected here,
not discovered as a wrong byte later.
-/
def Encodable (b : ByteReg) (hasRex : Bool) : Prop :=
  match b with
  | .high r => r ∈ highCapable ∧ hasRex = false
  | .low r => (r ∈ requiresRex ∨ r.isExtended = true) → hasRex = true

instance (b : ByteReg) (hasRex : Bool) : Decidable (b.Encodable hasRex) := by
  cases b <;> unfold Encodable <;> infer_instance

/-- The number written into the register field. For a high-byte register this is
its base register's index plus four, which is exactly the collision. -/
def encodingNumber : ByteReg → Nat
  | .low r => r.index.val
  | .high r => r.index.val + 4

/-- `ah` and `spl` are the same encoding number in the same field.

The collision `ByteReg` exists to keep visible, exhibited rather than described.
Any encoder that maps both constructors through `encodingNumber` and forgets to
consult the REX prefix will emit one where the author wrote the other. -/
theorem high_low_collide :
    (ByteReg.high .rax).encodingNumber = (ByteReg.low .rsp).encodingNumber := rfl

/-- No byte operand is encodable both with and without REX.

A consequence of the collision: whichever way the prefix goes, one of the two
readings is excluded. -/
theorem not_encodable_both (r : Gpr) (hr : r ∈ requiresRex) :
    ¬ ((ByteReg.low r).Encodable false) := by
  intro h
  exact absurd (h (Or.inl hr)) (by decide)

/-- A high-byte register is never encodable alongside a REX prefix. -/
theorem high_not_encodable_with_rex (r : Gpr) :
    ¬ ((ByteReg.high r).Encodable true) := fun h => by
  exact absurd h.2 (by decide)

end ByteReg

end Grass.ISA.X86
