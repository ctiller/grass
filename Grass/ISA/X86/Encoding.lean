import Grass.Std.Logical.Byte
import Grass.ISA.X86.Register

/-!
# REX, ModR/M and SIB byte layouts

The three bytes that carry operand selection in a 64-bit-mode instruction, as
structures with named bit fields plus their byte encodings and exhaustive
round-trip theorems.

## Why bit fields, and why concatenation

`docs/DECISIONS.md` 19 requires every writer to have a reader and to prove
round-trip. An encoder written as shifts and masks over one opaque byte can be
proved to round-trip too, but the failure it must exclude is a *field landing in
the wrong place*, and that failure is invisible when both sides are one byte.

So the fields are separate values of separate widths, and the encoder is

```lean
def ModRm.toByte (m : ModRm) : Byte := m.mod ++ m.reg ++ m.rm
```

which is not an implementation of the layout but a statement of it: 2 bits then
3 bits then 3 bits, in that order, checked by the type. There is no shift amount
to get wrong and no mask to mistype. The widths are structural for the same
reason — `reg : BitVec 3` cannot hold a register number 8-15, so the fact that
naming `r8` requires a REX bit is forced by the types rather than remembered.

## Round-trip in both directions

Each layout proves two theorems, and they say different things:

- `ofByte_toByte` says the reader recovers what the writer wrote. This is the
  correctness of the pair.
- `toByte_ofByte` says every byte re-encodes to itself, so the reader has no
  lossy inputs. For ModR/M and SIB every byte is meaningful, so it holds
  unconditionally. REX is different — only sixteen bytes are prefixes — and it
  says so through a partial reader and a hypothesis.

Both are settled by `decide` over the whole 256-byte domain — every case, not a
sample. That is affordable here precisely because the fields are small, and it
is preferred over `bv_decide` even though `docs/DECISIONS.md` 23 permits the
latter: `bv_decide` admits its SAT certificate as a generated axiom when its
normalizer does not close the goal alone, which `docs/DECISIONS.md` 31 rejects.
`Grass/ISA/X86/Register.lean` records that finding in full. Audited, the proofs
here depend on `propext` and `Quot.sound` only.

## Scope

These are byte *layouts*. What a given field combination means as an address —
the SIB escape, the RIP-relative form, the missing-base and missing-index cases —
is the addressing model, and the escapes are only named here. The theorems at
the end of this module record the one structural fact those rules rest on: the
escapes are two ordinary register numbers reused, so each captures a pair of
registers rather than one.
-/

namespace Grass.ISA.X86

open Grass.Core Grass.Cite Grass.Std.Logical

/-! ## Register fields -/

namespace Gpr

/-- The three bits of a register number that fit in a ModR/M, SIB or opcode
register field.

Written out as a table rather than derived from `index`, for two reasons. It is
the encoding table, and an encoding module should show one. And it reduces:
`BitVec.ofNat 3 (Gpr.index r).val` requires unfolding a `Fin` coercion before
anything can `decide` whether a field equals an escape value, which is the
question every addressing rule asks. `encodingBits_eq_index` keeps the table
honest against `index`. -/
def encodingBits : Gpr → BitVec 3
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3
  | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 0 | .r9 => 1 | .r10 => 2 | .r11 => 3
  | .r12 => 4 | .r13 => 5 | .r14 => 6 | .r15 => 7

/-- The table agrees with the architectural register number. -/
theorem encodingBits_eq_index (r : Gpr) :
    r.encodingBits = BitVec.ofNat 3 r.index.val := by cases r <;> rfl

/-- The fourth bit of a register number, carried by a REX extension bit.

Which REX bit carries it depends on the field: `REX.R` for `ModRM.reg`, `REX.X`
for `SIB.index`, `REX.B` for `ModRM.rm`, `SIB.base` and the opcode register. -/
def rexBit (r : Gpr) : Bool := r.isExtended

/-- A register is determined by its three encoding bits and its REX bit.

The property that makes an encoding decodable at all. It fails if `encodingBits`
is ever widened or `rexBit` dropped for a "short" form. -/
theorem eq_of_bits {a b : Gpr}
    (hb : a.encodingBits = b.encodingBits) (hr : a.rexBit = b.rexBit) : a = b := by
  revert hb hr; cases a <;> cases b <;> decide

end Gpr

/-! ## REX -/

/--
The REX prefix.

One of the sixteen bytes `0x40`-`0x4F`. In 64-bit mode those encodings no longer
mean the one-byte `INC`/`DEC` forms they mean in 32-bit mode, so a decoder
cannot be shared between modes without consulting the mode first.

The fields are `BitVec 1` rather than `Bool` because the byte is bits and the
encoding theorems are bitvector facts. `Rex.of` and the four predicates below
give the boolean reading for consumers that want it.
-/
structure Rex where
  /-- `REX.W`: promote the operation to a 64-bit operand size. -/
  w : BitVec 1
  /-- `REX.R`: the high bit of `ModRM.reg`. -/
  r : BitVec 1
  /-- `REX.X`: the high bit of `SIB.index`. -/
  x : BitVec 1
  /-- `REX.B`: the high bit of `ModRM.rm`, `SIB.base`, or an opcode register. -/
  b : BitVec 1
deriving DecidableEq, Repr, Inhabited

namespace Rex

/-- Build a prefix from boolean bit settings. -/
def of (w r x b : Bool) : Rex :=
  ⟨BitVec.ofBool w, BitVec.ofBool r, BitVec.ofBool x, BitVec.ofBool b⟩

/-- Whether this prefix promotes the operand size to 64 bits. -/
def promotesTo64 (p : Rex) : Bool := p.w == 1
/-- Whether this prefix extends `ModRM.reg`. -/
def extendsReg (p : Rex) : Bool := p.r == 1
/-- Whether this prefix extends `SIB.index`. -/
def extendsIndex (p : Rex) : Bool := p.x == 1
/-- Whether this prefix extends `ModRM.rm`, `SIB.base` or an opcode register. -/
def extendsBase (p : Rex) : Bool := p.b == 1

/--
A REX prefix with no bits set: `0x40`.

Not a no-op. *Any* REX prefix makes register numbers 4-7 in an 8-bit operand
denote `SPL`, `BPL`, `SIL` and `DIL` rather than `AH`, `CH`, `DH` and `BH`, and
this is the prefix to use when no extension bit is otherwise needed. So an
instruction on `SPL` carries a prefix byte that changes none of its fields and
is still required. See `ByteReg`.
-/
def bare : Rex := ⟨0, 0, 0, 0⟩

/-- The prefix byte, `0100WRXB`.

The definition is the layout: the fixed nibble `0100`, then W, R, X, B. -/
def toByte (p : Rex) : Byte := (0b0100 : BitVec 4) ++ p.w ++ p.r ++ p.x ++ p.b

@[simp] theorem toByte_bare : bare.toByte = 0x40 := rfl

/-- Whether a byte is a REX prefix: high nibble `0100`. -/
def isRexByte (v : Byte) : Bool := BitVec.extractLsb' 4 4 v == 0b0100

/-- Read a REX prefix, or `none` if the byte is not one.

Partial where `ModRm.ofByte` and `Sib.ofByte` are total, because only sixteen of
the 256 bytes are REX prefixes. A reader returning a `Rex` for every byte would
be claiming the other 240 encode one. -/
def ofByte? (v : Byte) : Option Rex :=
  if isRexByte v then
    some ⟨BitVec.extractLsb' 3 1 v, BitVec.extractLsb' 2 1 v,
          BitVec.extractLsb' 1 1 v, BitVec.extractLsb' 0 1 v⟩
  else Option.none

/-- Every encoded prefix is recognised as one. -/
@[simp] theorem isRexByte_toByte (p : Rex) : isRexByte p.toByte = true := by
  cases p with | mk w r x b => revert w r x b; decide

/-- The reader recovers exactly the prefix the writer wrote. -/
@[simp] theorem ofByte?_toByte (p : Rex) : ofByte? p.toByte = some p := by
  cases p with | mk w r x b => revert w r x b; decide

/-- Distinct prefixes have distinct bytes. -/
theorem toByte_injective {p q : Rex} (h : p.toByte = q.toByte) : p = q := by
  have := congrArg ofByte? h
  simpa using this

/-- Every byte the reader accepts re-encodes to itself.

With `ofByte?_toByte` this says the sixteen prefixes and the sixteen bytes
`0x40`-`0x4F` correspond exactly, with nothing left over on either side. -/
theorem toByte_ofByte? {v : Byte} {p : Rex} (h : ofByte? v = some p) :
    p.toByte = v := by
  revert h; revert p; revert v; decide

/-- A byte outside `0x40`-`0x4F` is not a REX prefix. -/
theorem ofByte?_eq_none {v : Byte} (h : isRexByte v = false) :
    ofByte? v = Option.none := by simp [ofByte?, h]

end Rex

/-! ## ModR/M -/

/--
The ModR/M byte: `mod` in bits 7:6, `reg` in bits 5:3, `r/m` in bits 2:0.

`reg` is a register number in some instructions and an opcode extension in
others — the `/digit` column of the vendor opcode tables — so it is not typed as
a register here. Which it is depends on the opcode, and that is the opcode
table's fact, not this byte's.
-/
structure ModRm where
  /-- Bits 7:6. Selects register-direct (`11`) or one of three memory forms. -/
  mod : BitVec 2
  /-- Bits 5:3. A register number extended by `REX.R`, or an opcode extension. -/
  reg : BitVec 3
  /-- Bits 2:0. A register number extended by `REX.B`, or a selector for the SIB
  and RIP-relative forms. -/
  rm : BitVec 3
deriving DecidableEq, Repr, Inhabited

namespace ModRm

/-- `mod = 11`: the r/m operand is a register, not a memory reference. -/
def modRegisterDirect : BitVec 2 := 3
/-- `mod = 00`: memory, with no displacement except in the special forms. -/
def modNoDisplacement : BitVec 2 := 0
/-- `mod = 01`: memory with a signed 8-bit displacement. -/
def modDisp8 : BitVec 2 := 1
/-- `mod = 10`: memory with a signed 32-bit displacement. -/
def modDisp32 : BitVec 2 := 2

/-- The `r/m` value that selects a following SIB byte when `mod ≠ 11`.

Equal to `rsp`'s low three bits, and therefore also `r12`'s: neither can be
named directly as a base, and both are reached through the SIB byte. -/
def rmSelectsSib : BitVec 3 := 4

/-- The `r/m` value that selects RIP-relative addressing when `mod = 00`.

Equal to `rbp`'s low three bits, and therefore also `r13`'s. -/
def rmSelectsRipRelative : BitVec 3 := 5

/-- The byte. The definition is the layout. -/
def toByte (m : ModRm) : Byte := m.mod ++ m.reg ++ m.rm

/-- The fields of a byte. Total: every byte is a ModR/M byte. -/
def ofByte (v : Byte) : ModRm :=
  ⟨BitVec.extractLsb' 6 2 v, BitVec.extractLsb' 3 3 v, BitVec.extractLsb' 0 3 v⟩

/-- The reader recovers exactly the fields the writer wrote. -/
@[simp] theorem ofByte_toByte (m : ModRm) : ofByte m.toByte = m := by
  cases m with | mk mod reg rm => revert mod reg rm; decide

/-- Every byte re-encodes to itself, so the reader loses nothing. -/
@[simp] theorem toByte_ofByte (v : Byte) : (ofByte v).toByte = v := by
  revert v; decide

/-- Distinct field triples have distinct bytes. -/
theorem toByte_injective {m n : ModRm} (h : m.toByte = n.toByte) : m = n := by
  have := congrArg ofByte h
  simpa using this

end ModRm

/-! ## SIB -/

/--
The SIB byte: `scale` in bits 7:6, `index` in bits 5:3, `base` in bits 2:0.

Present only when `ModRm.rm = 100` and `mod ≠ 11`.
-/
structure Sib where
  /-- Bits 7:6. The index is scaled by 1, 2, 4 or 8. -/
  scale : BitVec 2
  /-- Bits 5:3. A register number extended by `REX.X`; `100` with `REX.X = 0`
  means no index register at all. -/
  index : BitVec 3
  /-- Bits 2:0. A register number extended by `REX.B`; `101` with `mod = 00`
  means no base register and a 32-bit displacement. -/
  base : BitVec 3
deriving DecidableEq, Repr, Inhabited

namespace Sib

/-- The `index` value meaning "no index register", when `REX.X` is clear.

Equal to `rsp`'s low three bits. `rsp` therefore cannot be an index register at
all, while `r12` — which shares those bits but sets `REX.X` — can. This is the
one place where the shared-low-bits pattern does *not* capture both registers of
the pair, and the asymmetry is the reason. -/
def indexNone : BitVec 3 := 4

/-- The `base` value meaning "no base register" when `mod = 00`.

Equal to `rbp`'s low three bits, and `r13`'s. -/
def baseNone : BitVec 3 := 5

/-- The scale factor a `scale` field denotes. -/
def scaleFactor (s : BitVec 2) : Nat := 1 <<< s.toNat

@[simp] theorem scaleFactor_values :
    (scaleFactor 0, scaleFactor 1, scaleFactor 2, scaleFactor 3) = (1, 2, 4, 8) := rfl

/-- The byte. The definition is the layout. -/
def toByte (s : Sib) : Byte := s.scale ++ s.index ++ s.base

/-- The fields of a byte. Total: every byte is a SIB byte. -/
def ofByte (v : Byte) : Sib :=
  ⟨BitVec.extractLsb' 6 2 v, BitVec.extractLsb' 3 3 v, BitVec.extractLsb' 0 3 v⟩

/-- The reader recovers exactly the fields the writer wrote. -/
@[simp] theorem ofByte_toByte (s : Sib) : ofByte s.toByte = s := by
  cases s with | mk scale index base => revert scale index base; decide

/-- Every byte re-encodes to itself. -/
@[simp] theorem toByte_ofByte (v : Byte) : (ofByte v).toByte = v := by
  revert v; decide

/-- Distinct field triples have distinct bytes. -/
theorem toByte_injective {s t : Sib} (h : s.toByte = t.toByte) : s = t := by
  have := congrArg ofByte h
  simpa using this

end Sib

/-! ## The shared low-bit collisions

The four escape values above are not four unrelated conventions. They are two
register numbers reused, which is why each captures a *pair* of registers rather
than one, and why `r12` and `r13` inherit addressing restrictions that have
nothing to do with `r12` and `r13`.
-/

/-- The SIB escape in `ModRm.rm` is `rsp`'s low three bits. -/
theorem rmSelectsSib_eq_rsp : ModRm.rmSelectsSib = Gpr.encodingBits .rsp := rfl

/-- And therefore also `r12`'s, which is why `r12` needs a SIB byte to be a base
register even though nothing about `r12` itself is special. -/
theorem rmSelectsSib_eq_r12 : ModRm.rmSelectsSib = Gpr.encodingBits .r12 := rfl

/-- The RIP-relative escape in `ModRm.rm` is `rbp`'s low three bits. -/
theorem rmSelectsRip_eq_rbp :
    ModRm.rmSelectsRipRelative = Gpr.encodingBits .rbp := rfl

/-- And therefore also `r13`'s. -/
theorem rmSelectsRip_eq_r13 :
    ModRm.rmSelectsRipRelative = Gpr.encodingBits .r13 := rfl

/-- The "no index" escape in `Sib.index` is `rsp`'s low three bits. -/
theorem indexNone_eq_rsp : Sib.indexNone = Gpr.encodingBits .rsp := rfl

/-- The "no base" escape in `Sib.base` is `rbp`'s low three bits. -/
theorem baseNone_eq_rbp : Sib.baseNone = Gpr.encodingBits .rbp := rfl

/--
Exactly four registers are touched by the escapes.

Stated as a complete list rather than as separate facts, so a reader checking the
addressing rules knows there is no fifth special case waiting.
-/
theorem escapes_touch_only_rsp_rbp_r12_r13 (r : Gpr)
    (h : r.encodingBits = ModRm.rmSelectsSib ∨
         r.encodingBits = ModRm.rmSelectsRipRelative) :
    r ∈ [Gpr.rsp, Gpr.rbp, Gpr.r12, Gpr.r13] := by
  revert h; cases r <;> decide

/-- No register escapes both fields, so the two special cases never interact. -/
theorem no_register_hits_both_escapes (r : Gpr) :
    ¬ (r.encodingBits = ModRm.rmSelectsSib ∧
       r.encodingBits = ModRm.rmSelectsRipRelative) := by
  cases r <;> decide

end Grass.ISA.X86
