import Grass.ISA.X86.Encoding

/-!
# 64-bit-mode memory operands

What a ModR/M byte, an optional SIB byte and a displacement mean as an address,
and how an address is encoded into them.

## The hazards this module exists to contain

Every one of these is a case where the obvious encoding means something else.

- **`mod=00, rm=101` is RIP-relative, not `[disp32]`.** In 32-bit mode that
  encoding is an absolute displacement. In 64-bit mode it is `[rip + disp32]`,
  and the absolute form has to go through a SIB byte with no base. An encoder
  ported from 32-bit rules produces a program that reads the wrong address and
  is still a valid instruction.

- **`rm=100` is never a register.** It selects a SIB byte. So `rsp` cannot be a
  base register directly, and neither can `r12`, which shares its low three bits.

- **`[rbp]` and `[r13]` cannot use `mod=00`,** because that encoding is the
  RIP-relative escape. They need a displacement byte, even when the
  displacement is zero.

- **`rsp` cannot be an index register at all.** `index=100` with `REX.X` clear
  means *no index*. `r12` shares those low bits but sets `REX.X`, so `r12` is a
  perfectly good index register while `rsp` is unencodable. This is the one
  escape that does not capture both registers of its pair, and it is the one
  most often got wrong.

`Grass/ISA/X86/Encoding.lean` proves the shared-low-bit facts these rest on.
Here they become a total encoder that cannot emit them wrongly and a decoder
that reads them correctly.

## Why the encoder always uses a 32-bit displacement

`encode` below is deliberately not a size optimizer. It emits `mod=10` with a
full displacement wherever a displacement is possible, so the encoding of an
operand depends only on its shape and never on the numeric value of its
displacement.

That is a real cost — three extra bytes on `[rsp + 8]` — paid for a specific
reason. A size-optimizing encoder chooses between `mod=00`, `mod=01` and
`mod=10` by comparing the displacement against zero and against the signed 8-bit
range, and those comparisons interact with exactly the escapes above: the
`mod=00` shortcut is illegal for `rbp`/`r13`, and the zero-displacement shortcut
is illegal when the SIB base is absent. A first profile that gets the *meaning*
right and the *size* suboptimal is safe; one that gets sizes right and the
escapes wrong is not.

`docs/DECISIONS.md` 20 permits exactly this: "Exact x86 syntactic round-trip may
be weakened to semantic encode/decode equivalence when exactness harms
instruction reasoning." The decoder below accepts every form, including the
short ones this encoder does not emit, so decoding imported code is unaffected.
An optimizing encoder is a later refinement that must discharge the same
`decode_encode` obligation.
-/

namespace Grass.ISA.X86

open Grass.Core Grass.Std.Logical

/-! ## Register reconstruction -/

namespace Gpr

/-- The REX extension bit of a register, as a bit.

A table for the same reason as `encodingBits`: an addressing rule has to decide
whether this bit is set before it can tell `rsp` from `r12`. -/
def rexBitV : Gpr → BitVec 1
  | .rax | .rcx | .rdx | .rbx | .rsp | .rbp | .rsi | .rdi => 0
  | .r8 | .r9 | .r10 | .r11 | .r12 | .r13 | .r14 | .r15 => 1

/-- The table agrees with `rexBit`. -/
theorem rexBitV_eq_rexBit (r : Gpr) : r.rexBitV = BitVec.ofBool r.rexBit := by
  cases r <;> rfl

/-- The register named by a REX extension bit and a three-bit field. -/
def ofBits (x : BitVec 1) (b : BitVec 3) : Gpr := all.getD (x.toNat * 8 + b.toNat) .rax

/-- Encoding and decoding a register number agree.

The fact every addressing round-trip below rests on. -/
@[simp] theorem ofBits_encodingBits (r : Gpr) :
    ofBits r.rexBitV r.encodingBits = r := by cases r <;> rfl

end Gpr

/-! ## Scale -/

/-- The scale applied to an index register: 1, 2, 4 or 8. -/
inductive Scale where
  /-- Scale 1, encoded `00`. -/ | s1
  /-- Scale 2, encoded `01`. -/ | s2
  /-- Scale 4, encoded `10`. -/ | s4
  /-- Scale 8, encoded `11`. -/ | s8
deriving DecidableEq, Repr, Inhabited

namespace Scale

/-- The two-bit SIB field. -/
def bits : Scale → BitVec 2
  | .s1 => 0 | .s2 => 1 | .s4 => 2 | .s8 => 3

/-- The scale field's value. -/
def ofBits (v : BitVec 2) : Scale :=
  if v = 0 then .s1 else if v = 1 then .s2 else if v = 2 then .s4 else .s8

@[simp] theorem ofBits_bits (s : Scale) : ofBits s.bits = s := by cases s <;> rfl

@[simp] theorem bits_ofBits (v : BitVec 2) : (ofBits v).bits = v := by
  revert v; decide

/-- The multiplier this scale denotes. -/
def factor : Scale → Nat
  | .s1 => 1 | .s2 => 2 | .s4 => 4 | .s8 => 8

theorem factor_eq_scaleFactor (s : Scale) : s.factor = Sib.scaleFactor s.bits := by
  cases s <;> rfl

end Scale

/-! ## Memory operands -/

/--
A memory operand of 64-bit mode, as a meaning rather than an encoding.

Displacements are 32-bit and signed; a decoder sign-extends an 8-bit
displacement into this form, which is why `Displacement` is an encoding-level
type below and does not appear here.

`ripRelative` is a distinct constructor rather than `base rip disp` because
`rip` is not a general-purpose register, cannot be scaled or indexed, and is
resolved against the address of the *next* instruction rather than the current
one. Folding it into the base case would make all three of those facts
expressible and wrong.
-/
inductive MemOperand where
  /-- `[rip + disp]`, resolved against the end of the instruction. -/
  | ripRelative (disp : BitVec 32)
  /-- `[base + disp]`. -/
  | base (b : Gpr) (disp : BitVec 32)
  /-- `[base + index*scale + disp]`. Not encodable when `index` is `rsp`. -/
  | baseIndex (b : Gpr) (index : Gpr) (scale : Scale) (disp : BitVec 32)
  /-- `[index*scale + disp]`, with no base register. Not encodable when `index`
  is `rsp`. -/
  | indexOnly (index : Gpr) (scale : Scale) (disp : BitVec 32)
  /-- `[disp]`, an absolute 32-bit address with no base and no index. Reached
  through a SIB byte, never through `mod=00, rm=101`, which is RIP-relative. -/
  | absolute (disp : BitVec 32)
deriving DecidableEq, Repr, Inhabited

namespace MemOperand

/--
The index register this operand uses, if any.

`rsp` in this position is the unencodable case, so this is what
`Encodable` inspects.
-/
def indexRegister : MemOperand → Option Gpr
  | .baseIndex _ i _ _ => some i
  | .indexOnly i _ _ => some i
  | _ => Option.none

/--
The operand can be encoded at all.

The only obstruction is `rsp` as an index register: `Sib.index = 100` with
`REX.X` clear means *no index*, and there is no other way to name `rsp` in that
field. Every other combination has an encoding.
-/
def Encodable (m : MemOperand) : Prop := m.indexRegister ≠ some .rsp

instance (m : MemOperand) : Decidable m.Encodable :=
  inferInstanceAs (Decidable (¬ _))

/-- `r12` is a usable index register even though it shares `rsp`'s low bits.

The asymmetry that makes the `rsp` restriction easy to state too broadly. -/
theorem r12_usable_as_index (b : Gpr) (s : Scale) (d : BitVec 32) :
    (MemOperand.baseIndex b .r12 s d).Encodable := by
  simp [Encodable, indexRegister]

/-- `rsp` is not. -/
theorem rsp_unusable_as_index (b : Gpr) (s : Scale) (d : BitVec 32) :
    ¬ (MemOperand.baseIndex b .rsp s d).Encodable := by
  simp [Encodable, indexRegister]

end MemOperand

/-! ## Encoded form -/

/-- The displacement bytes that follow the ModR/M and SIB bytes. -/
inductive Displacement where
  /-- No displacement bytes. -/ | none
  /-- One byte, sign-extended to 32 bits when interpreted. -/ | d8 (v : BitVec 8)
  /-- Four bytes. -/ | d32 (v : BitVec 32)
deriving DecidableEq, Repr, Inhabited

namespace Displacement

/-- The 32-bit value this displacement contributes. -/
def value : Displacement → BitVec 32
  | .none => 0
  | .d8 v => BitVec.signExtend 32 v
  | .d32 v => v

/-- The number of bytes emitted. -/
def size : Displacement → Nat
  | .none => 0 | .d8 _ => 1 | .d32 _ => 4

end Displacement

/--
The r/m half of an encoded instruction: everything that describes the memory
operand, and nothing that describes the other one.

`ModRm.reg` is absent on purpose. It belongs to the register operand or is an
opcode extension, and an addressing encoder has no business choosing it. `rexR`
is absent for the same reason. What is here is exactly what the addressing form
determines.
-/
structure RmEncoding where
  /-- `ModRm.mod`. -/
  mod : BitVec 2
  /-- `ModRm.rm`. -/
  rm : BitVec 3
  /-- The SIB byte, when `rm` selects one. -/
  sib : Option Sib
  /-- The displacement bytes. -/
  disp : Displacement
  /-- `REX.X`, extending `Sib.index`. -/
  rexX : BitVec 1
  /-- `REX.B`, extending `ModRm.rm` or `Sib.base`. -/
  rexB : BitVec 1
deriving DecidableEq, Repr, Inhabited

namespace RmEncoding

/--
Join this addressing form to a `reg` field to make the complete ModR/M byte.

The `reg` field is the caller's: a register number for a two-operand
instruction, or the `/digit` opcode extension from the vendor tables. Supplying
it here rather than inside `encodeMem` is what keeps the addressing model
independent of the opcode.
-/
def modrm (e : RmEncoding) (reg : BitVec 3) : ModRm := ⟨e.mod, reg, e.rm⟩

/--
The REX prefix this addressing form needs, given the operand size and whether
the `reg` field names an extended register.

`W` and the `reg` extension come from the instruction; `X` and `B` come from the
address. Splitting them this way is why an addressing form can be encoded
without knowing the opcode, and why the opcode cannot accidentally drop an
extension bit the address needed.
-/
def rex (e : RmEncoding) (w regExtended : Bool) : Rex :=
  Rex.of w regExtended (e.rexX == 1) (e.rexB == 1)

/-- Whether this form needs a REX prefix at all when the operand size is not
promoted and the `reg` field names a low register. -/
def needsRex (e : RmEncoding) : Bool := e.rexX == 1 || e.rexB == 1

end RmEncoding

/-! ## Encoding -/

/--
Encode a memory operand.

`none` exactly when the operand names `rsp` as an index register; see
`MemOperand.Encodable`.

Always a 32-bit displacement where a displacement is possible. See this module's
header for why that is deliberate.
-/
def encodeMem (m : MemOperand) : Option RmEncoding :=
  match m with
  | .ripRelative d =>
      some { mod := ModRm.modNoDisplacement, rm := ModRm.rmSelectsRipRelative,
             sib := Option.none, disp := .d32 d, rexX := 0, rexB := 0 }
  | .base b d =>
      if b.encodingBits = ModRm.rmSelectsSib then
        -- `rsp` and `r12` cannot be named as a base directly.
        some { mod := ModRm.modDisp32, rm := ModRm.rmSelectsSib,
               sib := some ⟨Scale.s1.bits, Sib.indexNone, b.encodingBits⟩,
               disp := .d32 d, rexX := 0, rexB := b.rexBitV }
      else
        some { mod := ModRm.modDisp32, rm := b.encodingBits, sib := Option.none,
               disp := .d32 d, rexX := 0, rexB := b.rexBitV }
  | .baseIndex b i s d =>
      if i = .rsp then Option.none
      else
        some { mod := ModRm.modDisp32, rm := ModRm.rmSelectsSib,
               sib := some ⟨s.bits, i.encodingBits, b.encodingBits⟩,
               disp := .d32 d, rexX := i.rexBitV, rexB := b.rexBitV }
  | .indexOnly i s d =>
      if i = .rsp then Option.none
      else
        some { mod := ModRm.modNoDisplacement, rm := ModRm.rmSelectsSib,
               sib := some ⟨s.bits, i.encodingBits, Sib.baseNone⟩,
               disp := .d32 d, rexX := i.rexBitV, rexB := 0 }
  | .absolute d =>
      some { mod := ModRm.modNoDisplacement, rm := ModRm.rmSelectsSib,
             sib := some ⟨Scale.s1.bits, Sib.indexNone, Sib.baseNone⟩,
             disp := .d32 d, rexX := 0, rexB := 0 }

/-- Encoding fails exactly on the unencodable operands. -/
theorem encodeMem_isNone_iff (m : MemOperand) :
    encodeMem m = Option.none ↔ ¬ m.Encodable := by
  cases m <;>
    simp [encodeMem, MemOperand.Encodable, MemOperand.indexRegister] <;>
    split <;> simp_all

/-! ## Decoding -/

/--
Decode the r/m half of an instruction into the address it denotes.

`none` for a malformed or non-memory encoding: `mod=11` is a register operand,
and `rm=100` without a SIB byte is not a complete encoding.

This decoder accepts every legal 64-bit-mode memory form, including the short
displacement forms `encodeMem` never emits.
-/
def decodeMem (e : RmEncoding) : Option MemOperand :=
  if e.mod = ModRm.modRegisterDirect then Option.none
  else if e.mod = ModRm.modNoDisplacement ∧ e.rm = ModRm.rmSelectsRipRelative then
    -- 64-bit mode: this is RIP-relative, not an absolute displacement.
    -- REX.B is ignored here; the form does not name a general-purpose register.
    some (.ripRelative e.disp.value)
  else if e.rm = ModRm.rmSelectsSib then
    match e.sib with
    | Option.none => Option.none
    | some sib =>
        let hasIndex := ¬ (sib.index = Sib.indexNone ∧ e.rexX = 0)
        let noBase := sib.base = Sib.baseNone ∧ e.mod = ModRm.modNoDisplacement
        let idx := Gpr.ofBits e.rexX sib.index
        let scale := Scale.ofBits sib.scale
        let d := e.disp.value
        if hasIndex then
          if noBase then some (.indexOnly idx scale d)
          else some (.baseIndex (Gpr.ofBits e.rexB sib.base) idx scale d)
        else
          if noBase then some (.absolute d)
          else some (.base (Gpr.ofBits e.rexB sib.base) d)
  else
    some (.base (Gpr.ofBits e.rexB e.rm) e.disp.value)

/-! ## Round-trip -/

/-- The writer's round-trip: every encodable operand decodes back to itself.

`docs/DECISIONS.md` 19 requires this of every writer. Note what it rules out:
not just a lost displacement, but the RIP-relative form decoding as an absolute
address, `[r12]` decoding as `[rsp]`, and an index register reappearing as a
base. -/
theorem encode_then_decode (m : MemOperand) (h : m.Encodable) :
    (encodeMem m).bind decodeMem = some m := by
  cases m with
  | ripRelative d => rfl
  | absolute d => rfl
  | base b d => cases b <;> rfl
  | baseIndex b i s d =>
      cases i <;> cases b <;> cases s <;> first | rfl | exact absurd rfl h
  | indexOnly i s d =>
      cases i <;> cases s <;> first | rfl | exact absurd rfl h

/-- The same round-trip, phrased for a caller that already holds the encoding. -/
theorem decodeMem_encodeMem {m : MemOperand} {e : RmEncoding}
    (h : encodeMem m = some e) : decodeMem e = some m := by
  have hm : m.Encodable := by
    by_cases hc : m.Encodable
    · exact hc
    · rw [(encodeMem_isNone_iff m).mpr hc] at h
      exact absurd h (by simp)
  have := encode_then_decode m hm
  rw [h] at this
  exact this

/-! ## The hazards, as theorems

Each of these says that the encoder does *not* produce the encoding a naive one
would, and names the address that encoding would actually denote.
-/

/-- `[rip + d]` uses `mod=00, rm=101`, the 64-bit-mode RIP-relative form. -/
theorem ripRelative_encoding (d : BitVec 32) :
    encodeMem (.ripRelative d) =
      some { mod := ModRm.modNoDisplacement, rm := ModRm.rmSelectsRipRelative,
             sib := Option.none, disp := .d32 d, rexX := 0, rexB := 0 } := rfl

/-- An absolute address does **not** use `mod=00, rm=101`.

In 32-bit mode it would. Here that encoding means `[rip + d]`, so the absolute
form goes through a SIB byte with no base and no index. -/
theorem absolute_is_not_ripRelative_encoding (d : BitVec 32) :
    encodeMem (.absolute d) ≠ encodeMem (.ripRelative d) := by
  intro h
  simp only [encodeMem, Option.some.injEq, RmEncoding.mk.injEq] at h
  exact absurd h.2.1 (by decide)

/-- `[rsp + d]` is encoded through a SIB byte, because `rm=100` selects one. -/
theorem rsp_base_uses_sib (d : BitVec 32) :
    (encodeMem (.base .rsp d)).bind (·.sib) =
      some ⟨Scale.s1.bits, Sib.indexNone, Gpr.encodingBits .rsp⟩ := rfl

/-- So is `[r12 + d]`, for no reason having to do with `r12`. -/
theorem r12_base_uses_sib (d : BitVec 32) :
    (encodeMem (.base .r12 d)).bind (·.sib) =
      some ⟨Scale.s1.bits, Sib.indexNone, Gpr.encodingBits .r12⟩ := rfl

/-- `[rbp + d]` and `[r13 + d]` never use `mod=00`, which would be the
RIP-relative escape. -/
theorem rbp_base_avoids_mod00 (d : BitVec 32) :
    (encodeMem (.base .rbp d)).map (·.mod) = some ModRm.modDisp32 := rfl

/-- The same for `r13`. -/
theorem r13_base_avoids_mod00 (d : BitVec 32) :
    (encodeMem (.base .r13 d)).map (·.mod) = some ModRm.modDisp32 := rfl

/-- `rsp` as an index register has no encoding. -/
theorem no_encoding_for_rsp_index (b : Gpr) (s : Scale) (d : BitVec 32) :
    encodeMem (.baseIndex b .rsp s d) = Option.none := by
  simp [encodeMem]

/-- `r12` as an index register does, and sets `REX.X`. -/
theorem r12_index_sets_rexX (b : Gpr) (s : Scale) (d : BitVec 32) :
    (encodeMem (.baseIndex b .r12 s d)).map (·.rexX) = some 1 := rfl

end Grass.ISA.X86
