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
  RIP-relative escape — see `rbp_base_avoids_mod00` and `r13_base_avoids_mod00`.
  They need a displacement byte even when the displacement is zero.

- **`rsp` cannot be an index register at all.** `index=100` with `REX.X` clear
  means *no index*. `r12` shares those low bits but sets `REX.X`, so `r12` is a
  perfectly good index register while `rsp` is unencodable. This is the one
  escape that does not capture both registers of its pair, and it is the one
  most often got wrong.

`Grass/ISA/X86/Encoding.lean` proves the shared-low-bit facts these rest on.
Here they become an encoder that emits each hazard's correct form, checked by
`rsp_base_uses_sib`, `rbp_base_avoids_mod00`, `no_encoding_for_rsp_index` and
`ripRelative_encoding`, and a decoder that inverts it (`encode_then_decode`) on
records that denote a byte string (`encodeMem_wellFormed`).

Note what `encode_then_decode` does *not* establish. It relates two Grass
definitions to each other, so an encoder and decoder that were wrong in the same
way — `mod=00, rm=101` treated as absolute throughout, say — would satisfy it
just as well while emitting instructions no processor executes. Internal
consistency is all a round-trip theorem can give. The claim that these encodings
are x86-64 rested on a NASM differential over 1085 of them. It was removed on
2026-09-08; that check is currently absent, and its replacement as a Lean test
under `Tests/ISA/X86/**` is tracked against c-x86 (c-agent:78).

## Why the encoder always uses a 32-bit displacement

`encode` below is deliberately not a size optimizer. It always emits a 32-bit
displacement, so the encoding of an operand depends only on its shape and never
on the numeric value of its displacement. For the base forms that means
`mod=10`; the index-only and absolute forms use `mod=00`, because the SIB
no-base encoding exists only there and carries its `disp32` regardless.

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
  /-- `[disp]`, a displacement-only address with no base and no index. Reached
  through a SIB byte, never through `mod=00, rm=101`, which is RIP-relative.

  Not an arbitrary 32-bit address: the displacement is sign-extended to 64 bits
  (see `Displacement.value`), so this form reaches the low 2 GiB and the high
  2 GiB and nothing between them. -/
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

/-- The 32-bit value this displacement contributes.

Sign-extended, not zero-extended: an 8-bit displacement of `0x80` is `-128`. The
further sign-extension from 32 to 64 bits happens when the effective address is
formed, and is why the absolute form reaches only the low and high 2 GiB of the
address space rather than an arbitrary 32-bit address. -/
def value : Displacement → BitVec 32
  | .none => 0
  | .d8 v => BitVec.signExtend 32 v
  | .d32 v => v

/-- The number of bytes emitted. -/
def size : Displacement → Nat
  | .none => 0 | .d8 _ => 1 | .d32 _ => 4

end Displacement

/--
How many displacement bytes a set of ModR/M and SIB fields *promises* the
instruction stream contains.

This is not a preference. In x86-64 the `mod` field tells the processor how many
bytes to consume before the next instruction begins, so an encoding whose
displacement disagrees with its `mod` does not denote a different address — it
desynchronises the decoder and the following bytes are read as an instruction
that was never written.

The two `mod=00` exceptions are the escapes: `rm=101` is RIP-relative and always
carries four bytes, and a SIB byte with `base=101` and `mod=00` has no base
register and also always carries four. Neither is optional.
-/
inductive DispKind where
  /-- No displacement bytes follow. -/ | none
  /-- One byte follows. -/ | d8
  /-- Four bytes follow. -/ | d32
deriving DecidableEq, Repr, Inhabited

namespace Displacement

/-- Which kind of displacement this is. -/
def kind : Displacement → DispKind
  | .none => .none | .d8 _ => .d8 | .d32 _ => .d32

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

/--
How many displacement bytes a ModR/M byte and its SIB promise, as a function of
just those fields.

Standalone rather than a method on `RmEncoding`, because the decoder needs the
answer *before* it has read the displacement -- that is the whole point of the
question -- and a decoder that asked a different function than the encoder's
well-formedness condition could disagree with it. One definition, two callers.
-/
def dispKindFor (mod : BitVec 2) (rm : BitVec 3) (sib : Option Sib) : DispKind :=
  if mod = ModRm.modDisp8 then .d8
  else if mod = ModRm.modDisp32 then .d32
  else if mod = ModRm.modNoDisplacement then
    if rm = ModRm.rmSelectsRipRelative then .d32
    else match sib with
      | some s => if s.base = Sib.baseNone then .d32 else .none
      | Option.none => .none
  else .none

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
address, so an addressing form can be encoded without knowing the opcode.

The split has a cost this signature does not fix: `regExtended` is an unchecked
`Bool` argument, and nothing ties it to whatever register the caller passed to
`modrm`. A caller naming `r13` in the `reg` field and forgetting `regExtended`
gets a legal instruction naming `rbp` instead. Nor may it be set on a `/digit`
form, where REX.R has no meaning. Pairing the two is the job of the
instruction-level encoder — `encodeMemInsn` in `Grass/ISA/X86/Bytes.lean` takes
the register once and derives both — and is an **open obligation** here rather
than a property of this function.
-/
def rex (e : RmEncoding) (w regExtended : Bool) : Rex :=
  Rex.of w regExtended (e.rexX == 1) (e.rexB == 1)

/-- Whether this form needs a REX prefix at all when the operand size is not
promoted and the `reg` field names a low register.

This answers only for the *address*. A byte operand can require a prefix on its
own account — see `ByteReg.Encodable` — and an instruction encoder must consider
both. -/
def needsRex (e : RmEncoding) : Bool := e.rexX == 1 || e.rexB == 1

/-- The displacement these fields promise the instruction stream carries. See
`DispKind`. -/
def requiredDisp (e : RmEncoding) : DispKind := dispKindFor e.mod e.rm e.sib

/-- A SIB byte is in the stream exactly when `rm=100` and `mod ≠ 11`. -/
def requiresSib (e : RmEncoding) : Bool :=
  e.rm == ModRm.rmSelectsSib && e.mod != ModRm.modRegisterDirect

/--
This record denotes an actual byte string.

`RmEncoding` is a product of independent fields, and most of that product is not
reachable by any instruction. Two ways it can be unreachable, and both change
where the *next* instruction starts rather than merely naming a different
address:

- the displacement disagrees with what `mod` promises (`requiredDisp`);
- a SIB byte is present where none belongs, or absent where one is mandatory
  (`requiresSib`).

`decodeMem` rejects a record failing this rather than inventing an address for
it, and `encodeMem_wellFormed` proves the encoder only produces records that
satisfy it.
-/
def WellFormed (e : RmEncoding) : Prop :=
  e.disp.kind = e.requiredDisp ∧ (e.sib.isSome = e.requiresSib)

instance (e : RmEncoding) : Decidable e.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _))

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

/-- The encoder only produces records that denote a byte string.

Without this, `decodeMem`'s new well-formedness rejection could silently reject
the encoder's own output, and `encode_then_decode` would be proving something
about a smaller set of operands than it appears to. -/
theorem encodeMem_wellFormed (m : MemOperand) (e : RmEncoding)
    (h : encodeMem m = some e) : e.WellFormed := by
  cases m with
  | ripRelative d => cases h; exact ⟨rfl, rfl⟩
  | absolute d => cases h; exact ⟨rfl, rfl⟩
  | base b d =>
      cases b <;> (simp only [encodeMem] at h; cases h; exact ⟨rfl, rfl⟩)
  | baseIndex b i s d =>
      cases i <;> cases b <;> cases s <;> simp only [encodeMem] at h <;>
        (first | (cases h; exact ⟨rfl, rfl⟩) | exact absurd h (by simp))
  | indexOnly i s d =>
      cases i <;> cases s <;> simp only [encodeMem] at h <;>
        (first | (cases h; exact ⟨rfl, rfl⟩) | exact absurd h (by simp))

/-! ## Decoding -/

/--
Decode the r/m half of an instruction into the address it denotes.

`none` for a malformed or non-memory encoding: `mod=11` is a register operand,
and `rm=100` without a SIB byte is not a complete encoding.

Within its scope it accepts every legal ModR/M memory form, including the short
displacement forms `encodeMem` never emits. That scope is the default 64-bit
address size with no segment override, which is what `RmEncoding` can represent:
it has no field for a legacy prefix, so `67h` 32-bit addressing — under which
`mod=00, rm=101` becomes *EIP*-relative and the address truncates to 32 bits —
and `FS`/`GS` segment overrides are outside it, as are the `MOV moffs` forms,
which are not ModR/M operands at all. Those are gaps, not rejections: an
importer meeting one of them needs this model extended, not a `none`.
-/
def decodeMem (e : RmEncoding) : Option MemOperand :=
  if !decide e.WellFormed then Option.none
  else if e.mod = ModRm.modRegisterDirect then Option.none
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
