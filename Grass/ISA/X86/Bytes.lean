import Grass.ISA.X86.Addressing

/-!
# Instruction bytes

The layer that was missing: `RmEncoding` and `Rex` become an actual byte string.

## Why this had to exist before anything could be checked

Until this module, nothing in `Grass/ISA/X86/**` produced bytes. The round-trip
theorems in `Encoding.lean` and `Addressing.lean` related two abstract types to
each other, and an encoder that is self-consistent with its own decoder proves
those theorems whether or not it has anything to do with x86 — a model with
`reg` and `rm` transposed throughout round-trips perfectly and emits
instructions no processor will execute.

The opcode bytes were the visible symptom: `Tests/ISA/X86/Spike1Addressing.lean`
tabulated `FF 15 d32` and `C7 84 24 d32 imm32`, and the bytes `FF`, `8D` and
`C7` appeared nowhere in the repository. Only the ModR/M and SIB bytes were
modeled, so "golden bytes" covered two bytes of a seven-byte instruction.

With `toBytes` the model emits a complete instruction, which is what an
independent assembler can be compared against. `docs/VALIDATION.md` §2 puts the
real check in the differential layer, and that layer needs bytes on both sides.

## Byte order

Displacements and immediates are little-endian. `le32`/`le16` emit
least-significant byte first, and `split32`/`split16` are the reassembly
theorems the parser rests on. This is stated as a theorem rather than a comment
because byte order is exactly the kind of thing that is obviously right until it
is silently backwards.

## Prefix order

REX must be the **last** prefix before the opcode, after every legacy prefix and
immediately before the opcode or its `0F` escape. A REX separated from the
opcode by a `66`, `F2`, `F3`, `67`, segment or `LOCK` prefix is *ignored*, and
the instruction then executes without the register extensions and without the
64-bit operand size — a wrong instruction that still decodes. `toBytes` fixes
the order by construction; there is no field that could hold a prefix in the
wrong place.

Legacy prefixes are not modeled yet. That is a real gap rather than a decision:
this profile has no instruction needing one, and adding them must preserve the
ordering rule above.
-/

namespace Grass.ISA.X86

open Grass.Core Grass.Std.Logical

/-! ## Byte order -/

/-- A 32-bit value as four little-endian bytes. -/
def le32 (v : BitVec 32) : ByteSeq :=
  [BitVec.extractLsb' 0 8 v, BitVec.extractLsb' 8 8 v,
   BitVec.extractLsb' 16 8 v, BitVec.extractLsb' 24 8 v]

/-- A 64-bit value as eight little-endian bytes.

Only `mov r64, imm64` needs this: it is the one form in this profile whose
immediate is eight bytes, and `Grass.ISA.X86.OpcodeSpec.immSizeFor` is what
selects it, from the opcode's promotion flag and the prefix's `W` bit. See `Grass.ISA.X86.OpcodeSpec.immSizeFor`. -/
def le64 (v : BitVec 64) : ByteSeq :=
  [BitVec.extractLsb' 0 8 v, BitVec.extractLsb' 8 8 v,
   BitVec.extractLsb' 16 8 v, BitVec.extractLsb' 24 8 v,
   BitVec.extractLsb' 32 8 v, BitVec.extractLsb' 40 8 v,
   BitVec.extractLsb' 48 8 v, BitVec.extractLsb' 56 8 v]

/-- A 16-bit value as two little-endian bytes. -/
def le16 (v : BitVec 16) : ByteSeq :=
  [BitVec.extractLsb' 0 8 v, BitVec.extractLsb' 8 8 v]

/-- Reassembling four little-endian bytes recovers the value.

The parser's correctness rests on this, and it is the statement that fails if
the byte order is ever reversed. -/
theorem split32 (v : BitVec 32) :
    BitVec.extractLsb' 24 8 v ++ BitVec.extractLsb' 16 8 v ++
      BitVec.extractLsb' 8 8 v ++ BitVec.extractLsb' 0 8 v = v := by
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
  simp

/-- Reassembling eight little-endian bytes recovers the value. -/
theorem split64 (v : BitVec 64) :
    BitVec.extractLsb' 56 8 v ++ BitVec.extractLsb' 48 8 v ++
      BitVec.extractLsb' 40 8 v ++ BitVec.extractLsb' 32 8 v ++
      BitVec.extractLsb' 24 8 v ++ BitVec.extractLsb' 16 8 v ++
      BitVec.extractLsb' 8 8 v ++ BitVec.extractLsb' 0 8 v = v := by
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
  simp

/-- Reassembling two little-endian bytes recovers the value. -/
theorem split16 (v : BitVec 16) :
    BitVec.extractLsb' 8 8 v ++ BitVec.extractLsb' 0 8 v = v := by
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
  simp

@[simp] theorem length_le32 (v : BitVec 32) : (le32 v).length = 4 := rfl
@[simp] theorem length_le64 (v : BitVec 64) : (le64 v).length = 8 := rfl
@[simp] theorem length_le16 (v : BitVec 16) : (le16 v).length = 2 := rfl

/-! ## Displacement and immediate bytes -/

namespace Displacement

/-- The displacement bytes, little-endian. -/
def toBytes : Displacement → ByteSeq
  | .none => []
  | .d8 v => [v]
  | .d32 v => le32 v

/-- `size` counts the bytes `toBytes` emits. It was defined before there was a
serializer to count, and now says something. -/
@[simp] theorem length_toBytes (d : Displacement) : d.toBytes.length = d.size := by
  cases d <;> rfl

end Displacement

/-- The immediate operand that follows the displacement. -/
inductive Immediate where
  /-- No immediate. -/ | none
  /-- One byte. -/ | i8 (v : BitVec 8)
  /-- Four bytes, little-endian. -/ | i32 (v : BitVec 32)
  /-- Eight bytes, little-endian.

  Reachable only as `REX.W` plus a `B8+rd` opcode -- `mov r64, imm64`, the one
  x86-64 instruction with a full 64-bit immediate. It exists because a decoder
  without it reads four bytes where eight follow and then resumes in the middle
  of the immediate; see `Grass.ISA.X86.OpcodeSpec.immSizeFor`. -/
  | i64 (v : BitVec 64)
deriving DecidableEq, Repr, Inhabited

namespace Immediate

/-- The immediate bytes, little-endian. -/
def toBytes : Immediate → ByteSeq
  | .none => []
  | .i8 v => [v]
  | .i32 v => le32 v
  | .i64 v => le64 v

/-- The number of bytes emitted. -/
def size : Immediate → Nat
  | .none => 0 | .i8 _ => 1 | .i32 _ => 4 | .i64 _ => 8

@[simp] theorem length_toBytes (i : Immediate) : i.toBytes.length = i.size := by
  cases i <;> rfl

/-- How large an immediate an opcode takes. Distinct from `Immediate` because a
spec names a size without naming a value. -/
inductive Size where
  /-- No immediate operand. -/ | none
  /-- A one-byte immediate. -/ | i8
  /-- A four-byte immediate. -/ | i32
  /-- An eight-byte immediate. -/ | i64
deriving DecidableEq, Repr, Inhabited

/-- The size of this immediate. -/
def sizeOf : Immediate → Size
  | .none => .none | .i8 _ => .i8 | .i32 _ => .i32 | .i64 _ => .i64

end Immediate

/-! ## The instruction -/

/--
One encoded instruction.

The field order is the byte order, which is the point: there is no way to hold a
REX prefix after the opcode or a SIB byte before the ModR/M byte, because the
serializer walks the fields in order and the fields are in the order the
processor reads them.
-/
structure InsnEncoding where
  /-- The REX prefix, if one is present. `none` means no prefix byte at all,
  which is architecturally different from a prefix with no bits set: `0x40`
  changes which byte registers the encoding names. -/
  rex : Option Rex
  /-- Whether the opcode is in the `0F` two-byte space. -/
  escape : Bool
  /-- The primary opcode byte. -/
  opcode : Byte
  /-- The ModR/M byte, for opcodes that take one. -/
  modrm : Option ModRm
  /-- The SIB byte, when the ModR/M byte selects one. -/
  sib : Option Sib
  /-- The displacement bytes. -/
  disp : Displacement
  /-- The immediate bytes. -/
  imm : Immediate
deriving DecidableEq, Repr, Inhabited

namespace InsnEncoding

/-- The `0F` escape byte. -/
def escapeByte : Byte := 0x0F

/-! Each optional field's bytes, named.

Named rather than written as inline matches inside `toBytes`, so that the
decoder's round-trip proof and the writer speak the same language: a proof about
`sibBytes i.sib` has to be about the same term the writer emitted, and an inline
match forces the proof to reconstruct it. -/

/-- The REX prefix byte, if there is one. -/
def rexBytes : Option Rex → ByteSeq
  | some r => [r.toByte]
  | Option.none => []

/-- The `0F` escape byte, if the opcode is in the two-byte space. -/
def escapeBytes (escape : Bool) : ByteSeq := if escape then [escapeByte] else []

/-- The ModR/M byte, if the opcode takes one. -/
def modrmBytes : Option ModRm → ByteSeq
  | some m => [m.toByte]
  | Option.none => []

/-- The SIB byte, if the ModR/M byte selects one. -/
def sibBytes : Option Sib → ByteSeq
  | some s => [s.toByte]
  | Option.none => []

/--
The instruction's bytes, in stream order.

Prefix, escape, opcode, ModR/M, SIB, displacement, immediate — the order the
processor reads them. A REX prefix cannot land in the wrong place because
`InsnEncoding` has no field that could hold one elsewhere.
-/
def toBytes (i : InsnEncoding) : ByteSeq :=
  rexBytes i.rex ++ escapeBytes i.escape ++ [i.opcode] ++
    modrmBytes i.modrm ++ sibBytes i.sib ++ i.disp.toBytes ++ i.imm.toBytes

/--
This record denotes an instruction a decoder could read back.

`InsnEncoding` is a product of independent fields and most of that product is
unreachable, in the same way `RmEncoding` was before it gained a well-formedness
predicate. The failure is worse one layer up, because `toBytes` emits the fields
positionally: a record with a SIB byte and no ModR/M byte serialises the SIB
into the ModR/M position, so `8D 00 44 33 22 11` reads as `lea rax,[rax]`
followed by three stray bytes that the processor decodes as whatever they
happen to be.

`WellFormed` states the conditions in both directions, and none is about what
address is named:

- a SIB byte exists only as part of a ModR/M byte's r/m operand, so `WellFormed`
  requires a ModR/M byte that is actually selecting it;
- and the mirror: a ModR/M byte that *says* a SIB follows must have one. The
  first version checked only the direction that had a theorem, so
  `48 8D 04 44332211` -- ModR/M `mod=00, rm=100` with no SIB -- was well-formed
  and decodes as `lea rax,[rsp+rax*2]` followed by two stray instructions;
- the displacement matches what `mod` and the SIB promise, reusing
  `RmEncoding.requiredDisp` rather than restating it. `mod=00, rm=101` is the
  case that matters most: it is RIP-relative, it *requires* a disp32, and it is
  the form Spike 1 depends on;
- a displacement belongs to a ModR/M operand, so `WellFormed` requires one.

The immediate is deliberately *not* constrained here. Which immediate an opcode
takes is a fact about the opcode, and this module has no opcode table; putting a
guess here would be inventing a constraint rather than modeling one. It is an
**open obligation** for the instruction layer.
-/
def WellFormed (i : InsnEncoding) : Prop :=
  (i.sib.isSome → ∃ m, i.modrm = some m ∧ m.rm = ModRm.rmSelectsSib ∧
      m.mod ≠ ModRm.modRegisterDirect) ∧
    (∀ m, i.modrm = some m →
      (m.rm = ModRm.rmSelectsSib ∧ m.mod ≠ ModRm.modRegisterDirect →
        i.sib.isSome) ∧
      i.disp.kind = dispKindFor m.mod m.rm i.sib) ∧
    (i.disp ≠ .none → i.modrm.isSome)

instance (i : InsnEncoding) : Decidable i.WellFormed := by
  unfold WellFormed
  exact inferInstanceAs (Decidable (_ ∧ _))

/-- A SIB byte with no ModR/M byte is rejected, rather than being serialised
into the ModR/M position. -/
theorem not_wellFormed_sib_without_modrm {i : InsnEncoding}
    (hs : i.sib.isSome = true) (hm : i.modrm = Option.none) : ¬ i.WellFormed := by
  intro h
  obtain ⟨m, hm', _, _⟩ := h.1 hs
  rw [hm] at hm'
  exact absurd hm' (by simp)

/-- The encoded length in bytes. -/
def size (i : InsnEncoding) : Nat :=
  (if i.rex.isSome then 1 else 0) + (if i.escape then 1 else 0) + 1 +
    (if i.modrm.isSome then 1 else 0) + (if i.sib.isSome then 1 else 0) +
    i.disp.size + i.imm.size

/--
Where the displacement field starts, counted from the instruction's first byte.

Everything `toBytes` emits before the displacement: the REX prefix if present,
the escape byte if present, the opcode, and the ModR/M and SIB bytes if
present.

This exists for one consumer. A COFF relocation for a RIP-relative operand
names the *displacement field*, not the instruction, so a writer needs this
number and cannot get it from the byte string -- the bytes do not say where one
field ends and the next begins. `Grass/Platform/Win32/CoffText.lean` took it on
trust before this. -/
def dispOffset (i : InsnEncoding) : Nat :=
  (if i.rex.isSome then 1 else 0) + (if i.escape then 1 else 0) + 1 +
    (if i.modrm.isSome then 1 else 0) + (if i.sib.isSome then 1 else 0)

/--
Bytes of the instruction after the displacement field: the immediate, if any.

The other number a relocation needs. `IMAGE_REL_AMD64_REL32` resolves relative
to the byte after the field, so an instruction that continues past it takes
`REL32_1` through `REL32_5` instead -- selected by exactly this count. -/
def dispTrailing (i : InsnEncoding) : Nat := i.imm.size

/--
**The displacement field is where these two say it is.**

Offset, field, and trailing bytes account for the whole instruction. This is
what makes `dispOffset` and `dispTrailing` usable by a relocation: a
displacement placed anywhere else would still satisfy each definition
separately, and only their sum against `size` pins them together. -/
theorem dispOffset_add_disp_add_trailing (i : InsnEncoding) :
    i.dispOffset + i.disp.size + i.dispTrailing = i.size := by
  simp only [dispOffset, dispTrailing, size]

/-- **An instruction with no immediate has nothing after its displacement.**

The common case, and the one that makes plain `REL32` correct. -/
theorem dispTrailing_eq_zero_iff (i : InsnEncoding) :
    i.dispTrailing = 0 ↔ i.imm.size = 0 := Iff.rfl

/-- Every instruction is at least one byte, so a parser always makes progress. -/
theorem size_pos (i : InsnEncoding) : 0 < i.size := by
  simp only [size]; omega

/-- `size` counts the bytes `toBytes` emits.

Every other size function here has this theorem; without it for `InsnEncoding`
the two could drift, and the field most likely to cause that is the one easiest
to add later — a legacy-prefix field counted in one and emitted in the other. -/
@[simp] theorem length_toBytes (i : InsnEncoding) : i.toBytes.length = i.size := by
  cases i with | mk rex escape opcode modrm sib disp imm =>
  cases rex <;> cases escape <;> cases modrm <;> cases sib <;>
    simp [toBytes, size, rexBytes, escapeBytes, modrmBytes, sibBytes] <;> omega

end InsnEncoding

/-! ## Building instructions over a memory operand -/

/--
What occupies the ModR/M `reg` field.

Two constructors rather than a `BitVec 3` plus a `Bool`, because the two cases
disagree about `REX.R` and the disagreement is silent. A register operand needs
`REX.R` set when it is `r8`-`r15`; a `/digit` opcode extension has no register,
so `REX.R` means nothing there and must not be set from one.

Passing the bits and the extension flag separately lets a caller name `r13` and
forget the flag, which produces a legal instruction naming `rbp` — the same
class of silent substitution `ByteReg` exists to prevent for `AH`/`SPL`. Here
the register is named once and both bits are derived from it.
-/
inductive RegField where
  /-- A register operand. Supplies the `reg` bits and its own `REX.R`. -/
  | reg (r : Gpr)
  /-- A `/digit` opcode extension from the vendor tables. Carries no `REX.R`. -/
  | ext (digit : BitVec 3)
deriving DecidableEq, Repr, Inhabited

namespace RegField

/-- The three bits written into `ModRm.reg`. -/
def bits : RegField → BitVec 3
  | .reg r => r.encodingBits
  | .ext d => d

/-- Whether this field sets `REX.R`. Always false for a `/digit` extension. -/
def extended : RegField → Bool
  | .reg r => r.rexBit
  | .ext _ => false

/-- A `/digit` extension never sets `REX.R`. -/
@[simp] theorem ext_not_extended (d : BitVec 3) : (RegField.ext d).extended = false := rfl

/-- A register field sets `REX.R` exactly when the register needs it. -/
@[simp] theorem reg_extended (r : Gpr) : (RegField.reg r).extended = r.rexBit := rfl

end RegField

/--
Assemble an instruction whose r/m operand is a memory address.

The REX prefix is emitted only when it carries information: `w`, the `reg`
field's own extension bit, or an extension bit the address needs. A `Rex` with
no bits set is not the same as no prefix — see `Rex.bare` — so returning `none`
rather than an all-zero prefix is the difference between naming `AH` and naming
`SPL` in a byte-operand instruction.
-/
def encodeMemInsn (escape : Bool) (opcode : Byte) (w : Bool) (reg : RegField)
    (m : MemOperand) (imm : Immediate := .none) : Option InsnEncoding :=
  (encodeMem m).map fun e =>
    let needRex := w || reg.extended || e.rexX == 1 || e.rexB == 1
    { rex := if needRex then some (e.rex w reg.extended) else Option.none
      escape := escape
      opcode := opcode
      modrm := some (e.modrm reg.bits)
      sib := e.sib
      disp := e.disp
      imm := imm }

/--
`MOV r32, imm32` — `B8+rd id`.

The third place a register number can appear, after `ModRm.reg` and `ModRm.rm`:
added into the opcode byte itself, with `REX.B` — not `REX.R` — supplying its
fourth bit. Adding a register to an opcode looks alarming and is exactly what
the ABI specifies; the low three bits of `B8` are zero, so the sum is a
concatenation in disguise.

No `REX.W`, so this is the zero-extending 32-bit form: writing `eax` clears the
top half of `rax`. `Grass/ISA/X86/Register.lean` models that as
`writeBack.w32_clears_high`, and `Tests/ISA/X86/MachineProbes.lean` checks it on
the processor.
-/
def movRegImm32 (r : Gpr) (v : BitVec 32) : InsnEncoding :=
  { rex := if r.rexBit then some (Rex.of false false false true) else Option.none
    escape := false
    opcode := 0xB8 + BitVec.setWidth 8 r.encodingBits
    modrm := Option.none
    sib := Option.none
    disp := .none
    imm := .i32 v }

/-- The opcode-embedded form needs no ModR/M byte, so it is well-formed for the
reason `InsnEncoding.WellFormed` cares about: nothing to serialise into a
position that is not there. -/
theorem movRegImm32_wellFormed (r : Gpr) (v : BitVec 32) :
    (movRegImm32 r v).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact absurd h (by simp [movRegImm32])
  · intro m hm; exact absurd hm (by simp [movRegImm32])
  · intro h; exact absurd rfl h

/--
`MOV r64, imm64` — `REX.W + B8+rd io`.

The one x86-64 instruction with a full 64-bit immediate, and the only producer
of `Immediate.i64` anywhere in this library.

That last part is why it exists. A reviewer pointed out that `le64` had no
producer at all: nothing constructed an `i64` except the decoder, and the only
oracle touching the decoder compares length. So `le64`'s byte order rested
entirely on `split64`, which is agreement with `takeLe64` rather than with the
architecture. They reversed both together -- the same permutation, so `split64`'s
statement and proof were untouched -- and the build, both audits and all four
differentials stayed green while the decoder read
`48 B8 EF CD AB 89 67 45 23 01` as `0xefcdab8967452301` instead of
`0x0123456789abcdef`.

The contrast is what makes the point specific: the same permutation applied to
`le32` is caught instantly, because encoders emit 32-bit immediates and all 1085
NASM rows mismatch. `Tests/ISA/X86/NasmCorpus.lean` now emits this form too, so
`le64` sits under the same oracle.
-/
def movRegImm64 (r : Gpr) (v : BitVec 64) : InsnEncoding :=
  { rex := some (Rex.of true false false r.rexBit)
    escape := false
    opcode := 0xB8 + BitVec.setWidth 8 r.encodingBits
    modrm := Option.none
    sib := Option.none
    disp := .none
    imm := .i64 v }

/-- Well-formed for the same reason `movRegImm32` is: no ModR/M byte, so nothing
to serialise into one and no displacement to disagree with. -/
theorem movRegImm64_wellFormed (r : Gpr) (v : BitVec 64) :
    (movRegImm64 r v).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact absurd h (by simp [movRegImm64])
  · intro m hm; exact absurd hm (by simp [movRegImm64])
  · intro h; exact absurd rfl h

/-- `LEA r64, m` — `REX.W + 8D /r`.

The workhorse of the differential campaign: `LEA` accepts every memory operand,
takes no immediate, and performs no memory access, so one opcode exercises the
entire addressing model. -/
def leaR64 (dst : Gpr) (m : MemOperand) : Option InsnEncoding :=
  encodeMemInsn false 0x8D true (.reg dst) m

/-- `CALL qword ptr m` — `FF /2`.

Near call defaults to a 64-bit operand size in 64-bit mode, so no `REX.W` is
needed or permitted to change it; `w := false` here is not an oversight. -/
def callMem64 (m : MemOperand) : Option InsnEncoding :=
  encodeMemInsn false 0xFF false (.ext 2) m

/-- `MOV dword ptr m, imm32` — `C7 /0 id`. -/
def movMem32Imm32 (m : MemOperand) (v : BitVec 32) : Option InsnEncoding :=
  encodeMemInsn false 0xC7 false (.ext 0) m (.i32 v)

/-- `MOV qword ptr m, imm32` — `REX.W + C7 /0 id`, sign-extended to 64 bits. -/
def movMem64Imm32 (m : MemOperand) (v : BitVec 32) : Option InsnEncoding :=
  encodeMemInsn false 0xC7 true (.ext 0) m (.i32 v)

end Grass.ISA.X86
