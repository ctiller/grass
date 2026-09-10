import Std.Tactic.BVDecide
import Grass.ISA.AArch64.Control

/-!
# AArch64 A64 instruction encoding

Resolved A64 instructions (every operand concrete) with a canonical
`encode`/`decode` pair and the round-trip law `decode_encode`, per
`Grass.Target.ISA`. Authority: Arm DDI 0602 ID032025 (see
`Grass/ISA/AArch64/Sources.lean`, `Grass/ISA/AArch64/Citation.lean` for the
two families reused unmodified from `Grass.ISA.AArch64.Control`).

## Method

Each instruction family is a `structure` of BitVec-typed fields (register
numbers stay raw 5-bit fields, per `docs/TARGET_SEAMS.md`'s explicit-SP/XZR
requirement: no field of this module ever claims a value represents SP or
XZR, that reading is the state/step layer's). `encode` is a single `++`
concatenation naming every bit; `decode` extracts the same fields back out of
a word and accepts it only if re-encoding reproduces the word exactly (the
same accept-by-reencoding idiom `Control.CompareZero`/`Control.SupervisorCall`
already use). `decode_encode` for one family is `bv_decide` on the
extractions plus `simp`: this is a pure structural identity (concatenate,
extract) that `bv_decide`'s normalizer closes without calling its SAT
backend, so it never depends on a generated axiom (`docs/DECISIONS.md` 31;
`Grass/ISA/X86/Register.lean` records the same finding for x86).

`Instr` is the closed union. Its top-level `decode` tries each family's own
`decode` in a fixed order (`Option.orElse`); a family added later only ever
needs its own struct plus one more line in this chain and one more case in
`decode_encode` below, so adding a family adds one case, per the seam's
requirement. Distinguishing a new family's word from every earlier family's
requires one inequality between the fixed bits of the two encodings; unlike
the structural equalities above, `bv_decide` proves these only by calling the
SAT backend (an inequality is not closed by pure rewriting), which is exactly
the axiom `docs/DECISIONS.md` 31 rejects. Every inequality below is instead
proved by first reducing both sides, by the same axiom-free `bv_decide`
equalities, to values built only from the two families' own *fixed* bits at a
shared window (never a register, immediate, or other operand field), and then
closing the now-closed-literal comparison with plain `decide`. Where a small
enumerated field (a shift type, a move-wide opcode) would otherwise leak into
that window, the proof `cases` on it first — finitely many closed comparisons,
still no `bv_decide` SAT call.

## Coverage

Fifteen families, chosen because a leak-free (or `cases`-closeable) shared
window against every earlier family could be established within this pass:
move-wide (`movz`/`movn`/`movk`), add/sub immediate (covering `adds`/`subs`/
`cmp`/`cmn` as `setFlags`+operand choices), add/sub shifted-register (same
coverage, register form), logical immediate (`and`/`orr`/`eor`, restricted —
see `LogicalImm`), load/store unsigned-offset (`ldr`/`str`/`ldrb`/`strb`),
`cbz` and `svc` (reused from `Control`), `hlt`, unconditional branch
immediate (`b`/`bl`), unconditional branch register (`br`/`blr`/`ret`),
conditional branch (`b.cond`), `cbnz` (a dedicated struct — `Control.lean` is
out of scope for this pass, so it is not `CompareZero` plus an `op` bit),
PC-relative address (`adr`/`adrp`), logical shifted-register (`and`/`orr`/
`eor`/`ands`, restricted — see `LogicalShiftedReg`), and `nop`.

Nine of the fifteen families' dispatch windows were widened past the
original eight's shared `(23, 6)`/`(24, 5)` pair: `decode_none_at`/
`decodeX_none_at` generalize the same per-family proof shape over an
arbitrary `(pos, len, tag)` instead of hardcoding one window, and `BranchImm`
(clean only at `[30:26]`) and `BranchReg` (clean only at `[31:25]`, `[20:16]`,
or a subwindow) needed windows besides those two altogether.

`tbz`/`tbnz`, `ldp`/`stp`, register-offset and pre/post-index load/store,
`brk`, `mul`/`madd`, `udiv`/`sdiv`, `csel`/`cset`, and `lsl`/`lsr`/`asr`
immediate (`ubfm`/`sbfm`) are not covered: left out rather than shipped with
an unverified encoding or an un-discharged dispatch proof, per the brief's
"leave a family out rather than leave a gap." See the module docstring on
`Grass.ISA.AArch64.Target` for the full accounting.
-/

namespace Grass.ISA.AArch64.Target

open Grass.ISA.AArch64 (Cpu CompareZero)

/-- Local aliases for the reused `Control.SupervisorCall` codec, since this
module's own top-level `encode`/`decode` (the `Instr` ones, below) would
otherwise shadow them. -/
def svcEncode (imm : BitVec 16) : BitVec 32 := Grass.ISA.AArch64.SupervisorCall.encode imm
def svcDecode (w : BitVec 32) : Option (BitVec 16) := Grass.ISA.AArch64.SupervisorCall.decode w

theorem svcDecode_svcEncode (imm : BitVec 16) : svcDecode (svcEncode imm) = some imm :=
  Grass.ISA.AArch64.SupervisorCall.decode_encode imm

/-! ## Word/byte conversion -/

/-- The 4 bytes of a 32-bit instruction word, little-endian (byte 0 is the
least-significant). -/
def wordToBytes (w : BitVec 32) : List UInt8 :=
  [UInt8.ofBitVec (w.extractLsb' 0 8), UInt8.ofBitVec (w.extractLsb' 8 8),
   UInt8.ofBitVec (w.extractLsb' 16 8), UInt8.ofBitVec (w.extractLsb' 24 8)]

/-- Reassemble a word from 4 little-endian bytes. -/
def bytesToWord (b0 b1 b2 b3 : UInt8) : BitVec 32 :=
  b3.toBitVec ++ b2.toBitVec ++ b1.toBitVec ++ b0.toBitVec

/-- Every word is exactly the 4 bytes `wordToBytes` says it is: the fact the
top-level `decode_encode` uses to see past its own `bytesToWord`/`wordToBytes`
round trip. -/
theorem bytesToWord_wordToBytes' (w : BitVec 32) :
    bytesToWord (UInt8.ofBitVec (w.extractLsb' 0 8)) (UInt8.ofBitVec (w.extractLsb' 8 8))
      (UInt8.ofBitVec (w.extractLsb' 16 8)) (UInt8.ofBitVec (w.extractLsb' 24 8)) = w := by
  unfold bytesToWord; bv_decide

/-! ## Bool/BitVec-1 conversion (op, S, sh, isLoad flags) -/

def boolOfBit (b : BitVec 1) : Bool := b == 1
def bitOfBool (b : Bool) : BitVec 1 := if b then 1 else 0

theorem boolOfBit_bitOfBool : ∀ (b : Bool), boolOfBit (bitOfBool b) = b := by decide

/-! ## Family 1: move-wide (`movz`, `movn`, `movk`) -/

inductive MoveWideOp where
  | movn | movz | movk
  deriving DecidableEq, Repr

def MoveWideOp.code : MoveWideOp → BitVec 2
  | .movn => 0b00 | .movz => 0b10 | .movk => 0b11

def MoveWideOp.ofCode (c : BitVec 2) : Option MoveWideOp :=
  if c = 0b00 then some .movn
  else if c = 0b10 then some .movz
  else if c = 0b11 then some .movk
  else none

/-- `sf opc(2) 100101 hw(2) imm16(16) Rd(5)`. Arm DDI 0602 ID032025, "Move
wide (immediate)". `hw`'s upper bit is architecturally reserved when `sf`
selects the 32-bit form; this type does not exclude that combination
(decoding one back out yields the same field values, so round-trip still
holds — a machine step gives it whatever the real CPU gives an unallocated
encoding, which is outside this module's scope). -/
structure MoveWide where
  sf : BitVec 1
  op : MoveWideOp
  hw : BitVec 2
  imm16 : BitVec 16
  rd : BitVec 5
  deriving DecidableEq, Repr

def MoveWide.encode (i : MoveWide) : BitVec 32 :=
  i.sf ++ i.op.code ++ (0b100101#6) ++ i.hw ++ i.imm16 ++ i.rd

def MoveWide.decode (w : BitVec 32) : Option MoveWide :=
  match MoveWideOp.ofCode (w.extractLsb' 29 2) with
  | none => none
  | some op =>
    if (MoveWide.mk (w.extractLsb' 31 1) op (w.extractLsb' 21 2) (w.extractLsb' 5 16)
        (w.extractLsb' 0 5)).encode = w then
      some (MoveWide.mk (w.extractLsb' 31 1) op (w.extractLsb' 21 2) (w.extractLsb' 5 16)
        (w.extractLsb' 0 5))
    else none

theorem MoveWide.decode_encode (i : MoveWide) : MoveWide.decode i.encode = some i := by
  have hop : (i.encode).extractLsb' 29 2 = i.op.code := by unfold MoveWide.encode; bv_decide
  have h31 : (i.encode).extractLsb' 31 1 = i.sf := by unfold MoveWide.encode; bv_decide
  have h21 : (i.encode).extractLsb' 21 2 = i.hw := by unfold MoveWide.encode; bv_decide
  have h5 : (i.encode).extractLsb' 5 16 = i.imm16 := by unfold MoveWide.encode; bv_decide
  have h0 : (i.encode).extractLsb' 0 5 = i.rd := by unfold MoveWide.encode; bv_decide
  have hcode : MoveWideOp.ofCode i.op.code = some i.op := by cases i.op <;> decide
  unfold MoveWide.decode
  rw [hop, hcode]
  simp [h31, h21, h5, h0]

/-- Every family's own marker equals a literal at the shared dispatch window
`extractLsb' 23 6`, or is proved absent there — always by an equality
`bv_decide` closes structurally, never by a `bv_decide` inequality. -/
theorem MoveWide.marker23 (i : MoveWide) : (i.encode).extractLsb' 23 6 = 0b100101#6 := by
  unfold MoveWide.encode; bv_decide

theorem MoveWide.marker24 (i : MoveWide) : (i.encode).extractLsb' 24 5 = 0b10010#5 := by
  unfold MoveWide.encode; bv_decide

/-! ## Family 2: add/sub immediate (covers `add`/`adds`/`sub`/`subs`/`cmp`/`cmn`) -/

/-- `sf op S 100010 sh imm12(12) Rn(5) Rd(5)`. Arm DDI 0602 ID032025,
"Add/subtract (immediate)". `op = false` is `add`/`adds`, `true` is
`sub`/`subs`; `setFlags = true` with `rd = 0b11111` (XZR/WZR) is the `cmn`/
`cmp` alias — this module carries no alias table, the step semantics reads
`rd` directly. `sh = true` scales `imm12` left by 12 (`lsl #12`). -/
structure AddSubImm where
  sf : BitVec 1
  op : Bool
  setFlags : Bool
  sh : Bool
  imm12 : BitVec 12
  rn : BitVec 5
  rd : BitVec 5
  deriving DecidableEq, Repr

def AddSubImm.encode (i : AddSubImm) : BitVec 32 :=
  i.sf ++ bitOfBool i.op ++ bitOfBool i.setFlags ++ (0b100010#6) ++ bitOfBool i.sh ++
    i.imm12 ++ i.rn ++ i.rd

def AddSubImm.decode (w : BitVec 32) : Option AddSubImm :=
  let cand : AddSubImm :=
    ⟨w.extractLsb' 31 1, boolOfBit (w.extractLsb' 30 1), boolOfBit (w.extractLsb' 29 1),
      boolOfBit (w.extractLsb' 22 1), w.extractLsb' 10 12, w.extractLsb' 5 5, w.extractLsb' 0 5⟩
  if cand.encode = w then some cand else none

theorem AddSubImm.decode_encode (i : AddSubImm) : AddSubImm.decode i.encode = some i := by
  have h31 : (i.encode).extractLsb' 31 1 = i.sf := by unfold AddSubImm.encode; bv_decide
  have hb30 : (i.encode).extractLsb' 30 1 = bitOfBool i.op := by unfold AddSubImm.encode; bv_decide
  have h30 : boolOfBit ((i.encode).extractLsb' 30 1) = i.op := by
    rw [hb30]; exact boolOfBit_bitOfBool i.op
  have hb29 : (i.encode).extractLsb' 29 1 = bitOfBool i.setFlags := by
    unfold AddSubImm.encode; bv_decide
  have h29 : boolOfBit ((i.encode).extractLsb' 29 1) = i.setFlags := by
    rw [hb29]; exact boolOfBit_bitOfBool i.setFlags
  have hb22 : (i.encode).extractLsb' 22 1 = bitOfBool i.sh := by unfold AddSubImm.encode; bv_decide
  have h22 : boolOfBit ((i.encode).extractLsb' 22 1) = i.sh := by
    rw [hb22]; exact boolOfBit_bitOfBool i.sh
  have h10 : (i.encode).extractLsb' 10 12 = i.imm12 := by unfold AddSubImm.encode; bv_decide
  have h5 : (i.encode).extractLsb' 5 5 = i.rn := by unfold AddSubImm.encode; bv_decide
  have h0 : (i.encode).extractLsb' 0 5 = i.rd := by unfold AddSubImm.encode; bv_decide
  unfold AddSubImm.decode
  simp [h31, h30, h29, h22, h10, h5, h0]

theorem AddSubImm.marker23 (i : AddSubImm) : (i.encode).extractLsb' 23 6 = 0b100010#6 := by
  unfold AddSubImm.encode; bv_decide

theorem AddSubImm.marker24 (i : AddSubImm) : (i.encode).extractLsb' 24 5 = 0b10001#5 := by
  unfold AddSubImm.encode; bv_decide

/-! ## Family 3: logical immediate (`and`/`orr`/`eor`, restricted) -/

inductive LogicalOp where
  | and | orr | eor
  deriving DecidableEq, Repr

def LogicalOp.code : LogicalOp → BitVec 2
  | .and => 0b00 | .orr => 0b01 | .eor => 0b10

def LogicalOp.ofCode (c : BitVec 2) : Option LogicalOp :=
  if c = 0b00 then some .and
  else if c = 0b01 then some .orr
  else if c = 0b10 then some .eor
  else none

/-- `sf opc(2) 100100 N immr(6) imms(6) Rn(5) Rd(5)`, restricted to `sf = 1`
(64-bit only) and `N = 1, immr = 0`: the representable bitmask immediates are
exactly the 64-bit contiguous low-order runs `(1 <<< (imms + 1)) - 1` for
`imms : BitVec 6` (see `Semantics.lean`), i.e. Arm DDI 0602 ID032025's general
`DecodeBitMasks` rotate-and-replicate immediate space with the rotation and
sub-64 element size left unimplemented. Arm DDI 0602 ID032025, "Logical
(immediate)". -/
structure LogicalImm where
  opc : LogicalOp
  imms : BitVec 6
  rn : BitVec 5
  rd : BitVec 5
  deriving DecidableEq, Repr

def LogicalImm.encode (i : LogicalImm) : BitVec 32 :=
  (0b1#1) ++ i.opc.code ++ (0b100100#6) ++ (0b1#1) ++ (0b000000#6) ++ i.imms ++ i.rn ++ i.rd

def LogicalImm.decode (w : BitVec 32) : Option LogicalImm :=
  match LogicalOp.ofCode (w.extractLsb' 29 2) with
  | none => none
  | some opc =>
    let cand : LogicalImm := ⟨opc, w.extractLsb' 10 6, w.extractLsb' 5 5, w.extractLsb' 0 5⟩
    if cand.encode = w then some cand else none

theorem LogicalImm.decode_encode (i : LogicalImm) : LogicalImm.decode i.encode = some i := by
  have hopc : (i.encode).extractLsb' 29 2 = i.opc.code := by unfold LogicalImm.encode; bv_decide
  have h10 : (i.encode).extractLsb' 10 6 = i.imms := by unfold LogicalImm.encode; bv_decide
  have h5 : (i.encode).extractLsb' 5 5 = i.rn := by unfold LogicalImm.encode; bv_decide
  have h0 : (i.encode).extractLsb' 0 5 = i.rd := by unfold LogicalImm.encode; bv_decide
  have hcode : LogicalOp.ofCode i.opc.code = some i.opc := by cases i.opc <;> decide
  unfold LogicalImm.decode
  rw [hopc, hcode]
  simp [h10, h5, h0]

theorem LogicalImm.marker23 (i : LogicalImm) : (i.encode).extractLsb' 23 6 = 0b100100#6 := by
  unfold LogicalImm.encode; bv_decide

theorem LogicalImm.marker24 (i : LogicalImm) : (i.encode).extractLsb' 24 5 = 0b10010#5 := by
  unfold LogicalImm.encode; bv_decide

/-! ## Family 4: load/store unsigned offset (`ldr`/`str`/`ldrb`/`strb`) -/

inductive LsSize where
  | byte | word32 | double64
  deriving DecidableEq, Repr

def LsSize.code : LsSize → BitVec 2
  | .byte => 0b00 | .word32 => 0b10 | .double64 => 0b11

def LsSize.ofCode (c : BitVec 2) : Option LsSize :=
  if c = 0b00 then some .byte
  else if c = 0b10 then some .word32
  else if c = 0b11 then some .double64
  else none

/-- `size(2) 111001 0 L imm12(12) Rn(5) Rt(5)`, `L = 1` for `ldr`/`ldrb`,
`L = 0` for `str`/`strb`. Halfword (`size = 01`) and the signed-load `opc`
variants are excluded by construction (`LsSize` has no such constructor).
Arm DDI 0602 ID032025, "LDR/STR (immediate, unsigned offset)". -/
structure LoadStoreUImm where
  size : LsSize
  isLoad : Bool
  imm12 : BitVec 12
  rn : BitVec 5
  rt : BitVec 5
  deriving DecidableEq, Repr

def LoadStoreUImm.encode (i : LoadStoreUImm) : BitVec 32 :=
  i.size.code ++ (0b111001#6) ++ (0b0#1) ++ bitOfBool i.isLoad ++ i.imm12 ++ i.rn ++ i.rt

def LoadStoreUImm.decode (w : BitVec 32) : Option LoadStoreUImm :=
  match LsSize.ofCode (w.extractLsb' 30 2) with
  | none => none
  | some size =>
    let cand : LoadStoreUImm :=
      ⟨size, boolOfBit (w.extractLsb' 22 1), w.extractLsb' 10 12, w.extractLsb' 5 5,
        w.extractLsb' 0 5⟩
    if cand.encode = w then some cand else none

theorem LoadStoreUImm.decode_encode (i : LoadStoreUImm) :
    LoadStoreUImm.decode i.encode = some i := by
  have hsz : (i.encode).extractLsb' 30 2 = i.size.code := by unfold LoadStoreUImm.encode; bv_decide
  have hb22 : (i.encode).extractLsb' 22 1 = bitOfBool i.isLoad := by
    unfold LoadStoreUImm.encode; bv_decide
  have h22 : boolOfBit ((i.encode).extractLsb' 22 1) = i.isLoad := by
    rw [hb22]; exact boolOfBit_bitOfBool i.isLoad
  have h10 : (i.encode).extractLsb' 10 12 = i.imm12 := by unfold LoadStoreUImm.encode; bv_decide
  have h5 : (i.encode).extractLsb' 5 5 = i.rn := by unfold LoadStoreUImm.encode; bv_decide
  have h0 : (i.encode).extractLsb' 0 5 = i.rt := by unfold LoadStoreUImm.encode; bv_decide
  have hcode : LsSize.ofCode i.size.code = some i.size := by cases i.size <;> decide
  unfold LoadStoreUImm.decode
  rw [hsz, hcode]
  simp [h22, h10, h5, h0]

theorem LoadStoreUImm.marker23 (i : LoadStoreUImm) :
    (i.encode).extractLsb' 23 6 = 0b110010#6 := by unfold LoadStoreUImm.encode; bv_decide

theorem LoadStoreUImm.marker24 (i : LoadStoreUImm) :
    (i.encode).extractLsb' 24 5 = 0b11001#5 := by unfold LoadStoreUImm.encode; bv_decide

/-! ## Family 5: add/sub shifted register -/

inductive ShiftType where
  | lsl | lsr | asr
  deriving DecidableEq, Repr

def ShiftType.code : ShiftType → BitVec 2
  | .lsl => 0b00 | .lsr => 0b01 | .asr => 0b10

def ShiftType.ofCode (c : BitVec 2) : Option ShiftType :=
  if c = 0b00 then some .lsl
  else if c = 0b01 then some .lsr
  else if c = 0b10 then some .asr
  else none

/-- `sf op S 01011 shift(2) 0 Rm(5) imm6(6) Rn(5) Rd(5)`. `shift = 0b11`
(`ror`) is architecturally reserved for add/sub and is excluded by
construction. Arm DDI 0602 ID032025, "Add/subtract (shifted register)". -/
structure AddSubShiftedReg where
  sf : BitVec 1
  op : Bool
  setFlags : Bool
  shift : ShiftType
  rm : BitVec 5
  imm6 : BitVec 6
  rn : BitVec 5
  rd : BitVec 5
  deriving DecidableEq, Repr

def AddSubShiftedReg.encode (i : AddSubShiftedReg) : BitVec 32 :=
  i.sf ++ bitOfBool i.op ++ bitOfBool i.setFlags ++ (0b01011#5) ++ i.shift.code ++ (0b0#1) ++
    i.rm ++ i.imm6 ++ i.rn ++ i.rd

def AddSubShiftedReg.decode (w : BitVec 32) : Option AddSubShiftedReg :=
  match ShiftType.ofCode (w.extractLsb' 22 2) with
  | none => none
  | some shift =>
    let cand : AddSubShiftedReg :=
      ⟨w.extractLsb' 31 1, boolOfBit (w.extractLsb' 30 1), boolOfBit (w.extractLsb' 29 1), shift,
        w.extractLsb' 16 5, w.extractLsb' 10 6, w.extractLsb' 5 5, w.extractLsb' 0 5⟩
    if cand.encode = w then some cand else none

theorem AddSubShiftedReg.decode_encode (i : AddSubShiftedReg) :
    AddSubShiftedReg.decode i.encode = some i := by
  have h31 : (i.encode).extractLsb' 31 1 = i.sf := by unfold AddSubShiftedReg.encode; bv_decide
  have hb30 : (i.encode).extractLsb' 30 1 = bitOfBool i.op := by
    unfold AddSubShiftedReg.encode; bv_decide
  have h30 : boolOfBit ((i.encode).extractLsb' 30 1) = i.op := by
    rw [hb30]; exact boolOfBit_bitOfBool i.op
  have hb29 : (i.encode).extractLsb' 29 1 = bitOfBool i.setFlags := by
    unfold AddSubShiftedReg.encode; bv_decide
  have h29 : boolOfBit ((i.encode).extractLsb' 29 1) = i.setFlags := by
    rw [hb29]; exact boolOfBit_bitOfBool i.setFlags
  have h22 : (i.encode).extractLsb' 22 2 = i.shift.code := by
    unfold AddSubShiftedReg.encode; bv_decide
  have h16 : (i.encode).extractLsb' 16 5 = i.rm := by unfold AddSubShiftedReg.encode; bv_decide
  have h10 : (i.encode).extractLsb' 10 6 = i.imm6 := by unfold AddSubShiftedReg.encode; bv_decide
  have h5 : (i.encode).extractLsb' 5 5 = i.rn := by unfold AddSubShiftedReg.encode; bv_decide
  have h0 : (i.encode).extractLsb' 0 5 = i.rd := by unfold AddSubShiftedReg.encode; bv_decide
  have hcode : ShiftType.ofCode i.shift.code = some i.shift := by cases i.shift <;> decide
  unfold AddSubShiftedReg.decode
  rw [h22, hcode]
  simp [h31, h30, h29, h16, h10, h5, h0]

/-- Unlike the other families, `24 5` is not this family's full marker (that
also needs `shift`'s top bit at `23`, which varies), but it is a literal:
`shift.code`'s top bit never reaches bit 24. -/
theorem AddSubShiftedReg.marker24 (i : AddSubShiftedReg) :
    (i.encode).extractLsb' 24 5 = 0b01011#5 := by unfold AddSubShiftedReg.encode; bv_decide

/-! ## Family 6/7: `cbz` and `svc`, reused from `Grass.ISA.AArch64.Control` -/

theorem CompareZero.marker24 (i : CompareZero) :
    i.encode.extractLsb' 24 5 = 0b10100#5 := by
  unfold CompareZero.encode; bv_decide

theorem CompareZero.marker24_7 (i : CompareZero) :
    i.encode.extractLsb' 24 7 = 0b0110100#7 := by
  unfold CompareZero.encode; bv_decide

theorem svcMarker24 (imm : BitVec 16) :
    (svcEncode imm).extractLsb' 24 5 = 0b10100#5 := by
  unfold svcEncode Grass.ISA.AArch64.SupervisorCall.encode; bv_decide

theorem svcMarker24_7 (imm : BitVec 16) :
    (svcEncode imm).extractLsb' 24 7 = 0b1010100#7 := by
  unfold svcEncode Grass.ISA.AArch64.SupervisorCall.encode; bv_decide

theorem svcMarker21 (imm : BitVec 16) :
    (svcEncode imm).extractLsb' 21 11 = 0b11010100000#11 := by
  unfold svcEncode Grass.ISA.AArch64.SupervisorCall.encode; bv_decide

/-! ## Family 8: `hlt` -/

/-- `1101 0100 010 imm16(16) 00000`. Arm DDI 0602 ID032025, "HLT". The
fixed 11-bit prefix is cross-checked against `Control.SupervisorCall`'s own
audited prefix `0b11010100000#11` (`svc`'s `imm16 = 0`, `op2 = 00001` case):
`hlt`/`brk`/`svc` share the leading byte `0xD4` and differ only in the 3-bit
`opc` field this prefix carries (`svc = 000`, `brk = 001`, `hlt = 010`), and
in `op2` (`svc`'s trailing `00001` vs `hlt`'s `00000`). -/
structure Hlt where
  imm16 : BitVec 16
  deriving DecidableEq, Repr

def Hlt.encode (i : Hlt) : BitVec 32 := (0b11010100010#11) ++ i.imm16 ++ (0b00000#5)

def Hlt.decode (w : BitVec 32) : Option Hlt :=
  let cand : Hlt := ⟨w.extractLsb' 5 16⟩
  if cand.encode = w then some cand else none

theorem Hlt.decode_encode (i : Hlt) : Hlt.decode i.encode = some i := by
  have h5 : (i.encode).extractLsb' 5 16 = i.imm16 := by unfold Hlt.encode; bv_decide
  unfold Hlt.decode
  simp [h5]

theorem Hlt.marker23 (i : Hlt) : (i.encode).extractLsb' 23 6 = 0b101000#6 := by
  unfold Hlt.encode; bv_decide

theorem Hlt.marker24 (i : Hlt) : (i.encode).extractLsb' 24 5 = 0b10100#5 := by
  unfold Hlt.encode; bv_decide

theorem Hlt.marker24_7 (i : Hlt) : (i.encode).extractLsb' 24 7 = 0b1010100#7 := by
  unfold Hlt.encode; bv_decide

theorem Hlt.marker21 (i : Hlt) : (i.encode).extractLsb' 21 11 = 0b11010100010#11 := by
  unfold Hlt.encode; bv_decide


/-! ## Family 9: unconditional branch immediate (`b`, `bl`) -/

/-- `op(1) 00101 imm26(26)`. `op = false` is `b`, `true` is `bl`. Arm DDI
0602 ID032025, "Unconditional branch (immediate)". The only fixed-bit window
this family has is `[30:26]`; everything else is `op` or `imm26`. -/
structure BranchImm where
  op : BitVec 1
  imm26 : BitVec 26
  deriving DecidableEq, Repr

def BranchImm.encode (i : BranchImm) : BitVec 32 := i.op ++ (0b00101#5) ++ i.imm26

def BranchImm.decode (w : BitVec 32) : Option BranchImm :=
  let cand : BranchImm := ⟨w.extractLsb' 31 1, w.extractLsb' 0 26⟩
  if cand.encode = w then some cand else none

theorem BranchImm.decode_encode (i : BranchImm) : BranchImm.decode i.encode = some i := by
  have h31 : (i.encode).extractLsb' 31 1 = i.op := by unfold BranchImm.encode; bv_decide
  have h0 : (i.encode).extractLsb' 0 26 = i.imm26 := by unfold BranchImm.encode; bv_decide
  unfold BranchImm.decode
  simp [h31, h0]


theorem BranchImm.marker26_3 (i : BranchImm) : (i.encode).extractLsb' 26 3 = 0b101#3 := by
  unfold BranchImm.encode; bv_decide

theorem BranchImm.marker26_5 (i : BranchImm) : (i.encode).extractLsb' 26 5 = 0b00101#5 := by
  unfold BranchImm.encode; bv_decide

/-! ## Family 10: unconditional branch register (`br`, `blr`, `ret`) -/

inductive BranchRegOp where
  | br | blr | ret
  deriving DecidableEq, Repr

def BranchRegOp.code : BranchRegOp → BitVec 4
  | .br => 0b0000 | .blr => 0b0001 | .ret => 0b0010

def BranchRegOp.ofCode (c : BitVec 4) : Option BranchRegOp :=
  if c = 0b0000 then some .br
  else if c = 0b0001 then some .blr
  else if c = 0b0010 then some .ret
  else none

/-- `1101011 opc(4) 11111 000000 Rn(5) 00000`. `opc = 0000/0001/0010` is
`br`/`blr`/`ret`; other `opc` values (`eret`, `drps`, the pointer-
authentication forms) are excluded by construction. `br`/`blr` land through
`Rn` as an ordinary indirect control transfer — this ISA does not model an
import slot or a return-address predictor. Arm DDI 0602 ID032025,
"Unconditional branch (register)". -/
structure BranchReg where
  op : BranchRegOp
  rn : BitVec 5
  deriving DecidableEq, Repr

def BranchReg.encode (i : BranchReg) : BitVec 32 :=
  (0b1101011#7) ++ i.op.code ++ (0b11111#5) ++ (0b000000#6) ++ i.rn ++ (0b00000#5)

def BranchReg.decode (w : BitVec 32) : Option BranchReg :=
  match BranchRegOp.ofCode (w.extractLsb' 21 4) with
  | none => none
  | some op =>
    let cand : BranchReg := ⟨op, w.extractLsb' 5 5⟩
    if cand.encode = w then some cand else none

theorem BranchReg.decode_encode (i : BranchReg) : BranchReg.decode i.encode = some i := by
  have hop : (i.encode).extractLsb' 21 4 = i.op.code := by unfold BranchReg.encode; bv_decide
  have h5 : (i.encode).extractLsb' 5 5 = i.rn := by unfold BranchReg.encode; bv_decide
  have hcode : BranchRegOp.ofCode i.op.code = some i.op := by cases i.op <;> decide
  unfold BranchReg.decode
  rw [hop, hcode]
  simp [h5]


theorem BranchReg.marker25_4 (i : BranchReg) : (i.encode).extractLsb' 25 4 = 0b1011#4 := by
  unfold BranchReg.encode; bv_decide

theorem BranchReg.marker16_5 (i : BranchReg) : (i.encode).extractLsb' 16 5 = 0b11111#5 := by
  unfold BranchReg.encode; bv_decide

theorem BranchReg.marker25_5 (i : BranchReg) : (i.encode).extractLsb' 25 5 = 0b01011#5 := by
  unfold BranchReg.encode; bv_decide

theorem BranchReg.marker25_6 (i : BranchReg) : (i.encode).extractLsb' 25 6 = 0b101011#6 := by
  unfold BranchReg.encode; bv_decide

theorem BranchReg.marker25_7 (i : BranchReg) : (i.encode).extractLsb' 25 7 = 0b1101011#7 := by
  unfold BranchReg.encode; bv_decide

theorem BranchReg.marker26_5 (i : BranchReg) : (i.encode).extractLsb' 26 5 = 0b10101#5 := by
  unfold BranchReg.encode; bv_decide

theorem BranchReg.marker10_11 (i : BranchReg) : (i.encode).extractLsb' 10 11 = 0b11111000000#11 := by
  unfold BranchReg.encode; bv_decide

/-! ## Family 11: conditional branch (`b.cond`) -/

/-- `01010100 imm19(19) 0 cond(4)`. `cond` is a raw 4-bit field: every one of
the 16 encodings (including `1110`/`1111`, both "always") is a legal
`b.cond`, so unlike the enum-restricted families this one has no `ofCode`
partial function. Arm DDI 0602 ID032025, "Compare & branch, and conditional
branch (immediate)". -/
structure CondBranch where
  imm19 : BitVec 19
  cond : BitVec 4
  deriving DecidableEq, Repr

def CondBranch.encode (i : CondBranch) : BitVec 32 :=
  (0b01010100#8) ++ i.imm19 ++ (0b0#1) ++ i.cond

def CondBranch.decode (w : BitVec 32) : Option CondBranch :=
  let cand : CondBranch := ⟨w.extractLsb' 5 19, w.extractLsb' 0 4⟩
  if cand.encode = w then some cand else none

theorem CondBranch.decode_encode (i : CondBranch) : CondBranch.decode i.encode = some i := by
  have h5 : (i.encode).extractLsb' 5 19 = i.imm19 := by unfold CondBranch.encode; bv_decide
  have h0 : (i.encode).extractLsb' 0 4 = i.cond := by unfold CondBranch.encode; bv_decide
  unfold CondBranch.decode
  simp [h5, h0]

theorem CondBranch.marker24_5 (i : CondBranch) : (i.encode).extractLsb' 24 5 = 0b10100#5 := by
  unfold CondBranch.encode; bv_decide

theorem CondBranch.marker24_7 (i : CondBranch) : (i.encode).extractLsb' 24 7 = 0b1010100#7 := by
  unfold CondBranch.encode; bv_decide

theorem CondBranch.marker24_8 (i : CondBranch) : (i.encode).extractLsb' 24 8 = 0b01010100#8 := by
  unfold CondBranch.encode; bv_decide

theorem CondBranch.marker26_5 (i : CondBranch) : (i.encode).extractLsb' 26 5 = 0b10101#5 := by
  unfold CondBranch.encode; bv_decide

theorem CondBranch.marker25_7 (i : CondBranch) : (i.encode).extractLsb' 25 7 = 0b0101010#7 := by
  unfold CondBranch.encode; bv_decide

/-! ## Family 12: compare-and-branch-if-nonzero (`cbnz`) -/

/-- `sf 0110101 imm19(19) Rt(5)`: `Grass.ISA.AArch64.Control.CompareZero`
with its `op` bit (the one this repository does not own, since `Control.lean`
is out of scope for this pass) fixed to `1` instead of `0`. A dedicated
struct rather than an edit to `CompareZero`, per the file ownership for this
pass. Arm DDI 0602 ID032025, "Compare and branch (immediate)". -/
structure Cbnz where
  sf : BitVec 1
  imm19 : BitVec 19
  rt : BitVec 5
  deriving DecidableEq, Repr

def Cbnz.encode (i : Cbnz) : BitVec 32 := i.sf ++ (0b0110101#7) ++ i.imm19 ++ i.rt

def Cbnz.decode (w : BitVec 32) : Option Cbnz :=
  let cand : Cbnz := ⟨w.extractLsb' 31 1, w.extractLsb' 5 19, w.extractLsb' 0 5⟩
  if cand.encode = w then some cand else none

theorem Cbnz.decode_encode (i : Cbnz) : Cbnz.decode i.encode = some i := by
  have h31 : (i.encode).extractLsb' 31 1 = i.sf := by unfold Cbnz.encode; bv_decide
  have h5 : (i.encode).extractLsb' 5 19 = i.imm19 := by unfold Cbnz.encode; bv_decide
  have h0 : (i.encode).extractLsb' 0 5 = i.rt := by unfold Cbnz.encode; bv_decide
  unfold Cbnz.decode
  simp [h31, h5, h0]

theorem Cbnz.marker24_5 (i : Cbnz) : (i.encode).extractLsb' 24 5 = 0b10101#5 := by
  unfold Cbnz.encode; bv_decide

theorem Cbnz.marker24_7 (i : Cbnz) : (i.encode).extractLsb' 24 7 = 0b0110101#7 := by
  unfold Cbnz.encode; bv_decide

theorem Cbnz.marker26_5 (i : Cbnz) : (i.encode).extractLsb' 26 5 = 0b01101#5 := by
  unfold Cbnz.encode; bv_decide

theorem Cbnz.marker25_6 (i : Cbnz) : (i.encode).extractLsb' 25 6 = 0b011010#6 := by
  unfold Cbnz.encode; bv_decide

/-! ## Family 13: PC-relative address (`adr`, `adrp`) -/

/-- `op(1) immlo(2) 10000 immhi(19) Rd(5)`. `op = false` is `adr` (the
21-bit signed `immhi:immlo` byte offset added to the instruction's own PC);
`op = true` is `adrp` (the same offset, scaled by `<<< 12` and added to PC
with its low 12 bits masked off first — the page, not the byte, address).
Arm DDI 0602 ID032025, "PC-rel. addressing". -/
structure AdrAdrp where
  op : BitVec 1
  immlo : BitVec 2
  immhi : BitVec 19
  rd : BitVec 5
  deriving DecidableEq, Repr

def AdrAdrp.encode (i : AdrAdrp) : BitVec 32 :=
  i.op ++ i.immlo ++ (0b10000#5) ++ i.immhi ++ i.rd

def AdrAdrp.decode (w : BitVec 32) : Option AdrAdrp :=
  let cand : AdrAdrp :=
    ⟨w.extractLsb' 31 1, w.extractLsb' 29 2, w.extractLsb' 5 19, w.extractLsb' 0 5⟩
  if cand.encode = w then some cand else none

theorem AdrAdrp.decode_encode (i : AdrAdrp) : AdrAdrp.decode i.encode = some i := by
  have h31 : (i.encode).extractLsb' 31 1 = i.op := by unfold AdrAdrp.encode; bv_decide
  have h29 : (i.encode).extractLsb' 29 2 = i.immlo := by unfold AdrAdrp.encode; bv_decide
  have h5 : (i.encode).extractLsb' 5 19 = i.immhi := by unfold AdrAdrp.encode; bv_decide
  have h0 : (i.encode).extractLsb' 0 5 = i.rd := by unfold AdrAdrp.encode; bv_decide
  unfold AdrAdrp.decode
  simp [h31, h29, h5, h0]

theorem AdrAdrp.marker24_5 (i : AdrAdrp) : (i.encode).extractLsb' 24 5 = 0b10000#5 := by
  unfold AdrAdrp.encode; bv_decide

theorem AdrAdrp.marker26_3 (i : AdrAdrp) : (i.encode).extractLsb' 26 3 = 0b100#3 := by
  unfold AdrAdrp.encode; bv_decide

theorem AdrAdrp.marker25_4 (i : AdrAdrp) : (i.encode).extractLsb' 25 4 = 0b1000#4 := by
  unfold AdrAdrp.encode; bv_decide

/-! ## Family 14: logical shifted-register (`and`/`orr`/`eor`/`ands`) -/

inductive LogicalShiftOp where
  | and | orr | eor | ands
  deriving DecidableEq, Repr

def LogicalShiftOp.code : LogicalShiftOp → BitVec 2
  | .and => 0b00 | .orr => 0b01 | .eor => 0b10 | .ands => 0b11

def LogicalShiftOp.ofCode (c : BitVec 2) : Option LogicalShiftOp :=
  if c = 0b00 then some .and
  else if c = 0b01 then some .orr
  else if c = 0b10 then some .eor
  else if c = 0b11 then some .ands
  else none

/-- `sf opc(2) 01010 shift(2) N Rm(5) imm6(6) Rn(5) Rd(5)`, restricted to
`N = 0` (`bic`/`orn`/`eon`/`bics`, the negated forms, are excluded by
construction). `opc = 00/01/10/11` is `and`/`orr`/`eor`/`ands`;
`orr xd, xzr, xm` is `mov xd, xm` and `ands` with `rd = xzr` is `tst` —
both already fall out of the state layer's zero-register/discard-on-write
convention (`State.readGpr`/`State.writeGpr`), so no separate alias
constructor is needed. Arm DDI 0602 ID032025, "Logical (shifted register)". -/
structure LogicalShiftedReg where
  sf : BitVec 1
  opc : LogicalShiftOp
  shift : ShiftType
  rm : BitVec 5
  imm6 : BitVec 6
  rn : BitVec 5
  rd : BitVec 5
  deriving DecidableEq, Repr

def LogicalShiftedReg.encode (i : LogicalShiftedReg) : BitVec 32 :=
  i.sf ++ i.opc.code ++ (0b01010#5) ++ i.shift.code ++ (0b0#1) ++ i.rm ++ i.imm6 ++ i.rn ++ i.rd

def LogicalShiftedReg.decode (w : BitVec 32) : Option LogicalShiftedReg :=
  match LogicalShiftOp.ofCode (w.extractLsb' 29 2) with
  | none => none
  | some opc =>
    match ShiftType.ofCode (w.extractLsb' 22 2) with
    | none => none
    | some shift =>
      let cand : LogicalShiftedReg :=
        ⟨w.extractLsb' 31 1, opc, shift, w.extractLsb' 16 5, w.extractLsb' 10 6,
          w.extractLsb' 5 5, w.extractLsb' 0 5⟩
      if cand.encode = w then some cand else none

theorem LogicalShiftedReg.decode_encode (i : LogicalShiftedReg) :
    LogicalShiftedReg.decode i.encode = some i := by
  have hopc : (i.encode).extractLsb' 29 2 = i.opc.code := by
    unfold LogicalShiftedReg.encode; bv_decide
  have hshift : (i.encode).extractLsb' 22 2 = i.shift.code := by
    unfold LogicalShiftedReg.encode; bv_decide
  have h31 : (i.encode).extractLsb' 31 1 = i.sf := by unfold LogicalShiftedReg.encode; bv_decide
  have h16 : (i.encode).extractLsb' 16 5 = i.rm := by unfold LogicalShiftedReg.encode; bv_decide
  have h10 : (i.encode).extractLsb' 10 6 = i.imm6 := by unfold LogicalShiftedReg.encode; bv_decide
  have h5 : (i.encode).extractLsb' 5 5 = i.rn := by unfold LogicalShiftedReg.encode; bv_decide
  have h0 : (i.encode).extractLsb' 0 5 = i.rd := by unfold LogicalShiftedReg.encode; bv_decide
  have hcodeOpc : LogicalShiftOp.ofCode i.opc.code = some i.opc := by cases i.opc <;> decide
  have hcodeShift : ShiftType.ofCode i.shift.code = some i.shift := by cases i.shift <;> decide
  unfold LogicalShiftedReg.decode
  rw [hopc, hcodeOpc, hshift, hcodeShift]
  simp [h31, h16, h10, h5, h0]

theorem LogicalShiftedReg.marker24_5 (i : LogicalShiftedReg) :
    (i.encode).extractLsb' 24 5 = 0b01010#5 := by unfold LogicalShiftedReg.encode; bv_decide

theorem LogicalShiftedReg.marker26_3 (i : LogicalShiftedReg) :
    (i.encode).extractLsb' 26 3 = 0b010#3 := by unfold LogicalShiftedReg.encode; bv_decide

theorem LogicalShiftedReg.marker25_4 (i : LogicalShiftedReg) :
    (i.encode).extractLsb' 25 4 = 0b0101#4 := by unfold LogicalShiftedReg.encode; bv_decide

/-! ## Family 15: `nop` -/

/-- `hint #0`, the fixed word `0xD503201F`. No fields: every other `hint`
immediate, and every other system instruction, is out of scope. Arm DDI
0602 ID032025, "NOP". -/
structure Nop where
  deriving DecidableEq, Repr

def Nop.encode (_ : Nop) : BitVec 32 := 0xD503201F#32

def Nop.decode (w : BitVec 32) : Option Nop := if w = 0xD503201F#32 then some ⟨⟩ else none

theorem Nop.decode_encode (i : Nop) : Nop.decode i.encode = some i := by
  cases i; unfold Nop.decode Nop.encode; decide

theorem Nop.marker24_5 (i : Nop) : (i.encode).extractLsb' 24 5 = 0b10101#5 := by
  cases i; unfold Nop.encode; decide

theorem Nop.marker26_5 (i : Nop) : (i.encode).extractLsb' 26 5 = 0b10101#5 := by
  cases i; unfold Nop.encode; decide

theorem Nop.marker24_7 (i : Nop) : (i.encode).extractLsb' 24 7 = 0b1010101#7 := by
  cases i; unfold Nop.encode; decide

theorem Nop.marker10_11 (i : Nop) : (i.encode).extractLsb' 10 11 = 0b00011001000#11 := by
  cases i; unfold Nop.encode; decide


/-! ## The closed union -/

/-- Resolved A64 instructions. Every operand is concrete (a register field,
an immediate, a condition); nothing here names a label, a frame layout, or a
program. -/
inductive Instr where
  | moveWide (i : MoveWide)
  | addSubImm (i : AddSubImm)
  | logicalImm (i : LogicalImm)
  | loadStoreUImm (i : LoadStoreUImm)
  | addSubShiftedReg (i : AddSubShiftedReg)
  | cbz (i : CompareZero)
  | svc (imm : BitVec 16)
  | hlt (i : Hlt)
  | branchImm (i : BranchImm)
  | branchReg (i : BranchReg)
  | condBranch (i : CondBranch)
  | cbnz (i : Cbnz)
  | adrAdrp (i : AdrAdrp)
  | logicalShiftedReg (i : LogicalShiftedReg)
  | nop (i : Nop)
  deriving DecidableEq, Repr

def Instr.toWord : Instr → BitVec 32
  | .moveWide i => i.encode
  | .addSubImm i => i.encode
  | .logicalImm i => i.encode
  | .loadStoreUImm i => i.encode
  | .addSubShiftedReg i => i.encode
  | .cbz i => i.encode
  | .svc imm => svcEncode imm
  | .hlt i => i.encode
  | .branchImm i => i.encode
  | .branchReg i => i.encode
  | .condBranch i => i.encode
  | .cbnz i => i.encode
  | .adrAdrp i => i.encode
  | .logicalShiftedReg i => i.encode
  | .nop i => i.encode

/-- Canonical encoding of one instruction: its word, little-endian. -/
def encode (instr : Instr) : List UInt8 := wordToBytes instr.toWord

theorem encode_pos (instr : Instr) : 0 < (encode instr).length := by
  cases instr <;> simp [encode, Instr.toWord, wordToBytes]

def decodeMoveWide (w : BitVec 32) : Option (Instr × Nat) :=
  match MoveWide.decode w with | some i => some (.moveWide i, 4) | none => none

def decodeAddSubImm (w : BitVec 32) : Option (Instr × Nat) :=
  match AddSubImm.decode w with | some i => some (.addSubImm i, 4) | none => none

def decodeLogicalImm (w : BitVec 32) : Option (Instr × Nat) :=
  match LogicalImm.decode w with | some i => some (.logicalImm i, 4) | none => none

def decodeLoadStoreUImm (w : BitVec 32) : Option (Instr × Nat) :=
  match LoadStoreUImm.decode w with | some i => some (.loadStoreUImm i, 4) | none => none

def decodeAddSubShiftedReg (w : BitVec 32) : Option (Instr × Nat) :=
  match AddSubShiftedReg.decode w with | some i => some (.addSubShiftedReg i, 4) | none => none

def decodeCbz (w : BitVec 32) : Option (Instr × Nat) :=
  match CompareZero.decode w with | some i => some (.cbz i, 4) | none => none

def decodeSvc (w : BitVec 32) : Option (Instr × Nat) :=
  match svcDecode w with | some imm => some (.svc imm, 4) | none => none

def decodeHlt (w : BitVec 32) : Option (Instr × Nat) :=
  match Hlt.decode w with | some i => some (.hlt i, 4) | none => none

def decodeBranchImm (w : BitVec 32) : Option (Instr × Nat) :=
  match BranchImm.decode w with | some i => some (.branchImm i, 4) | none => none

def decodeBranchReg (w : BitVec 32) : Option (Instr × Nat) :=
  match BranchReg.decode w with | some i => some (.branchReg i, 4) | none => none

def decodeCondBranch (w : BitVec 32) : Option (Instr × Nat) :=
  match CondBranch.decode w with | some i => some (.condBranch i, 4) | none => none

def decodeCbnz (w : BitVec 32) : Option (Instr × Nat) :=
  match Cbnz.decode w with | some i => some (.cbnz i, 4) | none => none

def decodeAdrAdrp (w : BitVec 32) : Option (Instr × Nat) :=
  match AdrAdrp.decode w with | some i => some (.adrAdrp i, 4) | none => none

def decodeLogicalShiftedReg (w : BitVec 32) : Option (Instr × Nat) :=
  match LogicalShiftedReg.decode w with | some i => some (.logicalShiftedReg i, 4) | none => none

def decodeNop (w : BitVec 32) : Option (Instr × Nat) :=
  match Nop.decode w with | some i => some (.nop i, 4) | none => none

/-- Decode one instruction from the head of a byte list: the families are
tried in a fixed order, each fully self-verifying (it accepts a word only if
re-encoding its own extracted fields reproduces that word exactly), so an
earlier family accidentally claiming a later family's word is impossible by
construction, not by this ordering. -/
def decode (bytes : List UInt8) : Option (Instr × Nat) :=
  match bytes with
  | b0 :: b1 :: b2 :: b3 :: _ =>
    let w := bytesToWord b0 b1 b2 b3
    decodeMoveWide w <|> decodeAddSubImm w <|> decodeLogicalImm w <|> decodeLoadStoreUImm w <|>
      decodeAddSubShiftedReg w <|> decodeCbz w <|> decodeSvc w <|> decodeHlt w <|>
      decodeBranchImm w <|> decodeBranchReg w <|> decodeCondBranch w <|> decodeCbnz w <|>
      decodeAdrAdrp w <|> decodeLogicalShiftedReg w <|> decodeNop w
  | _ => none

/-- If `encodeA`'s own encoding always shows `tag` at `(pos, len)` (every
family's `markerPOSLEN` lemma above has this shape), and some word `w`
disagrees with `tag` there, no value of `A` can encode to `w`: this is the
only shape of inequality this file uses, and it is proved from two
`bv_decide` *equalities* (`marker`, folded into each call site) plus one
`decide` on closed literals — never a `bv_decide` inequality. -/
theorem encode_ne_of_marker_ne {A : Type} (encodeA : A → BitVec 32) {pos len : Nat} {tag : BitVec len}
    (marker : ∀ a, (encodeA a).extractLsb' pos len = tag) (a : A) (w : BitVec 32)
    (hne : tag ≠ w.extractLsb' pos len) : encodeA a ≠ w := by
  intro heq
  exact hne (by rw [← marker a, heq])

/-! ## Generic dispatch-window helpers for families 9-15

Families 1-8 above each prove `decodeX_none_Y` at one or two specific
`(pos, len)` windows. Families 9-15 need a few more windows against those
eight (still only the literal-mismatch technique `encode_ne_of_marker_ne`
uses, never a `bv_decide` inequality), so instead of one hardcoded lemma per
new window this section adds a single `decode_none_at` / `decodeX_none_at`
pair per family 1-8, generalized over `(pos, len, tag)`: the identical proof
shape as e.g. `MoveWide_decode_none_A`, just not committed to one window. -/

theorem MoveWide.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : MoveWide, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : MoveWide.decode w = none := by
  unfold MoveWide.decode
  cases MoveWideOp.ofCode (w.extractLsb' 29 2) with
  | none => rfl
  | some op => exact if_neg (encode_ne_of_marker_ne MoveWide.encode marker _ w hne)

theorem decodeMoveWide_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : MoveWide, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeMoveWide w = none := by
  unfold decodeMoveWide; rw [MoveWide.decode_none_at marker hne]

theorem AddSubImm.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : AddSubImm, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : AddSubImm.decode w = none := by
  unfold AddSubImm.decode
  exact if_neg (encode_ne_of_marker_ne AddSubImm.encode marker _ w hne)

theorem decodeAddSubImm_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : AddSubImm, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeAddSubImm w = none := by
  unfold decodeAddSubImm; rw [AddSubImm.decode_none_at marker hne]

theorem LogicalImm.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : LogicalImm, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : LogicalImm.decode w = none := by
  unfold LogicalImm.decode
  cases LogicalOp.ofCode (w.extractLsb' 29 2) with
  | none => rfl
  | some opc => exact if_neg (encode_ne_of_marker_ne LogicalImm.encode marker _ w hne)

theorem decodeLogicalImm_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : LogicalImm, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeLogicalImm w = none := by
  unfold decodeLogicalImm; rw [LogicalImm.decode_none_at marker hne]

theorem LoadStoreUImm.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : LoadStoreUImm, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : LoadStoreUImm.decode w = none := by
  unfold LoadStoreUImm.decode
  cases LsSize.ofCode (w.extractLsb' 30 2) with
  | none => rfl
  | some size => exact if_neg (encode_ne_of_marker_ne LoadStoreUImm.encode marker _ w hne)

theorem decodeLoadStoreUImm_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : LoadStoreUImm, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeLoadStoreUImm w = none := by
  unfold decodeLoadStoreUImm; rw [LoadStoreUImm.decode_none_at marker hne]

theorem AddSubShiftedReg.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : AddSubShiftedReg, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : AddSubShiftedReg.decode w = none := by
  unfold AddSubShiftedReg.decode
  cases ShiftType.ofCode (w.extractLsb' 22 2) with
  | none => rfl
  | some shift => exact if_neg (encode_ne_of_marker_ne AddSubShiftedReg.encode marker _ w hne)

theorem decodeAddSubShiftedReg_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : AddSubShiftedReg, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeAddSubShiftedReg w = none := by
  unfold decodeAddSubShiftedReg; rw [AddSubShiftedReg.decode_none_at marker hne]

theorem CompareZero.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : CompareZero, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : CompareZero.decode w = none := by
  unfold CompareZero.decode
  exact if_neg (encode_ne_of_marker_ne CompareZero.encode marker _ w hne)

theorem decodeCbz_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : CompareZero, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeCbz w = none := by
  unfold decodeCbz; rw [CompareZero.decode_none_at marker hne]

theorem svcDecode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ imm : BitVec 16, (svcEncode imm).extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : svcDecode w = none := by
  unfold svcDecode Grass.ISA.AArch64.SupervisorCall.decode
  exact if_neg (encode_ne_of_marker_ne Grass.ISA.AArch64.SupervisorCall.encode marker _ w hne)

theorem decodeSvc_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ imm : BitVec 16, (svcEncode imm).extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeSvc w = none := by
  unfold decodeSvc; rw [svcDecode_none_at marker hne]

theorem Hlt.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : Hlt, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : Hlt.decode w = none := by
  unfold Hlt.decode
  exact if_neg (encode_ne_of_marker_ne Hlt.encode marker _ w hne)

theorem decodeHlt_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : Hlt, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeHlt w = none := by
  unfold decodeHlt; rw [Hlt.decode_none_at marker hne]

/-! ## Extra fixed-bit windows on families 1-8, for dispatching families 9-15

Every theorem below is the same `unfold X.encode; bv_decide` structural
identity as `MoveWide.marker23` etc. above, just at a window one of families
9-15 needs. `26 3`/`26 5` distinguish against `BranchImm` (whose only clean
window is bits `[30:26]`, split at width 3 or 5 depending on whether the
compared family's own fixed bits reach bit 26); `25 4`/`16 5`/`25 5`/`25 6`/
`25 7` distinguish against `BranchReg` (clean only at bits `[31:25]`, `[20:16]`,
or subwindows of the former, since its `opc` occupies `[24:21]`). -/

theorem MoveWide.marker26_3 (i : MoveWide) : (i.encode).extractLsb' 26 3 = 0b100#3 := by
  unfold MoveWide.encode; bv_decide

theorem MoveWide.marker25_4 (i : MoveWide) : (i.encode).extractLsb' 25 4 = 0b1001#4 := by
  unfold MoveWide.encode; bv_decide

theorem AddSubImm.marker26_3 (i : AddSubImm) : (i.encode).extractLsb' 26 3 = 0b100#3 := by
  unfold AddSubImm.encode; bv_decide

theorem AddSubImm.marker25_4 (i : AddSubImm) : (i.encode).extractLsb' 25 4 = 0b1000#4 := by
  unfold AddSubImm.encode; bv_decide

theorem LogicalImm.marker26_3 (i : LogicalImm) : (i.encode).extractLsb' 26 3 = 0b100#3 := by
  unfold LogicalImm.encode; bv_decide

theorem LogicalImm.marker16_5 (i : LogicalImm) : (i.encode).extractLsb' 16 5 = 0b00000#5 := by
  unfold LogicalImm.encode; bv_decide

theorem LoadStoreUImm.marker26_3 (i : LoadStoreUImm) : (i.encode).extractLsb' 26 3 = 0b110#3 := by
  unfold LoadStoreUImm.encode; bv_decide

theorem LoadStoreUImm.marker25_5 (i : LoadStoreUImm) : (i.encode).extractLsb' 25 5 = 0b11100#5 := by
  unfold LoadStoreUImm.encode; bv_decide

theorem AddSubShiftedReg.marker26_3 (i : AddSubShiftedReg) :
    (i.encode).extractLsb' 26 3 = 0b010#3 := by unfold AddSubShiftedReg.encode; bv_decide

theorem AddSubShiftedReg.marker25_4 (i : AddSubShiftedReg) :
    (i.encode).extractLsb' 25 4 = 0b0101#4 := by unfold AddSubShiftedReg.encode; bv_decide

theorem CompareZero.marker26_5 (i : CompareZero) : i.encode.extractLsb' 26 5 = 0b01101#5 := by
  unfold CompareZero.encode; bv_decide

theorem CompareZero.marker25_6 (i : CompareZero) : i.encode.extractLsb' 25 6 = 0b011010#6 := by
  unfold CompareZero.encode; bv_decide

theorem svcMarker26_5 (imm : BitVec 16) : (svcEncode imm).extractLsb' 26 5 = 0b10101#5 := by
  unfold svcEncode Grass.ISA.AArch64.SupervisorCall.encode; bv_decide

theorem svcMarker25_7 (imm : BitVec 16) : (svcEncode imm).extractLsb' 25 7 = 0b1101010#7 := by
  unfold svcEncode Grass.ISA.AArch64.SupervisorCall.encode; bv_decide

theorem svcMarker24_8 (imm : BitVec 16) : (svcEncode imm).extractLsb' 24 8 = 0b11010100#8 := by
  unfold svcEncode Grass.ISA.AArch64.SupervisorCall.encode; bv_decide

theorem Hlt.marker26_5 (i : Hlt) : (i.encode).extractLsb' 26 5 = 0b10101#5 := by
  unfold Hlt.encode; bv_decide

theorem Hlt.marker25_7 (i : Hlt) : (i.encode).extractLsb' 25 7 = 0b1101010#7 := by
  unfold Hlt.encode; bv_decide

theorem Hlt.marker24_8 (i : Hlt) : (i.encode).extractLsb' 24 8 = 0b11010100#8 := by
  unfold Hlt.encode; bv_decide

theorem BranchImm.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : BranchImm, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : BranchImm.decode w = none := by
  unfold BranchImm.decode
  exact if_neg (encode_ne_of_marker_ne BranchImm.encode marker _ w hne)

theorem decodeBranchImm_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : BranchImm, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeBranchImm w = none := by
  unfold decodeBranchImm; rw [BranchImm.decode_none_at marker hne]

theorem decodeBranchImm_self (i : BranchImm) : decodeBranchImm i.encode = some (.branchImm i, 4) := by
  unfold decodeBranchImm; rw [BranchImm.decode_encode]

theorem BranchReg.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : BranchReg, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : BranchReg.decode w = none := by
  unfold BranchReg.decode
  cases BranchRegOp.ofCode (w.extractLsb' 21 4) with
  | none => rfl
  | some op => exact if_neg (encode_ne_of_marker_ne BranchReg.encode marker _ w hne)

theorem decodeBranchReg_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : BranchReg, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeBranchReg w = none := by
  unfold decodeBranchReg; rw [BranchReg.decode_none_at marker hne]

theorem decodeBranchReg_self (i : BranchReg) : decodeBranchReg i.encode = some (.branchReg i, 4) := by
  unfold decodeBranchReg; rw [BranchReg.decode_encode]

theorem CondBranch.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : CondBranch, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : CondBranch.decode w = none := by
  unfold CondBranch.decode
  exact if_neg (encode_ne_of_marker_ne CondBranch.encode marker _ w hne)

theorem decodeCondBranch_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : CondBranch, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeCondBranch w = none := by
  unfold decodeCondBranch; rw [CondBranch.decode_none_at marker hne]

theorem decodeCondBranch_self (i : CondBranch) :
    decodeCondBranch i.encode = some (.condBranch i, 4) := by
  unfold decodeCondBranch; rw [CondBranch.decode_encode]

theorem Cbnz.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : Cbnz, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : Cbnz.decode w = none := by
  unfold Cbnz.decode
  exact if_neg (encode_ne_of_marker_ne Cbnz.encode marker _ w hne)

theorem decodeCbnz_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : Cbnz, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeCbnz w = none := by
  unfold decodeCbnz; rw [Cbnz.decode_none_at marker hne]

theorem decodeCbnz_self (i : Cbnz) : decodeCbnz i.encode = some (.cbnz i, 4) := by
  unfold decodeCbnz; rw [Cbnz.decode_encode]

theorem AdrAdrp.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : AdrAdrp, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : AdrAdrp.decode w = none := by
  unfold AdrAdrp.decode
  exact if_neg (encode_ne_of_marker_ne AdrAdrp.encode marker _ w hne)

theorem decodeAdrAdrp_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : AdrAdrp, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeAdrAdrp w = none := by
  unfold decodeAdrAdrp; rw [AdrAdrp.decode_none_at marker hne]

theorem decodeAdrAdrp_self (i : AdrAdrp) : decodeAdrAdrp i.encode = some (.adrAdrp i, 4) := by
  unfold decodeAdrAdrp; rw [AdrAdrp.decode_encode]

theorem LogicalShiftedReg.decode_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : LogicalShiftedReg, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : LogicalShiftedReg.decode w = none := by
  unfold LogicalShiftedReg.decode
  cases LogicalShiftOp.ofCode (w.extractLsb' 29 2) with
  | none => rfl
  | some opc =>
    cases ShiftType.ofCode (w.extractLsb' 22 2) with
    | none => rfl
    | some shift => exact if_neg (encode_ne_of_marker_ne LogicalShiftedReg.encode marker _ w hne)

theorem decodeLogicalShiftedReg_none_at {w : BitVec 32} {pos len : Nat} {tag : BitVec len}
    (marker : ∀ i : LogicalShiftedReg, i.encode.extractLsb' pos len = tag)
    (hne : tag ≠ w.extractLsb' pos len) : decodeLogicalShiftedReg w = none := by
  unfold decodeLogicalShiftedReg; rw [LogicalShiftedReg.decode_none_at marker hne]

theorem decodeLogicalShiftedReg_self (i : LogicalShiftedReg) :
    decodeLogicalShiftedReg i.encode = some (.logicalShiftedReg i, 4) := by
  unfold decodeLogicalShiftedReg; rw [LogicalShiftedReg.decode_encode]

theorem decodeNop_self (i : Nop) : decodeNop i.encode = some (.nop i, 4) := by
  unfold decodeNop; rw [Nop.decode_encode]

theorem MoveWide_decode_none_A {w : BitVec 32} (hne : (0b100101#6 : BitVec 6) ≠ w.extractLsb' 23 6) :
    MoveWide.decode w = none := by
  unfold MoveWide.decode
  cases MoveWideOp.ofCode (w.extractLsb' 29 2) with
  | none => rfl
  | some op => exact if_neg (encode_ne_of_marker_ne MoveWide.encode MoveWide.marker23 _ w hne)

theorem MoveWide_decode_none_B {w : BitVec 32} (hne : (0b10010#5 : BitVec 5) ≠ w.extractLsb' 24 5) :
    MoveWide.decode w = none := by
  unfold MoveWide.decode
  cases MoveWideOp.ofCode (w.extractLsb' 29 2) with
  | none => rfl
  | some op => exact if_neg (encode_ne_of_marker_ne MoveWide.encode MoveWide.marker24 _ w hne)

theorem AddSubImm_decode_none_A {w : BitVec 32} (hne : (0b100010#6 : BitVec 6) ≠ w.extractLsb' 23 6) :
    AddSubImm.decode w = none := by
  unfold AddSubImm.decode
  exact if_neg (encode_ne_of_marker_ne AddSubImm.encode AddSubImm.marker23 _ w hne)

theorem AddSubImm_decode_none_B {w : BitVec 32} (hne : (0b10001#5 : BitVec 5) ≠ w.extractLsb' 24 5) :
    AddSubImm.decode w = none := by
  unfold AddSubImm.decode
  exact if_neg (encode_ne_of_marker_ne AddSubImm.encode AddSubImm.marker24 _ w hne)

theorem LogicalImm_decode_none_A {w : BitVec 32} (hne : (0b100100#6 : BitVec 6) ≠ w.extractLsb' 23 6) :
    LogicalImm.decode w = none := by
  unfold LogicalImm.decode
  cases LogicalOp.ofCode (w.extractLsb' 29 2) with
  | none => rfl
  | some opc => exact if_neg (encode_ne_of_marker_ne LogicalImm.encode LogicalImm.marker23 _ w hne)

theorem LogicalImm_decode_none_B {w : BitVec 32} (hne : (0b10010#5 : BitVec 5) ≠ w.extractLsb' 24 5) :
    LogicalImm.decode w = none := by
  unfold LogicalImm.decode
  cases LogicalOp.ofCode (w.extractLsb' 29 2) with
  | none => rfl
  | some opc => exact if_neg (encode_ne_of_marker_ne LogicalImm.encode LogicalImm.marker24 _ w hne)

theorem LoadStoreUImm_decode_none_A {w : BitVec 32}
    (hne : (0b110010#6 : BitVec 6) ≠ w.extractLsb' 23 6) : LoadStoreUImm.decode w = none := by
  unfold LoadStoreUImm.decode
  cases LsSize.ofCode (w.extractLsb' 30 2) with
  | none => rfl
  | some size =>
    exact if_neg (encode_ne_of_marker_ne LoadStoreUImm.encode LoadStoreUImm.marker23 _ w hne)

theorem LoadStoreUImm_decode_none_B {w : BitVec 32}
    (hne : (0b11001#5 : BitVec 5) ≠ w.extractLsb' 24 5) : LoadStoreUImm.decode w = none := by
  unfold LoadStoreUImm.decode
  cases LsSize.ofCode (w.extractLsb' 30 2) with
  | none => rfl
  | some size =>
    exact if_neg (encode_ne_of_marker_ne LoadStoreUImm.encode LoadStoreUImm.marker24 _ w hne)

theorem AddSubShiftedReg_decode_none_B {w : BitVec 32}
    (hne : (0b01011#5 : BitVec 5) ≠ w.extractLsb' 24 5) : AddSubShiftedReg.decode w = none := by
  unfold AddSubShiftedReg.decode
  cases ShiftType.ofCode (w.extractLsb' 22 2) with
  | none => rfl
  | some shift =>
    exact if_neg (encode_ne_of_marker_ne AddSubShiftedReg.encode AddSubShiftedReg.marker24 _ w hne)

theorem CompareZero_decode_none_B {w : BitVec 32}
    (hne : (0b10100#5 : BitVec 5) ≠ w.extractLsb' 24 5) : CompareZero.decode w = none := by
  unfold CompareZero.decode
  exact if_neg (encode_ne_of_marker_ne CompareZero.encode CompareZero.marker24 _ w hne)

theorem CompareZero_decode_none_C {w : BitVec 32}
    (hne : (0b0110100#7 : BitVec 7) ≠ w.extractLsb' 24 7) : CompareZero.decode w = none := by
  unfold CompareZero.decode
  exact if_neg (encode_ne_of_marker_ne CompareZero.encode CompareZero.marker24_7 _ w hne)

theorem SupervisorCall_decode_none_B {w : BitVec 32}
    (hne : (0b10100#5 : BitVec 5) ≠ w.extractLsb' 24 5) : svcDecode w = none := by
  unfold svcDecode
  exact if_neg (encode_ne_of_marker_ne svcEncode svcMarker24 _ w hne)

theorem SupervisorCall_decode_none_D {w : BitVec 32}
    (hne : (0b11010100000#11 : BitVec 11) ≠ w.extractLsb' 21 11) : svcDecode w = none := by
  unfold svcDecode
  exact if_neg (encode_ne_of_marker_ne svcEncode svcMarker21 _ w hne)

theorem decodeMoveWide_none_A {w : BitVec 32} (hne : (0b100101#6 : BitVec 6) ≠ w.extractLsb' 23 6) :
    decodeMoveWide w = none := by unfold decodeMoveWide; rw [MoveWide_decode_none_A hne]

theorem decodeMoveWide_none_B {w : BitVec 32} (hne : (0b10010#5 : BitVec 5) ≠ w.extractLsb' 24 5) :
    decodeMoveWide w = none := by unfold decodeMoveWide; rw [MoveWide_decode_none_B hne]

theorem decodeAddSubImm_none_A {w : BitVec 32} (hne : (0b100010#6 : BitVec 6) ≠ w.extractLsb' 23 6) :
    decodeAddSubImm w = none := by unfold decodeAddSubImm; rw [AddSubImm_decode_none_A hne]

theorem decodeAddSubImm_none_B {w : BitVec 32} (hne : (0b10001#5 : BitVec 5) ≠ w.extractLsb' 24 5) :
    decodeAddSubImm w = none := by unfold decodeAddSubImm; rw [AddSubImm_decode_none_B hne]

theorem decodeLogicalImm_none_A {w : BitVec 32} (hne : (0b100100#6 : BitVec 6) ≠ w.extractLsb' 23 6) :
    decodeLogicalImm w = none := by unfold decodeLogicalImm; rw [LogicalImm_decode_none_A hne]

theorem decodeLogicalImm_none_B {w : BitVec 32} (hne : (0b10010#5 : BitVec 5) ≠ w.extractLsb' 24 5) :
    decodeLogicalImm w = none := by unfold decodeLogicalImm; rw [LogicalImm_decode_none_B hne]

theorem decodeLoadStoreUImm_none_A {w : BitVec 32}
    (hne : (0b110010#6 : BitVec 6) ≠ w.extractLsb' 23 6) : decodeLoadStoreUImm w = none := by
  unfold decodeLoadStoreUImm; rw [LoadStoreUImm_decode_none_A hne]

theorem decodeLoadStoreUImm_none_B {w : BitVec 32}
    (hne : (0b11001#5 : BitVec 5) ≠ w.extractLsb' 24 5) : decodeLoadStoreUImm w = none := by
  unfold decodeLoadStoreUImm; rw [LoadStoreUImm_decode_none_B hne]

theorem decodeAddSubShiftedReg_none_B {w : BitVec 32}
    (hne : (0b01011#5 : BitVec 5) ≠ w.extractLsb' 24 5) : decodeAddSubShiftedReg w = none := by
  unfold decodeAddSubShiftedReg; rw [AddSubShiftedReg_decode_none_B hne]

theorem decodeCbz_none_C {w : BitVec 32}
    (hne : (0b0110100#7 : BitVec 7) ≠ w.extractLsb' 24 7) : decodeCbz w = none := by
  unfold decodeCbz; rw [CompareZero_decode_none_C hne]

theorem decodeSvc_none_D {w : BitVec 32}
    (hne : (0b11010100000#11 : BitVec 11) ≠ w.extractLsb' 21 11) : decodeSvc w = none := by
  unfold decodeSvc; rw [SupervisorCall_decode_none_D hne]

/-- The `MoveWide`/`AddSubImm`/`LogicalImm`/`LoadStoreUImm` cases above never
need this window, since none of these four families reads bit 23 as an
operand — see each `markerNN` docstring. `AddSubShiftedReg`'s `shift` field
does (its top bit sits at bit 23), which is why its own dispatch below uses
window `(24, 5)` throughout rather than `(23, 6)`. -/
theorem decodeMoveWide_self (i : MoveWide) : decodeMoveWide i.encode = some (.moveWide i, 4) := by
  unfold decodeMoveWide; rw [MoveWide.decode_encode]

theorem decodeAddSubImm_self (i : AddSubImm) :
    decodeAddSubImm i.encode = some (.addSubImm i, 4) := by
  unfold decodeAddSubImm; rw [AddSubImm.decode_encode]

theorem decodeLogicalImm_self (i : LogicalImm) :
    decodeLogicalImm i.encode = some (.logicalImm i, 4) := by
  unfold decodeLogicalImm; rw [LogicalImm.decode_encode]

theorem decodeLoadStoreUImm_self (i : LoadStoreUImm) :
    decodeLoadStoreUImm i.encode = some (.loadStoreUImm i, 4) := by
  unfold decodeLoadStoreUImm; rw [LoadStoreUImm.decode_encode]

theorem decodeAddSubShiftedReg_self (i : AddSubShiftedReg) :
    decodeAddSubShiftedReg i.encode = some (.addSubShiftedReg i, 4) := by
  unfold decodeAddSubShiftedReg; rw [AddSubShiftedReg.decode_encode]

theorem decodeCbz_self (i : CompareZero) : decodeCbz i.encode = some (.cbz i, 4) := by
  unfold decodeCbz; rw [CompareZero.decode_encode]

theorem decodeSvc_self (imm : BitVec 16) :
    decodeSvc (svcEncode imm) = some (.svc imm, 4) := by
  unfold decodeSvc; rw [svcDecode_svcEncode]

theorem decodeHlt_self (i : Hlt) : decodeHlt i.encode = some (.hlt i, 4) := by
  unfold decodeHlt; rw [Hlt.decode_encode]

theorem decode_encode (instr : Instr) :
    ∀ rest, decode (encode instr ++ rest) = some (instr, 4) := by
  intro rest
  unfold encode
  cases instr with
  | moveWide i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes', decodeMoveWide_self]; rfl
  | addSubImm i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_A (by rw [AddSubImm.marker23]; decide)]
    rw [decodeAddSubImm_self]; rfl
  | logicalImm i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_A (by rw [LogicalImm.marker23]; decide)]
    rw [decodeAddSubImm_none_A (by rw [LogicalImm.marker23]; decide)]
    rw [decodeLogicalImm_self]; rfl
  | loadStoreUImm i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_A (by rw [LoadStoreUImm.marker23]; decide)]
    rw [decodeAddSubImm_none_A (by rw [LoadStoreUImm.marker23]; decide)]
    rw [decodeLogicalImm_none_A (by rw [LoadStoreUImm.marker23]; decide)]
    rw [decodeLoadStoreUImm_self]; rfl
  | addSubShiftedReg i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_B (by rw [AddSubShiftedReg.marker24]; decide)]
    rw [decodeAddSubImm_none_B (by rw [AddSubShiftedReg.marker24]; decide)]
    rw [decodeLogicalImm_none_B (by rw [AddSubShiftedReg.marker24]; decide)]
    rw [decodeLoadStoreUImm_none_B (by rw [AddSubShiftedReg.marker24]; decide)]
    rw [decodeAddSubShiftedReg_self]; rfl
  | cbz i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_B (by rw [CompareZero.marker24]; decide)]
    rw [decodeAddSubImm_none_B (by rw [CompareZero.marker24]; decide)]
    rw [decodeLogicalImm_none_B (by rw [CompareZero.marker24]; decide)]
    rw [decodeLoadStoreUImm_none_B (by rw [CompareZero.marker24]; decide)]
    rw [decodeAddSubShiftedReg_none_B (by rw [CompareZero.marker24]; decide)]
    rw [decodeCbz_self]; rfl
  | svc imm =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_B (by rw [svcMarker24]; decide)]
    rw [decodeAddSubImm_none_B (by rw [svcMarker24]; decide)]
    rw [decodeLogicalImm_none_B (by rw [svcMarker24]; decide)]
    rw [decodeLoadStoreUImm_none_B (by rw [svcMarker24]; decide)]
    rw [decodeAddSubShiftedReg_none_B (by rw [svcMarker24]; decide)]
    rw [decodeCbz_none_C (by rw [svcMarker24_7]; decide)]
    rw [decodeSvc_self]; rfl
  | hlt i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_B (by rw [Hlt.marker24]; decide)]
    rw [decodeAddSubImm_none_B (by rw [Hlt.marker24]; decide)]
    rw [decodeLogicalImm_none_B (by rw [Hlt.marker24]; decide)]
    rw [decodeLoadStoreUImm_none_B (by rw [Hlt.marker24]; decide)]
    rw [decodeAddSubShiftedReg_none_B (by rw [Hlt.marker24]; decide)]
    rw [decodeCbz_none_C (by rw [Hlt.marker24_7]; decide)]
    rw [decodeSvc_none_D (by rw [Hlt.marker21]; decide)]
    rw [decodeHlt_self]; rfl
  | branchImm i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_at MoveWide.marker26_3 (by rw [BranchImm.marker26_3]; decide)]
    rw [decodeAddSubImm_none_at AddSubImm.marker26_3 (by rw [BranchImm.marker26_3]; decide)]
    rw [decodeLogicalImm_none_at LogicalImm.marker26_3 (by rw [BranchImm.marker26_3]; decide)]
    rw [decodeLoadStoreUImm_none_at LoadStoreUImm.marker26_3 (by rw [BranchImm.marker26_3]; decide)]
    rw [decodeAddSubShiftedReg_none_at AddSubShiftedReg.marker26_3
      (by rw [BranchImm.marker26_3]; decide)]
    rw [decodeCbz_none_at CompareZero.marker26_5 (by rw [BranchImm.marker26_5]; decide)]
    rw [decodeSvc_none_at svcMarker26_5 (by rw [BranchImm.marker26_5]; decide)]
    rw [decodeHlt_none_at Hlt.marker26_5 (by rw [BranchImm.marker26_5]; decide)]
    rw [decodeBranchImm_self]; rfl
  | branchReg i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_at MoveWide.marker25_4 (by rw [BranchReg.marker25_4]; decide)]
    rw [decodeAddSubImm_none_at AddSubImm.marker25_4 (by rw [BranchReg.marker25_4]; decide)]
    rw [decodeLogicalImm_none_at LogicalImm.marker16_5 (by rw [BranchReg.marker16_5]; decide)]
    rw [decodeLoadStoreUImm_none_at LoadStoreUImm.marker25_5 (by rw [BranchReg.marker25_5]; decide)]
    rw [decodeAddSubShiftedReg_none_at AddSubShiftedReg.marker25_4
      (by rw [BranchReg.marker25_4]; decide)]
    rw [decodeCbz_none_at CompareZero.marker25_6 (by rw [BranchReg.marker25_6]; decide)]
    rw [decodeSvc_none_at svcMarker25_7 (by rw [BranchReg.marker25_7]; decide)]
    rw [decodeHlt_none_at Hlt.marker25_7 (by rw [BranchReg.marker25_7]; decide)]
    rw [decodeBranchImm_none_at BranchImm.marker26_5 (by rw [BranchReg.marker26_5]; decide)]
    rw [decodeBranchReg_self]; rfl
  | condBranch i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_at MoveWide.marker24 (by rw [CondBranch.marker24_5]; decide)]
    rw [decodeAddSubImm_none_at AddSubImm.marker24 (by rw [CondBranch.marker24_5]; decide)]
    rw [decodeLogicalImm_none_at LogicalImm.marker24 (by rw [CondBranch.marker24_5]; decide)]
    rw [decodeLoadStoreUImm_none_at LoadStoreUImm.marker24 (by rw [CondBranch.marker24_5]; decide)]
    rw [decodeAddSubShiftedReg_none_at AddSubShiftedReg.marker24
      (by rw [CondBranch.marker24_5]; decide)]
    rw [decodeCbz_none_at CompareZero.marker24_7 (by rw [CondBranch.marker24_7]; decide)]
    rw [decodeSvc_none_at svcMarker24_8 (by rw [CondBranch.marker24_8]; decide)]
    rw [decodeHlt_none_at Hlt.marker24_8 (by rw [CondBranch.marker24_8]; decide)]
    rw [decodeBranchImm_none_at BranchImm.marker26_5 (by rw [CondBranch.marker26_5]; decide)]
    rw [decodeBranchReg_none_at BranchReg.marker25_7 (by rw [CondBranch.marker25_7]; decide)]
    rw [decodeCondBranch_self]; rfl
  | cbnz i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_at MoveWide.marker24 (by rw [Cbnz.marker24_5]; decide)]
    rw [decodeAddSubImm_none_at AddSubImm.marker24 (by rw [Cbnz.marker24_5]; decide)]
    rw [decodeLogicalImm_none_at LogicalImm.marker24 (by rw [Cbnz.marker24_5]; decide)]
    rw [decodeLoadStoreUImm_none_at LoadStoreUImm.marker24 (by rw [Cbnz.marker24_5]; decide)]
    rw [decodeAddSubShiftedReg_none_at AddSubShiftedReg.marker24 (by rw [Cbnz.marker24_5]; decide)]
    rw [decodeCbz_none_at CompareZero.marker24 (by rw [Cbnz.marker24_5]; decide)]
    rw [decodeSvc_none_at svcMarker24 (by rw [Cbnz.marker24_5]; decide)]
    rw [decodeHlt_none_at Hlt.marker24 (by rw [Cbnz.marker24_5]; decide)]
    rw [decodeBranchImm_none_at BranchImm.marker26_5 (by rw [Cbnz.marker26_5]; decide)]
    rw [decodeBranchReg_none_at BranchReg.marker25_6 (by rw [Cbnz.marker25_6]; decide)]
    rw [decodeCondBranch_none_at CondBranch.marker24_5 (by rw [Cbnz.marker24_5]; decide)]
    rw [decodeCbnz_self]; rfl
  | adrAdrp i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_at MoveWide.marker24 (by rw [AdrAdrp.marker24_5]; decide)]
    rw [decodeAddSubImm_none_at AddSubImm.marker24 (by rw [AdrAdrp.marker24_5]; decide)]
    rw [decodeLogicalImm_none_at LogicalImm.marker24 (by rw [AdrAdrp.marker24_5]; decide)]
    rw [decodeLoadStoreUImm_none_at LoadStoreUImm.marker24 (by rw [AdrAdrp.marker24_5]; decide)]
    rw [decodeAddSubShiftedReg_none_at AddSubShiftedReg.marker24
      (by rw [AdrAdrp.marker24_5]; decide)]
    rw [decodeCbz_none_at CompareZero.marker24 (by rw [AdrAdrp.marker24_5]; decide)]
    rw [decodeSvc_none_at svcMarker24 (by rw [AdrAdrp.marker24_5]; decide)]
    rw [decodeHlt_none_at Hlt.marker24 (by rw [AdrAdrp.marker24_5]; decide)]
    rw [decodeBranchImm_none_at BranchImm.marker26_3 (by rw [AdrAdrp.marker26_3]; decide)]
    rw [decodeBranchReg_none_at BranchReg.marker25_4 (by rw [AdrAdrp.marker25_4]; decide)]
    rw [decodeCondBranch_none_at CondBranch.marker24_5 (by rw [AdrAdrp.marker24_5]; decide)]
    rw [decodeCbnz_none_at Cbnz.marker24_5 (by rw [AdrAdrp.marker24_5]; decide)]
    rw [decodeAdrAdrp_self]; rfl
  | logicalShiftedReg i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_at MoveWide.marker24 (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeAddSubImm_none_at AddSubImm.marker24 (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeLogicalImm_none_at LogicalImm.marker24 (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeLoadStoreUImm_none_at LoadStoreUImm.marker24
      (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeAddSubShiftedReg_none_at AddSubShiftedReg.marker24
      (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeCbz_none_at CompareZero.marker24 (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeSvc_none_at svcMarker24 (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeHlt_none_at Hlt.marker24 (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeBranchImm_none_at BranchImm.marker26_3 (by rw [LogicalShiftedReg.marker26_3]; decide)]
    rw [decodeBranchReg_none_at BranchReg.marker25_4 (by rw [LogicalShiftedReg.marker25_4]; decide)]
    rw [decodeCondBranch_none_at CondBranch.marker24_5 (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeCbnz_none_at Cbnz.marker24_5 (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeAdrAdrp_none_at AdrAdrp.marker24_5 (by rw [LogicalShiftedReg.marker24_5]; decide)]
    rw [decodeLogicalShiftedReg_self]; rfl
  | nop i =>
    simp only [Instr.toWord, decode, wordToBytes, List.cons_append, List.nil_append]
    rw [bytesToWord_wordToBytes']
    rw [decodeMoveWide_none_at MoveWide.marker24 (by rw [Nop.marker24_5]; decide)]
    rw [decodeAddSubImm_none_at AddSubImm.marker24 (by rw [Nop.marker24_5]; decide)]
    rw [decodeLogicalImm_none_at LogicalImm.marker24 (by rw [Nop.marker24_5]; decide)]
    rw [decodeLoadStoreUImm_none_at LoadStoreUImm.marker24 (by rw [Nop.marker24_5]; decide)]
    rw [decodeAddSubShiftedReg_none_at AddSubShiftedReg.marker24 (by rw [Nop.marker24_5]; decide)]
    rw [decodeCbz_none_at CompareZero.marker24 (by rw [Nop.marker24_5]; decide)]
    rw [decodeSvc_none_at svcMarker24 (by rw [Nop.marker24_5]; decide)]
    rw [decodeHlt_none_at Hlt.marker24 (by rw [Nop.marker24_5]; decide)]
    rw [decodeBranchImm_none_at BranchImm.marker26_5 (by rw [Nop.marker26_5]; decide)]
    rw [decodeBranchReg_none_at BranchReg.marker10_11 (by rw [Nop.marker10_11]; decide)]
    rw [decodeCondBranch_none_at CondBranch.marker24_5 (by rw [Nop.marker24_5]; decide)]
    rw [decodeCbnz_none_at Cbnz.marker24_7 (by rw [Nop.marker24_7]; decide)]
    rw [decodeAdrAdrp_none_at AdrAdrp.marker24_5 (by rw [Nop.marker24_5]; decide)]
    rw [decodeLogicalShiftedReg_none_at LogicalShiftedReg.marker24_5 (by rw [Nop.marker24_5]; decide)]
    rw [decodeNop_self]; rfl

end Grass.ISA.AArch64.Target
