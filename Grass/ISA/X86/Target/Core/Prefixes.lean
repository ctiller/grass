import Grass.ISA.X86.Target.Core.Operands
import Grass.ISA.X86.Bytes

/-!
# Canonical Prefix, ModR/M, SIB/VSIB, Displacement, and Immediate Codecs

Provides structured byte-level representations, encoders, decoders, and formal
round-trip proofs (`decode_encode` and `encode_pos`) for:
- Legacy Prefixes (Groups 1–4: `LOCK`/`REPNE`/`REP`, segment overrides, `66`, `67`)
- REX prefix (`0x40`–`0x4F`) with high-byte register disambiguation (`AH`..`BH` vs `SPL`..`DIL`)
- 2-byte VEX (`C5`), 3-byte VEX (`C4`), 4-byte EVEX (`62`), and AMD XOP (`8F` with `m-mmmm >= 8`
  formally disambiguated from `POP r/m64` (`8F /0`))
- ModR/M, SIB, VSIB (vector SIB addressing), Displacements, and Immediates/`is4`
- $O(1)$ Prefix Header Classifier (`classifyPrefixHeader`) and formal disjointness theorems.
-/

namespace Grass.ISA.X86.Target.Core

export Grass.ISA.X86 (Rex ModRm Sib Displacement Immediate)

/-! ## Legacy Prefixes (Groups 1–4) -/

/-- Group 1 prefixes: `LOCK` (`0xF0`), `REPNE`/`REPNZ` (`0xF2`), `REP`/`REPE`/`REPZ` (`0xF3`). -/
inductive LegacyGroup1 where
  | lock
  | repne
  | rep
deriving DecidableEq, Repr, Inhabited

namespace LegacyGroup1

def toByte : LegacyGroup1 → UInt8
  | .lock => 0xF0
  | .repne => 0xF2
  | .rep => 0xF3

def ofByte? (b : UInt8) : Option LegacyGroup1 :=
  if b == 0xF0 then some .lock
  else if b == 0xF2 then some .repne
  else if b == 0xF3 then some .rep
  else none

@[simp] theorem ofByte?_toByte (g : LegacyGroup1) : ofByte? g.toByte = some g := by
  cases g <;> decide

end LegacyGroup1

/-- Group 2 segment override prefixes (`CS`, `SS`, `DS`, `ES`, `FS`, `GS`). -/
inductive LegacyGroup2 where
  | cs | ss | ds | es | fs | gs
deriving DecidableEq, Repr, Inhabited

namespace LegacyGroup2

def toByte : LegacyGroup2 → UInt8
  | .cs => 0x2E
  | .ss => 0x36
  | .ds => 0x3E
  | .es => 0x26
  | .fs => 0x64
  | .gs => 0x65

def ofByte? (b : UInt8) : Option LegacyGroup2 :=
  if b == 0x2E then some .cs
  else if b == 0x36 then some .ss
  else if b == 0x3E then some .ds
  else if b == 0x26 then some .es
  else if b == 0x64 then some .fs
  else if b == 0x65 then some .gs
  else none

@[simp] theorem ofByte?_toByte (g : LegacyGroup2) : ofByte? g.toByte = some g := by
  cases g <;> decide

end LegacyGroup2

/-- Whether a byte is a legacy prefix byte (Groups 1–4). -/
def isLegacyPrefixByte (b : UInt8) : Bool :=
  b == 0xF0 || b == 0xF2 || b == 0xF3 ||
  b == 0x2E || b == 0x36 || b == 0x3E || b == 0x26 || b == 0x64 || b == 0x65 ||
  b == 0x66 || b == 0x67

/-- Canonical Legacy Prefixes bundle emitted in deterministic Group 1 → 2 → 3 → 4 order. -/
structure LegacyPrefixes where
  group1 : Option LegacyGroup1 := none
  group2 : Option LegacyGroup2 := none
  opSizeOverride : Bool := false
  addrSizeOverride : Bool := false
deriving DecidableEq, Repr, Inhabited

namespace LegacyPrefixes

def encodeGroup1 : Option LegacyGroup1 → List UInt8
  | some g => [g.toByte]
  | none => []

def encodeGroup2 : Option LegacyGroup2 → List UInt8
  | some g => [g.toByte]
  | none => []

def encodeGroup3 (b : Bool) : List UInt8 := if b then [0x66] else []
def encodeGroup4 (b : Bool) : List UInt8 := if b then [0x67] else []

/-- Canonical byte encoder for legacy prefixes (Group 1 → Group 2 → `0x66` → `0x67`). -/
def encode (p : LegacyPrefixes) : List UInt8 :=
  encodeGroup1 p.group1 ++ encodeGroup2 p.group2 ++
  encodeGroup3 p.opSizeOverride ++ encodeGroup4 p.addrSizeOverride

def decodeGroup1 : List UInt8 → Option LegacyGroup1 × List UInt8
  | b :: rest =>
      match LegacyGroup1.ofByte? b with
      | some g => (some g, rest)
      | none => (none, b :: rest)
  | [] => (none, [])

def decodeGroup2 : List UInt8 → Option LegacyGroup2 × List UInt8
  | b :: rest =>
      match LegacyGroup2.ofByte? b with
      | some g => (some g, rest)
      | none => (none, b :: rest)
  | [] => (none, [])

def decodeGroup3 : List UInt8 → Bool × List UInt8
  | b :: rest => if b == 0x66 then (true, rest) else (false, b :: rest)
  | [] => (false, [])

def decodeGroup4 : List UInt8 → Bool × List UInt8
  | b :: rest => if b == 0x67 then (true, rest) else (false, b :: rest)
  | [] => (false, [])

/-- Consume optional legacy prefixes in canonical Group 1 → 2 → 3 → 4 order. -/
def decode (bs : List UInt8) : LegacyPrefixes × List UInt8 :=
  let (g1, bs1) := decodeGroup1 bs
  let (g2, bs2) := decodeGroup2 bs1
  let (opSz, bs3) := decodeGroup3 bs2
  let (addrSz, bs4) := decodeGroup4 bs3
  (⟨g1, g2, opSz, addrSz⟩, bs4)

private theorem not_g1 (b : UInt8) (hb : isLegacyPrefixByte b = false) :
    LegacyGroup1.ofByte? b = none := by
  unfold isLegacyPrefixByte at hb
  unfold LegacyGroup1.ofByte?
  simp only [Bool.or_eq_false_iff] at hb
  rcases hb with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  simp [h1, h2, h3]

private theorem not_g2 (b : UInt8) (hb : isLegacyPrefixByte b = false) :
    LegacyGroup2.ofByte? b = none := by
  unfold isLegacyPrefixByte at hb
  unfold LegacyGroup2.ofByte?
  simp only [Bool.or_eq_false_iff] at hb
  rcases hb with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, _⟩, _⟩
  simp [h1, h2, h3, h4, h5, h6]

private theorem not_g3 (b : UInt8) (hb : isLegacyPrefixByte b = false) :
    (b == 0x66) = false := by
  unfold isLegacyPrefixByte at hb
  simp only [Bool.or_eq_false_iff] at hb
  exact hb.1.2

private theorem not_g4 (b : UInt8) (hb : isLegacyPrefixByte b = false) :
    (b == 0x67) = false := by
  unfold isLegacyPrefixByte at hb
  simp only [Bool.or_eq_false_iff] at hb
  exact hb.2

@[simp] private theorem g2_not_g1 (g : LegacyGroup2) : LegacyGroup1.ofByte? g.toByte = none := by
  cases g <;> decide

@[simp] private theorem g3_not_g1 : LegacyGroup1.ofByte? 0x66 = none := by decide
@[simp] private theorem g4_not_g1 : LegacyGroup1.ofByte? 0x67 = none := by decide

@[simp] private theorem g3_not_g2 : LegacyGroup2.ofByte? 0x66 = none := by decide
@[simp] private theorem g4_not_g2 : LegacyGroup2.ofByte? 0x67 = none := by decide

@[simp] private theorem g4_not_g3 : ((0x67 : UInt8) == 0x66) = false := by decide

set_option linter.unusedSimpArgs false in
/-- Formal round-trip theorem for canonical legacy prefixes when followed by a non-legacy-prefix byte. -/
theorem decode_encode (p : LegacyPrefixes) {b : UInt8} (hb : isLegacyPrefixByte b = false)
    (rest : List UInt8) :
    decode (encode p ++ b :: rest) = (p, b :: rest) := by
  cases p with
  | mk g1 g2 opSz addrSz =>
      have h1 := not_g1 b hb
      have h2 := not_g2 b hb
      have h3 := not_g3 b hb
      have h4 := not_g4 b hb
      cases g1 <;> cases g2 <;> cases opSz <;> cases addrSz <;>
        simp [encode, decode, encodeGroup1, encodeGroup2, encodeGroup3, encodeGroup4,
          decodeGroup1, decodeGroup2, decodeGroup3, decodeGroup4, h1, h2, h3, h4]

end LegacyPrefixes

/-! ## REX Prefix (`0x40`–`0x4F`) & High-Byte Register Disambiguation (`AH`..`BH` vs `SPL`..`DIL`) -/

/-- Reconstruct a `Gpr` from its REX extension bit and 3-bit register field. -/
def Gpr.ofSplit (ext : Bool) (low : BitVec 3) : Gpr :=
  Gpr.ofIndex ⟨(if ext then 8 else 0) + low.toNat, by revert ext low; decide⟩

@[simp] theorem Gpr.ofSplit_split (r : Gpr) : Gpr.ofSplit r.isExtended r.encodingBits = r := by
  cases r <;> decide

/-- Disambiguate an 8-bit register field (`ByteReg`) given whether a REX prefix is present (`hasRex`),
the REX extension bit (`ext`), and the 3-bit ModR/M/opcode register field (`bits`). -/
def disambiguateByteReg (hasRex : Bool) (ext : Bool) (bits : BitVec 3) : ByteReg :=
  if hasRex then
    .low (Gpr.ofSplit ext bits)
  else
    if bits.toNat < 4 then
      .low (Gpr.ofIndex ⟨bits.toNat, by revert bits; decide⟩)
    else
      .high (Gpr.ofIndex ⟨bits.toNat - 4, by revert bits; decide⟩)

/-- Encode a `ByteReg` into `(extBit, low3Bits)`. -/
def encodeByteRegField : ByteReg → Bool × BitVec 3
  | .low r => (r.isExtended, r.encodingBits)
  | .high r => (false, BitVec.ofNat 3 (r.index.val + 4))

/-- Round-trip theorem: every encodable `ByteReg` under `hasRex` is recovered uniquely by `disambiguateByteReg`. -/
theorem disambiguateByteReg_encodeByteRegField (b : ByteReg) (hasRex : Bool)
    (h : b.Encodable hasRex) :
    let (ext, bits) := encodeByteRegField b
    disambiguateByteReg hasRex ext bits = b := by
  revert h
  cases b with
  | low r => cases r <;> cases hasRex <;> decide
  | high r => cases r <;> cases hasRex <;> decide

/-! ## 2-Byte VEX Prefix (`C5`) -/

/-- 2-byte VEX prefix (`0xC5`, byte 1: `~R | ~vvvv | L | pp`). -/
structure Vex2 where
  r : Bool
  vvvv : BitVec 4
  l : Bool
  pp : BitVec 2
deriving DecidableEq, Repr, Inhabited

namespace Vex2

/-- Pack byte 1 of a 2-byte VEX prefix: `~R` (bit 7), `~vvvv` (bits 6:3), `L` (bit 2), `pp` (bits 1:0). -/
def toByte1 (v : Vex2) : UInt8 :=
  let rBit : BitVec 1 := BitVec.ofBool (!v.r)
  let vvvvInv : BitVec 4 := ~~~v.vvvv
  let lBit : BitVec 1 := BitVec.ofBool v.l
  UInt8.ofBitVec (rBit ++ vvvvInv ++ lBit ++ v.pp)

/-- Unpack byte 1 of a 2-byte VEX prefix. -/
def ofByte1 (b : UInt8) : Vex2 :=
  let bv := b.toBitVec
  let rBit := BitVec.extractLsb' 7 1 bv
  let vvvvInv := BitVec.extractLsb' 3 4 bv
  let lBit := BitVec.extractLsb' 2 1 bv
  let ppBits := BitVec.extractLsb' 0 2 bv
  { r := !(rBit == 1)
    vvvv := ~~~vvvvInv
    l := lBit == 1
    pp := ppBits }

@[simp] theorem ofByte1_toByte1 (v : Vex2) : ofByte1 (toByte1 v) = v := by
  cases v with
  | mk r vvvv l pp => revert r vvvv l pp; decide

/-- Encode a 2-byte VEX prefix to 2 bytes (`0xC5 :: toByte1 v`). -/
def encode (v : Vex2) : List UInt8 := [0xC5, toByte1 v]

/-- Decode a 2-byte VEX prefix from the head of a byte stream. -/
def decode : List UInt8 → Option (Vex2 × List UInt8)
  | 0xC5 :: b1 :: rest => some (ofByte1 b1, rest)
  | _ => none

/-- Formal round-trip theorem for 2-byte VEX prefixes (`C5`). -/
@[simp] theorem decode_encode (v : Vex2) (rest : List UInt8) :
    decode (encode v ++ rest) = some (v, rest) := by
  simp [encode, decode, ofByte1_toByte1]

/-- Encoded length of a 2-byte VEX prefix is strictly positive ($2 > 0$). -/
theorem encode_pos (v : Vex2) : 0 < (encode v).length := by simp [encode]

end Vex2

/-! ## 3-Byte VEX Prefix (`C4`) -/

/-- Pack byte 1 of a 3-byte VEX / XOP prefix: `~R | ~X | ~B | m-mmmm`. -/
def packVexByte1 (r x b : Bool) (mmmmm : BitVec 5) : UInt8 :=
  UInt8.ofBitVec (BitVec.ofBool (!r) ++ BitVec.ofBool (!x) ++ BitVec.ofBool (!b) ++ mmmmm)

/-- Unpack byte 1 of a 3-byte VEX / XOP prefix. -/
def unpackVexByte1 (b1 : UInt8) : Bool × Bool × Bool × BitVec 5 :=
  let bv1 := b1.toBitVec
  (!(BitVec.extractLsb' 7 1 bv1 == 1),
   !(BitVec.extractLsb' 6 1 bv1 == 1),
   !(BitVec.extractLsb' 5 1 bv1 == 1),
   BitVec.extractLsb' 0 5 bv1)

@[simp] theorem unpackVexByte1_packVexByte1 (r x b : Bool) (mmmmm : BitVec 5) :
    unpackVexByte1 (packVexByte1 r x b mmmmm) = (r, x, b, mmmmm) := by
  revert r x b mmmmm; decide

/-- Pack byte 2 of a 3-byte VEX / XOP prefix: `W | ~vvvv | L | pp`. -/
def packVexByte2 (w : Bool) (vvvv : BitVec 4) (l : Bool) (pp : BitVec 2) : UInt8 :=
  UInt8.ofBitVec (BitVec.ofBool w ++ ~~~vvvv ++ BitVec.ofBool l ++ pp)

/-- Unpack byte 2 of a 3-byte VEX / XOP prefix. -/
def unpackVexByte2 (b2 : UInt8) : Bool × BitVec 4 × Bool × BitVec 2 :=
  let bv2 := b2.toBitVec
  (BitVec.extractLsb' 7 1 bv2 == 1,
   ~~~(BitVec.extractLsb' 3 4 bv2),
   BitVec.extractLsb' 2 1 bv2 == 1,
   BitVec.extractLsb' 0 2 bv2)

@[simp] theorem unpackVexByte2_packVexByte2 (w : Bool) (vvvv : BitVec 4) (l : Bool) (pp : BitVec 2) :
    unpackVexByte2 (packVexByte2 w vvvv l pp) = (w, vvvv, l, pp) := by
  revert w vvvv l pp; decide

/-- 3-byte VEX prefix (`0xC4`, byte 1: `~R | ~X | ~B | m-mmmm`, byte 2: `W | ~vvvv | L | pp`). -/
structure Vex3 where
  r : Bool
  x : Bool
  b : Bool
  mmmmm : BitVec 5
  w : Bool
  vvvv : BitVec 4
  l : Bool
  pp : BitVec 2
deriving DecidableEq, Repr, Inhabited

namespace Vex3

def toByte1 (v : Vex3) : UInt8 := packVexByte1 v.r v.x v.b v.mmmmm
def toByte2 (v : Vex3) : UInt8 := packVexByte2 v.w v.vvvv v.l v.pp

def ofBytes (b1 b2 : UInt8) : Vex3 :=
  let (r, x, b, mmmmm) := unpackVexByte1 b1
  let (w, vvvv, l, pp) := unpackVexByte2 b2
  { r, x, b, mmmmm, w, vvvv, l, pp }

@[simp] theorem ofBytes_toBytes (v : Vex3) : ofBytes (toByte1 v) (toByte2 v) = v := by
  cases v
  simp [ofBytes, toByte1, toByte2]

/-- Encode a 3-byte VEX prefix to 3 bytes (`0xC4 :: toByte1 v :: toByte2 v`). -/
def encode (v : Vex3) : List UInt8 := [0xC4, toByte1 v, toByte2 v]

/-- Decode a 3-byte VEX prefix from the head of a byte stream. -/
def decode : List UInt8 → Option (Vex3 × List UInt8)
  | 0xC4 :: b1 :: b2 :: rest => some (ofBytes b1 b2, rest)
  | _ => none

/-- Formal round-trip theorem for 3-byte VEX prefixes (`C4`). -/
@[simp] theorem decode_encode (v : Vex3) (rest : List UInt8) :
    decode (encode v ++ rest) = some (v, rest) := by
  simp [encode, decode, ofBytes_toBytes]

/-- Encoded length of a 3-byte VEX prefix is strictly positive ($3 > 0$). -/
theorem encode_pos (v : Vex3) : 0 < (encode v).length := by simp [encode]

end Vex3

/-! ## 4-Byte EVEX Prefix (`62`) -/

/-- Pack EVEX `P0`: `~R | ~X | ~B | ~R' | 00 | mm`. -/
def packEvexP0 (r x b rPrime : Bool) (mm : BitVec 2) : UInt8 :=
  UInt8.ofBitVec (BitVec.ofBool (!r) ++ BitVec.ofBool (!x) ++ BitVec.ofBool (!b) ++
    BitVec.ofBool (!rPrime) ++ (0 : BitVec 2) ++ mm)

/-- Unpack EVEX `P0` if bits 3:2 are `00`. -/
def unpackEvexP0? (p0 : UInt8) : Option (Bool × Bool × Bool × Bool × BitVec 2) :=
  let bv0 := p0.toBitVec
  if BitVec.extractLsb' 2 2 bv0 == 0 then
    some (!(BitVec.extractLsb' 7 1 bv0 == 1),
          !(BitVec.extractLsb' 6 1 bv0 == 1),
          !(BitVec.extractLsb' 5 1 bv0 == 1),
          !(BitVec.extractLsb' 4 1 bv0 == 1),
          BitVec.extractLsb' 0 2 bv0)
  else none

@[simp] theorem unpackEvexP0?_packEvexP0 (r x b rPrime : Bool) (mm : BitVec 2) :
    unpackEvexP0? (packEvexP0 r x b rPrime mm) = some (r, x, b, rPrime, mm) := by
  revert r x b rPrime mm; decide

/-- Pack EVEX `P1`: `W | ~vvvv | 1 | pp`. -/
def packEvexP1 (w : Bool) (vvvv : BitVec 4) (pp : BitVec 2) : UInt8 :=
  UInt8.ofBitVec (BitVec.ofBool w ++ ~~~vvvv ++ (1 : BitVec 1) ++ pp)

/-- Unpack EVEX `P1` if bit 2 is `1`. -/
def unpackEvexP1? (p1 : UInt8) : Option (Bool × BitVec 4 × BitVec 2) :=
  let bv1 := p1.toBitVec
  if BitVec.extractLsb' 2 1 bv1 == 1 then
    some (BitVec.extractLsb' 7 1 bv1 == 1,
          ~~~(BitVec.extractLsb' 3 4 bv1),
          BitVec.extractLsb' 0 2 bv1)
  else none

@[simp] theorem unpackEvexP1?_packEvexP1 (w : Bool) (vvvv : BitVec 4) (pp : BitVec 2) :
    unpackEvexP1? (packEvexP1 w vvvv pp) = some (w, vvvv, pp) := by
  revert w vvvv pp; decide

/-- Pack EVEX `P2`: `z | L'L | b | ~V' | aaa`. -/
def packEvexP2 (z : Bool) (ll : BitVec 2) (bFlag vPrime : Bool) (aaa : BitVec 3) : UInt8 :=
  UInt8.ofBitVec (BitVec.ofBool z ++ ll ++ BitVec.ofBool bFlag ++ BitVec.ofBool (!vPrime) ++ aaa)

/-- Unpack EVEX `P2`. -/
def unpackEvexP2 (p2 : UInt8) : Bool × BitVec 2 × Bool × Bool × BitVec 3 :=
  let bv2 := p2.toBitVec
  (BitVec.extractLsb' 7 1 bv2 == 1,
   BitVec.extractLsb' 5 2 bv2,
   BitVec.extractLsb' 4 1 bv2 == 1,
   !(BitVec.extractLsb' 3 1 bv2 == 1),
   BitVec.extractLsb' 0 3 bv2)

@[simp] theorem unpackEvexP2_packEvexP2 (z : Bool) (ll : BitVec 2) (bFlag vPrime : Bool) (aaa : BitVec 3) :
    unpackEvexP2 (packEvexP2 z ll bFlag vPrime aaa) = (z, ll, bFlag, vPrime, aaa) := by
  revert z ll bFlag vPrime aaa; decide

/-- 4-byte EVEX prefix (`0x62`, `P0`, `P1`, `P2`). -/
structure Evex where
  r : Bool
  x : Bool
  b : Bool
  rPrime : Bool
  mm : BitVec 2
  w : Bool
  vvvv : BitVec 4
  pp : BitVec 2
  z : Bool
  ll : BitVec 2
  bFlag : Bool
  vPrime : Bool
  aaa : BitVec 3
deriving DecidableEq, Repr, Inhabited

namespace Evex

def toP0 (e : Evex) : UInt8 := packEvexP0 e.r e.x e.b e.rPrime e.mm
def toP1 (e : Evex) : UInt8 := packEvexP1 e.w e.vvvv e.pp
def toP2 (e : Evex) : UInt8 := packEvexP2 e.z e.ll e.bFlag e.vPrime e.aaa

def ofBytes? (p0 p1 p2 : UInt8) : Option Evex :=
  match unpackEvexP0? p0, unpackEvexP1? p1 with
  | some (r, x, b, rPrime, mm), some (w, vvvv, pp) =>
      let (z, ll, bFlag, vPrime, aaa) := unpackEvexP2 p2
      some { r, x, b, rPrime, mm, w, vvvv, pp, z, ll, bFlag, vPrime, aaa }
  | _, _ => none

@[simp] theorem ofBytes?_toBytes (e : Evex) :
    ofBytes? (toP0 e) (toP1 e) (toP2 e) = some e := by
  cases e
  simp [ofBytes?, toP0, toP1, toP2]

/-- Encode a 4-byte EVEX prefix to 4 bytes (`0x62 :: toP0 e :: toP1 e :: toP2 e`). -/
def encode (e : Evex) : List UInt8 := [0x62, toP0 e, toP1 e, toP2 e]

/-- Decode a 4-byte EVEX prefix from the head of a byte stream. -/
def decode : List UInt8 → Option (Evex × List UInt8)
  | 0x62 :: p0 :: p1 :: p2 :: rest =>
      match ofBytes? p0 p1 p2 with
      | some e => some (e, rest)
      | none => none
  | _ => none

/-- Formal round-trip theorem for 4-byte EVEX prefixes (`62`). -/
@[simp] theorem decode_encode (e : Evex) (rest : List UInt8) :
    decode (encode e ++ rest) = some (e, rest) := by
  simp [encode, decode, ofBytes?_toBytes]

/-- Encoded length of a 4-byte EVEX prefix is strictly positive ($4 > 0$). -/
theorem encode_pos (e : Evex) : 0 < (encode e).length := by simp [encode]

end Evex

/-! ## 3-Byte AMD XOP Prefix (`8F` with `m-mmmm >= 8`, disambiguated from `POP r/m64`) -/

/-- AMD XOP opcode map selector (`m-mmmm >= 8`: map 8, map 9, map 10). -/
inductive XopMap where
  | m8
  | m9
  | m10
deriving DecidableEq, Repr, Inhabited

namespace XopMap

def toBits : XopMap → BitVec 5
  | .m8 => 8
  | .m9 => 9
  | .m10 => 10

def ofBits? (b : BitVec 5) : Option XopMap :=
  if b == 8 then some .m8
  else if b == 9 then some .m9
  else if b == 10 then some .m10
  else none

@[simp] theorem ofBits?_toBits (m : XopMap) : ofBits? m.toBits = some m := by
  cases m <;> decide

theorem toBits_ge_8 (m : XopMap) : 8 ≤ m.toBits.toNat := by
  cases m <;> decide

end XopMap

/-- 3-byte AMD XOP prefix (`0x8F`, byte 1: `~R | ~X | ~B | m-mmmm` with `map ∈ {8,9,10}`,
byte 2: `W | ~vvvv | L | pp`).
Disambiguated from `POP r/m64` (`8F /0`), whose ModR/M byte has `reg = 0` (bits 5:3 = `000`),
which means bits 4:0 are always `< 8`. -/
structure Xop where
  r : Bool
  x : Bool
  b : Bool
  map : XopMap
  w : Bool
  vvvv : BitVec 4
  l : Bool
  pp : BitVec 2
deriving DecidableEq, Repr, Inhabited

namespace Xop

def toByte1 (x : Xop) : UInt8 := packVexByte1 x.r x.x x.b x.map.toBits
def toByte2 (x : Xop) : UInt8 := packVexByte2 x.w x.vvvv x.l x.pp

def ofBytes? (b1 b2 : UInt8) : Option Xop :=
  let u1 := unpackVexByte1 b1
  let u2 := unpackVexByte2 b2
  match XopMap.ofBits? u1.2.2.2 with
  | some map =>
      some { r := u1.1, x := u1.2.1, b := u1.2.2.1, map := map,
             w := u2.1, vvvv := u2.2.1, l := u2.2.2.1, pp := u2.2.2.2 }
  | none => none

@[simp] theorem ofBytes?_toBytes (x : Xop) : ofBytes? (toByte1 x) (toByte2 x) = some x := by
  cases x
  simp [ofBytes?, toByte1, toByte2]

/-- Encode a 3-byte XOP prefix to 3 bytes (`0x8F :: toByte1 x :: toByte2 x`). -/
def encode (x : Xop) : List UInt8 := [0x8F, toByte1 x, toByte2 x]

/-- Decode a 3-byte XOP prefix from the head of a byte stream. -/
def decode : List UInt8 → Option (Xop × List UInt8)
  | 0x8F :: b1 :: b2 :: rest =>
      match ofBytes? b1 b2 with
      | some x => some (x, rest)
      | none => none
  | _ => none

/-- Formal round-trip theorem for 3-byte XOP prefixes (`8F` with `m-mmmm >= 8`). -/
@[simp] theorem decode_encode (x : Xop) (rest : List UInt8) :
    decode (encode x ++ rest) = some (x, rest) := by
  simp [encode, decode, ofBytes?_toBytes]

/-- Encoded length of a 3-byte XOP prefix is strictly positive ($3 > 0$). -/
theorem encode_pos (x : Xop) : 0 < (encode x).length := by simp [encode]

/-- Formal disambiguation theorem: any `POP r/m64` (`8F /0`) ModR/M byte has `reg = 0`,
so its low 5 bits (`mmmmm`) are strictly less than 8 and `ofBytes?` returns `none`. -/
theorem pop_modrm_not_xop (mod : BitVec 2) (rm : BitVec 3) (b2 : UInt8) :
    ofBytes? (UInt8.ofBitVec (ModRm.mk mod 0 rm).toByte) b2 = none := by
  have h : XopMap.ofBits? (unpackVexByte1 (UInt8.ofBitVec (ModRm.mk mod 0 rm).toByte)).2.2.2 = none := by
    revert mod rm; decide
  dsimp only [ofBytes?]
  rw [h]

end Xop

/-! ## VSIB (Vector SIB Addressing) & `is4` Immediate Specifier -/

/-- Pack a SIB byte from scale, 3-bit index, and 3-bit base. -/
def packSibByte (scale : BitVec 2) (index : BitVec 3) (base : BitVec 3) : UInt8 :=
  UInt8.ofBitVec (Sib.mk scale index base).toByte

/-- Unpack a SIB byte into `(scale, index, base)`. -/
def unpackSibByte (b : UInt8) : BitVec 2 × BitVec 3 × BitVec 3 :=
  let s := Sib.ofByte b.toBitVec
  (s.scale, s.index, s.base)

@[simp] theorem unpackSibByte_packSibByte (scale : BitVec 2) (index base : BitVec 3) :
    unpackSibByte (packSibByte scale index base) = (scale, index, base) := by
  revert scale index base; decide

/-- Vector SIB addressing structure (SIB byte where `index` selects a vector register `xmm`/`ymm`/`zmm`). -/
structure Vsib where
  scale : BitVec 2
  indexVec : VecReg
  baseGpr : Gpr
deriving DecidableEq, Repr, Inhabited

namespace Vsib

/-- Emit the SIB byte corresponding to a VSIB operand (`scale | indexVec.low3 | baseGpr.encodingBits`). -/
def toSibByte (v : Vsib) : UInt8 :=
  packSibByte v.scale v.indexVec.low3 v.baseGpr.encodingBits

/-- Reconstruct a `Vsib` from a SIB byte together with the vector index's `X'` (bit 4) and `X` (bit 3)
bits and the base register's `B` (bit 3) bit. -/
def ofSibByte (xPrime xBit bBit : Bool) (sibByte : UInt8) : Vsib :=
  let (scale, idxBits, baseBits) := unpackSibByte sibByte
  { scale := scale
    indexVec := VecReg.ofSplit xPrime xBit idxBits
    baseGpr := Gpr.ofSplit bBit baseBits }

@[simp] theorem ofSibByte_toSibByte (v : Vsib) :
    ofSibByte v.indexVec.bit4 v.indexVec.bit3 v.baseGpr.isExtended (toSibByte v) = v := by
  cases v with
  | mk scale indexVec baseGpr =>
      simp only [toSibByte, ofSibByte, unpackSibByte_packSibByte, VecReg.ofSplit_split, Gpr.ofSplit_split]

end Vsib

/-- Pack an `is4` specifier byte: low 4 bits of `reg` in bits 7:4, `payload` in bits 3:0. -/
def packIs4Byte (reg4 : BitVec 4) (payload : BitVec 4) : UInt8 :=
  UInt8.ofBitVec (reg4 ++ payload)

/-- Unpack an `is4` specifier byte into `(reg4, payload)`. -/
def unpackIs4Byte (b : UInt8) : BitVec 4 × BitVec 4 :=
  let bv := b.toBitVec
  (BitVec.extractLsb' 4 4 bv, BitVec.extractLsb' 0 4 bv)

@[simp] theorem unpackIs4Byte_packIs4Byte (reg4 payload : BitVec 4) :
    unpackIs4Byte (packIs4Byte reg4 payload) = (reg4, payload) := by
  revert reg4 payload; decide

def VecReg.low4 (r : VecReg) : BitVec 4 := BitVec.ofNat 4 (r.val % 16)

def VecReg.ofBit4AndLow4 (b4 : Bool) (low4 : BitVec 4) : VecReg :=
  ⟨(if b4 then 16 else 0) + low4.toNat, by revert b4 low4; decide⟩

@[simp] theorem VecReg.ofBit4AndLow4_split (r : VecReg) :
    VecReg.ofBit4AndLow4 (VecReg.bit4 r) (VecReg.low4 r) = r := by
  revert r; decide

/-- 4th-operand immediate specifier byte (`is4`) for VEX/XOP 4-operand instructions (e.g., `VFMADD*` FMA4, `VPBLENDVB`). -/
structure Is4 where
  reg : VecReg
  payload : BitVec 4
deriving DecidableEq, Repr, Inhabited

namespace Is4

/-- Encode an `is4` specifier byte (bits 7:4 hold low 4 bits of `reg`, bits 3:0 hold `payload`). -/
def toByte (i : Is4) : UInt8 :=
  packIs4Byte i.reg.low4 i.payload

/-- Decode an `is4` specifier byte given bit 4 (`regBit4`, always `false` in 16-register VEX mode). -/
def ofByte (regBit4 : Bool) (b : UInt8) : Is4 :=
  let (reg4, payload) := unpackIs4Byte b
  { reg := VecReg.ofBit4AndLow4 regBit4 reg4
    payload := payload }

@[simp] theorem ofByte_toByte (i : Is4) :
    ofByte i.reg.bit4 (toByte i) = i := by
  cases i with
  | mk reg payload =>
      simp only [toByte, ofByte, unpackIs4Byte_packIs4Byte, VecReg.ofBit4AndLow4_split]

end Is4

/-! ## $O(1)$ Prefix Header Classifier & Formal Disjointness Theorems -/

/-- High-level prefix/header classification for $O(1)$ family dispatch in `decode`. -/
inductive PrefixHeaderClass where
  /-- 4-byte EVEX prefix (`0x62`). -/
  | evex
  /-- 2-byte VEX prefix (`0xC5`). -/
  | vex2
  /-- 3-byte VEX prefix (`0xC4`). -/
  | vex3
  /-- 3-byte AMD XOP prefix (`0x8F` with `m-mmmm >= 8`). -/
  | xop
  /-- Legacy prefix (Groups 1–4) or REX prefix (`0x40`–`0x4F`). -/
  | legacyOrRex
  /-- Primary opcode byte directly (or `POP r/m64` `0x8F /0`). -/
  | opcode
deriving DecidableEq, Repr, Inhabited

/-- Classify the leading header byte(s) of a byte stream in $O(1)$ time. -/
def classifyPrefixHeader : List UInt8 → PrefixHeaderClass
  | [] => .opcode
  | b0 :: rest =>
      if b0 == 0x62 then .evex
      else if b0 == 0xC5 then .vex2
      else if b0 == 0xC4 then .vex3
      else if b0 == 0x8F then
        match rest with
        | b1 :: _ => if 8 ≤ (BitVec.extractLsb' 0 5 b1.toBitVec).toNat then .xop else .opcode
        | [] => .opcode
      else if isLegacyPrefixByte b0 || (0x40 ≤ b0.toNat && b0.toNat ≤ 0x4F) then .legacyOrRex
      else .opcode

/-- Formal disjointness: any EVEX-encoded instruction classifies strictly as `.evex`. -/
@[simp] theorem classifyPrefixHeader_evex (e : Evex) (rest : List UInt8) :
    classifyPrefixHeader (Evex.encode e ++ rest) = .evex := rfl

/-- Formal disjointness: any 2-byte VEX-encoded instruction classifies strictly as `.vex2`. -/
@[simp] theorem classifyPrefixHeader_vex2 (v : Vex2) (rest : List UInt8) :
    classifyPrefixHeader (Vex2.encode v ++ rest) = .vex2 := rfl

/-- Formal disjointness: any 3-byte VEX-encoded instruction classifies strictly as `.vex3`. -/
@[simp] theorem classifyPrefixHeader_vex3 (v : Vex3) (rest : List UInt8) :
    classifyPrefixHeader (Vex3.encode v ++ rest) = .vex3 := rfl

private theorem xop_toByte1_ge_8 (x : Xop) :
    8 ≤ (BitVec.extractLsb' 0 5 (Xop.toByte1 x).toBitVec).toNat := by
  cases x with
  | mk r xb bb map w vvvv l pp =>
      have hm : BitVec.extractLsb' 0 5 (packVexByte1 r xb bb map.toBits).toBitVec = map.toBits := by
        cases map <;> revert r xb bb <;> decide
      simp only [Xop.toByte1, hm, XopMap.toBits_ge_8]

/-- Formal disjointness: any XOP-encoded instruction (`m-mmmm >= 8`) classifies strictly as `.xop`. -/
@[simp] theorem classifyPrefixHeader_xop (x : Xop) (rest : List UInt8) :
    classifyPrefixHeader (Xop.encode x ++ rest) = .xop := by
  have h := xop_toByte1_ge_8 x
  simp only [Xop.encode, List.cons_append, classifyPrefixHeader, h, ↓reduceIte]
  decide

/-- Formal disjointness: any `POP r/m64` (`0x8F /0`) classifies strictly as `.opcode`, never `.xop`. -/
theorem classifyPrefixHeader_pop (mod : BitVec 2) (rm : BitVec 3) (rest : List UInt8) :
    classifyPrefixHeader (0x8F :: UInt8.ofBitVec (ModRm.mk mod 0 rm).toByte :: rest) = .opcode := by
  have hlt : ¬ (8 ≤ (BitVec.extractLsb' 0 5 (UInt8.ofBitVec (ModRm.mk mod 0 rm).toByte).toBitVec).toNat) := by
    revert mod rm; decide
  simp only [classifyPrefixHeader, hlt, ↓reduceIte]
  decide

private theorem rex_header_byte_class (r : Rex) :
    let b0 := UInt8.ofBitVec r.toByte
    (b0 == 0x62) = false ∧ (b0 == 0xC5) = false ∧ (b0 == 0xC4) = false ∧ (b0 == 0x8F) = false ∧
    (isLegacyPrefixByte b0 || (0x40 ≤ b0.toNat && b0.toNat ≤ 0x4F)) = true := by
  cases r with
  | mk w rb xb bb => revert w rb xb bb; decide

/-- Formal disjointness: any REX prefix byte (`0x40`–`0x4F`) classifies strictly as `.legacyOrRex`. -/
@[simp] theorem classifyPrefixHeader_rex (r : Rex) (rest : List UInt8) :
    classifyPrefixHeader (UInt8.ofBitVec r.toByte :: rest) = .legacyOrRex := by
  have ⟨h1, h2, h3, h4, h5⟩ := rex_header_byte_class r
  simp only [classifyPrefixHeader, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]

end Grass.ISA.X86.Target.Core
