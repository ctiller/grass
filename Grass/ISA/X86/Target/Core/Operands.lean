import Grass.ISA.X86.Register

/-!
# Unified Operand Representations for the 64-bit x86-64 ISA Seam

Defines the unified operand types shared across all x86-64 instruction families:
- General-purpose registers (`Gpr`, `ByteReg`, `Width`, `GprView`) reusing `Grass.ISA.X86.Register`
- Vector registers (`VecReg` as `Fin 32`, `VecWidth`, `VecView` with `xmm`/`ymm`/`zmm` views)
- Opmask registers (`MaskReg` as `Fin 8` for `k0`–`k7`)
- Segment registers (`SegReg`: `es`, `cs`, `ss`, `ds`, `fs`, `gs`)
- Control registers (`CtrlReg`: `CR0`–`CR15`)
- Debug registers (`DbgReg`: `DR0`–`DR7`)
- X87 FPU stack registers (`X87Reg`: `ST0`–`ST7`)
- Rounding modes (`RoundingMode`: `rn`, `rd`, `ru`, `rz`)
- EVEX compressed displacement tuple types (`TupleType`) and scaling (`scaleDisp8` / `unscaleDisp8`)
  with formal round-trip proofs (`unscaleDisp8_scaleDisp8`).
-/

namespace Grass.ISA.X86.Target.Core

export Grass.ISA.X86 (Gpr Width ByteReg writeBack)

/-! ## General-purpose register views -/

/-- A width-annotated general-purpose register operand (8/16/32/64-bit views). -/
inductive GprView where
  /-- 8-bit register operand (`al`..`r15b` or `ah`..`bh`). -/
  | r8 (reg : ByteReg)
  /-- 16-bit register operand (`ax`..`r15w`). -/
  | r16 (reg : Gpr)
  /-- 32-bit register operand (`eax`..`r15d`), zero-extending on write. -/
  | r32 (reg : Gpr)
  /-- 64-bit register operand (`rax`..`r15`). -/
  | r64 (reg : Gpr)
deriving DecidableEq, Repr, Inhabited

namespace GprView

/-- The operand width of a `GprView`. -/
def width : GprView → Width
  | .r8 _ => .w8
  | .r16 _ => .w16
  | .r32 _ => .w32
  | .r64 _ => .w64

/-- The underlying 64-bit general-purpose register of a `GprView`. -/
def baseGpr : GprView → Gpr
  | .r8 (.low r) => r
  | .r8 (.high r) => r
  | .r16 r => r
  | .r32 r => r
  | .r64 r => r

end GprView

/-! ## Vector registers (`xmm0`–`xmm31`, `ymm0`–`ymm31`, `zmm0`–`zmm31`) -/

/-- Architectural vector register index (`0`–`31`). -/
abbrev VecReg : Type := Fin 32

namespace VecReg

/-- Convert a 5-bit vector register encoding (`R'`/`V'`/`X'`/`B'` + 4-bit field) to `VecReg`. -/
def ofBits (b : BitVec 5) : VecReg := ⟨b.toNat, b.isLt⟩

/-- The 5-bit architectural encoding of a `VecReg`. -/
def toBits (r : VecReg) : BitVec 5 := BitVec.ofNat 5 r.val

@[simp] theorem ofBits_toBits (r : VecReg) : ofBits (toBits r) = r := by
  ext
  simp only [ofBits, toBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt r.isLt

@[simp] theorem toBits_ofBits (b : BitVec 5) : toBits (ofBits b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [toBits, ofBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt b.isLt

/-- The low 3 bits written into ModR/M or SIB `reg`/`rm`/`index` fields. -/
def low3 (r : VecReg) : BitVec 3 := BitVec.ofNat 3 (r.val % 8)

/-- Bit 3 of the vector register index (REX/VEX/EVEX `R`/`X`/`B` bit). -/
def bit3 (r : VecReg) : Bool := (r.val / 8) % 2 == 1

/-- Bit 4 of the vector register index (EVEX `R'`/`V'`/`X'` bit). -/
def bit4 (r : VecReg) : Bool := (r.val / 16) % 2 == 1

/-- Reconstruct a 5-bit `VecReg` from bit 4, bit 3, and low 3 bits. -/
def ofSplit (b4 b3 : Bool) (low : BitVec 3) : VecReg :=
  ⟨(if b4 then 16 else 0) + (if b3 then 8 else 0) + low.toNat, by revert b4 b3 low; decide⟩

@[simp] theorem ofSplit_split (r : VecReg) :
    ofSplit (bit4 r) (bit3 r) (low3 r) = r := by
  revert r; decide

end VecReg

/-- Vector operand width: 128-bit (`xmm`), 256-bit (`ymm`), or 512-bit (`zmm`). -/
inductive VecWidth where
  | v128
  | v256
  | v512
deriving DecidableEq, Repr, Inhabited

namespace VecWidth

/-- Vector width in bits (128, 256, or 512). -/
def bits : VecWidth → Nat
  | .v128 => 128
  | .v256 => 256
  | .v512 => 512

/-- Vector width in bytes (16, 32, or 64). -/
def bytes : VecWidth → Nat
  | .v128 => 16
  | .v256 => 32
  | .v512 => 64

/-- EVEX `L'L` 2-bit encoding (`00` = 128, `01` = 256, `10` = 512). -/
def toLL : VecWidth → BitVec 2
  | .v128 => 0
  | .v256 => 1
  | .v512 => 2

/-- Decode EVEX `L'L` 2-bit field into a `VecWidth` (`11` is reserved/invalid). -/
def ofLL? (ll : BitVec 2) : Option VecWidth :=
  if ll == 0 then some .v128
  else if ll == 1 then some .v256
  else if ll == 2 then some .v512
  else none

@[simp] theorem ofLL?_toLL (w : VecWidth) : ofLL? w.toLL = some w := by
  cases w <;> decide

end VecWidth

/-- A width-annotated vector register (`xmm0`–`xmm31`, `ymm0`–`ymm31`, `zmm0`–`zmm31`). -/
inductive VecView where
  | xmm (reg : VecReg)
  | ymm (reg : VecReg)
  | zmm (reg : VecReg)
deriving DecidableEq, Repr, Inhabited

namespace VecView

/-- Underlying vector register number (`0`–`31`). -/
def reg : VecView → VecReg
  | .xmm r => r
  | .ymm r => r
  | .zmm r => r

/-- Vector register width (`v128`, `v256`, `v512`). -/
def width : VecView → VecWidth
  | .xmm _ => .v128
  | .ymm _ => .v256
  | .zmm _ => .v512

/-- Construct a `VecView` from a width and register index. -/
def mkView : VecWidth → VecReg → VecView
  | .v128, r => .xmm r
  | .v256, r => .ymm r
  | .v512, r => .zmm r

@[simp] theorem mkView_width_reg (v : VecView) : mkView v.width v.reg = v := by
  cases v <;> rfl

end VecView

/-! ## Opmask registers (`k0`–`k7`) -/

/-- Architectural opmask register index (`k0`–`k7`). -/
abbrev MaskReg : Type := Fin 8

namespace MaskReg

def k0 : MaskReg := ⟨0, by decide⟩
def k1 : MaskReg := ⟨1, by decide⟩
def k2 : MaskReg := ⟨2, by decide⟩
def k3 : MaskReg := ⟨3, by decide⟩
def k4 : MaskReg := ⟨4, by decide⟩
def k5 : MaskReg := ⟨5, by decide⟩
def k6 : MaskReg := ⟨6, by decide⟩
def k7 : MaskReg := ⟨7, by decide⟩

/-- Convert a 3-bit encoding (`aaa` field in EVEX / ModR/M) to `MaskReg`. -/
def ofBits (b : BitVec 3) : MaskReg := ⟨b.toNat, b.isLt⟩

/-- Convert a `MaskReg` to its 3-bit architectural encoding. -/
def toBits (k : MaskReg) : BitVec 3 := BitVec.ofNat 3 k.val

@[simp] theorem ofBits_toBits (k : MaskReg) : ofBits (toBits k) = k := by
  ext
  simp only [ofBits, toBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt k.isLt

@[simp] theorem toBits_ofBits (b : BitVec 3) : toBits (ofBits b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [toBits, ofBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt b.isLt

end MaskReg

/-! ## Segment registers (`es`, `cs`, `ss`, `ds`, `fs`, `gs`) -/

/-- The six architectural segment registers of x86-64. -/
inductive SegReg where
  | es | cs | ss | ds | fs | gs
deriving DecidableEq, Repr, Inhabited

namespace SegReg

def all : List SegReg := [.es, .cs, .ss, .ds, .fs, .gs]

@[simp] theorem length_all : all.length = 6 := rfl

/-- The 3-bit segment register number (`es=0`, `cs=1`, `ss=2`, `ds=3`, `fs=4`, `gs=5`). -/
def toBits : SegReg → BitVec 3
  | .es => 0 | .cs => 1 | .ss => 2 | .ds => 3 | .fs => 4 | .gs => 5

/-- Decode a 3-bit segment register field (`6` and `7` are reserved). -/
def ofBits? (b : BitVec 3) : Option SegReg :=
  if b == 0 then some .es
  else if b == 1 then some .cs
  else if b == 2 then some .ss
  else if b == 3 then some .ds
  else if b == 4 then some .fs
  else if b == 5 then some .gs
  else none

@[simp] theorem ofBits?_toBits (s : SegReg) : ofBits? s.toBits = some s := by
  cases s <;> decide

/-- Architectural 3-bit encoding index for a segment register. -/
def toFin : SegReg → Fin 6
  | .es => ⟨0, by omega⟩
  | .cs => ⟨1, by omega⟩
  | .ss => ⟨2, by omega⟩
  | .ds => ⟨3, by omega⟩
  | .fs => ⟨4, by omega⟩
  | .gs => ⟨5, by omega⟩

end SegReg

/-! ## Control registers (`CR0`–`CR15`) -/

/-- Control registers `CR0`–`CR15` accessible in Ring-0 via `MOV CRn, r64` / `MOV r64, CRn`. -/
inductive CtrlReg where
  | cr0 | cr1 | cr2 | cr3 | cr4 | cr5 | cr6 | cr7
  | cr8 | cr9 | cr10 | cr11 | cr12 | cr13 | cr14 | cr15
deriving DecidableEq, Repr, Inhabited

namespace CtrlReg

def all : List CtrlReg :=
  [.cr0, .cr1, .cr2, .cr3, .cr4, .cr5, .cr6, .cr7,
   .cr8, .cr9, .cr10, .cr11, .cr12, .cr13, .cr14, .cr15]

@[simp] theorem length_all : all.length = 16 := rfl

def index : CtrlReg → Fin 16
  | .cr0 => 0 | .cr1 => 1 | .cr2 => 2 | .cr3 => 3
  | .cr4 => 4 | .cr5 => 5 | .cr6 => 6 | .cr7 => 7
  | .cr8 => 8 | .cr9 => 9 | .cr10 => 10 | .cr11 => 11
  | .cr12 => 12 | .cr13 => 13 | .cr14 => 14 | .cr15 => 15

def ofIndex (i : Fin 16) : CtrlReg := all.getD i.val .cr0

@[simp] theorem ofIndex_index (r : CtrlReg) : ofIndex r.index = r := by
  cases r <;> rfl

@[simp] theorem index_ofIndex (i : Fin 16) : (ofIndex i).index = i := by
  revert i; decide

def lowBits (r : CtrlReg) : BitVec 3 := BitVec.ofNat 3 (r.index.val % 8)

def isExtended (r : CtrlReg) : Bool := decide (8 ≤ r.index.val)

def ofSplit (ext : Bool) (low : BitVec 3) : CtrlReg :=
  ofIndex ⟨(if ext then 8 else 0) + low.toNat, by revert ext low; decide⟩

@[simp] theorem ofSplit_split (r : CtrlReg) : ofSplit r.isExtended r.lowBits = r := by
  cases r <;> decide

end CtrlReg

/-! ## Debug registers (`DR0`–`DR7`) -/

/-- Debug registers `DR0`–`DR7` accessible in Ring-0 via `MOV DRn, r64` / `MOV r64, DRn`. -/
inductive DbgReg where
  | dr0 | dr1 | dr2 | dr3 | dr4 | dr5 | dr6 | dr7
deriving DecidableEq, Repr, Inhabited

namespace DbgReg

def all : List DbgReg := [.dr0, .dr1, .dr2, .dr3, .dr4, .dr5, .dr6, .dr7]

@[simp] theorem length_all : all.length = 8 := rfl

def index : DbgReg → Fin 8
  | .dr0 => 0 | .dr1 => 1 | .dr2 => 2 | .dr3 => 3
  | .dr4 => 4 | .dr5 => 5 | .dr6 => 6 | .dr7 => 7

def ofIndex (i : Fin 8) : DbgReg := all.getD i.val .dr0

@[simp] theorem ofIndex_index (r : DbgReg) : ofIndex r.index = r := by
  cases r <;> rfl

@[simp] theorem index_ofIndex (i : Fin 8) : (ofIndex i).index = i := by
  revert i; decide

def toBits (r : DbgReg) : BitVec 3 := BitVec.ofNat 3 r.index.val

def ofBits (b : BitVec 3) : DbgReg := ofIndex ⟨b.toNat, b.isLt⟩

@[simp] theorem ofBits_toBits (r : DbgReg) : ofBits r.toBits = r := by
  cases r <;> decide

@[simp] theorem toBits_ofBits (b : BitVec 3) : (ofBits b).toBits = b := by
  revert b; decide

end DbgReg

/-! ## X87 FPU registers (`ST0`–`ST7`) -/

/-- X87 FPU stack registers `ST(0)`–`ST(7)`. -/
inductive X87Reg where
  | st0 | st1 | st2 | st3 | st4 | st5 | st6 | st7
deriving DecidableEq, Repr, Inhabited

namespace X87Reg

def all : List X87Reg := [.st0, .st1, .st2, .st3, .st4, .st5, .st6, .st7]

@[simp] theorem length_all : all.length = 8 := rfl

def index : X87Reg → Fin 8
  | .st0 => 0 | .st1 => 1 | .st2 => 2 | .st3 => 3
  | .st4 => 4 | .st5 => 5 | .st6 => 6 | .st7 => 7

def ofIndex (i : Fin 8) : X87Reg := all.getD i.val .st0

@[simp] theorem ofIndex_index (r : X87Reg) : ofIndex r.index = r := by
  cases r <;> rfl

@[simp] theorem index_ofIndex (i : Fin 8) : (ofIndex i).index = i := by
  revert i; decide

def toBits (r : X87Reg) : BitVec 3 := BitVec.ofNat 3 r.index.val

def ofBits (b : BitVec 3) : X87Reg := ofIndex ⟨b.toNat, b.isLt⟩

@[simp] theorem ofBits_toBits (r : X87Reg) : ofBits r.toBits = r := by
  cases r <;> decide

@[simp] theorem toBits_ofBits (b : BitVec 3) : (ofBits b).toBits = b := by
  revert b; decide

end X87Reg

/-! ## IEEE-754 / EVEX Rounding Modes (`{rn-sae}`, `{rd-sae}`, `{ru-sae}`, `{rz-sae}`) -/

/-- IEEE-754 rounding control modes (`L'L` field when `EVEX.b = 1` on reg-reg instructions). -/
inductive RoundingMode where
  /-- Round to nearest (even). -/
  | rn
  /-- Round down (toward $-\infty$). -/
  | rd
  /-- Round up (toward $+\infty$). -/
  | ru
  /-- Round toward zero (truncate). -/
  | rz
deriving DecidableEq, Repr, Inhabited

namespace RoundingMode

def toBits : RoundingMode → BitVec 2
  | .rn => 0
  | .rd => 1
  | .ru => 2
  | .rz => 3

def ofBits (b : BitVec 2) : RoundingMode :=
  if b == 0 then .rn
  else if b == 1 then .rd
  else if b == 2 then .ru
  else .rz

@[simp] theorem ofBits_toBits (m : RoundingMode) : ofBits m.toBits = m := by
  cases m <;> decide

@[simp] theorem toBits_ofBits (b : BitVec 2) : (ofBits b).toBits = b := by
  revert b; decide

end RoundingMode

/-! ## EVEX Tuple Types & Compressed Displacement Scaling (`disp8*N`) -/

/-- EVEX compressed displacement tuple types (Intel SDM Vol. 2A §2.6.5 Table 2-34/2-35). -/
inductive TupleType where
  /-- Full Vector (16/32/64 bytes, or element size when broadcasting). -/
  | full
  /-- Half Vector (8/16/32 bytes, or element size when broadcasting). -/
  | half
  /-- Full Vector Memory (no broadcast, 16/32/64 bytes). -/
  | fullMem
  /-- Tuple1 Scalar (scalar element size: 1/2/4/8 bytes). -/
  | tuple1Scalar
  /-- Tuple1 Fixed (fixed 4 or 8 bytes regardless of vector length). -/
  | tuple1Fixed
  /-- Tuple2 (2 elements: 8 or 16 bytes). -/
  | tuple2
  /-- Tuple4 (4 elements: 16 or 32 bytes). -/
  | tuple4
  /-- Tuple8 (8 elements: 32 bytes). -/
  | tuple8
  /-- Quarter Vector (4/8/16 bytes). -/
  | quarter
  /-- Eighth Vector (2/4/8 bytes). -/
  | eighth
  /-- Mem128 (fixed 16 bytes). -/
  | mem128
  /-- MOVDDUP (8/32/64 bytes). -/
  | dup
deriving DecidableEq, Repr, Inhabited

namespace TupleType

/-- Compute the positive scaling factor $N$ (`disp8*N`) for a given tuple type, vector width,
element size in bytes (`1`, `2`, `4`, or `8`), and broadcast flag. -/
def scaleFactor (tt : TupleType) (vl : VecWidth) (elemBytes : Nat) (broadcast : Bool) : Nat :=
  let eb := if elemBytes = 0 then 1 else elemBytes
  match tt with
  | .full => if broadcast then eb else vl.bytes
  | .half => if broadcast then eb else vl.bytes / 2
  | .fullMem => vl.bytes
  | .tuple1Scalar => eb
  | .tuple1Fixed => eb
  | .tuple2 => 2 * eb
  | .tuple4 => 4 * eb
  | .tuple8 => 8 * eb
  | .quarter => max 1 (vl.bytes / 4)
  | .eighth => max 1 (vl.bytes / 8)
  | .mem128 => 16
  | .dup =>
      match vl with
      | .v128 => 8
      | .v256 => 32
      | .v512 => 64

/-- The compressed displacement scaling factor is strictly positive ($0 < N$). -/
theorem scaleFactor_pos (tt : TupleType) (vl : VecWidth) (elemBytes : Nat) (broadcast : Bool) :
    0 < scaleFactor tt vl elemBytes broadcast := by
  unfold scaleFactor
  have heb : 0 < (if elemBytes = 0 then 1 else elemBytes) := by
    split <;> omega
  cases tt <;> cases vl <;> cases broadcast <;> simp [VecWidth.bytes] <;> omega

end TupleType

/-- Scale an 8-bit signed compressed displacement (`disp8`) by scale factor `scale` ($N$). -/
def scaleDisp8 (scale : Nat) (disp8 : BitVec 8) : Int :=
  disp8.toInt * Int.ofNat scale

/-- Unscale a byte displacement (`dispBytes`) back to an 8-bit signed compressed displacement
(`disp8`), checking exact divisibility and 8-bit signed range $[-128, 127]$. -/
def unscaleDisp8 (scale : Nat) (dispBytes : Int) : Option (BitVec 8) :=
  if scale = 0 then none
  else
    let s : Int := Int.ofNat scale
    if dispBytes % s == 0 then
      let q := dispBytes / s
      if -128 ≤ q ∧ q ≤ 127 then
        some (BitVec.ofInt 8 q)
      else none
    else none

private theorem bitvec8_toInt_bounds (d : BitVec 8) : -128 ≤ d.toInt ∧ d.toInt ≤ 127 := by
  revert d; decide

private theorem bitvec8_ofInt_toInt (d : BitVec 8) : BitVec.ofInt 8 d.toInt = d := by
  revert d; decide

/-- Round-trip theorem: scaling an 8-bit compressed displacement by any positive factor `scale`
and unscaling recovers the exact 8-bit displacement `disp8`. -/
theorem unscaleDisp8_scaleDisp8 {scale : Nat} (hpos : 0 < scale) (disp8 : BitVec 8) :
    unscaleDisp8 scale (scaleDisp8 scale disp8) = some disp8 := by
  unfold unscaleDisp8 scaleDisp8
  have hne : scale ≠ 0 := Nat.ne_of_gt hpos
  have hsne : (Int.ofNat scale : Int) ≠ 0 := Int.ofNat_ne_zero.mpr hne
  have hmod : (disp8.toInt * Int.ofNat scale) % Int.ofNat scale = 0 :=
    Int.mul_emod_left disp8.toInt (Int.ofNat scale)
  have hdiv : (disp8.toInt * Int.ofNat scale) / Int.ofNat scale = disp8.toInt :=
    Int.mul_ediv_cancel disp8.toInt hsne
  have hbounds : -128 ≤ disp8.toInt ∧ disp8.toInt ≤ 127 := bitvec8_toInt_bounds disp8
  simp only [hne, ↓reduceIte, hmod, beq_self_eq_true, hdiv, hbounds,
    and_self, bitvec8_ofInt_toInt]

end Grass.ISA.X86.Target.Core
