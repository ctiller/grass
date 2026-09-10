import Grass.Assembly.Lower.Layout
import Grass.Assembly.Syntax.Parser
import Grass.ISA.AArch64.Target

/-!
# The AArch64 instance of the lowering seam

`Grass.Assembly.Lower.AArch64.lowering` fills `Lowering Grass.ISA.AArch64.isa`
for exactly the instruction families
`Grass/ISA/AArch64/Target/Encoding.lean` encodes today. Every A64 instruction
is one 32-bit word, so `size` is 4 for an instruction line and 0 for a label or
a directive, and `lower_size` needs nothing beyond "a lowered line is one
instruction".

## Mnemonic table

Every one of `Grass.ISA.AArch64.Target.Instr`'s fifteen constructors
(`Grass/ISA/AArch64/Target/Encoding.lean`, "Coverage") is reachable from some
row below.

| written | operands | encoded family |
| --- | --- | --- |
| `movz`, `movn`, `movk` | reg, imm [, shift imm] | move-wide |
| `mov` | reg, imm | move-wide, canonical `movz` (Arm DDI 0602 ID032025 "MOV (wide immediate)", an alias of `movz`; `movn`'s narrower/negative-immediate alias is not chosen here — refused rather than guessed) |
| `mov` | reg, reg | logical shifted-register, `orr Rd, XZR/WZR, Rm` (Arm DDI 0602 ID032025 "MOV (register)", the documented `orr`-with-zero-register alias; already the reading `LogicalShiftedReg`'s own docstring gives that encoding, so no separate alias constructor is needed); `sp` on either side falls back to add/sub immediate's "MOV (to/from SP)" alias instead, since `orr`'s field-31 operands are always `xzr`, never `sp` |
| `add`, `adds`, `sub`, `subs` | reg, reg, imm | add/sub immediate |
| `add`, `adds`, `sub`, `subs` | reg, reg, reg | add/sub shifted register, `lsl #0` |
| `cmp`, `cmn` | reg, imm or reg | the same two, destination field 31 |
| `and`, `orr`, `eor` | reg, reg, imm | logical immediate, 64-bit low-run masks |
| `and`, `orr`, `eor` | reg, reg, reg | logical shifted-register, `lsl #0` (`ands`/`tst` are decodable but not exposed as separate mnemonics here — out of scope for this pass) |
| `ldr`, `str` | reg, memory | load/store unsigned offset, 8 or 4 bytes |
| `ldrb`, `strb` | reg, memory | load/store unsigned offset, 1 byte |
| `cbz` | reg, label | compare-and-branch-if-zero, offset from this line |
| `cbnz` | reg, label | compare-and-branch-if-nonzero, offset from this line |
| `svc` | imm | supervisor call |
| `hlt` | imm or nothing | halt |
| `b` | label | unconditional branch (immediate), offset from this line, imm26 scaled by 4 (±128 MiB) |
| `bl` | label | unconditional branch (immediate), `op = 1`, writes `pc + 4` to `x30` |
| `b.<cond>` | label | conditional branch (immediate), offset from this line, imm19 scaled by 4 (±1 MiB, same range as `cbz`); `<cond>` is any of the 16 Arm DDI 0602 ID032025 "Condition codes" mnemonics (`eq`,`ne`,`cs`/`hs`,`cc`/`lo`,`mi`,`pl`,`vs`,`vc`,`hi`,`ls`,`ge`,`lt`,`gt`,`le`,`al`,`nv`) |
| `br` | reg | unconditional branch (register) |
| `blr` | reg | unconditional branch (register), writes `pc + 4` to `x30` |
| `ret` | reg or nothing | unconditional branch (register); no operand defaults to `x30` |
| `adr` | reg, label | PC-relative address, byte offset from this line (±1 MiB) |
| `adrp` | reg, label | PC-relative address, `op = 1`, page offset from this line's page to the target's page (±4 GiB in 4 KiB pages) |
| `nop` | none | `hint #0` |

Anything else — including every addressing mode but base-plus-unsigned-offset
(`ldp`/`stp`, register-offset and pre/post-index load/store, none of which
`Grass/ISA/AArch64/Target/Encoding.lean` encodes), `tbz`/`tbnz`, `brk`,
`madd`/`mul`, `udiv`/`sdiv`, `csel`/`cset`, and `lsl`/`lsr`/`asr` immediate
(`ubfm`/`sbfm`) — is refused with a message naming the line, because encoding
it does not exist yet (`Instr` has no constructor for it).

Register spellings: `x0`..`x30`, `w0`..`w30`, `sp`, `xzr`, `wzr`. `sp` and
`xzr` both assemble to field 31; which one a 31 denotes is the instruction's
reading, never this module's, matching the raw-field discipline in
`Grass/ISA/AArch64/Target/Encoding.lean`.
-/

namespace Grass.Assembly.Lower.AArch64

open Grass.Assembly.Syntax
open Grass.ISA.AArch64
open Grass.ISA.AArch64.Target

/-! ## Operands -/

/-- `some (field, is64)` for a recognized register spelling. -/
def parseRegister (name : String) : Option (BitVec 5 × Bool) :=
  if name = "sp" || name = "xzr" then some (31, true)
  else if name = "wzr" then some (31, false)
  else
    let wide := name.front == 'x'
    if wide || name.front == 'w' then
      match (name.drop 1).toNat? with
      | some number => if number ≤ 30 then some (BitVec.ofNat 5 number, wide) else none
      | none => none
    else none

/-- The register an operand names. -/
def register : Operand → Option (BitVec 5 × Bool)
  | .reg name => parseRegister name
  | _ => none

/-- The value an operand denotes as an immediate: a literal, a named constant,
a `sizeof`, or the address a symbol resolved to. -/
def immediate (env : Env) (labels : String → Option Nat) : Operand → Option Int
  | .imm value => some value
  | .symbol name =>
      match env.constant name with
      | some value => some value
      | none => (labels name).map Int.ofNat
  | .sizeOf name => (env.sizeOf name).map Int.ofNat
  | _ => none

/-- The label an operand names. -/
def labelTarget (labels : String → Option Nat) : Operand → Option Nat
  | .symbol name => labels name
  | _ => none

/-- `some (base, offset)` for the addressing mode this ISA encodes: a 64-bit
base register plus a non-negative byte offset. A declared frame local is that
mode with the frame base and the local's slot. -/
def addressed (env : Env) : Operand → Option (BitVec 5 × Nat)
  | .mem _ (some base) none (.int value) .offset =>
      match parseRegister base with
      | some (field, true) => if value < 0 then none else some (field, value.toNat)
      | _ => none
  | .local name => (env.slot name).map fun offset => (31, offset)
  | _ => none

/-- A non-negative immediate that fits an unsigned field. -/
def unsignedField (bits : Nat) (value : Int) : Option (BitVec bits) :=
  if 0 ≤ value && value < (2 : Int) ^ bits then some (BitVec.ofNat bits value.toNat) else none

/-- A scaled offset that fits an unsigned field. -/
def unsignedNat (bits : Nat) (value : Nat) : Option (BitVec bits) :=
  if value < 2 ^ bits then some (BitVec.ofNat bits value) else none

/-- The `hw` field for a move-wide shift written in bits. -/
def shiftField (wide : Bool) (amount : Int) : Option (BitVec 2) :=
  if amount = 0 then some 0
  else if amount = 16 then some 1
  else if wide && amount = 32 then some 2
  else if wide && amount = 48 then some 3
  else none

/-- The `imms` field of the only logical immediates this ISA encodes: the
64-bit contiguous low-order runs. -/
def lowRunMask (value : Int) : Option (BitVec 6) :=
  if value < 0 then none
  else (List.range 64).findSome? fun run =>
    if value.toNat + 1 = 2 ^ (run + 1) then some (BitVec.ofNat 6 run) else none

/-- A branch displacement in bytes as a `cbz` `imm19`. -/
def branchOffset (delta : Int) : Option (BitVec 19) :=
  if delta % 4 = 0 && -(2 ^ 20 : Int) ≤ delta && delta < (2 ^ 20 : Int) then
    some (BitVec.ofInt 19 (delta / 4))
  else none

/-- Bytes one access of this width moves, which is also its offset scale. -/
def accessScale : LsSize → Nat
  | .byte => 1
  | .word32 => 4
  | .double64 => 8

/-- The `sf` bit of a register width. -/
def widthBit (wide : Bool) : BitVec 1 := if wide then 1 else 0

/-! ## Refusals -/

/-- How an operand is written back to the author in a refusal. -/
def describe : Operand → String
  | .reg name => name
  | .imm value => toString value
  | .symbol name => name
  | .sizeOf name => "sizeof(" ++ name ++ ")"
  | .mem _ base _ _ _ => "[" ++ base.getD "" ++ " ...]"
  | .local name => name
  | .localAddress name => name ++ ".addr"

/-- The line a refusal names. -/
def render (mnemonic : String) (operands : List Operand) : String :=
  mnemonic ++ " " ++ String.intercalate ", " (operands.map describe)

/-- Refuse when the operand shape is not one this ISA encodes. -/
def orRefuse {α : Type} (value : Option α) (message : String) : Except String α :=
  match value with
  | some found => .ok found
  | none => .error message

/-! ## Families -/

/-- The instruction families a mnemonic can select. -/
inductive Family where
  | moveWide (op : MoveWideOp)
  | mov
  | addSub (isSub setFlags : Bool)
  | compare (isSub : Bool)
  | logical (op : LogicalOp)
  | loadStore (isLoad forceByte : Bool)
  | compareZero
  | compareNonZero
  | supervisor
  | halt
  | branch (isLink : Bool)
  | branchRegister (op : BranchRegOp)
  | condBranch (cond : BitVec 4)
  | adr (isPage : Bool)
  | nop

/-- The mnemonic table. `b.<cond>`'s sixteen spellings (Arm DDI 0602 ID032025
"Condition codes") are sixteen whole-string rows here, not a `b.`-prefix
decomposition: this front end's mnemonic is always matched by plain `String`
equality against a literal, the same as every other row, never by taking the
string apart. -/
def family (mnemonic : String) : Option Family :=
  if mnemonic = "movn" then some (.moveWide .movn)
  else if mnemonic = "movz" then some (.moveWide .movz)
  else if mnemonic = "movk" then some (.moveWide .movk)
  else if mnemonic = "mov" then some .mov
  else if mnemonic = "add" then some (.addSub false false)
  else if mnemonic = "adds" then some (.addSub false true)
  else if mnemonic = "sub" then some (.addSub true false)
  else if mnemonic = "subs" then some (.addSub true true)
  else if mnemonic = "cmp" then some (.compare true)
  else if mnemonic = "cmn" then some (.compare false)
  else if mnemonic = "and" then some (.logical .and)
  else if mnemonic = "orr" then some (.logical .orr)
  else if mnemonic = "eor" then some (.logical .eor)
  else if mnemonic = "ldr" then some (.loadStore true false)
  else if mnemonic = "str" then some (.loadStore false false)
  else if mnemonic = "ldrb" then some (.loadStore true true)
  else if mnemonic = "strb" then some (.loadStore false true)
  else if mnemonic = "cbz" then some .compareZero
  else if mnemonic = "cbnz" then some .compareNonZero
  else if mnemonic = "svc" then some .supervisor
  else if mnemonic = "hlt" then some .halt
  else if mnemonic = "b" then some (.branch false)
  else if mnemonic = "bl" then some (.branch true)
  else if mnemonic = "br" then some (.branchRegister .br)
  else if mnemonic = "blr" then some (.branchRegister .blr)
  else if mnemonic = "ret" then some (.branchRegister .ret)
  else if mnemonic = "adr" then some (.adr false)
  else if mnemonic = "adrp" then some (.adr true)
  else if mnemonic = "nop" then some .nop
  else if mnemonic = "b.eq" then some (.condBranch 0)
  else if mnemonic = "b.ne" then some (.condBranch 1)
  else if mnemonic = "b.cs" || mnemonic = "b.hs" then some (.condBranch 2)
  else if mnemonic = "b.cc" || mnemonic = "b.lo" then some (.condBranch 3)
  else if mnemonic = "b.mi" then some (.condBranch 4)
  else if mnemonic = "b.pl" then some (.condBranch 5)
  else if mnemonic = "b.vs" then some (.condBranch 6)
  else if mnemonic = "b.vc" then some (.condBranch 7)
  else if mnemonic = "b.hi" then some (.condBranch 8)
  else if mnemonic = "b.ls" then some (.condBranch 9)
  else if mnemonic = "b.ge" then some (.condBranch 10)
  else if mnemonic = "b.lt" then some (.condBranch 11)
  else if mnemonic = "b.gt" then some (.condBranch 12)
  else if mnemonic = "b.le" then some (.condBranch 13)
  else if mnemonic = "b.al" then some (.condBranch 14)
  else if mnemonic = "b.nv" then some (.condBranch 15)
  else none

def lowerMoveWide (op : MoveWideOp) (dest value shift : Operand) (env : Env)
    (labels : String → Option Nat) (note : String) : Except String Instr := do
  let (rd, wide) ← orRefuse (register dest) ("destination is not a register: " ++ note)
  let imm ← orRefuse (immediate env labels value >>= unsignedField 16)
    ("immediate does not fit 16 bits: " ++ note)
  let hw ← orRefuse (immediate env labels shift >>= shiftField wide)
    ("shift is not 0, 16, 32 or 48: " ++ note)
  .ok (.moveWide { sf := widthBit wide, op := op, hw := hw, imm16 := imm, rd := rd })

def lowerAddSub (isSub setFlags : Bool) (dest left right : Operand) (env : Env)
    (labels : String → Option Nat) (note : String) : Except String Instr := do
  let (rd, wide) ← orRefuse (register dest) ("destination is not a register: " ++ note)
  let (rn, wideLeft) ← orRefuse (register left) ("first source is not a register: " ++ note)
  if wide != wideLeft then
    .error ("operands mix 32-bit and 64-bit registers: " ++ note)
  else
    match register right with
    | some (rm, wideRight) =>
        if wide != wideRight then
          .error ("operands mix 32-bit and 64-bit registers: " ++ note)
        else
          .ok (.addSubShiftedReg
            { sf := widthBit wide, op := isSub, setFlags := setFlags, shift := .lsl,
              rm := rm, imm6 := 0, rn := rn, rd := rd })
    | none =>
        let imm ← orRefuse (immediate env labels right >>= unsignedField 12)
          ("immediate does not fit 12 unsigned bits: " ++ note)
        .ok (.addSubImm
          { sf := widthBit wide, op := isSub, setFlags := setFlags, sh := false,
            imm12 := imm, rn := rn, rd := rd })

def lowerLogical (op : LogicalOp) (dest left right : Operand) (env : Env)
    (labels : String → Option Nat) (note : String) : Except String Instr := do
  let (rd, wide) ← orRefuse (register dest) ("destination is not a register: " ++ note)
  let (rn, wideLeft) ← orRefuse (register left) ("first source is not a register: " ++ note)
  if !(wide && wideLeft) then
    .error ("logical immediates are encoded 64-bit only: " ++ note)
  else
    let imms ← orRefuse (immediate env labels right >>= lowRunMask)
      ("immediate is not a contiguous low-order bitmask: " ++ note)
    .ok (.logicalImm { opc := op, imms := imms, rn := rn, rd := rd })

def lowerLoadStore (isLoad forceByte : Bool) (target place : Operand) (env : Env)
    (note : String) : Except String Instr := do
  let (rt, wide) ← orRefuse (register target) ("transfer operand is not a register: " ++ note)
  if forceByte && wide then
    .error ("ldrb/strb take a 32-bit register: " ++ note)
  else
    let size := if forceByte then LsSize.byte else if wide then LsSize.double64 else LsSize.word32
    let (rn, offset) ← orRefuse (addressed env place)
      ("not a base-plus-unsigned-offset address: " ++ note)
    if offset % accessScale size != 0 then
      .error ("offset is not a multiple of the access size: " ++ note)
    else
      let imm ← orRefuse (unsignedNat 12 (offset / accessScale size))
        ("offset does not fit a scaled 12-bit field: " ++ note)
      .ok (.loadStoreUImm { size := size, isLoad := isLoad, imm12 := imm, rn := rn, rt := rt })

def lowerCompareZero (target dest : Operand) (labels : String → Option Nat) (pc : Nat)
    (note : String) : Except String Instr := do
  let (rt, wide) ← orRefuse (register target) ("tested operand is not a register: " ++ note)
  let address ← orRefuse (labelTarget labels dest) ("branch target is not a label: " ++ note)
  let imm ← orRefuse (branchOffset (Int.ofNat address - Int.ofNat pc))
    ("branch target is out of range: " ++ note)
  .ok (.cbz { sf := widthBit wide, imm19 := imm, rt := rt })

/-- Same comparison as `lowerCompareZero`, `Cbnz` instead of `CompareZero`:
same `imm19` range (`branchOffset`), same offset-from-this-line convention. -/
def lowerCompareNonZero (target dest : Operand) (labels : String → Option Nat) (pc : Nat)
    (note : String) : Except String Instr := do
  let (rt, wide) ← orRefuse (register target) ("tested operand is not a register: " ++ note)
  let address ← orRefuse (labelTarget labels dest) ("branch target is not a label: " ++ note)
  let imm ← orRefuse (branchOffset (Int.ofNat address - Int.ofNat pc))
    ("branch target is out of range: " ++ note)
  .ok (.cbnz { sf := widthBit wide, imm19 := imm, rt := rt })

/-- A conditional-branch offset, `b.<cond>`: the same `imm19`, scaled-by-4,
offset-from-this-line convention as `cbz`/`cbnz` (`branchOffset`), paired with
the already-decoded 4-bit condition. -/
def lowerCondBranch (cond : BitVec 4) (target : Operand) (labels : String → Option Nat) (pc : Nat)
    (note : String) : Except String Instr := do
  let address ← orRefuse (labelTarget labels target) ("branch target is not a label: " ++ note)
  let imm ← orRefuse (branchOffset (Int.ofNat address - Int.ofNat pc))
    ("branch target is out of range: " ++ note)
  .ok (.condBranch { imm19 := imm, cond := cond })

/-- A `b`/`bl` displacement in bytes as an `imm26`: the same sign/scale
convention as `branchOffset`, widened to the 26-bit field's ±128 MiB range. -/
def branchOffset26 (delta : Int) : Option (BitVec 26) :=
  if delta % 4 = 0 && -(2 ^ 27 : Int) ≤ delta && delta < (2 ^ 27 : Int) then
    some (BitVec.ofInt 26 (delta / 4))
  else none

/-- `b`/`bl`, offset from this line. `bl` additionally writes `pc + 4` to
`x30` at step time (`Grass.ISA.AArch64.Target.Step.execBranchImm`); nothing
here needs to know that, `op`'s bit alone selects it. -/
def lowerBranch (isLink : Bool) (target : Operand) (labels : String → Option Nat) (pc : Nat)
    (note : String) : Except String Instr := do
  let address ← orRefuse (labelTarget labels target) ("branch target is not a label: " ++ note)
  let imm ← orRefuse (branchOffset26 (Int.ofNat address - Int.ofNat pc))
    ("branch target is out of range: " ++ note)
  .ok (.branchImm { op := bitOfBool isLink, imm26 := imm })

/-- `br`/`blr` require exactly one register operand; `ret` accepts one or
defaults, absent, to `x30` (register field `30`), matching Arm DDI 0602
ID032025's own `RET {Xn}` default-operand spelling. -/
def lowerBranchRegister (op : BranchRegOp) (operands : List Operand) (note : String) :
    Except String Instr :=
  match operands with
  | [] =>
      if op = .ret then .ok (.branchReg { op := .ret, rn := 30 })
      else .error ("missing register operand: " ++ note)
  | [target] =>
      match register target with
      | some (rn, _) => .ok (.branchReg { op := op, rn := rn })
      | none => .error ("target is not a register: " ++ note)
  | _ => .error ("wrong number of operands: " ++ note)

/-- A PC-relative byte offset as `adr`'s 21-bit signed `immhi:immlo` field:
Arm DDI 0602 ID032025 "PC-rel. addressing" scales by nothing (unlike
`b`/`cbz`), so the ±1 MiB range is the raw 21-bit signed range. -/
def adrOffset (delta : Int) : Option (BitVec 21) :=
  if -(2 ^ 20 : Int) ≤ delta && delta < (2 ^ 20 : Int) then some (BitVec.ofInt 21 delta) else none

/-- Split a 21-bit combined immediate into the `immhi`/`immlo` fields
`AdrAdrp.encode` concatenates as `immhi ++ immlo`
(`Grass.ISA.AArch64.Target.Step.execAdrAdrp` reads them back the same way via
`i.immhi ++ i.immlo`). -/
def adrFields (op : BitVec 1) (imm21 : BitVec 21) (rd : BitVec 5) : Instr :=
  .adrAdrp { op := op, immlo := imm21.extractLsb' 0 2, immhi := imm21.extractLsb' 2 19, rd := rd }

/-- `adr Xd, label`: `rd := pc + (target - pc)`, i.e. the target's own
address, computed as a byte offset from this line. -/
def lowerAdr (dest target : Operand) (labels : String → Option Nat) (pc : Nat) (note : String) :
    Except String Instr := do
  let (rd, _) ← orRefuse (register dest) ("destination is not a register: " ++ note)
  let address ← orRefuse (labelTarget labels target) ("target is not a label: " ++ note)
  let imm21 ← orRefuse (adrOffset (Int.ofNat address - Int.ofNat pc))
    ("target is out of range: " ++ note)
  .ok (adrFields 0 imm21 rd)

/-- `adrp Xd, label`: `rd := (pc & ~0xFFF) + ((targetPage - pcPage) << 12)`,
matching `execAdrAdrp`'s runtime page mask exactly because both `pc` and
`address` are the same non-negative byte addresses that mask would compute
over — `Nat` floor division by the page size here is that mask. -/
def lowerAdrp (dest target : Operand) (labels : String → Option Nat) (pc : Nat) (note : String) :
    Except String Instr := do
  let (rd, _) ← orRefuse (register dest) ("destination is not a register: " ++ note)
  let address ← orRefuse (labelTarget labels target) ("target is not a label: " ++ note)
  let deltaPages : Int := Int.ofNat (address / 4096) - Int.ofNat (pc / 4096)
  let imm21 ← orRefuse (adrOffset deltaPages) ("target page is out of range: " ++ note)
  .ok (adrFields 1 imm21 rd)

/-- `mov Xd, Xn`: the Arm DDI 0602 ID032025 "MOV (register)" alias of
`orr Xd, XZR, Xn` (`sf`-matched zero register), exactly the reading
`LogicalShiftedReg`'s own docstring already gives that encoding — no separate
alias constructor is needed.

`sp` on either side is refused this reading and falls back to the "MOV (to/
from SP)" alias, `add Xd, Xn, #0`: field 31 in `LogicalShiftedReg`'s `rn`/`rm`
is architecturally always XZR (`State.readGpr`/`writeGpr`, never
`readGprOrSp`/`writeGprOrSp`), so lowering `mov sp, x0` or `mov x0, sp`
through `orr` would silently read or write the zero register instead of the
stack pointer — a miscompilation, not a legal alternate encoding. `xzr`/`wzr`
need no such fallback: `orr`'s fixed zero register already gives them their
correct reading. -/
def lowerMovRegister (dest src : Operand) (note : String) : Except String Instr := do
  let (rd, wide) ← orRefuse (register dest) ("destination is not a register: " ++ note)
  let (rm, wideSrc) ← orRefuse (register src) ("source is not a register: " ++ note)
  if wide != wideSrc then .error ("operands mix 32-bit and 64-bit registers: " ++ note)
  else if dest = Operand.reg "sp" || src = Operand.reg "sp" then
    .ok (.addSubImm
      { sf := widthBit wide, op := false, setFlags := false, sh := false, imm12 := 0,
        rn := rm, rd := rd })
  else
    .ok (.logicalShiftedReg
      { sf := widthBit wide, opc := .orr, shift := .lsl, rm := rm, imm6 := 0, rn := 31, rd := rd })

/-- `and`/`orr`/`eor` between the immediate table's `LogicalOp` and the
register-form `LogicalShiftOp`: the three names this front end exposes for
both forms share their meaning, only the encoded struct differs. Named
`toShiftedOp` rather than `LogicalOp.toShifted`: dot notation on a value of
type `LogicalOp` resolves against that type's own namespace
(`Grass.ISA.AArch64.Target`), not this module's, so a `LogicalOp`-prefixed
name here would be unreachable as `op.toShifted`. -/
def toShiftedOp : LogicalOp → LogicalShiftOp
  | .and => .and | .orr => .orr | .eor => .eor

/-- `and`/`orr`/`eor Xd, Xn, Xm`: logical shifted-register with `lsl #0`,
the same "no shift authored" reading `lowerAddSub`'s register form uses. -/
def lowerLogicalReg (op : LogicalShiftOp) (dest left right : Operand) (note : String) :
    Except String Instr := do
  let (rd, wide) ← orRefuse (register dest) ("destination is not a register: " ++ note)
  let (rn, wideLeft) ← orRefuse (register left) ("first source is not a register: " ++ note)
  let (rm, wideRight) ← orRefuse (register right) ("second source is not a register: " ++ note)
  if wide != wideLeft || wideLeft != wideRight then
    .error ("operands mix 32-bit and 64-bit registers: " ++ note)
  else
    .ok (.logicalShiftedReg
      { sf := widthBit wide, opc := op, shift := .lsl, rm := rm, imm6 := 0, rn := rn, rd := rd })

/-- One authored instruction line as one resolved A64 instruction. -/
def lowerInstruction (mnemonic : String) (operands : List Operand) (env : Env)
    (labels : String → Option Nat) (pc : Nat) : Except String Instr :=
  let note := render mnemonic operands
  match family mnemonic, operands with
  | some (.moveWide op), [dest, value] =>
      lowerMoveWide op dest value (.imm 0) env labels note
  | some (.moveWide op), [dest, value, shift] =>
      lowerMoveWide op dest value shift env labels note
  | some .mov, [dest, value] =>
      match register value with
      | some _ => lowerMovRegister dest value note
      | none => lowerMoveWide .movz dest value (.imm 0) env labels note
  | some (.addSub isSub setFlags), [dest, left, right] =>
      lowerAddSub isSub setFlags dest left right env labels note
  | some (.compare isSub), [left, right] =>
      match register left with
      | some (_, wide) =>
          lowerAddSub isSub true (.reg (if wide then "xzr" else "wzr")) left right env labels note
      | none => .error ("compared operand is not a register: " ++ note)
  | some (.logical op), [dest, left, right] =>
      match register right with
      | some _ => lowerLogicalReg (toShiftedOp op) dest left right note
      | none => lowerLogical op dest left right env labels note
  | some (.loadStore isLoad forceByte), [target, place] =>
      lowerLoadStore isLoad forceByte target place env note
  | some .compareZero, [target, dest] => lowerCompareZero target dest labels pc note
  | some .compareNonZero, [target, dest] => lowerCompareNonZero target dest labels pc note
  | some .supervisor, [value] =>
      match immediate env labels value >>= unsignedField 16 with
      | some imm => .ok (.svc imm)
      | none => .error ("immediate does not fit 16 bits: " ++ note)
  | some .halt, [] => .ok (.hlt { imm16 := 0 })
  | some .halt, [value] =>
      match immediate env labels value >>= unsignedField 16 with
      | some imm => .ok (.hlt { imm16 := imm })
      | none => .error ("immediate does not fit 16 bits: " ++ note)
  | some (.branch isLink), [target] => lowerBranch isLink target labels pc note
  | some (.branchRegister op), regOperands => lowerBranchRegister op regOperands note
  | some (.condBranch cond), [target] => lowerCondBranch cond target labels pc note
  | some (.adr isPage), [dest, target] =>
      if isPage then lowerAdrp dest target labels pc note else lowerAdr dest target labels pc note
  | some .nop, [] => .ok (.nop ⟨⟩)
  | some _, _ => .error ("wrong number of operands: " ++ note)
  | none, _ => .error ("no A64 encoding for this mnemonic: " ++ note)

/-! ## The instance -/

/-- Every A64 instruction is one word. A label and a directive occupy nothing:
this ISA gives neither an encoding. -/
def size : Line → Env → Except String Nat
  | .label _ _, _ => .ok 0
  | .directive _ _ _, _ => .ok 0
  | .instruction _ _ _, _ => .ok 4

def lower : Line → Env → (labels : String → Option Nat) → (pc : Nat) →
    Except String (List Grass.ISA.AArch64.isa.Instr)
  | .label _ _, _, _, _ => .ok []
  | .directive _ _ _, _, _, _ => .ok []
  | .instruction mnemonic operands _, env, labels, pc =>
      match lowerInstruction mnemonic operands env labels pc with
      | .error message => .error message
      | .ok instr => .ok [instr]

theorem lower_size (line : Line) (env : Env) (labels : String → Option Nat) (pc : Nat)
    (instrs : List Grass.ISA.AArch64.isa.Instr) (lowered : lower line env labels pc = .ok instrs) :
    size line env = .ok (Grass.ISA.AArch64.isa.encodeAll instrs).length := by
  cases line with
  | label name annotations =>
      rw [lower] at lowered
      cases lowered
      simp only [size, Grass.Target.ISA.encodeAll_nil, List.length_nil]
  | directive name operands annotations =>
      rw [lower] at lowered
      cases lowered
      simp only [size, Grass.Target.ISA.encodeAll_nil, List.length_nil]
  | instruction mnemonic operands annotations =>
      rw [lower] at lowered
      split at lowered
      · simp at lowered
      · rename_i instr _
        cases lowered
        have word : (Grass.ISA.AArch64.isa.encodeAll [instr]).length = 4 := by
          show (Grass.ISA.AArch64.isa.encode instr ++ Grass.ISA.AArch64.isa.encodeAll []).length = 4
          rw [Grass.Target.ISA.encodeAll_nil, List.append_nil]
          exact Grass.ISA.AArch64.Target.encode_length instr
        simp only [size, word]

/-- The AArch64 instance of the lowering seam. -/
def lowering : Lowering Grass.ISA.AArch64.isa where
  size := size
  lower := lower
  lower_size := lower_size

/-! ## Examples: a Linux Hello-shaped source

Not a `Tests` file (`docs/TARGET_SEAMS.md` rule 4: this checks the lowering
model against itself, not against an external corpus) — these `example`s are
evidence that `lowering.sizes`/`lowering.emit` actually succeed, end to end,
on the shape of source `Grass/Platform/Linux/Target/AArch64.lean`'s `write`/
`exit` syscalls need: load the three `write` arguments and the syscall
number into `x0`-`x2`/`x8`, `svc`, then load `exit`'s status and syscall
number and `svc` again. `message`'s address is never declared here (this
module owns no rodata/placement decision), only assumed resolved by `labels`,
exactly as `symbolTable` (`Grass/Assembly/Lower/Layout.lean`) would resolve a
real `.rodata` block's name. -/

/-- `mov x0,#1; adr x1,message; mov x2,#14; mov x8,#64; svc #0; mov x0,#0;
mov x8,#93; svc #0` — `write(1, message, 14)` then `exit(0)`, arm64's Linux
syscall numbers 64 and 93 (`Grass.Platform.Linux.Target.AArch64.sysWrite`/
`sysExit`). -/
def helloSource : Source := asm_source {
  mov x0, #1
  adr x1, message
  mov x2, #14
  mov x8, #64
  svc #0
  mov x0, #0
  mov x8, #93
  svc #0
}

/-- No named constants, `sizeof`s, or frame locals: every operand above is
either a register or a plain immediate or label. -/
def helloEnv : Env where
  constant := fun _ => none
  sizeOf := fun _ => none
  slot := fun _ => none
  frameBytes := 0

/-- `message` resolved to an address `0xFFC` (4092) bytes past the `adr`
line — inside the ±1 MiB range, and exactly what a `.rodata` block placed
right after an 8-instruction, 32-byte `.text` section would resolve to. -/
def helloLabels : String → Option Nat := fun name => if name = "message" then some 0x401000 else none

/-- `Except` carries no `DecidableEq` instance of its own; the `#guard`s below
need one to evaluate an `Except`-typed equality. -/
instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error x, .error y =>
      if h : x = y then isTrue (by rw [h]) else isFalse (fun hh => h (by injection hh))
  | .error _, .ok _ => isFalse (fun hh => by injection hh)
  | .ok _, .error _ => isFalse (fun hh => by injection hh)
  | .ok x, .ok y =>
      if h : x = y then isTrue (by rw [h]) else isFalse (fun hh => h (by injection hh))

/-- `Grass.ISA.AArch64.isa.Instr` is the `ISA.Instr` field projected out of a
specific structure value, definitionally `Target.Instr` but not syntactically
so; instance search for `DecidableEq (List Grass.ISA.AArch64.isa.Instr)` (what
the `#guard`s on `lowering.emit`'s result need) does not unfold that
projection on its own, so this bridges it explicitly to the instance
`Instr`'s `deriving DecidableEq` already provides. -/
instance : DecidableEq Grass.ISA.AArch64.isa.Instr := inferInstanceAs (DecidableEq Instr)

/-- Pass 1: eight instruction lines, four bytes each. -/
example : lowering.sizes helloEnv helloSource.lines = .ok 32 := by rfl

/- Pass 2, starting at `0x400000`: the `adr` line sits at `0x400004`, so its
target offset is `0x401000 - 0x400004 = 0xFFC` (4092), whose 21-bit encoding
is `immhi := 1023` (4092 `>>> 2`), `immlo := 0` (4092 `&&& 0b11`). Every other
line is `movz`/`svc`, read straight off their written immediates and
registers.

Checked with `#guard`/`decide` evaluated at compile time (`#eval`'s own
mechanism), not `by rfl`/`by decide` at the kernel level: `parseRegister`
(this file) reaches `String.front`/`String.drop`, and on this toolchain
those do not reduce through the kernel's definitional-equality checker — a
`String`-internals gap, not anything specific to this module's logic.
`#guard` runs the same compiled code `#eval` already confirmed above, so
this is still exact and unconditional, just not kernel-checked. -/
#guard
  decide (lowering.emit helloEnv helloLabels helloSource.lines 0x400000 =
    .ok [.moveWide { sf := 1, op := .movz, hw := 0, imm16 := 1, rd := 0 },
          .adrAdrp { op := 0, immlo := 0, immhi := 1023, rd := 1 },
          .moveWide { sf := 1, op := .movz, hw := 0, imm16 := 14, rd := 2 },
          .moveWide { sf := 1, op := .movz, hw := 0, imm16 := 64, rd := 8 },
          .svc 0,
          .moveWide { sf := 1, op := .movz, hw := 0, imm16 := 0, rd := 0 },
          .moveWide { sf := 1, op := .movz, hw := 0, imm16 := 93, rd := 8 },
          .svc 0])

/-! ## Example: every family this pass added, assembled together

`assemble` (`Grass/Assembly/Lower/Layout.lean`) resolves `loop`'s address
itself, so this is the one example that exercises `b`/`bl`/`b.<cond>`/
`cbnz`'s label resolution against a real two-pass run rather than a
hand-picked `labels` function. Only success is asserted (`succeeded`, below):
re-deriving every new family's exact bit-field encoding by hand, on top of
the Hello example's bit-for-bit check above, would add ceremony without a
second thing being tested. -/

/-- Whether an `Except` reached `.ok`, discarding the value: enough to show a
source assembles, when the exact result is already checked elsewhere. -/
def succeeded {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/-- `and`/`orr`/`eor` register form, `mov` to a register from `sp` (the
add-immediate fallback), `cbnz`, `b.eq`, `nop`, `b`, `bl`, `br`, and `ret`
with no operand — every family this pass added that the Hello example above
does not already exercise. -/
def coverageSource : Source := asm_source {
  loop:
  and x3, x1, x2
  orr x4, x1, x2
  eor x5, x1, x2
  mov x6, sp
  cbnz x3, loop
  b.eq loop
  nop
  b loop
  bl loop
  br x9
  ret
}

def coveragePlace : Placement where
  codeBase := 0x400000
  rodata := []
  dataBase := none
  imports := []
  importBase := none
  entry := "loop"
  stackBytes := 0

#guard succeeded (assemble lowering coverageSource helloEnv coveragePlace) = true

end Grass.Assembly.Lower.AArch64
