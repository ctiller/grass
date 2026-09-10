import Grass.Assembly.Lower.Layout
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

| written | operands | encoded family |
| --- | --- | --- |
| `movz`, `movn`, `movk` | reg, imm [, shift imm] | move-wide |
| `add`, `adds`, `sub`, `subs` | reg, reg, imm | add/sub immediate |
| `add`, `adds`, `sub`, `subs` | reg, reg, reg | add/sub shifted register, `lsl #0` |
| `cmp`, `cmn` | reg, imm or reg | the same two, destination field 31 |
| `and`, `orr`, `eor` | reg, reg, imm | logical immediate, 64-bit low-run masks |
| `ldr`, `str` | reg, memory | load/store unsigned offset, 8 or 4 bytes |
| `ldrb`, `strb` | reg, memory | load/store unsigned offset, 1 byte |
| `cbz` | reg, label | compare-and-branch, offset from this line |
| `svc` | imm | supervisor call |
| `hlt` | imm or nothing | halt |

Anything else — including `mov`, `b`, `bl`, `ret`, `adr` and every addressing
mode but base-plus-unsigned-offset — is refused with a message naming the line,
because encoding it does not exist yet.

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
  | addSub (isSub setFlags : Bool)
  | compare (isSub : Bool)
  | logical (op : LogicalOp)
  | loadStore (isLoad forceByte : Bool)
  | compareZero
  | supervisor
  | halt

/-- The mnemonic table. -/
def family (mnemonic : String) : Option Family :=
  if mnemonic = "movn" then some (.moveWide .movn)
  else if mnemonic = "movz" then some (.moveWide .movz)
  else if mnemonic = "movk" then some (.moveWide .movk)
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
  else if mnemonic = "svc" then some .supervisor
  else if mnemonic = "hlt" then some .halt
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

/-- One authored instruction line as one resolved A64 instruction. -/
def lowerInstruction (mnemonic : String) (operands : List Operand) (env : Env)
    (labels : String → Option Nat) (pc : Nat) : Except String Instr :=
  let note := render mnemonic operands
  match family mnemonic, operands with
  | some (.moveWide op), [dest, value] =>
      lowerMoveWide op dest value (.imm 0) env labels note
  | some (.moveWide op), [dest, value, shift] =>
      lowerMoveWide op dest value shift env labels note
  | some (.addSub isSub setFlags), [dest, left, right] =>
      lowerAddSub isSub setFlags dest left right env labels note
  | some (.compare isSub), [left, right] =>
      match register left with
      | some (_, wide) =>
          lowerAddSub isSub true (.reg (if wide then "xzr" else "wzr")) left right env labels note
      | none => .error ("compared operand is not a register: " ++ note)
  | some (.logical op), [dest, left, right] =>
      lowerLogical op dest left right env labels note
  | some (.loadStore isLoad forceByte), [target, place] =>
      lowerLoadStore isLoad forceByte target place env note
  | some .compareZero, [target, dest] => lowerCompareZero target dest labels pc note
  | some .supervisor, [value] =>
      match immediate env labels value >>= unsignedField 16 with
      | some imm => .ok (.svc imm)
      | none => .error ("immediate does not fit 16 bits: " ++ note)
  | some .halt, [] => .ok (.hlt { imm16 := 0 })
  | some .halt, [value] =>
      match immediate env labels value >>= unsignedField 16 with
      | some imm => .ok (.hlt { imm16 := imm })
      | none => .error ("immediate does not fit 16 bits: " ++ note)
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

end Grass.Assembly.Lower.AArch64
