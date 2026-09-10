import Grass.ISA.AArch64.Target.State
import Grass.ISA.AArch64.Target.Encoding
import Grass.Target.ISA

/-!
# AArch64 execution semantics

`step : State → StepOutcome State NativeCall NativeReturn Fault`: fetch 4
bytes at `pc` (`Fault.executeNonExecutable`/`Fault.undecodable` if that
fails), execute the eight families `Target.Encoding` decodes. Flag semantics
(`nzcv` after `adds`/`subs`) follow Arm DDI 0602 ID032025's `AddWithCarry`
pseudocode (§ "Add/subtract (immediate)" and "... (shifted register)"),
computed here over `Nat` rather than reproduced bit-by-bit, which is the same
content: unsigned overflow is `a.toNat + b.toNat ≥ 2 ^ width` and signed
overflow is same-sign operands producing a different-signed result.

## Coverage

`svc` steps to `.external`, carrying `CallTarget.supervisor`; `hlt` steps to
`.halted`. Every other family is `.internal`: `movz`/`movn`/`movk`, add/sub
immediate and shifted-register with `adds`/`subs`/`cmp`/`cmn` folded in via
`setFlags` and the destination register, logical immediate, `ldr`/`str`/
`ldrb`/`strb`, `cbz`/`cbnz`, `b`/`bl`/`b.cond`, `br`/`blr`/`ret` (ordinary
indirect control transfer — no import slot or return-address check), `adr`/
`adrp`, logical shifted-register (`and`/`orr`/`eor`/`ands`, with `mov`/`tst`
falling out of the zero-register/discard-on-write convention rather than a
separate alias case), and `nop`. `brk` is not covered (`Target.Encoding`
does not decode it), matching that module's documented gap.
-/

namespace Grass.ISA.AArch64.Target

open Grass.Target (StepOutcome)

/-- `sf = 1` selects the 64-bit form; `sf = 0` computes over the low 32 bits
and zero-extends the result back to 64, per every 32-bit-form GPR write. -/
def truncateForSf (sf : BitVec 1) (v : BitVec 64) : BitVec 64 :=
  if sf = 1 then v else (v.setWidth 32).setWidth 64

def mkNZCV (n z c v : Bool) : BitVec 4 :=
  bitOfBool n ++ bitOfBool z ++ bitOfBool c ++ bitOfBool v

/-- `AddWithCarry(a, b, 0)`'s result and flags, at `width` bits (32 or 64),
carried in 64-bit registers with the high bits already truncated away by the
caller. -/
def addFlags (a b : BitVec 64) (width : Nat) : BitVec 4 :=
  let sum := a + b
  let modulus : Nat := 2 ^ width
  let n := sum.msb
  let z := sum.setWidth width == 0
  let c := decide (a.toNat % modulus + b.toNat % modulus ≥ modulus)
  let v := decide ((a.setWidth width).msb = (b.setWidth width).msb ∧
    (sum.setWidth width).msb ≠ (a.setWidth width).msb)
  mkNZCV n z c v

/-- `AddWithCarry(a, ~b, 1)`'s flags for `a - b`. -/
def subFlags (a b : BitVec 64) (width : Nat) : BitVec 4 :=
  let modulus : Nat := 2 ^ width
  let a' := a.toNat % modulus
  let b' := b.toNat % modulus
  let diff := a - b
  let n := (diff.setWidth width).msb
  let z := diff.setWidth width == 0
  let c := decide (a' ≥ b')
  let v := decide ((a.setWidth width).msb ≠ (b.setWidth width).msb ∧
    (diff.setWidth width).msb ≠ (a.setWidth width).msb)
  mkNZCV n z c v

/-! ## Move-wide -/

def execMoveWide (s : State) (i : MoveWide) : State :=
  let shift := i.hw.toNat * 16
  let base : BitVec 64 := (i.imm16.setWidth 64) <<< shift
  let value := match i.op with
    | .movz => base
    | .movn => ~~~base
    | .movk => (s.readGpr i.rd &&& ~~~((0xFFFF#64) <<< shift)) ||| base
  s.writeGpr i.rd (truncateForSf i.sf value) |>.advancePc

/-! ## Add/subtract -/

def execAddSubImm (s : State) (i : AddSubImm) : State :=
  let a := s.readGprOrSp i.rn
  let b : BitVec 64 := (if i.sh then i.imm12.setWidth 64 <<< 12 else i.imm12.setWidth 64)
  let width := if i.sf = 1 then 64 else 32
  let result := truncateForSf i.sf (if i.op then a - b else a + b)
  let s' := s.writeGprOrSp i.rd result
  let s'' := if i.setFlags then { s' with nzcv := if i.op then subFlags a b width else addFlags a b width } else s'
  s''.advancePc

def execAddSubShiftedReg (s : State) (i : AddSubShiftedReg) : State :=
  let a := s.readGpr i.rn
  let raw := s.readGpr i.rm
  let amount := i.imm6.toNat
  let shifted : BitVec 64 :=
    match i.shift with
    | .lsl => raw <<< amount
    | .lsr => raw >>> amount
    | .asr => (raw.sshiftRight amount)
  let width := if i.sf = 1 then 64 else 32
  let b := truncateForSf i.sf shifted
  let result := truncateForSf i.sf (if i.op then a - b else a + b)
  let s' := s.writeGpr i.rd result
  let s'' := if i.setFlags then { s' with nzcv := if i.op then subFlags a b width else addFlags a b width } else s'
  s''.advancePc

/-! ## Logical immediate -/

/-- The 64-bit contiguous low-order bitmask `LogicalImm.imms` denotes; see
`LogicalImm`'s docstring for the represented subset. -/
def logicalImmMask (imms : BitVec 6) : BitVec 64 :=
  ((BitVec.allOnes 64) >>> (63 - imms.toNat))

def execLogicalImm (s : State) (i : LogicalImm) : State :=
  let a := s.readGpr i.rn
  let mask := logicalImmMask i.imms
  let result := match i.opc with
    | .and => a &&& mask
    | .orr => a ||| mask
    | .eor => a ^^^ mask
  s.writeGpr i.rd result |>.advancePc

/-! ## Load/store unsigned offset -/

def lsScale : LsSize → Nat
  | .byte => 1 | .word32 => 4 | .double64 => 8

def lsBytes : LsSize → Nat
  | .byte => 1 | .word32 => 4 | .double64 => 8

def execLoadStoreUImm (s : State) (i : LoadStoreUImm) :
    StepOutcome State NativeCall NativeReturn Fault :=
  let addr := s.readGprOrSp i.rn + (i.imm12.setWidth 64) * (BitVec.ofNat 64 (lsScale i.size))
  let size := lsBytes i.size
  if s.deviceAt addr.toNat then
    -- A device window: the access is a native call the platform gives
    -- meaning to, never a memory read or write. A load lands the platform's
    -- `x0` in `rt`; a store's answer is ignored beyond advancing `pc`.
    if i.isLoad then
      .external
        { target := .mmioLoad addr.toNat size, reg := s.x, sp := s.sp,
          read := fun a n => s.readBytes a n }
        (fun ret => (s.writeGpr i.rt ret.x0).advancePc)
    else
      .external
        { target := .mmioStore addr.toNat (leBytesOf (s.readGpr i.rt) size), reg := s.x,
          sp := s.sp, read := fun a n => s.readBytes a n }
        (fun _ => s.advancePc)
  else if i.isLoad then
    match s.readBytes addr.toNat size with
    | some bytes => .internal ((s.writeGpr i.rt (bitsOfLE bytes)).advancePc)
    | none => .fault (.readOutsideImage addr.toNat size)
  else
    match s.writeBytes addr.toNat (leBytesOf (s.readGpr i.rt) size) with
    | some s' => .internal s'.advancePc
    | none => .fault (.writeOutsideImage addr.toNat size)

/-! ## `cbz` -/

def execCbz (s : State) (i : CompareZero) : State :=
  let value := s.readGpr i.rt
  let isZero := if i.sf = 0 then value.setWidth 32 == 0 else value == 0
  if isZero then
    let offset := (i.imm19 ++ (0b00#2)).signExtend 64
    { s with pc := s.pc + offset }
  else s.advancePc

/-! ## Unconditional branch immediate (`b`, `bl`) -/

/-- `imm26 ++ 00`, sign-extended: Arm DDI 0602 ID032025 scales the immediate
by 4 and treats it as relative to the branch instruction's own PC (not the
fallthrough PC), same convention as `Control.CompareZero.offset`. -/
def branchImmOffset (i : BranchImm) : BitVec 64 := (i.imm26 ++ (0b00#2)).signExtend 64

/-- `op = 0` is `b`; `op = 1` is `bl`, which additionally writes the return
address `pc + 4` to `x30` before branching. -/
def execBranchImm (s : State) (i : BranchImm) : State :=
  let s' := if i.op = 1 then s.writeGpr 30 (s.pc + 4) else s
  { s' with pc := s.pc + branchImmOffset i }

/-! ## Unconditional branch register (`br`, `blr`, `ret`) -/

/-- `br`/`ret` set `pc` to `Rn`; `blr` additionally writes `pc + 4` to `x30`
first. All three are ordinary indirect control transfer at this layer — no
import slot or return-address check is modeled (`docs/TARGET_SEAMS.md`: an
ISA never knows what a call means). -/
def execBranchReg (s : State) (i : BranchReg) : State :=
  let s' := match i.op with
    | .blr => s.writeGpr 30 (s.pc + 4)
    | .br | .ret => s
  { s' with pc := s.readGpr i.rn }

/-! ## Conditional branch (`b.cond`) -/

/-- The 16-way `cond` table, Arm DDI 0602 ID032025 "Condition codes":
`nzcv` is `N ++ Z ++ C ++ V` (`mkNZCV`'s own field order), so bit 3 is `N`,
bit 2 is `Z`, bit 1 is `C`, bit 0 is `V`. `1110`/`1111` ("al"/"nv") both
always hold, matching the architecture's documented redundancy. -/
def evalCond (cond : BitVec 4) (nzcv : BitVec 4) : Bool :=
  let n := boolOfBit (nzcv.extractLsb' 3 1)
  let z := boolOfBit (nzcv.extractLsb' 2 1)
  let c := boolOfBit (nzcv.extractLsb' 1 1)
  let v := boolOfBit (nzcv.extractLsb' 0 1)
  match cond.toNat with
  | 0 => z | 1 => !z | 2 => c | 3 => !c | 4 => n | 5 => !n | 6 => v | 7 => !v
  | 8 => c && !z | 9 => !(c && !z) | 10 => n == v | 11 => !(n == v)
  | 12 => !z && (n == v) | 13 => !(!z && (n == v)) | _ => true

def execCondBranch (s : State) (i : CondBranch) : State :=
  if evalCond i.cond s.nzcv then
    { s with pc := s.pc + (i.imm19 ++ (0b00#2)).signExtend 64 }
  else s.advancePc

/-! ## `cbnz` -/

/-- Same comparison as `execCbz`, branch taken on the opposite outcome. -/
def execCbnz (s : State) (i : Cbnz) : State :=
  let value := s.readGpr i.rt
  let isZero := if i.sf = 0 then value.setWidth 32 == 0 else value == 0
  if isZero then s.advancePc
  else { s with pc := s.pc + (i.imm19 ++ (0b00#2)).signExtend 64 }

/-! ## PC-relative address (`adr`, `adrp`) -/

/-- `adr`: `rd := pc + sign_extend(immhi:immlo)`. `adrp`: `rd := (pc & ~0xFFF)
+ (sign_extend(immhi:immlo) << 12)` — the page address, per Arm DDI 0602
ID032025 "ADRP". -/
def execAdrAdrp (s : State) (i : AdrAdrp) : State :=
  let imm21 : BitVec 21 := i.immhi ++ i.immlo
  let s' :=
    if i.op = 1 then
      let pageBase := s.pc &&& ~~~(0xFFF#64)
      s.writeGpr i.rd (pageBase + ((imm21.signExtend 64) <<< 12))
    else
      s.writeGpr i.rd (s.pc + imm21.signExtend 64)
  s'.advancePc

/-! ## Logical shifted-register (`and`/`orr`/`eor`/`ands`) -/

/-- `ands` (only) writes flags: `N`/`Z` from the result, `C`/`V` both forced
to `0` — Arm DDI 0602 ID032025's "Logical (shifted register)" pseudocode
does not route the shifter's carry into `C` here, unlike AArch32's `ANDS`. -/
def execLogicalShiftedReg (s : State) (i : LogicalShiftedReg) : State :=
  let rm := s.readGpr i.rm
  let shifted : BitVec 64 :=
    match i.shift with
    | .lsl => rm <<< i.imm6.toNat
    | .lsr => rm >>> i.imm6.toNat
    | .asr => rm.sshiftRight i.imm6.toNat
  let rn := s.readGpr i.rn
  let width := if i.sf = 1 then 64 else 32
  let raw := match i.opc with
    | .and => rn &&& shifted
    | .orr => rn ||| shifted
    | .eor => rn ^^^ shifted
    | .ands => rn &&& shifted
  let result := truncateForSf i.sf raw
  let s' := s.writeGpr i.rd result
  let s'' :=
    if i.opc = .ands then
      { s' with
        nzcv := mkNZCV ((result.setWidth width).msb) ((result.setWidth width) == 0) false false }
    else s'
  s''.advancePc

/-! ## `nop` -/

def execNop (s : State) (_ : Nop) : State := s.advancePc

/-! ## `svc` and `hlt` -/

def svcCall (s : State) (imm : BitVec 16) : NativeCall :=
  { target := .supervisor (UInt16.ofBitVec imm), reg := s.x, sp := s.sp,
    read := fun addr size => s.readBytes addr size }

/-- Apply a platform's answer: `x0` (and `x1`, if given) land in the return
registers, `maps` are installed next (zero-filled, per `State.mapRegion` --
a MAP_ANONYMOUS mapping reads as zero, `man 2 mmap`), then `writes` are
applied to memory (a write outside every writable region is silently dropped
rather than propagated as a fault — `NativeReturn` has no failure mode, so a
platform must only ever offer writes its own `Responds` relation already
knows are in bounds), and finally `unmaps` removes any regions this answer
releases. Installing `maps` before `writes` means a write into a region this
same return just mapped lands on an already-installed, already-zeroed region
within one return, rather than having its bytes erased by a later zero-fill.
Applying `unmaps` after `writes` means a same-return write into a region
being released is meaningless (nothing after this return can ever observe
it) and cannot be undone by a later step of the same return once the region
is gone. `clobbers`ed registers are left as this step found them (this
machine is deterministic; a genuinely unspecified post-call value is the
platform's choice to make, not this step's to fabricate), and `pc` advances
past the call site. -/
def applySvcReturn (s : State) : NativeReturn → State := fun ret =>
  let s1 := s.writeGpr 0 ret.x0
  let s2 := match ret.x1 with | some v => s1.writeGpr 1 v | none => s1
  let mapped := s2.mapRegions
    (ret.maps.map fun m =>
      { base := m.base, size := m.size, readable := m.readable, writable := m.writable,
        executable := false })
  let s3 := ret.writes.foldl (fun st (addr, bytes) => (st.writeBytes addr bytes).getD st) mapped
  let s4 := s3.unmapRegions ret.unmaps
  s4.advancePc

/-! ## Fetch and dispatch -/

def fetch (s : State) : Fault ⊕ List UInt8 :=
  if s.executableAt s.pc.toNat then
    match s.readBytes s.pc.toNat 4 with
    | some bytes => .inr bytes
    | none => .inl (.executeNonExecutable s.pc.toNat)
  else .inl (.executeNonExecutable s.pc.toNat)

def stepInstr (s : State) : Instr → StepOutcome State NativeCall NativeReturn Fault
  | .moveWide i => .internal (execMoveWide s i)
  | .addSubImm i => .internal (execAddSubImm s i)
  | .logicalImm i => .internal (execLogicalImm s i)
  | .loadStoreUImm i => execLoadStoreUImm s i
  | .addSubShiftedReg i => .internal (execAddSubShiftedReg s i)
  | .cbz i => .internal (execCbz s i)
  | .svc imm => .external (svcCall s imm) (applySvcReturn s)
  | .hlt _ => .halted
  | .branchImm i => .internal (execBranchImm s i)
  | .branchReg i => .internal (execBranchReg s i)
  | .condBranch i => .internal (execCondBranch s i)
  | .cbnz i => .internal (execCbnz s i)
  | .adrAdrp i => .internal (execAdrAdrp s i)
  | .logicalShiftedReg i => .internal (execLogicalShiftedReg s i)
  | .nop i => .internal (execNop s i)

def step (s : State) : StepOutcome State NativeCall NativeReturn Fault :=
  match fetch s with
  | .inl f => .fault f
  | .inr bytes =>
    match decode bytes with
    | none => .fault .undecodable
    | some (instr, _) => stepInstr s instr

end Grass.ISA.AArch64.Target
