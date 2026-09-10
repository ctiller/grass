import Grass.ISA.X86.Target.State
import Grass.Target.ISA
import Grass.Target.Raw

/-!
# The x86-64 instance of the target seam

`Grass.ISA.X86.isa : Grass.Target.ISA` instantiates every field
`Grass/Target/ISA.lean` asks for: `Instr`/`encode`/`decode` with
`decode_encode`/`encode_pos` (`Grass/ISA/X86/Target/Encode.lean`), `Raw :=
Grass.Target.Sectioned` (`Grass/Target/Raw.lean`), `State`
(`Grass/ISA/X86/Target/State.lean`), `initial`, and `step`, defined here.

`step` has no theorem obligation of its own — the seam's only proof burden is
the encode/decode round trip — but it is still the fact every later adequacy
proof rests on, so its fault behaviour is deliberate: a memory access outside
a mapped, correctly-permissioned region is a `fault`, not a saturating or
wrapping "best effort" read, because a `fault` is what makes the machine
tier's reachability obligation say something.
-/

namespace Grass.ISA.X86.Target

open Grass.Target (Sectioned Section StepOutcome)

/-! ## `initial` -/

/-- The byte at `addr`, read out of whichever loaded section covers it. -/
private def sectionByte (program : Sectioned) (addr : Nat) : Option UInt8 :=
  program.sections.findSome? fun sec =>
    if sec.virtualAddress ≤ addr then sec.bytes[addr - sec.virtualAddress]? else none

/-- One region per loaded section, carrying the section's own permissions. -/
private def sectionRegions (program : Sectioned) : List Region :=
  program.sections.map fun sec =>
    { base := sec.virtualAddress, size := sec.bytes.length, readable := sec.readable,
      writable := sec.writable, executable := sec.executable }

/-- Map a program's sections into memory, place the stack and argument block
the platform chose, and start execution at the entry address. -/
def initial (program : Sectioned) (ctx : InitialContext) : State :=
  let stackBase := ctx.stackTop - ctx.stackBytes
  let stackRegion : Region :=
    { base := stackBase, size := ctx.stackBytes, readable := true, writable := true,
      executable := false }
  let argRegion : Region :=
    { base := ctx.argumentBlockAddress, size := ctx.argumentBlock.length, readable := true,
      writable := false, executable := false }
  let unwritten : State :=
    { reg := ctx.reg, rip := program.entry, cf := false, zf := false, sf := false,
      ofFlag := false, mem := sectionByte program, regions := sectionRegions program ++
        [stackRegion, argRegion] }
  (unwritten.setReg .rsp (UInt64.ofNat ctx.stackTop)).writeBytes
    ctx.argumentBlockAddress ctx.argumentBlock

/-! ## `step` -/

/-- A register's value truncated to an operand width: `w32` zero-extends by
masking to 32 bits, `w64` is the register as stored. Matches
`Grass.ISA.X86.writeBack`'s rule for the widths this profile's instructions
use. -/
def regRead (s : State) (sz : Sz) (r : Reg) : UInt64 :=
  match sz with
  | .w64 => s.reg r
  | .w32 => s.reg r &&& 0xFFFFFFFF

/-- Write a value at an operand width: `w32` clears the high 32 bits (the
zero-extension rule), `w64` replaces the register outright. -/
def regWrite (s : State) (sz : Sz) (r : Reg) (v : UInt64) : State :=
  match sz with
  | .w64 => s.setReg r v
  | .w32 => s.setReg r (v &&& 0xFFFFFFFF)

/-- The all-ones mask of an operand width. -/
def maskFor : Sz → UInt64
  | .w32 => 0xFFFFFFFF
  | .w64 => 0xFFFFFFFFFFFFFFFF

/-- The sign-bit mask of an operand width. -/
def signBitFor : Sz → UInt64
  | .w32 => 0x80000000
  | .w64 => 0x8000000000000000

/-- A `[base+disp32]`/`[rip+disp32]` effective address: the base plus the
displacement, sign-extended. Not bounds-checked here — `readableAt` et al.
are what turn an out-of-range result into a fault. -/
def effAddr (base : Nat) (disp : BitVec 32) : Nat :=
  ((Int.ofNat base) + disp.toInt).toNat

/-- Little-endian bytes as a `UInt64`, low byte first. -/
def leToUInt64 (bs : List UInt8) : UInt64 :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.toUInt64) 0

/-- `sz`-wide little-endian bytes of a value: 4 bytes for `w32`, 8 for
`w64`. -/
def toLE (sz : Sz) (v : UInt64) : List UInt8 :=
  match sz with
  | .w32 => [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]
  | .w64 =>
      [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8,
       (v >>> 32).toUInt8, (v >>> 40).toUInt8, (v >>> 48).toUInt8, (v >>> 56).toUInt8]

/-- How many bytes an operand width occupies. -/
def byteCount : Sz → Nat
  | .w32 => 4
  | .w64 => 8

/-- Read an `sz`-wide value from memory, or `none` if any of its bytes is
unreadable. -/
def readMem (s : State) (sz : Sz) (addr : Nat) : Option UInt64 :=
  (s.readBytes addr (byteCount sz)).map leToUInt64

/-- Write an `sz`-wide value to memory, unconditionally — the caller checks
`writableRange` first. -/
def writeMem (s : State) (sz : Sz) (addr : Nat) (v : UInt64) : State :=
  s.writeBytes addr (toLE sz v)

/-!
### Arithmetic flags

Intel SDM Vol. 1 §3.4.3 and Vol. 2A's per-instruction "Operation" sections.
`CF`/`ZF`/`SF`/`OF` are the four this profile models (`docs` above); `AF`/`PF`
are not, so the corresponding writes are simply absent — no field carries
them, rather than a field that is written wrong.
-/

/-- `ADD`/`SUB`/`CMP` flags for `a + b` at width `sz`, `sub` selecting which
operation (`SUB`/`CMP` compute `a + (-b)` and carry/overflow are stated
against that, per the SDM's own `SBB`-style definition). `cf` is unsigned
overflow of the addition; `of` is signed overflow: the two operands share a
sign and the result's sign differs from theirs. -/
def addSubFlags (sz : Sz) (sub : Bool) (a b : UInt64) : Bool × Bool × Bool × Bool :=
  let mask := maskFor sz
  let a' := a &&& mask
  let bRaw := b &&& mask
  let b' := if sub then (mask ^^^ bRaw) + (1 : UInt64) &&& mask else bRaw
  let r := (a' + b') &&& mask
  let cf := if sub then bRaw.toNat > a'.toNat else a'.toNat + bRaw.toNat > mask.toNat
  let zf := r == 0
  let signBit := signBitFor sz
  let sf := (r &&& signBit) != 0
  let aSign := (a' &&& signBit) != 0
  let bSign := ((if sub then bRaw else b') &&& signBit) != 0
  let rSign := sf
  let ofFlag := if sub then aSign != bSign && rSign != aSign else aSign == bSign && rSign != aSign
  (cf, zf, sf, ofFlag)

/-- `AND`/`OR`/`XOR`/`TEST` flags: `CF` and `OF` are always cleared (SDM
Vol. 2A, each instruction's "Flags Affected"), `ZF`/`SF` come from the
result. -/
def logicFlags (sz : Sz) (r : UInt64) : Bool × Bool × Bool × Bool :=
  let masked := r &&& maskFor sz
  (false, masked == 0, (masked &&& signBitFor sz) != 0, false)

/-- `dst := dst op src`, or the comparison-only forms `cmp`/`test`, folded
into one function since they differ only in whether the result is written
back. -/
def aluApply (op : AluOp) (sz : Sz) (a b : UInt64) : UInt64 × (Bool × Bool × Bool × Bool) :=
  match op with
  | .add => let r := (a + b) &&& maskFor sz; (r, addSubFlags sz false a b)
  | .sub => let r := (a - b) &&& maskFor sz; (r, addSubFlags sz true a b)
  | .cmp => let r := (a - b) &&& maskFor sz; (r, addSubFlags sz true a b)
  | .and_ => let r := a &&& b &&& maskFor sz; (r, logicFlags sz r)
  | .or_ => let r := (a ||| b) &&& maskFor sz; (r, logicFlags sz r)
  | .xor_ => let r := (a ^^^ b) &&& maskFor sz; (r, logicFlags sz r)

/-- Whether a condition code holds against the current flags (Intel SDM
Vol. 1 Table 3-1). Parity (`P`/`NP`) is not modeled — this profile has no
`PF` — so `jp`/`jnp`/`setp`/`cmovp` are absent from `Cond` entirely rather
than evaluated wrong. -/
def condHolds (s : State) : Cond → Bool
  | .o => s.ofFlag
  | .no => !s.ofFlag
  | .b => s.cf
  | .ae => !s.cf
  | .e => s.zf
  | .ne => !s.zf
  | .be => s.cf || s.zf
  | .a => !s.cf && !s.zf
  | .s => s.sf
  | .ns => !s.sf
  | .p => false
  | .np => true
  | .l => s.sf != s.ofFlag
  | .ge => s.sf == s.ofFlag
  | .le => (s.sf != s.ofFlag) || s.zf
  | .g => (s.sf == s.ofFlag) && !s.zf

/-- Sign-extend the low `bits` of `v` to 64 bits (used by `movsx`). -/
def signExtendFrom (bits : Nat) (v : UInt64) : UInt64 :=
  let signBit : UInt64 := 1 <<< (UInt64.ofNat (bits - 1))
  let mask : UInt64 := (signBit <<< 1) - 1
  let low := v &&& mask
  if low &&& signBit != 0 then low ||| (~~~mask) else low

/-- Pop a 64-bit value: read at `rsp`, then increment `rsp` by 8. -/
def popValue (s : State) : Option (UInt64 × State) :=
  (readMem s .w64 (s.reg .rsp).toNat).map fun v =>
    (v, s.setReg .rsp (s.reg .rsp + 8))

/-- One instruction's effect, given the decoded instruction and its encoded
length. Memory faults, `ud2`, and control transfer to the platform
(`call`/`syscall`) are the only ways this is not `.internal`. -/
def execInstr (s : State) (instr : Instr) (len : Nat) :
    StepOutcome State NativeCall NativeReturn Fault :=
  let next : State := { s with rip := s.rip + len }
  match instr with
  | .movRR sz dst src => .internal (regWrite next sz dst (regRead next sz src))
  | .movRI32 dst imm => .internal (regWrite next .w32 dst (UInt64.ofNat imm.toNat))
  | .movRI64 dst imm => .internal (regWrite next .w64 dst (UInt64.ofNat imm.toNat))
  | .movzxRR dstSz dst src srcIs16 =>
      let bits := if srcIs16 then 16 else 8
      let mask : UInt64 := (1 <<< (UInt64.ofNat bits)) - 1
      .internal (regWrite next dstSz dst (s.reg src &&& mask))
  | .movsxRR dstSz dst src srcIs16 =>
      let bits := if srcIs16 then 16 else 8
      .internal (regWrite next dstSz dst (signExtendFrom bits (s.reg src)))
  | .aluRR op sz dst src =>
      let (r, (cf, zf, sf, ofFlag)) := aluApply op sz (regRead s sz dst) (regRead s sz src)
      .internal ((regWrite next sz dst r).setFlags cf zf sf ofFlag)
  | .aluRI op sz dst imm =>
      let (r, (cf, zf, sf, ofFlag)) := aluApply op sz (regRead s sz dst) (UInt64.ofNat imm.toNat)
      .internal ((regWrite next sz dst r).setFlags cf zf sf ofFlag)
  | .testRR sz a b =>
      let (_, (cf, zf, sf, ofFlag)) := aluApply .and_ sz (regRead s sz a) (regRead s sz b)
      .internal (next.setFlags cf zf sf ofFlag)
  | .testRI sz a imm =>
      let (_, (cf, zf, sf, ofFlag)) := aluApply .and_ sz (regRead s sz a) (UInt64.ofNat imm.toNat)
      .internal (next.setFlags cf zf sf ofFlag)
  | .shiftImm op sz dst imm =>
      let count := imm.toNat % 64
      let v := regRead s sz dst
      let r :=
        match op with
        | .shl => (v <<< (UInt64.ofNat count)) &&& maskFor sz
        | .shr => (v &&& maskFor sz) >>> (UInt64.ofNat count)
        | .sar =>
            let signBit := signBitFor sz
            if v &&& signBit != 0 then
              ((v &&& maskFor sz) >>> (UInt64.ofNat count)) |||
                ((~~~((maskFor sz) >>> (UInt64.ofNat count))) &&& maskFor sz)
            else (v &&& maskFor sz) >>> (UInt64.ofNat count)
      .internal (regWrite next sz dst r)
  | .imul2 sz dst src =>
      .internal (regWrite next sz dst ((regRead s sz dst * regRead s sz src) &&& maskFor sz))
  | .inc sz dst => .internal (regWrite next sz dst ((regRead s sz dst + 1) &&& maskFor sz))
  | .dec sz dst => .internal (regWrite next sz dst ((regRead s sz dst - 1) &&& maskFor sz))
  | .push r =>
      let newRsp := next.reg .rsp - 8
      if s.writableRange newRsp.toNat 8 then
        .internal ((writeMem next .w64 newRsp.toNat (s.reg r)).setReg .rsp newRsp)
      else .fault (.writeOutsideImage newRsp.toNat)
  | .pop r =>
      match popValue next with
      | some (v, s') => .internal (s'.setReg r v)
      | none => .fault (.readOutsideImage (next.reg .rsp).toNat)
  | .callRel32 rel =>
      let target := effAddr next.rip rel
      let retAddr := next.reg .rsp - 8
      if s.writableRange retAddr.toNat 8 then
        .internal { (writeMem next .w64 retAddr.toNat next.rip.toUInt64).setReg .rsp retAddr with
          rip := target }
      else .fault (.writeOutsideImage retAddr.toNat)
  | .ret =>
      match popValue s with
      | some (retAddr, s') => .internal { s' with rip := retAddr.toNat }
      | none => .fault (.readOutsideImage (s.reg .rsp).toNat)
  | .jmpRel32 rel => .internal { next with rip := effAddr next.rip rel }
  | .jmpRel8 rel => .internal { next with rip := effAddr next.rip (BitVec.signExtend 32 rel) }
  | .jccRel32 cc rel =>
      .internal (if condHolds s cc then { next with rip := effAddr next.rip rel } else next)
  | .jccRel8 cc rel =>
      .internal (if condHolds s cc then
          { next with rip := effAddr next.rip (BitVec.signExtend 32 rel) }
        else next)
  | .syscall =>
      .external
        { target := .syscall
          reg := s.reg
          rsp := s.reg .rsp
          returnAddress := UInt64.ofNat next.rip
          read := fun addr count => s.readBytes addr count }
        (fun ret =>
          let withRax := next.setReg .rax ret.rax
          let withRdx := match ret.rdx with | some v => withRax.setReg .rdx v | none => withRax
          let clobbered := ret.clobbers.foldl (fun st r => st.setReg r 0) withRdx
          ret.writes.foldl (fun st (aw : Nat × List UInt8) => st.writeBytes aw.1 aw.2) clobbered)
  | .ud2 => .fault .explicitUndefined
  | .hlt => .halted
  | .nop => .internal next
  | .cdq =>
      let signBit : UInt64 := 0x80000000
      let edx := if (s.reg .rax &&& signBit) != 0 then (0xFFFFFFFF : UInt64) else 0
      .internal (regWrite next .w32 .rdx edx)
  | .cqo =>
      let signBit : UInt64 := 0x8000000000000000
      let rdx := if (s.reg .rax &&& signBit) != 0 then (0xFFFFFFFFFFFFFFFF : UInt64) else 0
      .internal (regWrite next .w64 .rdx rdx)
  | .div sz src =>
      let divisor := regRead s sz src
      if divisor == 0 then .fault .divideByZero
      else .internal (regWrite next sz .rax ((regRead s sz .rax) / divisor))
  | .idiv sz src =>
      let divisor := regRead s sz src
      if divisor == 0 then .fault .divideByZero
      else .internal (regWrite next sz .rax ((regRead s sz .rax) / divisor))
  | .mul sz src =>
      .internal (regWrite next sz .rax ((regRead s sz .rax * regRead s sz src) &&& maskFor sz))
  | .setcc cc dst =>
      let v : UInt64 := if condHolds s cc then 1 else 0
      let old := s.reg dst
      .internal (next.setReg dst ((old &&& (~~~(0xFF : UInt64))) ||| v))
  | .cmovcc sz cc dst src =>
      .internal (if condHolds s cc then regWrite next sz dst (regRead s sz src) else next)
  | .xchgRR sz a b =>
      let va := regRead s sz a
      let vb := regRead s sz b
      .internal (regWrite (regWrite next sz a vb) sz b va)

/-- Fetch, decode and execute one instruction. `rip` not executable and an
undecodable window are the only decode-time faults; every other fault comes
from `execInstr`'s own memory checks. -/
def step (s : State) : StepOutcome State NativeCall NativeReturn Fault :=
  if !s.executableAt s.rip then .fault (.executeNonExecutable s.rip)
  else
    match decode (s.fetchWindow s.rip State.maxInstrBytes) with
    | some (instr, len) => execInstr s instr len
    | none => .fault .undecodable

end Grass.ISA.X86.Target

namespace Grass.ISA.X86

open Grass.ISA.X86.Target

/-- The x86-64 instance of the target seam: `Instr`, `encode`/`decode` with
their round-trip laws, the native-call surface, the whole machine `State`,
`initial`, and `step`. -/
def isa : Grass.Target.ISA where
  Instr := Instr
  encode := encode
  decode := decode
  decode_encode := decode_encode
  encode_pos := encode_pos
  Raw := Grass.Target.Sectioned
  InitialContext := InitialContext
  State := State
  initial := initial
  NativeCall := NativeCall
  NativeReturn := NativeReturn
  Fault := Fault
  step := step

end Grass.ISA.X86
