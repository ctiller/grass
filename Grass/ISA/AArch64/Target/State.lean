import Grass.ISA.AArch64.Target.Native
import Grass.Target.Raw

/-!
# AArch64 machine state

The whole machine state (`State`, memory included), the mapped-region model
that turns an out-of-image or permission-violating access into a `Fault`
(never a silent wraparound), and `initial : Sectioned → InitialContext →
State`, the loader.

Registers follow `docs/TARGET_SEAMS.md`'s split: the register *file* is
`Reg → BitVec 64` (31 genuine GPRs, `Grass.ISA.AArch64.Reg := Fin 31`); SP and
XZR are not stored anywhere, they are what reading or writing operand index 31
means at a given operand position, decided by `readGpr`/`readGprOrSp` and
their write-side counterparts below — never by a third register-file slot.
-/

namespace Grass.ISA.AArch64.Target

/-- A mapped region of the address space: `size` bytes starting at `base`,
with the permissions a loaded section or the stack carries. -/
structure Region where
  base : Nat
  size : Nat
  readable : Bool
  writable : Bool
  executable : Bool
  deriving Repr

/-- Whether `address` falls inside `region`. -/
def Region.contains (region : Region) (address : Nat) : Bool :=
  decide (region.base ≤ address ∧ address < region.base + region.size)

/-- The whole AArch64 machine state: X0..X30, SP, PC, the NZCV condition
flags, and flat byte-addressed memory with the region map that gives it
permissions. `mem` answers `none` for an address no region has ever placed a
byte at; a region's own bytes are always `some`, so "mapped but never
written" is not a representable state — every mapped byte starts at some
value (the loader's `initial` gives every image byte a value and the stack a
fixed fill, per its docstring below). -/
structure State where
  x : Reg → BitVec 64
  sp : BitVec 64
  pc : BitVec 64
  nzcv : BitVec 4
  mem : Nat → Option UInt8
  regions : List Region
  /-- Device windows (`InitialContext.devices`), carried so `step` can route
  a load or store inside one to the platform as a native call. -/
  devices : List (Nat × Nat)

/-- Whether `address` lies inside a declared device window. -/
def State.deviceAt (s : State) (address : Nat) : Bool :=
  s.devices.any (fun d => decide (d.1 ≤ address ∧ address < d.1 + d.2))

/-- Read GPR `r`; operand encoding 31 is XZR, the zero register (reads as
`0`, per Arm DDI 0602 ID032025's zero-register operand convention — never a
stored register). -/
def State.readGpr (s : State) (r : BitVec 5) : BitVec 64 :=
  if h : r.toNat < 31 then s.x ⟨r.toNat, h⟩ else 0

/-- Read GPR `r`, treating encoding 31 as the current stack pointer instead
of XZR (the base-register convention `ldr`/`str`/`add`/`sub` immediate
forms use). -/
def State.readGprOrSp (s : State) (r : BitVec 5) : BitVec 64 :=
  if h : r.toNat < 31 then s.x ⟨r.toNat, h⟩ else s.sp

/-- Write GPR `r`; encoding 31 is XZR and the write is discarded, which is
also the correct machine effect of every `setFlags`-only encoding (`cmp`,
`cmn`, `tst`) once `rd = 0b11111`: no separate alias table is needed. -/
def State.writeGpr (s : State) (r : BitVec 5) (v : BitVec 64) : State :=
  if h : r.toNat < 31 then
    { s with x := fun j => if j = (⟨r.toNat, h⟩ : Reg) then v else s.x j }
  else s

/-- Write GPR `r`, treating encoding 31 as SP instead of XZR. -/
def State.writeGprOrSp (s : State) (r : BitVec 5) (v : BitVec 64) : State :=
  if h : r.toNat < 31 then
    { s with x := fun j => if j = (⟨r.toNat, h⟩ : Reg) then v else s.x j }
  else { s with sp := v }

def State.advancePc (s : State) : State := { s with pc := s.pc + 4 }

/-- The region containing `address`, if any. -/
def State.regionAt (s : State) (address : Nat) : Option Region :=
  s.regions.find? (fun r => r.contains address)

def State.readable (s : State) (address : Nat) : Bool :=
  match s.regionAt address with | some r => r.readable | none => false

def State.writable (s : State) (address : Nat) : Bool :=
  match s.regionAt address with | some r => r.writable | none => false

def State.executableAt (s : State) (address : Nat) : Bool :=
  match s.regionAt address with | some r => r.executable | none => false

/-- Read `n` little-endian bytes starting at `address`; `none` if any of them
is outside a readable region — an out-of-image or permission-violating read
is a fault at the call site, never a value this returns. -/
def State.readBytes (s : State) (address : Nat) (n : Nat) : Option (List UInt8) :=
  (List.range n).mapM (fun off => if s.readable (address + off) then s.mem (address + off) else none)

/-- Write little-endian `bytes` starting at `address`, if every one of those
addresses is inside a writable region; `none` otherwise (the caller faults). -/
def State.writeBytes (s : State) (address : Nat) (bytes : List UInt8) : Option State :=
  if (List.range bytes.length).all (fun off => s.writable (address + off)) then
    some { s with
      mem := fun a =>
        if address ≤ a ∧ a < address + bytes.length then bytes[a - address]? else s.mem a }
  else none

/-- Read a little-endian `BitVec 64` (byte count from `n`, `n ∈ {1, 4, 8}`
is all this ISA uses) from `n` bytes, least-significant byte first. -/
def bitsOfLE (bytes : List UInt8) : BitVec 64 :=
  bytes.foldr (fun b acc => (acc <<< 8) ||| (BitVec.ofNat 64 b.toNat)) 0

/-- The little-endian bytes of the low `n` bytes of `v`. -/
def leBytesOf (v : BitVec 64) (n : Nat) : List UInt8 :=
  (List.range n).map (fun i => UInt8.ofBitVec ((v >>> (i * 8)).extractLsb' 0 8))

/-- What the loader hands the machine at entry: the sections of an assembled
program placed at their virtual addresses (readable/writable/executable per
`Grass.Target.Section`, verbatim — this loader does not reinterpret a
section's own permission bits), a stack region of `context.staged`'s and the
platform's choosing, and `context`'s initial registers and SP, with `pc` set
to the program's entry address. Every image byte is defined (`some`); no
byte outside a loaded section or the stack is ever mapped. -/
def initial (program : Grass.Target.Sectioned) (context : InitialContext) : State :=
  let sectionRegions : List Region :=
    program.sections.map fun sec =>
      { base := sec.virtualAddress, size := sec.bytes.length, readable := sec.readable,
        writable := sec.writable, executable := sec.executable }
  let stackBase := context.sp.toNat - program.stackBytes
  let stackRegion : Region :=
    { base := stackBase, size := program.stackBytes, readable := true, writable := true,
      executable := false }
  let sectionByte : Nat → Option UInt8 := fun addr =>
    program.sections.findSome? fun sec =>
      if sec.virtualAddress ≤ addr ∧ addr < sec.virtualAddress + sec.bytes.length then
        sec.bytes[addr - sec.virtualAddress]?
      else none
  let stagedByte : Nat → Option UInt8 := fun addr =>
    context.staged.findSome? fun (base, bytes) =>
      if base ≤ addr ∧ addr < base + bytes.length then bytes[addr - base]? else none
  { x := context.registers
    sp := context.sp
    pc := BitVec.ofNat 64 program.entry
    nzcv := 0
    regions := sectionRegions ++ [stackRegion]
    devices := context.devices
    mem := fun addr =>
      match sectionByte addr with
      | some b => some b
      | none =>
        match stagedByte addr with
        | some b => some b
        | none => if stackRegion.contains addr then some 0 else none }

end Grass.ISA.AArch64.Target
