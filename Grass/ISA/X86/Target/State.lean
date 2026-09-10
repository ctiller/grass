import Grass.ISA.X86.Target.Encode

/-!
# The x86-64 machine state

The whole state `step` (`Grass/ISA/X86/Target.lean`) transitions: the
register file, `rip`, the four condition flags this profile models, and a
flat byte-addressed memory guarded by a region map. Nothing here names a
platform, a service domain, or a program — a region is an address range and
three permission bits, nothing more.
-/

namespace Grass.ISA.X86.Target

/-- One mapped region of the address space: a contiguous byte range and what
may be done with it. Disjoint regions are a well-formedness property of a
loaded program (`Grass.Target.Sectioned.Disjoint`), not enforced here. -/
structure Region where
  /-- The lowest address the region occupies. -/
  base : Nat
  /-- The region's size in bytes. -/
  size : Nat
  /-- Whether loaded code may read this region. -/
  readable : Bool
  /-- Whether loaded code may write this region. -/
  writable : Bool
  /-- Whether loaded code may fetch and execute from this region. -/
  executable : Bool
deriving Repr, DecidableEq, Inhabited

namespace Region

/-- The address one past the region's last byte. -/
def endAddr (r : Region) : Nat := r.base + r.size

/-- Whether an address lies inside the region. -/
def Contains (r : Region) (addr : Nat) : Prop := r.base ≤ addr ∧ addr < r.endAddr

instance (r : Region) (addr : Nat) : Decidable (r.Contains addr) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Region

/-- The whole machine state: registers, the instruction pointer, the four
condition flags this profile models (Intel SDM Vol. 1 §3.4.3: `CF`, `ZF`,
`SF`, `OF`), and a flat memory with a region map recording which addresses
are mapped and what may be done with them.

`mem` is total (`Nat → Option UInt8`) so an out-of-range address is simply
`none` rather than requiring a proof of boundedness; `regions` is the
authority on whether an address may be *read*, *written* or *fetched* at
all — `mem` may hold a byte at an address no region covers, and `step` must
never consult it there. -/
structure State where
  /-- The sixteen general-purpose registers. -/
  reg : Reg → UInt64
  /-- The instruction pointer: the address `step` fetches from next. -/
  rip : Nat
  /-- The carry flag. -/
  cf : Bool
  /-- The zero flag. -/
  zf : Bool
  /-- The sign flag. -/
  sf : Bool
  /-- The overflow flag. -/
  ofFlag : Bool
  /-- The byte at an address, if the address is backed by memory at all.
  Permission to access it is a separate question — see `readableAt` et al. -/
  mem : Nat → Option UInt8
  /-- The mapped regions of the address space. -/
  regions : List Region
deriving Inhabited

namespace State

/-- Replace one register, leaving the others unchanged. -/
def setReg (s : State) (r : Reg) (v : UInt64) : State :=
  { s with reg := fun r' => if r' = r then v else s.reg r' }

/-- Set the four condition flags together, as every arithmetic instruction
that touches flags does. -/
def setFlags (s : State) (cf zf sf ofFlag : Bool) : State :=
  { s with cf := cf, zf := zf, sf := sf, ofFlag := ofFlag }

/-- The region containing an address, if any. An address in two overlapping
regions (a malformed program; see `Grass.Target.Sectioned.Disjoint`) picks
the first, which is why overlap is refused upstream rather than resolved
here. -/
def regionAt (s : State) (addr : Nat) : Option Region :=
  s.regions.find? fun r => decide (r.Contains addr)

/-- Whether an address may be read. -/
def readableAt (s : State) (addr : Nat) : Bool :=
  match s.regionAt addr with | some r => r.readable | none => false

/-- Whether an address may be written. -/
def writableAt (s : State) (addr : Nat) : Bool :=
  match s.regionAt addr with | some r => r.writable | none => false

/-- Whether an address may be fetched from and executed. -/
def executableAt (s : State) (addr : Nat) : Bool :=
  match s.regionAt addr with | some r => r.executable | none => false

/-- The byte at `addr`, or `none` if the address is not backed by memory or
is not readable. -/
def readByte (s : State) (addr : Nat) : Option UInt8 :=
  if s.readableAt addr then s.mem addr else none

/-- `count` consecutive bytes from `addr`, or `none` if any of them is not
readable. -/
def readBytes (s : State) (addr count : Nat) : Option (List UInt8) :=
  (List.range count).mapM fun i => s.readByte (addr + i)

/-- Whether every byte of `[addr, addr+count)` is readable. -/
def readableRange (s : State) (addr count : Nat) : Bool :=
  (List.range count).all fun i => s.readableAt (addr + i)

/-- Whether every byte of `[addr, addr+count)` is writable. -/
def writableRange (s : State) (addr count : Nat) : Bool :=
  (List.range count).all fun i => s.writableAt (addr + i)

/-- Write one byte, unconditionally (permission is the caller's job). -/
def writeByte (s : State) (addr : Nat) (v : UInt8) : State :=
  { s with mem := fun a => if a = addr then some v else s.mem a }

/-- Write a run of bytes starting at `addr`, in order. -/
def writeBytes (s : State) (addr : Nat) : List UInt8 → State
  | [] => s
  | b :: rest => (s.writeByte addr b).writeBytes (addr + 1) rest

/-- Greedily read as many consecutive executable, mapped bytes as available
starting at `addr`, up to a bound. Stops at the first unreadable or
unmapped byte rather than failing outright, so a short instruction near the
end of a section still decodes. -/
def fetchWindow (s : State) (addr bound : Nat) : List UInt8 :=
  match bound with
  | 0 => []
  | n + 1 =>
      if s.executableAt addr then
        match s.mem addr with
        | some b => b :: s.fetchWindow (addr + 1) n
        | none => []
      else []

/-- The longest an x86-64 instruction this profile encodes can be: one REX
byte, one `0F` escape, one opcode, one ModR/M, one SIB, four displacement
bytes, eight immediate bytes. `fetchWindow` reads at most this many. -/
def maxInstrBytes : Nat := 17

/-- Read a 64-bit value at `addr`, little-endian, or `none` if any of its
eight bytes is not readable. -/
def readU64 (s : State) (addr : Nat) : Option UInt64 :=
  (s.readBytes addr 8).map fun bs =>
    bs.foldr (fun b acc => (acc <<< 8) ||| b.toUInt64) 0

/-- Write a 64-bit value at `addr`, little-endian. -/
def writeU64 (s : State) (addr : Nat) (v : UInt64) : State :=
  s.writeBytes addr
    [ (v).toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8,
      (v >>> 32).toUInt8, (v >>> 40).toUInt8, (v >>> 48).toUInt8, (v >>> 56).toUInt8 ]

end State

end Grass.ISA.X86.Target
