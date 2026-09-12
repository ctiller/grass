import Grass.ISA.X86.Target.Encode
import Grass.ISA.X86.Target.Core.Operands

/-!
# The x86-64 machine state

The whole state `step` (`Grass/ISA/X86/Target.lean`) transitions: the
register file, `rip`, the four condition flags this profile models, and a
flat byte-addressed memory guarded by a region map. Nothing here names a
platform, a service domain, or a program — a region is an address range and
three permission bits, nothing more.
-/

namespace Grass.ISA.X86.Target

export Core (SegReg)

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

/-- An x86-64 system descriptor table register (`GDTR` or `IDTR`, Intel SDM Vol. 3A §2.4). -/
structure DescriptorTable where
  /-- 16-bit table limit (table size in bytes minus 1). -/
  limit : UInt16 := 0
  /-- 64-bit linear base address. -/
  base : UInt64 := 0
deriving Repr, DecidableEq, Inhabited

/-- An x86-64 segment register visible selector and hidden descriptor cache
(Intel SDM Vol. 3A §3.4.3). -/
structure SegmentDescriptor where
  /-- 16-bit segment selector. -/
  selector : UInt16 := 0
  /-- 64-bit segment base address (active for FS and GS in 64-bit mode). -/
  base : UInt64 := 0
  /-- 32-bit segment limit. -/
  limit : UInt32 := 0xFFFFFFFF
  /-- Segment access attributes (type, S, DPL, P, L, D/B, G). -/
  attr : UInt16 := 0
deriving Repr, DecidableEq, Inhabited

/-- Extended 64-bit `RFLAGS` status, control, and system flags beyond the four primary
arithmetic flags `CF`, `ZF`, `SF`, `OF` (Intel SDM Vol. 1 §3.4.3). -/
structure RFlags where
  /-- Bit 2: Parity Flag (`PF`). -/
  pf : Bool := false
  /-- Bit 4: Auxiliary Carry Flag (`AF`). -/
  af : Bool := false
  /-- Bit 8: Trap Flag (`TF`). -/
  tf : Bool := false
  /-- Bit 9: Interrupt Enable Flag (`IF`). -/
  ifFlag : Bool := true
  /-- Bit 10: Direction Flag (`DF`). -/
  df : Bool := false
  /-- Bits 13:12: I/O Privilege Level (`IOPL`). -/
  iopl : BitVec 2 := 0
  /-- Bit 14: Nested Task Flag (`NT`). -/
  nt : Bool := false
  /-- Bit 16: Resume Flag (`RF`). -/
  rf : Bool := false
  /-- Bit 17: Virtual-8086 Mode Flag (`VM`). -/
  vm : Bool := false
  /-- Bit 18: Alignment Check / SMAP Access Control Flag (`AC`). -/
  ac : Bool := false
  /-- Bit 19: Virtual Interrupt Flag (`VIF`). -/
  vif : Bool := false
  /-- Bit 20: Virtual Interrupt Pending Flag (`VIP`). -/
  vip : Bool := false
  /-- Bit 21: CPUID Identification Flag (`ID`). -/
  id : Bool := true
deriving Repr, DecidableEq, Inhabited

/-- x87 FPU architectural state (Intel SDM Vol. 1 §8.1). -/
structure X87State where
  /-- Eight 80-bit physical floating-point data registers. -/
  st : Fin 8 → BitVec 80 := fun _ => 0
  /-- Top-of-stack pointer (`TOP`, bits 13:11 of FPU status word). -/
  top : Fin 8 := ⟨0, by omega⟩
  /-- 16-bit x87 FPU Control Word (reset default `0x037F`). -/
  fpuControl : BitVec 16 := 0x037F#16
  /-- 16-bit x87 FPU Status Word (reset default `0x0000`). -/
  fpuStatus : BitVec 16 := 0x0000#16
  /-- 16-bit x87 FPU Tag Word (reset default `0xFFFF`, all registers empty). -/
  fpuTag : BitVec 16 := 0xFFFF#16
deriving Inhabited

namespace X87State

/-- Physical register index corresponding to stack-relative `ST(i)`. -/
def physIndex (x : X87State) (i : Fin 8) : Fin 8 :=
  ⟨(x.top.val + i.val) % 8, Nat.mod_lt _ (by decide)⟩

/-- Read stack-relative register `ST(i)`. -/
def getSt (x : X87State) (i : Fin 8) : BitVec 80 :=
  x.st (x.physIndex i)

/-- Write stack-relative register `ST(i)`. -/
def setSt (x : X87State) (i : Fin 8) (v : BitVec 80) : X87State :=
  let p := x.physIndex i
  { x with st := fun r => if r = p then v else x.st r }

/-- Push an 80-bit value onto the x87 stack (`TOP := (TOP - 1) mod 8`, `ST(0) := v`). -/
def push (x : X87State) (v : BitVec 80) : X87State :=
  let newTop : Fin 8 := ⟨(x.top.val + 7) % 8, Nat.mod_lt _ (by decide)⟩
  { x with
    top := newTop
    st := fun r => if r = newTop then v else x.st r }

/-- Pop an 80-bit value from the x87 stack (`v := ST(0)`, `TOP := (TOP + 1) mod 8`). -/
def pop (x : X87State) : BitVec 80 × X87State :=
  let v := x.st x.top
  let newTop : Fin 8 := ⟨(x.top.val + 1) % 8, Nat.mod_lt _ (by decide)⟩
  (v, { x with top := newTop })

end X87State

/-- Ring-0 privileged and system architectural state (Intel SDM Vol. 3A §2.5). -/
structure SystemState where
  /-- Control registers `CR0`–`CR15`. -/
  cr : Fin 16 → UInt64 := fun _ => 0
  /-- Debug registers `DR0`–`DR7`. -/
  dr : Fin 8 → UInt64 := fun _ => 0
  /-- Extended Feature Enable Register (`IA32_EFER`, MSR `0xC0000080`). -/
  efer : UInt64 := 0
  /-- Model-Specific Registers (`MSR` 32-bit index → 64-bit value). -/
  msrs : UInt32 → UInt64 := fun _ => 0
  /-- Global Descriptor Table Register (`GDTR`). -/
  gdtr : DescriptorTable := {}
  /-- Interrupt Descriptor Table Register (`IDTR`). -/
  idtr : DescriptorTable := {}
  /-- Local Descriptor Table Register selector (`LDTR`). -/
  ldtr : UInt16 := 0
  /-- Task Register selector (`TR`). -/
  tr : UInt16 := 0
  /-- Segment registers (`ES`, `CS`, `SS`, `DS`, `FS`, `GS`). -/
  segs : SegReg → SegmentDescriptor := fun _ => {}
  /-- Current Privilege Level (`CPL`, 0..3; 3 = user mode, 0 = Ring 0 kernel mode). -/
  cpl : Fin 4 := ⟨3, by omega⟩
deriving Inhabited

/-- The whole x86-64 architectural state: general-purpose registers, instruction
pointer, condition flags (`CF`, `ZF`, `SF`, `OF` plus extended `RFLAGS`),
32 512-bit vector registers (`zmm0`–`zmm31`), 8 opmask registers (`k0`–`k7`),
`MXCSR`, x87 FPU state, Ring-0 system/privileged state, and flat byte-addressed
memory with a region map.

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
  cf : Bool := false
  /-- The zero flag. -/
  zf : Bool := false
  /-- The sign flag. -/
  sf : Bool := false
  /-- The overflow flag. -/
  ofFlag : Bool := false
  /-- Extended RFLAGS status, control, and system flags (`PF`, `AF`, `TF`, `IF`, `DF`, `IOPL`, `NT`, `RF`, `VM`, `AC`, `VIF`, `VIP`, `ID`). -/
  rflags : RFlags := {}
  /-- Thirty-two 512-bit vector registers (`zmm0`–`zmm31`). -/
  zmm : Fin 32 → BitVec 512 := fun _ => 0
  /-- Eight 64-bit opmask registers (`k0`–`k7`). -/
  opmask : Fin 8 → BitVec 64 := fun _ => 0
  /-- SIMD Floating-Point Control and Status Register (`MXCSR`, reset default `0x1F80`). -/
  mxcsr : BitVec 32 := 0x1F80#32
  /-- x87 FPU architectural state (`ST0`–`ST7`, `TOP`, control/status/tag words). -/
  x87 : X87State := {}
  /-- Ring-0 privileged and system state (`CR0`–`CR15`, `DR0`–`DR7`, `EFER`, MSRs, descriptor tables, segment descriptors, `CPL`). -/
  system : SystemState := {}
  /-- The byte at an address, if the address is backed by memory at all.
  Permission to access it is a separate question — see `readableAt` et al. -/
  mem : Nat → Option UInt8
  /-- The mapped regions of the address space. -/
  regions : List Region
  /-- Loaded target addresses eligible for an external indirect-call handoff.
  Actual memory reads and return-slot writes still check current permissions. -/
  externalTargets : List UInt64 := []
  /-- A native return can fail while popping its post-effect return slot.
  Retain the reached state and emit this exact fault before another fetch.
  This is transition bookkeeping, not an architectural register. -/
  pendingFault : Option Fault := none
deriving Inhabited

namespace State

/-- Replace one register, leaving the others unchanged. -/
def setReg (s : State) (r : Reg) (v : UInt64) : State :=
  { s with reg := fun r' => if r' = r then v else s.reg r' }

/-- Compute the parity of the lowest 8 bits of `v` (`true` if the number of set
bits in `v[7:0]` is even, Intel SDM Vol. 1 §3.4.3.1). -/
def parity8 (v : UInt64) : Bool :=
  let b0 := (v >>> 0) &&& 1
  let b1 := (v >>> 1) &&& 1
  let b2 := (v >>> 2) &&& 1
  let b3 := (v >>> 3) &&& 1
  let b4 := (v >>> 4) &&& 1
  let b5 := (v >>> 5) &&& 1
  let b6 := (v >>> 6) &&& 1
  let b7 := (v >>> 7) &&& 1
  ((b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4 ^^^ b5 ^^^ b6 ^^^ b7) == 0)

/-- Set the four primary condition flags together, as every arithmetic instruction
that touches flags does. -/
def setFlags (s : State) (cf zf sf ofFlag : Bool) : State :=
  { s with cf := cf, zf := zf, sf := sf, ofFlag := ofFlag }

/-- Set the primary and extended arithmetic flags (`CF`, `PF`, `AF`, `ZF`, `SF`, `OF`). -/
def setArithFlags (s : State) (cf pf af zf sf ofFlag : Bool) : State :=
  { s with
    cf := cf
    zf := zf
    sf := sf
    ofFlag := ofFlag
    rflags := { s.rflags with pf := pf, af := af } }

/-- Serialize the complete 64-bit architectural `RFLAGS` register (Intel SDM Vol. 1 §3.4.3).
Bit 1 is architecturally reserved and hardwired to 1. -/
def toRFlagsU64 (s : State) : UInt64 :=
  (if s.cf then (1 : UInt64) <<< 0 else 0) |||
  ((1 : UInt64) <<< 1) |||
  (if s.rflags.pf then (1 : UInt64) <<< 2 else 0) |||
  (if s.rflags.af then (1 : UInt64) <<< 4 else 0) |||
  (if s.zf then (1 : UInt64) <<< 6 else 0) |||
  (if s.sf then (1 : UInt64) <<< 7 else 0) |||
  (if s.rflags.tf then (1 : UInt64) <<< 8 else 0) |||
  (if s.rflags.ifFlag then (1 : UInt64) <<< 9 else 0) |||
  (if s.rflags.df then (1 : UInt64) <<< 10 else 0) |||
  (if s.ofFlag then (1 : UInt64) <<< 11 else 0) |||
  ((UInt64.ofNat s.rflags.iopl.toNat) <<< 12) |||
  (if s.rflags.nt then (1 : UInt64) <<< 14 else 0) |||
  (if s.rflags.rf then (1 : UInt64) <<< 16 else 0) |||
  (if s.rflags.vm then (1 : UInt64) <<< 17 else 0) |||
  (if s.rflags.ac then (1 : UInt64) <<< 18 else 0) |||
  (if s.rflags.vif then (1 : UInt64) <<< 19 else 0) |||
  (if s.rflags.vip then (1 : UInt64) <<< 20 else 0) |||
  (if s.rflags.id then (1 : UInt64) <<< 21 else 0)

/-- Load a 64-bit value into the architectural `RFLAGS` register. -/
def setRFlagsU64 (s : State) (v : UInt64) : State :=
  { s with
    cf := ((v >>> 0) &&& 1) != 0
    zf := ((v >>> 6) &&& 1) != 0
    sf := ((v >>> 7) &&& 1) != 0
    ofFlag := ((v >>> 11) &&& 1) != 0
    rflags := {
      pf := ((v >>> 2) &&& 1) != 0
      af := ((v >>> 4) &&& 1) != 0
      tf := ((v >>> 8) &&& 1) != 0
      ifFlag := ((v >>> 9) &&& 1) != 0
      df := ((v >>> 10) &&& 1) != 0
      iopl := BitVec.ofNat 2 ((v >>> 12) &&& 3).toNat
      nt := ((v >>> 14) &&& 1) != 0
      rf := ((v >>> 16) &&& 1) != 0
      vm := ((v >>> 17) &&& 1) != 0
      ac := ((v >>> 18) &&& 1) != 0
      vif := ((v >>> 19) &&& 1) != 0
      vip := ((v >>> 20) &&& 1) != 0
      id := ((v >>> 21) &&& 1) != 0 } }

/-! ### Vector register accessors (`XMM`/`YMM`/`ZMM`) -/

/-- Read the 128-bit `XMM` view (bits `127:0`) of vector register `r`. -/
def getXmm (s : State) (r : Fin 32) : BitVec 128 :=
  (s.zmm r).truncate 128

/-- Read the 256-bit `YMM` view (bits `255:0`) of vector register `r`. -/
def getYmm (s : State) (r : Fin 32) : BitVec 256 :=
  (s.zmm r).truncate 256

/-- Read the full 512-bit `ZMM` vector register `r`. -/
def getZmm (s : State) (r : Fin 32) : BitVec 512 :=
  s.zmm r

/-- Write the 128-bit `XMM` view of vector register `r`.
When `preserveUpper = true` (Legacy SSE semantics, Intel SDM Vol. 1 §15.1.2),
bits `511:128` of `ZMM[r]` are preserved unmodified.
When `preserveUpper = false` (VEX/EVEX 128-bit semantics), bits `511:128` are zeroed. -/
def setXmm (s : State) (r : Fin 32) (v : BitVec 128) (preserveUpper : Bool := false) : State :=
  let newZmm : BitVec 512 :=
    if preserveUpper then
      BitVec.append ((s.zmm r).extractLsb' 128 384) v
    else
      v.zeroExtend 512
  { s with zmm := fun r' => if r' = r then newZmm else s.zmm r' }

/-- Write `XMM[r]` with legacy SSE semantics (bits `511:128` preserved). -/
def setXmmSse (s : State) (r : Fin 32) (v : BitVec 128) : State :=
  s.setXmm r v true

/-- Write `XMM[r]` with VEX/EVEX semantics (bits `511:128` zeroed). -/
def setXmmVex (s : State) (r : Fin 32) (v : BitVec 128) : State :=
  s.setXmm r v false

/-- Write the 256-bit `YMM` view of vector register `r`.
When `preserveUpper = false` (VEX/EVEX 256-bit semantics, Intel SDM Vol. 1 §15.1.2),
bits `511:256` of `ZMM[r]` are zeroed.
When `preserveUpper = true`, bits `511:256` of `ZMM[r]` are preserved. -/
def setYmm (s : State) (r : Fin 32) (v : BitVec 256) (preserveUpper : Bool := false) : State :=
  let newZmm : BitVec 512 :=
    if preserveUpper then
      BitVec.append ((s.zmm r).extractLsb' 256 256) v
    else
      v.zeroExtend 512
  { s with zmm := fun r' => if r' = r then newZmm else s.zmm r' }

/-- Write the full 512-bit `ZMM` vector register `r`. -/
def setZmm (s : State) (r : Fin 32) (v : BitVec 512) : State :=
  { s with zmm := fun r' => if r' = r then v else s.zmm r' }

/-- Zero bits `511:128` of vector registers `zmm0`–`zmm15` (`VZEROUPPER` semantics). -/
def vzeroupper (s : State) : State :=
  let lowMask : BitVec 512 := (BitVec.allOnes 128).zeroExtend 512
  { s with zmm := fun r => if r.val < 16 then (s.zmm r) &&& lowMask else s.zmm r }

/-- Zero all vector registers `zmm0`–`zmm31` (`VZEROALL` semantics). -/
def vzeroall (s : State) : State :=
  { s with zmm := fun _ => 0 }

/-! ### Opmask register accessors (`k0`–`k7`) -/

/-- Read 64-bit opmask register `k`. -/
def getMask (s : State) (k : Fin 8) : BitVec 64 :=
  s.opmask k

/-- Write 64-bit opmask register `k`. -/
def setMask (s : State) (k : Fin 8) (v : BitVec 64) : State :=
  { s with opmask := fun k' => if k' = k then v else s.opmask k' }

/-- Evaluate AVX-512 predication mask for `lane` under opmask register `k`.
Opmask register `k = 0` (`k0`) architecturally represents unmasked execution
where all lanes are active (Intel SDM Vol. 1 §15.6.1). -/
def isLaneActive (s : State) (k : Fin 8) (lane : Nat) : Bool :=
  if k.val = 0 then true
  else (s.opmask k).getLsbD lane

/-! ### System & Segment register accessors -/

/-- Read control register `CR[i]`. -/
def getCr (s : State) (i : Fin 16) : UInt64 :=
  s.system.cr i

/-- Write control register `CR[i]`. -/
def setCr (s : State) (i : Fin 16) (v : UInt64) : State :=
  { s with system := { s.system with cr := fun i' => if i' = i then v else s.system.cr i' } }

/-- Read debug register `DR[i]`. -/
def getDr (s : State) (i : Fin 8) : UInt64 :=
  s.system.dr i

/-- Write debug register `DR[i]`. -/
def setDr (s : State) (i : Fin 8) (v : UInt64) : State :=
  { s with system := { s.system with dr := fun i' => if i' = i then v else s.system.dr i' } }

/-- Read Model-Specific Register `MSR[idx]`. -/
def getMsr (s : State) (idx : UInt32) : UInt64 :=
  s.system.msrs idx

/-- Write Model-Specific Register `MSR[idx]`. -/
def setMsr (s : State) (idx : UInt32) (v : UInt64) : State :=
  { s with system := { s.system with msrs := fun idx' => if idx' = idx then v else s.system.msrs idx' } }

/-- Read segment descriptor `segs[seg]`. -/
def getSeg (s : State) (seg : SegReg) : SegmentDescriptor :=
  s.system.segs seg

/-- Write segment descriptor `segs[seg]`. -/
def setSeg (s : State) (seg : SegReg) (desc : SegmentDescriptor) : State :=
  { s with system := { s.system with segs := fun seg' => if seg' = seg then desc else s.system.segs seg' } }

/-- Read the `FS` segment base address (`FS.base`). -/
def getFsBase (s : State) : UInt64 :=
  (s.system.segs .fs).base

/-- Write the `FS` segment base address (`FS.base`). -/
def setFsBase (s : State) (base : UInt64) : State :=
  let old := s.system.segs .fs
  s.setSeg .fs { old with base := base }

/-- Read the `GS` segment base address (`GS.base`). -/
def getGsBase (s : State) : UInt64 :=
  (s.system.segs .gs).base

/-- Write the `GS` segment base address (`GS.base`). -/
def setGsBase (s : State) (base : UInt64) : State :=
  let old := s.system.segs .gs
  s.setSeg .gs { old with base := base }

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

/-- Install a freshly mapped region: append it to `regions` and zero-fill
its bytes in `mem`, overwriting whatever `mem` already held there. A
MAP_ANONYMOUS mapping reads as zero (`man 2 mmap`: "the contents ... are
initialized to zero"), so a freshly mapped page must not silently inherit
stale bytes `mem` happened to carry at an address no region has ever
covered before. -/
def mapRegion (s : State) (r : Region) : State :=
  { s with
    regions := s.regions ++ [r]
    mem := fun a => if r.Contains a then some 0 else s.mem a }

/-- Install every region of `rs`, in order, via `mapRegion`. -/
def mapRegions (s : State) (rs : List Region) : State :=
  rs.foldl (fun st r => st.mapRegion r) s

/-- Remove every region whose base address is `base` (a successful `munmap`/
`HeapFree` releasing the handle a prior `mapRegion` installed at that
address). `mem` is left untouched: once `regions` no longer covers those
addresses, `readableAt`/`writableAt`/`executableAt` all report `false` there
regardless of what `mem` still holds, so a post-unmap access faults exactly
as an address that was never mapped would -- there is no need to also
scrub `mem`. -/
def unmapRegion (s : State) (base : Nat) : State :=
  { s with regions := s.regions.filter fun r => r.base != base }

/-- Remove every region named in `bases`, in order, via `unmapRegion`. -/
def unmapRegions (s : State) (bases : List Nat) : State :=
  bases.foldl (fun st b => st.unmapRegion b) s

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

/-- Read a 16-bit value at `addr`, little-endian, or `none` if any of its
two bytes is not readable. -/
def readU16 (s : State) (addr : Nat) : Option UInt16 :=
  (s.readBytes addr 2).map fun bs =>
    bs.foldr (fun b acc => (acc <<< 8) ||| b.toUInt16) 0

/-- Write a 16-bit value at `addr`, little-endian. -/
def writeU16 (s : State) (addr : Nat) (v : UInt16) : State :=
  s.writeBytes addr [ v.toUInt8, (v >>> 8).toUInt8 ]

/-- Read a 32-bit value at `addr`, little-endian, or `none` if any of its
four bytes is not readable. -/
def readU32 (s : State) (addr : Nat) : Option UInt32 :=
  (s.readBytes addr 4).map fun bs =>
    bs.foldr (fun b acc => (acc <<< 8) ||| b.toUInt32) 0

/-- Write a 32-bit value at `addr`, little-endian. -/
def writeU32 (s : State) (addr : Nat) (v : UInt32) : State :=
  s.writeBytes addr
    [ v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8 ]

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

/-- Assemble a list of little-endian bytes into a `BitVec w`. -/
def bytesToBitVecLE (w : Nat) (bs : List UInt8) : BitVec w :=
  BitVec.ofNat w (bs.foldr (fun b acc => (acc * 256) + b.toNat) 0)

/-- Split a `BitVec w` into `count` little-endian bytes. -/
def bitVecToBytesLE (w : Nat) (v : BitVec w) (count : Nat) : List UInt8 :=
  (List.range count).map fun i => UInt8.ofNat ((v.toNat >>> (i * 8)) % 256)

/-- Read a 128-bit vector value at `addr`, little-endian. -/
def readVec128 (s : State) (addr : Nat) : Option (BitVec 128) :=
  (s.readBytes addr 16).map (bytesToBitVecLE 128)

/-- Write a 128-bit vector value at `addr`, little-endian. -/
def writeVec128 (s : State) (addr : Nat) (v : BitVec 128) : State :=
  s.writeBytes addr (bitVecToBytesLE 128 v 16)

/-- Read a 256-bit vector value at `addr`, little-endian. -/
def readVec256 (s : State) (addr : Nat) : Option (BitVec 256) :=
  (s.readBytes addr 32).map (bytesToBitVecLE 256)

/-- Write a 256-bit vector value at `addr`, little-endian. -/
def writeVec256 (s : State) (addr : Nat) (v : BitVec 256) : State :=
  s.writeBytes addr (bitVecToBytesLE 256 v 32)

/-- Read a 512-bit vector value at `addr`, little-endian. -/
def readVec512 (s : State) (addr : Nat) : Option (BitVec 512) :=
  (s.readBytes addr 64).map (bytesToBitVecLE 512)

/-- Write a 512-bit vector value at `addr`, little-endian. -/
def writeVec512 (s : State) (addr : Nat) (v : BitVec 512) : State :=
  s.writeBytes addr (bitVecToBytesLE 512 v 64)

/-! ### Formal algebraic laws for `State` accessors -/

@[simp] theorem getReg_setReg_self (s : State) (r : Reg) (v : UInt64) :
    (s.setReg r v).reg r = v := by
  simp [setReg]

@[simp] theorem getReg_setReg_ne (s : State) (r r' : Reg) (v : UInt64) (h : r' ≠ r) :
    (s.setReg r v).reg r' = s.reg r' := by
  simp [setReg, h]

@[simp] theorem getZmm_setZmm_self (s : State) (r : Fin 32) (v : BitVec 512) :
    (s.setZmm r v).getZmm r = v := by
  simp [getZmm, setZmm]

@[simp] theorem getZmm_setZmm_ne (s : State) (r r' : Fin 32) (v : BitVec 512) (h : r' ≠ r) :
    (s.setZmm r v).getZmm r' = s.getZmm r' := by
  simp [getZmm, setZmm, h]

@[simp] theorem getXmm_setXmmVex_self (s : State) (r : Fin 32) (v : BitVec 128) :
    (s.setXmmVex r v).getXmm r = v := by
  simp [getXmm, setXmmVex, setXmm]

@[simp] theorem getXmm_setXmmSse_self (s : State) (r : Fin 32) (v : BitVec 128) :
    (s.setXmmSse r v).getXmm r = v := by
  ext i hi
  simp [getXmm, setXmmSse, setXmm]
  rw [BitVec.getLsbD_append]
  simp [hi]

@[simp] theorem getYmm_setYmm_vex_self (s : State) (r : Fin 32) (v : BitVec 256) :
    (s.setYmm r v false).getYmm r = v := by
  simp [getYmm, setYmm]

@[simp] theorem getYmm_setYmm_sse_self (s : State) (r : Fin 32) (v : BitVec 256) :
    (s.setYmm r v true).getYmm r = v := by
  ext i hi
  simp [getYmm, setYmm]
  rw [BitVec.getLsbD_append]
  simp [hi]

@[simp] theorem extractUpper_setXmmSse (s : State) (r : Fin 32) (v : BitVec 128) :
    ((s.setXmmSse r v).getZmm r).extractLsb' 128 384 = (s.getZmm r).extractLsb' 128 384 := by
  ext i hi
  simp [getZmm, setXmmSse, setXmm]
  rw [BitVec.getLsbD_append]
  have h : ¬ (128 + i < 128) := by omega
  simp [h, hi]

@[simp] theorem extractUpper_setXmmVex (s : State) (r : Fin 32) (v : BitVec 128) :
    ((s.setXmmVex r v).getZmm r).extractLsb' 128 384 = 0#384 := by
  ext i hi
  simp [getZmm, setXmmVex, setXmm]

@[simp] theorem extractUpper_setYmm_vex (s : State) (r : Fin 32) (v : BitVec 256) :
    ((s.setYmm r v false).getZmm r).extractLsb' 256 256 = 0#256 := by
  ext i hi
  simp [getZmm, setYmm]

@[simp] theorem extractUpper_setYmm_sse (s : State) (r : Fin 32) (v : BitVec 256) :
    ((s.setYmm r v true).getZmm r).extractLsb' 256 256 = (s.getZmm r).extractLsb' 256 256 := by
  ext i hi
  simp [getZmm, setYmm]
  rw [BitVec.getLsbD_append]
  have h : ¬ (256 + i < 256) := by omega
  simp [h, hi]

@[simp] theorem getMask_setMask_self (s : State) (k : Fin 8) (v : BitVec 64) :
    (s.setMask k v).getMask k = v := by
  simp [getMask, setMask]

@[simp] theorem getMask_setMask_ne (s : State) (k k' : Fin 8) (v : BitVec 64) (h : k' ≠ k) :
    (s.setMask k v).getMask k' = s.getMask k' := by
  simp [getMask, setMask, h]

@[simp] theorem isLaneActive_k0 (s : State) (lane : Nat) :
    s.isLaneActive ⟨0, by omega⟩ lane = true := rfl

@[simp] theorem getCr_setCr_self (s : State) (i : Fin 16) (v : UInt64) :
    (s.setCr i v).getCr i = v := by
  simp [getCr, setCr]

@[simp] theorem getDr_setDr_self (s : State) (i : Fin 8) (v : UInt64) :
    (s.setDr i v).getDr i = v := by
  simp [getDr, setDr]

@[simp] theorem getMsr_setMsr_self (s : State) (idx : UInt32) (v : UInt64) :
    (s.setMsr idx v).getMsr idx = v := by
  simp [getMsr, setMsr]

@[simp] theorem getSeg_setSeg_self (s : State) (seg : SegReg) (desc : SegmentDescriptor) :
    (s.setSeg seg desc).getSeg seg = desc := by
  simp [getSeg, setSeg]

@[simp] theorem getFsBase_setFsBase (s : State) (base : UInt64) :
    (s.setFsBase base).getFsBase = base := by
  simp [getFsBase, setFsBase, setSeg]

@[simp] theorem getGsBase_setGsBase (s : State) (base : UInt64) :
    (s.setGsBase base).getGsBase = base := by
  simp [getGsBase, setGsBase, setSeg]

end State

end Grass.ISA.X86.Target
