import Grass.Target.Raw

/-!
# AArch64 native-call surface

The types a platform needs to give meaning to an A64 native call, independent
of any instruction encoding or execution semantics: what a call site *is*
(`CallTarget`), what the machine hands the platform at that site (`NativeCall`),
what the platform hands back (`NativeReturn`), why a step can get stuck
(`Fault`), and what the platform hands the machine at entry (`InitialContext`).

Per `docs/TARGET_SEAMS.md`, none of this names a platform, a service domain, or
a program: `CallTarget.supervisor` is an SVC immediate, not a syscall number
meaning; `CallTarget.importSlot` is an address a `BLR` landed through, not a
library function identity.
-/

namespace Grass.ISA.AArch64

/-- General-purpose register index, X0..X30. An instruction operand field
encoding 31 means SP or XZR depending on the operand position, which is a
property of *where* the field is read, not of this index type: no `Reg` value
represents SP or XZR, and operand-reading code decides which zero-or-SP
convention applies before it ever forms one. -/
abbrev Reg := Fin 31

/-- The identity of a native call site. `supervisor` is the immediate an `SVC`
carried; `importSlot` is the address a `BLR` landed through, i.e. the loader-
filled slot (a Win32 IAT entry, an ELF GOT entry) the platform recognizes. -/
inductive CallTarget where
  | supervisor (imm : UInt16)
  | importSlot (slotAddress : Nat)
  /-- A load of `size` bytes from `address`, where `address` lies in one of
  the device windows the platform declared in `InitialContext.devices`. The
  platform answers with the loaded value in `NativeReturn.x0`; the ISA lands
  it in the destination register. -/
  | mmioLoad (address : Nat) (size : Nat)
  /-- A store of `bytes` to `address` inside a declared device window. The
  ISA does not know what the device does with them; the platform's answer is
  ignored by the store's `resume` beyond advancing `pc`. -/
  | mmioStore (address : Nat) (bytes : List UInt8)
  deriving Repr, DecidableEq

/-- The register/stack/memory view of a native call site, handed to the
platform to decode into a portable `Service.Request`. `read` answers a byte
range from the machine's memory (`none` if any byte in the range is
unmapped), so the platform can read a caller-supplied buffer without the ISA
naming what the buffer is for. -/
structure NativeCall where
  target : CallTarget
  /-- Snapshot of X0..X30 at the call site. -/
  reg : Reg → BitVec 64
  /-- Snapshot of SP at the call site. -/
  sp : BitVec 64
  /-- Read `size` bytes starting at `address`; `none` if any byte is unmapped
  or unreadable. -/
  read : (address : Nat) → (size : Nat) → Option (List UInt8)

/-- The machine-level effect of a platform's answer to a native call: result
registers and any memory writes the platform's response performs (e.g. bytes
a `read` service delivered into a caller buffer). `clobbers` lists registers
the call convention destroys beyond `x0`/`x1` (nothing here claims which ABI
that is; a platform fills it from its own convention). -/
structure NativeReturn where
  x0 : BitVec 64
  x1 : Option (BitVec 64) := none
  writes : List (Nat × List UInt8) := []
  clobbers : List Reg := []

/-- Why a step could not proceed. Every constructor here makes the machine
stuck, which is the point: memory and control safety is the absence of a
reachable `fault`. -/
inductive Fault where
  /-- The fetched word (or its 4-byte-aligned prefix) is not a bit pattern
  this `decode` recognizes, or fewer than 4 bytes were available to fetch. -/
  | undecodable
  /-- A read of `size` bytes at `address` touched a byte outside every mapped
  region, or a region without read permission. -/
  | readOutsideImage (address : Nat) (size : Nat)
  /-- A write of `size` bytes at `address` touched a byte outside every
  mapped region, or a region without write permission. -/
  | writeOutsideImage (address : Nat) (size : Nat)
  /-- `pc` pointed into memory that is mapped but not executable, or is
  unmapped. -/
  | executeNonExecutable (address : Nat)
  /-- An access required `requiredAlignment`-byte alignment at `address` and
  did not have it. -/
  | unaligned (address : Nat) (requiredAlignment : Nat)
  /-- A `BLR` landed through an address that is not a recognized import
  slot. -/
  | unallocatedImport (slotAddress : Nat)
  deriving Repr, DecidableEq

/-- What the platform hands the machine at entry: initial register values
(a platform may leave most at zero and set only what its ABI specifies, e.g.
argc/argv registers), the initial stack pointer, and any extra bytes the
platform must stage in memory before the first instruction runs (an
argv/envp block, an auxiliary vector) as `(address, bytes)` regions, in the
same shape `NativeReturn.writes` uses. The ISA does not interpret these
bytes; it only installs them. -/
structure InitialContext where
  registers : Reg → BitVec 64
  sp : BitVec 64
  staged : List (Nat × List UInt8)
  /-- Device windows as `(base, size)` byte ranges: a load or store whose
  address falls inside one is reported to the platform as an `.external`
  native call (`CallTarget.mmioLoad`/`CallTarget.mmioStore`) instead of
  touching memory. Hosted platforms leave this empty; a bare-metal platform
  names its memory-mapped device registers here. The ISA never interprets
  which device a window is. -/
  devices : List (Nat × Nat) := []

end Grass.ISA.AArch64
