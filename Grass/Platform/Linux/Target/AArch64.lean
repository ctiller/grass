import Grass.ISA.AArch64.Target.Native
import Grass.Platform.Hosted.Responds
import Grass.Platform.Linux.Target.Errno
import Grass.Artifact.Binary.LittleEndian

/-!
# Linux AArch64 native-call ABI

The AArch64 half of the Linux platform, mirroring `Grass.Platform.Linux.
Target.X86` for the A64 `SVC` calling convention. See that module's docstring
for the shared decode/encodeReturn table and rationale; only the ABI details
that actually differ are repeated here.

## Syscall ABI

`man 2 syscall`, "Architecture calling conventions": on arm64 the syscall
number is in `x8`; up to six arguments are in `x0`-`x5`; the result is
returned in `x0`. Unlike x86-64's `syscall`/`sysret` pair, an arm64 `SVC`
exception return does not need to reuse any argument register to get back to
user mode, so the kernel does not document any register as clobbered beyond
the result in `x0`. Numbers are from `include/uapi/asm-generic/unistd.h`, the
generic syscall table arm64 uses directly (`arch/arm64/kernel/entry-common.c`
routes `x8` through it via `do_el0_svc`) -- the same table
`Grass.Platform.Linux.Syscall.number .aarch64` cites for `read`/`write`/
`exit`/`exit_group`.

`Grass.ISA.AArch64.NativeCall.reg`/`NativeReturn.x0`/`InitialContext.registers`
are `BitVec 64`-valued (the register file's actual shape, `Grass/ISA/AArch64/
Target/Native.lean`), unlike x86-64's `UInt64`-valued surface -- syscall
numbers and ABI constants below are `BitVec 64` so they compare directly
against a register read with no conversion at every comparison site; only the
handful of places that meet a `Nat`- or `UInt64`-typed neighbour (`NativeCall.
read`'s address/count, `Errno.negative`, `Console.Request.exit`'s `UInt32`)
convert at that single boundary.
-/

namespace Grass.Platform.Linux.Target.AArch64

open Grass.ISA.AArch64 (Reg NativeCall NativeReturn CallTarget InitialContext)
open Grass.Service
open Grass.Platform.Hosted (Environment domain)
open Grass.Platform.Linux.Target.Errno
open Grass.Artifact.Binary (writeU64LE)

/-- `Grass.ISA.AArch64.Reg` is `Fin 31`; name the six argument/number
registers this ABI reads. -/
def x0 : Reg := 0
def x1 : Reg := 1
def x5 : Reg := 5
def x8 : Reg := 8

/-! ## Syscall numbers (generic table, `include/uapi/asm-generic/unistd.h`) -/

/-- `__NR3264_read`, `63`. -/
def sysRead : BitVec 64 := 63

/-- `__NR3264_write`, `64`. -/
def sysWrite : BitVec 64 := 64

/-- `__NR3264_brk`, `214`. -/
def sysBrk : BitVec 64 := 214

/-- `__NR3264_munmap`, `215`. -/
def sysMunmap : BitVec 64 := 215

/-- `__NR3264_mmap`, `222`. -/
def sysMmap : BitVec 64 := 222

/-- `__NR_clock_gettime`, `113`. -/
def sysClockGettime : BitVec 64 := 113

/-- `__NR_exit`, `93`. -/
def sysExit : BitVec 64 := 93

/-- `__NR_exit_group`, `94`. -/
def sysExitGroup : BitVec 64 := 94

/-- `include/uapi/linux/time.h`: `#define CLOCK_MONOTONIC 1`. -/
def CLOCK_MONOTONIC : BitVec 64 := 1

/-- `PROT_READ (0x1) | PROT_WRITE (0x2)`, `include/uapi/asm-generic/
mman-common.h`; identical bit values to x86-64. -/
def PROT_READ_WRITE : BitVec 64 := 0x3

/-- `MAP_PRIVATE (0x02) | MAP_ANONYMOUS (0x20)`,
`include/uapi/asm-generic/mman-common.h` / `mman.h`; identical bit values to
x86-64 (`asm-generic` is shared by both). -/
def MAP_PRIVATE_ANONYMOUS : BitVec 64 := 0x22

/-! ## Decode -/

/-- Decode one AArch64 `SVC` site into `Grass.Platform.Hosted.domain`'s
portable request. Same mapping as `Grass.Platform.Linux.Target.X86.decode`,
read off `x0`-`x5`/`x8` instead of `rdi`/`rsi`/`rdx`/`r10`/`r8`/`r9`/`rax`. A
`mmioLoad`/`mmioStore` target is a bare-metal device-window access
(`InitialContext.devices`); this hosted platform never declares one, so
those two constructors decode to `none` alongside `importSlot` -- a real
Linux process never reaches either shape. -/
def decode (call : NativeCall) : Option domain.Request :=
  match call.target with
  | .importSlot _ => none
  | .mmioLoad _ _ => none
  | .mmioStore _ _ => none
  | .supervisor _imm =>
    let number := call.reg x8
    if number = sysWrite then
      let fd := call.reg x0
      let bufAddr := (call.reg x1).toNat
      let count := (call.reg (2 : Reg)).toNat
      if fd = 1 then
        (call.read bufAddr count).map (fun bytes => .inl (.inl (.write .stdout bytes)))
      else if fd = 2 then
        (call.read bufAddr count).map (fun bytes => .inl (.inl (.write .stderr bytes)))
      else none
    else if number = sysRead then
      let fd := call.reg x0
      let count := (call.reg (2 : Reg)).toNat
      if fd = 0 then some (.inl (.inl (.read .stdin count))) else none
    else if number = sysExit ∨ number = sysExitGroup then
      some (.inl (.inl (.exit (UInt32.ofNat (call.reg x0).toNat))))
    else if number = sysMmap then
      let addr := call.reg x0
      let len := call.reg x1
      let prot := call.reg (2 : Reg)
      let flags := call.reg (3 : Reg)
      let fd := call.reg (4 : Reg)
      let offset := call.reg x5
      -- `fd`'s low 32 bits are compared (not the full 64), matching
      -- `Grass.Platform.Linux.Target.X86.decode`'s `mmap` case: a compiler
      -- may load the ABI `int fd = -1` argument either sign-extended or via
      -- a 32-bit move that the write rule zero-extends, both of which put
      -- `-1` in exactly the low 32 bits.
      if addr = 0 ∧ prot = PROT_READ_WRITE ∧ flags = MAP_PRIVATE_ANONYMOUS ∧
          BitVec.setWidth 32 fd = (0xFFFFFFFF : BitVec 32) ∧ offset = 0 then
        some (.inl (.inr (.allocate len.toNat)))
      else none
    else if number = sysMunmap then
      some (.inl (.inr (.release (call.reg x0).toNat)))
    else if number = sysClockGettime then
      if call.reg x0 = CLOCK_MONOTONIC then some (.inr .now) else none
    else if number = sysBrk then
      -- Unsupported: this platform grows the heap only through `mmap`
      -- (`Heap.allocate`/`Heap.release`), never through the program break.
      none
    else
      none

/-! ## encodeReturn -/

/-- One 16-byte `struct timespec`, little-endian; see
`Grass.Platform.Linux.Target.X86.encodeTimespec`. -/
def encodeTimespec (nanoseconds : Nat) : List UInt8 :=
  writeU64LE (UInt64.ofNat (nanoseconds / 1000000000)) ++
    writeU64LE (UInt64.ofNat (nanoseconds % 1000000000))

/-- Encode the environment's answer as the ABI-level effect of returning from
`call`. An arm64 `SVC` return clobbers only `x0` (the result register itself,
already modeled), so `clobbers` is empty throughout. `Errno.negative`'s
`UInt64` result is converted to the ABI's native `BitVec 64` via `.toBitVec`
(`UInt64` is literally a `BitVec 64` wrapper, so this conversion is exact). -/
def encodeReturn (call : NativeCall) : (request : domain.Request) → domain.Response request →
    NativeReturn
  | .inl (.inl (.write _stream _bytes)), response =>
      match response with
      | .accepted count => { x0 := BitVec.ofNat 64 count, x1 := none, writes := [], clobbers := [] }
      | .failed => { x0 := (negative EIO).toBitVec, x1 := none, writes := [], clobbers := [] }
  | .inl (.inl (.read _stream _max)), response =>
      match response with
      | .delivered bytes =>
          { x0 := BitVec.ofNat 64 bytes.length, x1 := none
            writes := [((call.reg x1).toNat, bytes)], clobbers := [] }
      | .failed => { x0 := (negative EIO).toBitVec, x1 := none, writes := [], clobbers := [] }
  | .inl (.inl (.query _stream)), _response =>
      { x0 := (negative ENOSYS).toBitVec, x1 := none, writes := [], clobbers := [] }
  | .inl (.inl (.exit _status)), response => response.elim
  | .inl (.inr (.allocate bytes)), response =>
      match response with
      | some address =>
          -- See `Grass.Platform.Linux.Target.X86.encodeReturn`'s `.allocate`
          -- case: `mmap`'s point is a region the process could not touch
          -- before, so this answer also maps `[address, address + bytes)`
          -- read/write, non-executable, matching `PROT_READ|PROT_WRITE`.
          { x0 := BitVec.ofNat 64 address, x1 := none, writes := [], clobbers := []
            maps := [{ base := address, size := bytes, readable := true, writable := true }] }
      | none => { x0 := (negative ENOMEM).toBitVec, x1 := none, writes := [], clobbers := [] }
  | .inl (.inr (.reallocate _handle _bytes)), response =>
      match response with
      | some address => { x0 := BitVec.ofNat 64 address, x1 := none, writes := [], clobbers := [] }
      | none => { x0 := (negative ENOSYS).toBitVec, x1 := none, writes := [], clobbers := [] }
  | .inl (.inr (.release _handle)), response =>
      -- Over-approximates on release: see
      -- `Grass.Platform.Linux.Target.X86.encodeReturn`'s `.release` case.
      -- `NativeReturn` has no region-removal effect, so a successful
      -- `munmap` here still leaves the region readable/writable afterward.
      match response with
      | true => { x0 := 0, x1 := none, writes := [], clobbers := [] }
      | false => { x0 := (negative EINVAL).toBitVec, x1 := none, writes := [], clobbers := [] }
  | .inr .now, response =>
      { x0 := 0, x1 := none
        writes := [((call.reg x1).toNat, encodeTimespec response)], clobbers := [] }

/-! ## Process entry -/

/-- See `Grass.Platform.Linux.Target.X86.cString`. -/
def cString (s : String) : List UInt8 := s.toUTF8.toList ++ [0]

/-- See `Grass.Platform.Linux.Target.X86.headerWords`; the AAPCS64 process
entry stack image has the same shape as the SysV AMD64 one. -/
def headerWords (argc : Nat) : Nat := 1 + argc + 1 + 1 + 2

/-- See `Grass.Platform.Linux.Target.X86.buildArgumentBlock`. -/
def buildArgumentBlock (arguments : List String) (sp : Nat) : List UInt8 :=
  let strings := arguments.map cString
  let stringBase := sp + headerWords arguments.length * 8
  let addresses : List Nat :=
    (strings.foldl (fun (acc : List Nat × Nat) s => (acc.1 ++ [acc.2], acc.2 + s.length))
      ([], stringBase)).1
  let argcWord := writeU64LE (UInt64.ofNat arguments.length)
  let argvWords := (addresses.map (fun a => writeU64LE (UInt64.ofNat a))).flatten
  let argvNull := writeU64LE 0
  let envpNull := writeU64LE 0
  let auxvNull := writeU64LE 0 ++ writeU64LE 0
  argcWord ++ argvWords ++ argvNull ++ envpNull ++ auxvNull ++ strings.flatten

/-- See `Grass.Platform.Linux.Target.X86.argumentBlockLength`. -/
def argumentBlockLength (arguments : List String) : Nat :=
  headerWords arguments.length * 8 + (arguments.map (fun s => s.toUTF8.toList.length + 1)).sum

/-- Fill the ISA's entry context from the hosted environment. AAPCS64 leaves
the process-entry register state unspecified beyond `sp` (the kernel's
`ELF(32)_PLAT_INIT`/generic `start_thread` clears the general-purpose
registers it controls, but no ABI document commits to that for every
register), so every register but `sp` defaults to `0`, matching
`Grass.Platform.Linux.Target.X86.entry`'s reading of the SysV AMD64 ABI:
picking a concrete value excludes nothing a real kernel could hand back.
`devices` is left empty: this is a hosted platform, with no memory-mapped
device windows for the ISA to route `mmioLoad`/`mmioStore` through. -/
def entry (env : Environment) : InitialContext :=
  let stackTop : Nat := 0x0000FFFFFFFFF000
  let blockLength := argumentBlockLength env.arguments
  let sp : Nat := ((stackTop - blockLength) / 16) * 16
  { registers := fun _ => 0
    sp := BitVec.ofNat 64 sp
    staged := [(sp, buildArgumentBlock env.arguments sp)]
    devices := [] }

end Grass.Platform.Linux.Target.AArch64
