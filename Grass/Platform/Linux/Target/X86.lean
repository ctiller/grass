import Grass.ISA.X86.Target.Native
import Grass.Platform.Hosted.Responds
import Grass.Platform.Linux.Target.Errno
import Grass.Artifact.Binary.LittleEndian

/-!
# Linux x86-64 native-call ABI

The x86-64 half of the Linux platform: `decode`s a `syscall` instruction's
register/memory snapshot into `Grass.Platform.Hosted.domain`'s portable
requests, `encodeReturn`s the environment's answer back into the ABI's result
registers and memory writes, and builds the System V AMD64 process-entry
stack image `entry` hands the loaded machine.

## Syscall ABI

The kernel's raw `syscall` boundary (`man 2 syscall`, "Architecture calling
conventions"; `arch/x86/entry/entry_64.S`): the syscall number is in `rax`;
up to six arguments are in `rdi`, `rsi`, `rdx`, `r10`, `r8`, `r9` (`r10`
stands in for `rcx`, which `syscall` itself overwrites with the return
address); the result is returned in `rax`; `rcx` and `r11` are always
clobbered (`rcx` holds the return address, `r11` holds `rflags`, both
consumed by the matching `sysret`). Numbers below are from
`arch/x86/entry/syscalls/syscall_64.tbl`.

## Decode / encodeReturn table

| Syscall | Decode | Encode on success | Encode on failure/absence |
|---|---|---|---|
| `write(fd,buf,len)`, `fd∈{1,2}` | `Console.write stdout\|stderr bytes` (bytes read via `NativeCall.read`; unreadable buffer → stuck, `none`) | `rax :=` accepted count | `rax := -EIO` |
| `read(0,buf,len)` | `Console.read stdin len` | `rax :=` count, buffer bytes written at `buf` | `rax := -EIO` |
| `exit(code)` / `exit_group(code)` | `Console.exit code` (terminal) | n/a: `Console.Response (.exit _) = Empty`, eliminated | n/a |
| `mmap(NULL,len,PROT_READ\|WRITE,MAP_PRIVATE\|ANONYMOUS,-1,0)` | `Heap.allocate len` | `rax :=` address | `rax := -ENOMEM` |
| `munmap(addr,len)` | `Heap.release addr` (`addr` is the opaque handle `mmap` returned) | `rax := 0` | `rax := -EINVAL` |
| `clock_gettime(CLOCK_MONOTONIC,ts)` | `Clock.now` | `rax := 0`, 16-byte `timespec` written at `ts` | (never fails: `Clock.Response` is total) |
| `brk(addr)` | unsupported: `none` (this platform grows the heap only through `mmap`/`Heap.allocate`) | — | — |
| anything else, or `mmap`/`munmap`/`read`/`write` with an unrecognized fd/flag combination | unsupported: `none` | — | — |
| an `importSlot` call | not a Linux syscall: `none` | — | — |

`read`, `write` and `clock_gettime`'s buffer/`fd`/`clockid` are re-read from
the original `NativeCall` inside `encodeReturn`, not carried in the portable
`Request`: `Service.Domain` is address-space-agnostic, so the address the
answer gets written to is exactly the kind of platform/ABI detail the
portable vocabulary must not know.
-/

namespace Grass.Platform.Linux.Target.X86

open Grass.ISA.X86.Target (NativeCall NativeReturn CallTarget Reg InitialContext)
open Grass.Service
open Grass.Platform.Hosted (Environment domain)
open Grass.Platform.Linux.Target.Errno
open Grass.Artifact.Binary (writeU64LE)

/-! ## Syscall numbers (x86-64) -/

/-- `arch/x86/entry/syscalls/syscall_64.tbl`: `0  common  read`. -/
def sysRead : UInt64 := 0

/-- `arch/x86/entry/syscalls/syscall_64.tbl`: `1  common  write`. -/
def sysWrite : UInt64 := 1

/-- `arch/x86/entry/syscalls/syscall_64.tbl`: `9  common  mmap`. -/
def sysMmap : UInt64 := 9

/-- `arch/x86/entry/syscalls/syscall_64.tbl`: `11  common  munmap`. -/
def sysMunmap : UInt64 := 11

/-- `arch/x86/entry/syscalls/syscall_64.tbl`: `12  common  brk`. -/
def sysBrk : UInt64 := 12

/-- `arch/x86/entry/syscalls/syscall_64.tbl`: `60  common  exit`. -/
def sysExit : UInt64 := 60

/-- `arch/x86/entry/syscalls/syscall_64.tbl`: `228  common  clock_gettime`. -/
def sysClockGettime : UInt64 := 228

/-- `arch/x86/entry/syscalls/syscall_64.tbl`: `231  common  exit_group`. -/
def sysExitGroup : UInt64 := 231

/-- `include/uapi/linux/time.h`: `#define CLOCK_MONOTONIC 1`. The only clock
id this platform realizes, matching `Service.Clock`'s domain, which "only
ever promises monotonicity" (`Grass/Platform/Hosted/Clock.lean`). -/
def CLOCK_MONOTONIC : UInt64 := 1

/-- `include/uapi/asm-generic/mman-common.h`: `PROT_READ (0x1) | PROT_WRITE
(0x2)`. The only protection this platform's `mmap` decode realizes. -/
def PROT_READ_WRITE : UInt64 := 0x3

/-- `include/uapi/asm-generic/mman-common.h`: `MAP_PRIVATE (0x02)`;
`include/uapi/asm-generic/mman.h`: `MAP_ANONYMOUS (0x20)`. The only mapping
kind this platform's `mmap` decode realizes: an anonymous, non-shared region,
matching `Service.Heap`'s handle-based arena (nothing backs it by a file, and
no other address space shares it). -/
def MAP_PRIVATE_ANONYMOUS : UInt64 := 0x22

/-! ## Decode -/

/-- Decode one x86-64 `syscall` site into `Grass.Platform.Hosted.domain`'s
portable request. See the module docstring's table for the full mapping;
`none` is either a genuine refusal (unsupported syscall, unrecognized `fd` or
`mmap` flag combination) or an unreadable argument buffer, both of which the
generic machine tier (`Grass.Target.Machine.stuck_of_undecoded`) turns into a
stuck state -- the correct, visible refusal for a call this platform does not
realize. -/
def decode (call : NativeCall) : Option domain.Request :=
  match call.target with
  -- Linux resolves every syscall through the `syscall` instruction; an
  -- import-table call is a Win32/PE convention this platform never uses.
  | .importSlot _ => none
  | .syscall =>
    let number := call.reg .rax
    if number = sysWrite then
      let fd := call.reg .rdi
      let bufAddr := (call.reg .rsi).toNat
      let count := (call.reg .rdx).toNat
      if fd = 1 then
        (call.read bufAddr count).map (fun bytes => .inl (.inl (.write .stdout bytes)))
      else if fd = 2 then
        (call.read bufAddr count).map (fun bytes => .inl (.inl (.write .stderr bytes)))
      else none
    else if number = sysRead then
      let fd := call.reg .rdi
      let count := (call.reg .rdx).toNat
      if fd = 0 then some (.inl (.inl (.read .stdin count))) else none
    else if number = sysExit ∨ number = sysExitGroup then
      some (.inl (.inl (.exit (call.reg .rdi).toUInt32)))
    else if number = sysMmap then
      let addr := call.reg .rdi
      let len := call.reg .rsi
      let prot := call.reg .rdx
      let flags := call.reg .r10
      let fd := call.reg .r8
      let offset := call.reg .r9
      -- Only the one shape `Service.Heap.allocate` can mean: a fresh,
      -- anonymous, private, read-write region with no file and no address
      -- hint. `fd`'s low 32 bits are compared (not the full 64), since a
      -- compiler may load the ABI `int fd = -1` argument either sign-
      -- extended (`mov $-1, %r8`) or zero-extended via a 32-bit move
      -- (`mov r8d, -1`, which the x86-64 write rule zero-extends to 64 bits);
      -- both encode `-1` in the low 32 bits.
      if addr = 0 ∧ prot = PROT_READ_WRITE ∧ flags = MAP_PRIVATE_ANONYMOUS ∧
          fd.toUInt32 = 0xFFFFFFFF ∧ offset = 0 then
        some (.inl (.inr (.allocate len.toNat)))
      else none
    else if number = sysMunmap then
      -- `Service.Heap`'s handles are opaque; this platform's opaque handle
      -- *is* the address `mmap` returned, so `munmap`'s address is exactly
      -- the handle `release` needs.
      some (.inl (.inr (.release (call.reg .rdi).toNat)))
    else if number = sysClockGettime then
      if call.reg .rdi = CLOCK_MONOTONIC then some (.inr .now) else none
    else if number = sysBrk then
      -- Unsupported: this platform grows the heap only through `mmap`
      -- (`Heap.allocate`/`Heap.release`), never through the program break.
      none
    else
      none

/-! ## encodeReturn -/

/-- One 16-byte `struct timespec { long tv_sec; long tv_nsec; }`
(`include/uapi/linux/time.h`), little-endian, both fields 8 bytes on the
LP64 x86-64 ABI. `Service.Clock.now`'s `Nat` is nanoseconds since an
unspecified monotonic epoch (`Grass/Platform/Hosted/Clock.lean`); this is
where that unit is fixed into wire bytes. -/
def encodeTimespec (nanoseconds : Nat) : List UInt8 :=
  writeU64LE (UInt64.ofNat (nanoseconds / 1000000000)) ++
    writeU64LE (UInt64.ofNat (nanoseconds % 1000000000))

/-- Encode the environment's answer as the ABI-level effect of returning from
`call`. Matches on the request before the response, since `domain.Response`
is dependent on it. `rcx`/`r11` are clobbered by every `syscall` return,
whether the call succeeded or not. -/
def encodeReturn (call : NativeCall) : (request : domain.Request) → domain.Response request →
    NativeReturn
  | .inl (.inl (.write _stream _bytes)), response =>
      match response with
      | .accepted count =>
          { rax := UInt64.ofNat count, rdx := none, writes := [], clobbers := [.rcx, .r11] }
      | .failed => { rax := negative EIO, rdx := none, writes := [], clobbers := [.rcx, .r11] }
  | .inl (.inl (.read _stream _max)), response =>
      match response with
      | .delivered bytes =>
          { rax := UInt64.ofNat bytes.length, rdx := none
            writes := [((call.reg .rsi).toNat, bytes)], clobbers := [.rcx, .r11] }
      | .failed => { rax := negative EIO, rdx := none, writes := [], clobbers := [.rcx, .r11] }
  | .inl (.inl (.query _stream)), _response =>
      -- `decode` never produces this request: no syscall in this platform's
      -- table answers "is this fd connected". Kept only so `encodeReturn` is
      -- total over the whole domain; see the report for `Console.query` as a
      -- possible future `isatty`/`fstat` mapping.
      { rax := negative ENOSYS, rdx := none, writes := [], clobbers := [.rcx, .r11] }
  | .inl (.inl (.exit _status)), response =>
      -- `Console.Response (.exit _) = Empty`: no answer is ever delivered to
      -- a terminal request, so there is no value to encode.
      response.elim
  | .inl (.inr (.allocate bytes)), response =>
      match response with
      | some address =>
          -- `mmap`'s whole point is a region the process could not touch
          -- before: `rax` alone (the address value) is not enough for the
          -- machine to honor a later access there, so this answer also maps
          -- `[address, address + bytes)` read/write, non-executable --
          -- `PROT_READ|PROT_WRITE` is exactly what `decode`'s `mmap` match
          -- above requires of the call that produced this request.
          { rax := UInt64.ofNat address, rdx := none, writes := [], clobbers := [.rcx, .r11]
            maps := [{ base := address, size := bytes, readable := true, writable := true }] }
      | none => { rax := negative ENOMEM, rdx := none, writes := [], clobbers := [.rcx, .r11] }
  | .inl (.inr (.reallocate _handle _bytes)), response =>
      -- `decode` never produces this request: `mremap` is not in this
      -- platform's syscall table. Kept only for `encodeReturn`'s totality.
      match response with
      | some address =>
          { rax := UInt64.ofNat address, rdx := none, writes := [], clobbers := [.rcx, .r11] }
      | none => { rax := negative ENOSYS, rdx := none, writes := [], clobbers := [.rcx, .r11] }
  | .inl (.inr (.release _handle)), response =>
      -- `munmap`'s converse effect -- narrowing what the process may access
      -- -- has no counterpart in `NativeReturn`: only `maps` exists, adding
      -- regions, never removing one. This profile therefore over-approximates
      -- on the safe-for-the-program-but-unsound-for-the-kernel-model side: a
      -- successful `release` still leaves the released region readable and
      -- writable in `State.regions`, so an access after `munmap` that a real
      -- kernel would fault (`SIGSEGV`) is admitted here instead of refused.
      -- Closing this needs an `unmaps` effect (region removal by base
      -- address) symmetric to `maps`; not added in this slice.
      match response with
      | true => { rax := 0, rdx := none, writes := [], clobbers := [.rcx, .r11] }
      | false => { rax := negative EINVAL, rdx := none, writes := [], clobbers := [.rcx, .r11] }
  | .inr .now, response =>
      { rax := 0, rdx := none
        writes := [((call.reg .rsi).toNat, encodeTimespec response)], clobbers := [.rcx, .r11] }

/-! ## Process entry -/

/-- One `NUL`-terminated `argv`/`envp` string, as C expects it in memory. -/
def cString (s : String) : List UInt8 := s.toUTF8.toList ++ [0]

/-- The fixed-size part of the SysV AMD64 process-entry block, in 8-byte
words: `argc` (1) + `argv[0..argc-1]` pointers (`argc`) + the `argv` `NULL`
terminator (1) + an empty `envp`'s sole `NULL` terminator (1: this platform
does not yet expose the process environment, only `Environment.arguments`;
see the report) + the single `AT_NULL` auxiliary-vector entry, a `(type,
value)` pair of two words (2). -/
def headerWords (argc : Nat) : Nat := 1 + argc + 1 + 1 + 2

/-- The SysV AMD64 process-entry stack image (`man 2 syscall`'s sibling
`execve(2)` and the psABI §3.4.1 "Initial Process Stack"): `argc`, the
`argv` pointer array terminated by `NULL`, an empty `envp` (its `NULL`
terminator only), a single `AT_NULL` auxiliary-vector entry, and finally the
argument strings themselves -- the layout `sysdeps/x86_64/start.S`'s `_start`
reads directly off `rsp`. `rsp` (here, the block's start address) is where
the string pointers' absolute addresses are computed from. -/
def buildArgumentBlock (arguments : List String) (rsp : Nat) : List UInt8 :=
  let strings := arguments.map cString
  let stringBase := rsp + headerWords arguments.length * 8
  let addresses : List Nat :=
    (strings.foldl (fun (acc : List Nat × Nat) s => (acc.1 ++ [acc.2], acc.2 + s.length))
      ([], stringBase)).1
  let argcWord := writeU64LE (UInt64.ofNat arguments.length)
  let argvWords := (addresses.map (fun a => writeU64LE (UInt64.ofNat a))).flatten
  let argvNull := writeU64LE 0
  let envpNull := writeU64LE 0
  let auxvNull := writeU64LE 0 ++ writeU64LE 0
  argcWord ++ argvWords ++ argvNull ++ envpNull ++ auxvNull ++ strings.flatten

/-- The bytes the process-entry block needs, before any address is chosen for
it: the fixed-size header plus every argument string's `NUL`-terminated
encoding. -/
def argumentBlockLength (arguments : List String) : Nat :=
  headerWords arguments.length * 8 + (arguments.map (fun s => s.toUTF8.toList.length + 1)).sum

/-- Fill the ISA's entry context from the hosted environment: a fixed-size
stack region topped at a canonical low-half address below `TASK_SIZE_MAX`
(`arch/x86/include/asm/processor.h`; no ASLR is modeled), `rsp` -- and so the
argument block's start -- rounded down to a 16-byte boundary beneath that top
per the psABI's process-entry alignment requirement, `rdx := 0` (no dynamic
linker termination function to register with `atexit`, matching a statically
linked or already-relocated image), and every other register left at `0`:
the ABI does not specify them, so no value a real kernel could hand back is
excluded by picking one. -/
def entry (env : Environment) : InitialContext :=
  let stackTop : Nat := 0x00007FFFFFFFF000
  let stackBytes : Nat := 8 * 1024 * 1024
  let blockLength := argumentBlockLength env.arguments
  let rsp : Nat := ((stackTop - blockLength) / 16) * 16
  { reg := fun r => if r = .rsp then UInt64.ofNat rsp else 0
    stackTop := stackTop
    stackBytes := stackBytes
    argumentBlockAddress := rsp
    argumentBlock := buildArgumentBlock env.arguments rsp }

end Grass.Platform.Linux.Target.X86
