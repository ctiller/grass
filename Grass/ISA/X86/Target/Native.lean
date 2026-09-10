import Grass.ISA.X86.Register

/-!
# x86-64 native-call surface

The types a `Grass.Target.Platform Grass.ISA.X86.isa D` decodes against, split
out from `Grass/ISA/X86/Target.lean` so a platform author has a stable target
before the rest of the ISA (`Instr`, `encode`/`decode`, `State`, `step`) is
finished. Nothing here names a platform, a service domain, or a program: a
`NativeCall` is a snapshot of registers, memory and the call site, exactly
what a decoder needs to read a portable request out of an ABI it alone knows.

`Reg` reuses `Grass.ISA.X86.Gpr`: the sixteen 64-bit general-purpose registers
of long mode, already proved (`Grass/ISA/X86/Register.lean`) to round-trip
through their three-bit encoding plus a REX extension bit. Introducing a
second, unrelated `Reg` type here would duplicate that proof for no reason.
-/

namespace Grass.ISA.X86.Target

/-- A general-purpose register. The sixteen registers of 64-bit mode; see
`Grass.ISA.X86.Gpr`. -/
abbrev Reg := Grass.ISA.X86.Gpr

/-- What a `call`-shaped instruction's target resolves to.

The ISA decides *which encoded form* (`call qword ptr [rip+disp32]` vs.
`syscall`) produced the call; it does not decide what the call means. A
platform's `decode : NativeCall → Option Request` matches on this to tell an
import-table call (resolved by the loader to a fixed slot address) from a
system call (numbered in a register by convention). -/
inductive CallTarget where
  /-- `call qword ptr [rip+disp32]` (or any other resolved indirect call
  through memory) where the loaded address is an import table / GOT slot. -/
  | importSlot (slotAddress : Nat)
  /-- The `syscall` instruction. The syscall number lives in the register
  snapshot at the ABI's conventional register; the ISA does not interpret it. -/
  | syscall
deriving DecidableEq, Repr

/-- The register/stack/memory view of a native call site.

Everything a platform's ABI needs to decode a portable service request: which
kind of call this is, the full register file at the call (arguments are
wherever the platform's calling convention puts them), a bounded memory
reader for arguments passed in memory, and where control returns.
-/
structure NativeCall where
  /-- What this call resolves to. -/
  target : CallTarget
  /-- The register file at the call site. -/
  reg : Reg → UInt64
  /-- Read `count` bytes starting at `address`, or `none` if any byte of the
  range is outside the loaded image or unreadable. A platform uses this to
  fetch by-reference arguments (a buffer pointer and length, a C string). -/
  read : (address : Nat) → (count : Nat) → Option (List UInt8)
  /-- The stack pointer at the call site. -/
  rsp : UInt64
  /-- The address execution resumes at once the call returns. For
  `call [rip+disp32]` this is the address of the following instruction; for
  `syscall` it is likewise the next instruction, since `syscall` does not push
  a return address. -/
  returnAddress : UInt64

/-- The machine-level effect of a platform's answer to a `NativeCall`.

Carries exactly what `step` needs to resume the machine: the integer result
registers a call convention returns values in, any memory the platform's
answer wrote (an output buffer, a written struct), and which registers the
call convention documents as clobbered (their post-call value is not modeled
beyond "some value", so a program depending on one being preserved is not
proved safe by accident). -/
structure NativeReturn where
  /-- The primary return value register (`rax` in the SysV and Win64
  conventions this profile targets). -/
  rax : UInt64
  /-- The secondary return value register (`rdx`), for calls that return a
  value wider than 64 bits or a `(value, error)` pair. `none` when the call
  convention leaves it unspecified. -/
  rdx : Option UInt64
  /-- Memory the platform's answer wrote: an address and the bytes placed
  there, in order. -/
  writes : List (Nat × List UInt8)
  /-- Registers the call convention documents as clobbered by this call,
  beyond `rax`/`rdx`. -/
  clobbers : List Reg
deriving Inhabited

/-- Why a step could not execute.

Every constructor makes the machine stuck (`Grass.Target.StepOutcome.fault`):
proving a machine adequate is proving none of these is reachable. -/
inductive Fault where
  /-- The bytes at `rip` are not a valid encoding of any instruction this ISA
  models. -/
  | undecodable
  /-- A read touched an address outside the loaded image, or inside it but
  marked unreadable. -/
  | readOutsideImage (address : Nat)
  /-- A write touched an address outside the loaded image, or inside it but
  marked unwritable. -/
  | writeOutsideImage (address : Nat)
  /-- Control reached an address outside the loaded image, or inside it but
  marked non-executable. -/
  | executeNonExecutable (address : Nat)
  /-- An access required an alignment the address does not have. -/
  | unaligned (address : Nat)
  /-- `div`/`idiv` with a zero divisor. -/
  | divideByZero
  /-- `div`/`idiv` whose quotient does not fit the destination register. -/
  | divideOverflow
  /-- `ud2`, or any other instruction whose defined behaviour is to fault. -/
  | explicitUndefined
deriving DecidableEq, Repr

/-- What the platform hands the machine at entry: initial register values,
where the stack lives, and the argument block bytes the platform placed in
memory before jumping to `entry`.

Kept separate from `Sectioned` (`Grass/Target/Raw.lean`): `Sectioned` is the
program, fixed by the artifact; `InitialContext` is the environment's choice
of how to start it (the platform fills this without knowing the program's
sections, and `Grass.ISA.X86.Target.initial` combines the two). -/
structure InitialContext where
  /-- The initial value of every general-purpose register, before the
  platform's stack and argument-block placement is applied via `rsp`. -/
  reg : Reg → UInt64
  /-- The address of the top of the reserved stack region (the highest
  address the stack occupies; `rsp` starts here, growing down). -/
  stackTop : Nat
  /-- The stack region's size in bytes, reserved below `stackTop`. -/
  stackBytes : Nat
  /-- The address the platform placed the argument block at (`argv`-style
  bytes: a `Win32`/`Linux` process's command line or argument vector,
  already laid out in the platform's own format). -/
  argumentBlockAddress : Nat
  /-- The argument block's bytes, written into memory at
  `argumentBlockAddress` before entry. -/
  argumentBlock : List UInt8
deriving Inhabited

end Grass.ISA.X86.Target
