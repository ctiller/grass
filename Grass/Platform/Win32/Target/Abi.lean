import Grass.ABI.Win64.Convention
import Grass.Artifact.Binary.LittleEndian
import Grass.ISA.X86.Target.Native

/-!
# Reading Win64 arguments off a `NativeCall`

Integer/pointer arguments 0-3 are in `RCX`, `RDX`, `R8`, `R9`
(`Grass.ABI.Win64.argumentRegister`, reused rather than restated); arguments
4 and up are on the stack, starting at `[rsp + 0x28]` — the 8-byte return
address starts at `call.rsp`, followed at `call.rsp + 8` by the 32-byte shadow
space every Win64 call site reserves (`Grass.ABI.Win64.shadowSpaceBytes`).
`Grass.ISA.X86.Target.NativeCall` is captured at the callee's first
instruction, before any prologue runs; `stackArgumentOffset` includes both
areas when locating stack-passed arguments.

Source: Microsoft Learn, "x64 calling convention",
https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention (register
and stack argument placement) and
https://learn.microsoft.com/en-us/cpp/build/stack-usage (shadow space and
the return-address offset at a callee's entry point). Single-sourced: this is
a Microsoft-defined contract, not an architectural fact — see
`Grass/ABI/Win64/Convention.lean`'s module docstring for the same point made
about the hand-built frame this reuses.
-/

namespace Grass.Platform.Win32.Target

open Grass.ISA.X86.Target (NativeCall)

/-- Integer/pointer argument 0, in `RCX`
(`Grass.ABI.Win64.argumentRegister 0 = some .rcx`). -/
def arg0 (call : NativeCall) : UInt64 := call.reg .rcx

/-- Integer/pointer argument 1, in `RDX`. -/
def arg1 (call : NativeCall) : UInt64 := call.reg .rdx

/-- Integer/pointer argument 2, in `R8`. -/
def arg2 (call : NativeCall) : UInt64 := call.reg .r8

/-- Integer/pointer argument 3, in `R9`. -/
def arg3 (call : NativeCall) : UInt64 := call.reg .r9

/-- `arg0`-`arg3` are exactly `Grass.ABI.Win64.argumentRegister`'s first four
positions, stated once so a reviewer can compare the two definitions instead
of re-deriving the register assignment. -/
theorem arg0_register : Grass.ABI.Win64.argumentRegister 0 = some .rcx := rfl
theorem arg1_register : Grass.ABI.Win64.argumentRegister 1 = some .rdx := rfl
theorem arg2_register : Grass.ABI.Win64.argumentRegister 2 = some .r8 := rfl
theorem arg3_register : Grass.ABI.Win64.argumentRegister 3 = some .r9 := rfl

/-- Byte offset from `RSP` at the callee's first instruction of stack-passed
argument `index` (`index ≥ Grass.ABI.Win64.registerArgumentCount`): past the
8-byte return address and the 32-byte shadow space every Win64 call site
reserves. `index = 4` (the first stack argument) lands at `0x28`. -/
def stackArgumentOffset (index : Nat) : Nat :=
  8 + Grass.ABI.Win64.shadowSpaceBytes + 8 * (index - Grass.ABI.Win64.registerArgumentCount)

@[simp] theorem stackArgumentOffset_four : stackArgumentOffset 4 = 0x28 := rfl

/-- A stack-passed argument (`index ≥ 4`), read little-endian off `call`'s
memory view at `call.rsp + stackArgumentOffset index`
(`Grass.Artifact.Binary.readU64LE`, already round-trip proved — reused
rather than re-derived here). `none` if the slot is unreadable (outside the
loaded image), which every caller of this function propagates to `none`: an
unreadable stack argument slot is a caller bug, not a platform gap. -/
def stackArgument (call : NativeCall) (index : Nat) : Option UInt64 :=
  match call.read (call.rsp.toNat + stackArgumentOffset index) 8 with
  | some bytes => (Grass.Artifact.Binary.readU64LE bytes).map Prod.fst
  | none => none

/-- The low 32 bits of a Win64 argument: what a `DWORD`/`UINT`/`BOOL`
parameter occupies. The convention does not promise the high 32 bits of an
argument register are zero for a narrower argument, so a 32-bit argument
must always be read this way rather than compared as a full 64-bit value. -/
def low32 (value : UInt64) : UInt32 := UInt32.ofNat value.toNat

end Grass.Platform.Win32.Target
