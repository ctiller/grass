import Grass.ABI.Win64.Convention
import Grass.ISA.X86.Target.Native

/-!
# The Win32 entry context

`Grass.Target.Platform.entry : Environment → isa.InitialContext` fills what
the loader hands the machine at the program's first instruction. It takes no
program (`Grass.ISA.X86.Target.InitialContext`'s docstring: `entry` "fills
this without knowing the program's sections"), so a fact that genuinely
belongs to the program — the stack reservation a PE header requests via
`Sectioned.stackBytes` (`Grass/Target/Raw.lean`) — has to reach `entry`
through the environment instead. `Grass.ISA.X86.Target.initial` is what
combines the two.

The concrete `Environment` this platform will eventually parameterize
`Grass.Target.Platform` with is not this module's to define: a hosted
process's environment (arguments, console, heap, clock) is the same shape
for Win32, Linux and WASI, and is being written once, shared, as
`Grass.Platform.Hosted.Environment` (not yet present in this tree — see
`Grass/Platform/Win32/Target.lean`, "Dependencies"). Until it lands, `entry`
is parameterized over an abstract `Environment` plus the one thing it
actually needs out of it — `StackConfig` — so it can be re-pointed at the
real type later without changing this function's body: instantiate
`StackConfig` with `Hosted.Environment`'s own stack fields (whatever they
turn out to be named) once that module exists.
-/

namespace Grass.Platform.Win32.Target

open Grass.ISA.X86.Target

/-- What `entry` needs out of an environment: where the reserved stack
region sits. Everything else `InitialContext` asks for is fixed by the Win64
loader contract, not chosen per environment. -/
structure StackConfig (Environment : Type) where
  /-- The highest address the reserved stack region occupies. Assumed
  16-byte aligned, matching a real Win32 loader's stack placement — `entry`
  computes `RSP` from it under that assumption and does not itself verify
  it, since verifying an `Environment`'s own well-formedness is
  `Platform.Admits`'s job, not `entry`'s. -/
  stackTop : Environment → Nat
  /-- Bytes reserved below `stackTop`. Sourced from the loaded program's
  `Sectioned.stackBytes` by whoever builds the `Environment` (the loader) —
  `entry` never sees `Sectioned` to read it from directly, by the seam's own
  design (see the module docstring above). -/
  stackBytes : Environment → Nat

/-- The loader hands the machine a stack pointer 16-byte aligned minus 8, as
if execution had just been reached by a `call` from the loader
(`Grass.ABI.Win64.entryMisalignment`/`stackAlignment`: the Win64 convention's
own statement of a callee's entry alignment, reused rather than restated).

`RCX`/`RDX` — and every other general-purpose register besides `RSP` — are
set to a fixed representative value (`0`) rather than modeled as truly
unspecified, because `InitialContext.reg` is a total function
`Reg → UInt64` with no room for "any value": a per-program proof must not
rely on this value being `0` specifically, only that it is *some* fixed
value, which `0` witnesses as well as any other.

The argument block is empty: `GetCommandLineW`, the only way a Win32 program
reaches its command line, is out of scope for this profile (see
`Grass/Platform/Win32/Target.lean`, "Unsupported"), so there is nothing to
place there. -/
def entry {Environment : Type} (config : StackConfig Environment) (env : Environment) :
    InitialContext :=
  { reg := fun r => if r = .rsp then
        UInt64.ofNat (config.stackTop env - Grass.ABI.Win64.entryMisalignment)
      else 0
    stackTop := config.stackTop env
    stackBytes := config.stackBytes env
    argumentBlockAddress := 0
    argumentBlock := [] }

end Grass.Platform.Win32.Target
