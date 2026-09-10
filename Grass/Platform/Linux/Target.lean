import Grass.Platform.Linux.Target.X86
import Grass.Platform.Linux.Target.AArch64
import Grass.ISA.AArch64.Target
import Grass.Target.Platform
import Grass.ISA.X86.Target

/-!
# The Linux platform

Assembles `Grass.Platform.Linux.Target.X86`/`.AArch64`'s ABI-specific
`entry`/`decode`/`encodeReturn` with `Grass.Platform.Hosted`'s shared
`Environment`/`Admits`/`Responds`/`domain` into `Grass.Target.Platform`
instances for each ISA this platform hosts.

`Grass.ISA.X86.isa` -- the whole-machine `Instr`/`encode`/`decode`/`State`/
`step` record `Grass.Target.Platform` is indexed by -- does not exist in this
worktree yet (only the `Native` call surface `Grass/ISA/X86/Target/
Native.lean` exports does). `platformX86` below stays commented out for
exactly that reason; every field it would need (`entry`, `decode`,
`encodeReturn`, `Environment`, `Admits`, `Responds`) is already built and
typechecked against the concrete `NativeCall`/`NativeReturn`/`InitialContext`
types, so assembling the record is a one-line change once its `isa` argument
exists. `Grass.ISA.AArch64.isa` now exists (`Grass/ISA/AArch64/Target.lean`),
so `platformAArch64` below is wired up. See the report for a distinct,
structural seam gap this file's `encodeReturn` had to accommodate rather than
fix (`Console.Request.exit`'s terminal/`Empty` shape, `Grass/Target/
Machine.lean`'s `Step.terminal`).

## `mmap`/`Heap.allocate` and the ISA's address space

`Service.Heap.allocate`'s response is `Option Nat`: an opaque handle. This
platform's `decode`/`encodeReturn` for `mmap`/`munmap` treat that handle as
the mapped region's address directly (the same `Nat` `mmap` returns in `rax`/
`x0` is the `munmap` argument that later releases it) -- that much needs
nothing beyond `NativeReturn.rax`/`NativeReturn.writes`, which is all this
module produces.

What it cannot produce: `Grass.ISA.X86.Target.Native.NativeReturn` and
`Grass.ISA.AArch64.Target.Native.NativeReturn` (`Grass/ISA/X86/Target/
Native.lean`, `Grass/ISA/AArch64/Target/Native.lean`) carry only `rax`/`x0`,
an optional `rdx`/`x1`, `writes : List (Nat × List UInt8)` (bytes at
*already-mapped* addresses) and `clobbers`. Neither has a "map this address
range as readable/writable, starting from nothing" effect. A real `mmap`
does not write bytes into existing memory; it extends what addresses the
process may access at all. So `encodeReturn`'s answer to `mmap` hands back an
address the ISA's `State`/`step` have no documented way to actually back with
fresh, accessible memory -- the address is correct as a *value* (what a
real kernel would return, and what a real program's later loads/stores at
that address are entitled to expect), but nothing in the current ISA seam
lets the machine tier honor an access there. This is a genuine seam gap, not
a bug in this file: the fix is a `mapRegion (address : Nat) (bytes : Nat)
(permission : ...) : State → State`-shaped effect (or an equivalent addition
to `NativeReturn`) in `Grass.Target.ISA`, which this worktree's rules forbid
editing. `decode`/`encodeReturn` for `.allocate`/`.release` are implemented
here anyway, exactly as asked, so that once that effect exists, wiring it in
is the only remaining change.
-/

namespace Grass.Platform.Linux.Target

def platformX86 : Grass.Target.Platform Grass.ISA.X86.isa Grass.Platform.Hosted.domain where
  Environment := Grass.Platform.Hosted.Environment
  Admits := Grass.Platform.Hosted.Admits
  entry := Grass.Platform.Linux.Target.X86.entry
  decode := Grass.Platform.Linux.Target.X86.decode
  Responds := Grass.Platform.Hosted.Responds
  encodeReturn := Grass.Platform.Linux.Target.X86.encodeReturn

def platformAArch64 : Grass.Target.Platform Grass.ISA.AArch64.isa Grass.Platform.Hosted.domain where
  Environment := Grass.Platform.Hosted.Environment
  Admits := Grass.Platform.Hosted.Admits
  entry := Grass.Platform.Linux.Target.AArch64.entry
  decode := Grass.Platform.Linux.Target.AArch64.decode
  Responds := Grass.Platform.Hosted.Responds
  encodeReturn := Grass.Platform.Linux.Target.AArch64.encodeReturn

end Grass.Platform.Linux.Target
