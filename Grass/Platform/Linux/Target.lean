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

`Grass.ISA.X86.isa` and `Grass.ISA.AArch64.isa` (`Grass/ISA/X86/Target.lean`,
`Grass/ISA/AArch64/Target.lean`) now both exist, so `platformX86` and
`platformAArch64` below are both wired up. See the report for a distinct,
structural seam gap this file's `encodeReturn` had to accommodate rather than
fix (`Console.Request.exit`'s terminal/`Empty` shape, `Grass/Target/
Machine.lean`'s `Step.terminal`).

## `mmap`/`Heap.allocate` and the ISA's address space

`Service.Heap.allocate`'s response is `Option Nat`: an opaque handle. This
platform's `decode`/`encodeReturn` for `mmap`/`munmap` treat that handle as
the mapped region's address directly (the same `Nat` `mmap` returns in `rax`/
`x0` is the `munmap` argument that later releases it).

`Grass.Target.ISA.NativeReturn` is an ISA-defined type (`Grass/Target/
ISA.lean`), not part of the seam's own fixed shape, so each ISA is free to
extend its own `NativeReturn` without touching the seam. `Grass.ISA.X86.
Target.Native.NativeReturn` and `Grass.ISA.AArch64.Target.Native.NativeReturn`
(`Grass/ISA/X86/Target/Native.lean`, `Grass/ISA/AArch64/Target/Native.lean`)
now additionally carry `maps : List MappedRegion` (default `[]`): regions the
answer newly mapped, which `resume`/`applySvcReturn` install into
`State.regions` and zero-fill in `State.mem` (a MAP_ANONYMOUS mapping reads
as zero, `man 2 mmap`) before applying `writes`. This module's `.allocate`
success case now sets `maps := [{ base := address, size := bytes,
readable := true, writable := true }]`, so `mmap`'s answer both hands back
the address value and actually backs it with fresh, accessible memory.

`NativeReturn` now also carries `unmaps : List Nat` (default `[]`), the
converse effect: base addresses of regions the answer releases, which
`execInstr`/`applySvcReturn` remove from `State.regions` after applying
`writes`. This module's `.release` success case sets `unmaps := [handle]`
(`handle` being the address `mmap` returned, per this module's own opaque-
handle-is-an-address convention above), so a successful `munmap` now actually
removes the released region: an access there after `munmap` faults, matching
a real kernel's `SIGSEGV`, instead of being admitted.

Separately, `Grass.Platform.Hosted.Heap.respondsHeap` (`Grass/Platform/
Hosted/Heap.lean`) now requires a successful `.allocate`'s address to be
disjoint from every existing live allocation and from `Environment.reserved`
(the program image, stack, and argument block) -- the environment's job, not
this platform's: a platform only encodes whatever address the environment
already chose not to hand out over the code.
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
