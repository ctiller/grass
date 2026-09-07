import Grass.Platform.Win32.Console
import Grass.Platform.Win32.Profile

/-!
# The Win32 API facade

`docs/MODULES.md` defines this as "the public facade for the Win32 API family",
and replaces the spike spelling `Grass.Platform.Win10.X64` with it. The
replacement is not a rename: a Windows version floor and an architecture/ABI
selection "remain explicit profile values selected through this API; neither
belongs in the module path".

`Grass.Platform.Win32.Profile` is where they went. `decision16` is the profile
`docs/DECISIONS.md` 16 fixes -- Windows 10 baseline, x64, documented APIs rather
than direct syscalls -- and `Profile.FollowsDecision16` is decidable, so a
profile can be compared and discharged rather than spelled.

This module declares nothing; it is the import list and this note.

## The cone

Two shards, and through `Grass.Platform.Win32.Console` one further edge to
`Grass.ABI.Win64.Convention`, which reaches `Grass.ISA.X86.Register`.

That last edge is worth stating plainly, because a first draft of this note
denied it. A calling convention is partly a statement about registers --
`Grass.ABI.Win64.volatility` and `Grass.ABI.Win64.argumentRegister` are
functions of `Grass.ISA.X86.Gpr` -- so register vocabulary is inside this cone
and is meant to be. What is outside is the instruction encoder and decoder:
nothing about calling `WriteFile` depends on how a `mov` is spelled in bytes.

`Tests/Facade/PlatformWin32.lean` pins that boundary in both directions, and it
is the fixture that caught the draft's claim rather than a reviewer.

## What is here, and what that is worth

`Grass.Platform.Win32.Console` covers `GetStdHandle`, `WriteFile` against a
console handle, and `ExitProcess`. Its `WriteRequest`/`WriteResponse` pair
carries a decidable `Allowed` relation, and `writeAdequate` shows the relation is
inhabited for every request, so a partial write and a zero-length write are both
modelled rather than assumed away.

`GetStdHandle` and `ExitProcess` carry no `Allowed` relation. That is an open
obligation recorded in `Grass/Platform/Win32/Console.lean`, not a claim that
those calls cannot fail, and `StdHandleId.value` is pinned only by the mutual
distinctness `StdHandleId.value_injective` states.
-/
