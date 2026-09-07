import Grass.Platform.Win32.Console
import Grass.Platform.Win32.Profile

/-!
# The Win32 API facade

## Where the rule comes from

`docs/MODULES.md` calls this "the public facade for the Win32 API family", and
decision 134 ratifies `Grass.Platform.*` as a stable author-facing facade. The
spike spelling `Grass.Platform.Win10.X64` "must be replaced by
`Grass.Platform.Win32`, not retained as an alias" -- a requirement, and not yet
a completed action, since the spike corpus still imports the old spelling.

That is not a rename either way: a Windows version floor and an architecture/ABI
selection "remain explicit profile values selected through this API; neither
belongs in the module path".

An earlier draft of this paragraph said the rule lived on an unmerged commit and
was not checkable from this tree. That was false -- the ruling had already
merged, and the true statement was only that this branch was behind `main`. It
went in because I asserted a fact about git ancestry on a reviewer's word
without running `git merge-base` myself.

`Grass.Platform.Win32.Profile` is where they went, and its own header is candid
about how little is enforced there: the only mechanism is that
`TargetAbi.handleBits` and `TargetAbi.pointerBits` are total. Nothing consumes
the profile yet.

This module declares nothing; it is the import list and this note.

## The cone

Five Grass modules, listed exactly in `Tests/Facade/PlatformWin32.lean` and
compared against the environment on every build, so this paragraph is checked
rather than asserted.

`Grass.ISA.X86.Citation` is the only x86 module in it: the console entry points
carry external-authority citations like every other machine-facing declaration
here.

An earlier draft claimed a different edge -- that `Grass.ABI.Win64.Convention`
was in the cone because a calling convention is partly a statement about
registers -- and pinned `Grass.ISA.X86.Gpr` as vocabulary this facade exports.
`Console.lean` imported `Convention` and used nothing from it. The import was
dead, and pinning `Gpr` had made it load bearing, so the cleanup `lake shake`
exists to prompt would have failed the fixture. `Console.lean` now imports the
module it actually needs.

## What is here, and what that is worth

`Grass.Platform.Win32.Console` covers `GetStdHandle`, `WriteFile`, and
`ExitProcess`. `Allowed` is the decidable relation between a `WriteRequest` and
a `WriteResponse`, and `partialWrite_allowed` and `zeroWrite_allowed` are what
say a partial write and a zero-length write are modelled rather than assumed
away.

`writeAdequate` is *not* that, though an earlier draft here said it was: it
witnesses `∃ r, Allowed q r` with `.failure 0`, and `Console.lean` records a
reviewer's point that this proves adequacy using the one response whose
lawfulness is least certain. It shows the relation is inhabited and nothing
more.

`WriteRequest.handle` is an opaque `BitVec 64`; nothing in the model ties it to
a console handle specifically. `GetStdHandle` and `ExitProcess` carry no
`Allowed` relation at all -- an open obligation recorded in `Console.lean`, not
a claim that those calls cannot fail -- and `StdHandleId.value` is pinned only
by the mutual distinctness `StdHandleId.value_injective` states.
-/
