import Grass.Platform.Win32.Console

/-!
# The widths `docs/DECISIONS.md` 16's profile selects

`Grass/Platform/Win32/Profile.lean` states `TargetAbi.handleBits` and
`TargetAbi.pointerBits`, and `Grass/Platform/Win32/Console.lean` now takes its
`Handle` width from the first of them rather than writing `BitVec 64`
independently. These pin the values.

**What this file does and does not establish.** It makes the ABI numbers
mutation-detectable, which nothing did before: changing `handleBits` to 32 used
to leave the whole build green. It does *not* establish that `Console` is wired
to the profile. Nothing can, while one `TargetAbi` exists -- an equation that
holds by `rfl` under every extension is not a safeguard, which is the standard
`Profile.lean`'s own header sets and this file is held to.

The wiring's guarantee is structural instead: `handleBits` is a total function,
so a second ABI cannot be added without answering for it, and there is now one
declaration to answer rather than two that agree by inspection.
-/

namespace Tests.Platform.Win32.ProfileWidths

open Grass.Platform.Win32

/-- A Win32 `HANDLE` is 64 bits under the selected ABI. -/
example : decision16.abi.handleBits = 64 := rfl

/-- And a pointer is too. Stated separately because they are separate facts
that happen to coincide on x64; a target where they differ is exactly what
`TargetAbi` exists to keep expressible. -/
example : decision16.abi.pointerBits = 64 := rfl

/-- The width `Console` actually uses is that one. This is the consequence, not
an independent claim -- it reduces to the equation above. -/
example : Handle = BitVec 64 := rfl

/-- `INVALID_HANDLE_VALUE` is all ones at that width.

Worth pinning for a reason the mutation run turned up. `invalidHandleValue` is
written as the literal `0xFFFFFFFFFFFFFFFF`, and `BitVec`'s `OfNat` truncates
rather than refusing, so at a narrower width it silently becomes all ones *at
that width* -- still `(HANDLE)-1`, still distinguishable from null, and every
theorem in `Console` still true. That is why narrowing `handleBits` broke
nothing there. The model is width-polymorphic; only this file says which width
was selected. -/
example : GetStdHandleResult.invalidHandleValue = BitVec.allOnes 64 := rfl

end Tests.Platform.Win32.ProfileWidths
