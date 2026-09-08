import Grass.Platform.Win32.Console

/-!
# The two exit statuses, at the values `docs/HELLO_WORLD.md` gives

`Grass/Platform/Win32/Console.lean` proves `statuses_distinct`: the success and
failure statuses differ, which is what makes the terminal protocol's
`distinguish` law satisfiable. That is the property the module needs and it is
not a pin. Distinctness survives moving either status to any other value, so a
sweep changing `successStatus` to 2 left the whole repository green.

The document is specific: "Success means the full string was written and
terminal status is zero", and a failing run "has status one". Zero and one are
the values, not merely two different numbers.

It matters more than it looks. A process exit status is what a shell, a test
harness or a parent process branches on, and every one of them treats zero as
success by convention -- so a program returning 2 for success reports failure to
everything that runs it, while satisfying `statuses_distinct` perfectly.
-/

namespace Tests.Platform.Win32.ExitStatuses

open Grass.Platform.Win32

/-- Zero, per `docs/HELLO_WORLD.md`. -/
example : successStatus = 0 := rfl

/-- One. The document gives a single public failure outcome, so the three
distinguishable internal failures share this. -/
example : failureStatus = 1 := rfl

/-- Success is specifically *zero* and not merely "the other one". This is the
example that would fail if the two were swapped, which `statuses_distinct`
cannot see. -/
example : successStatus ≠ 1 ∧ failureStatus ≠ 0 := by decide

/-- `Spikes/5_Spinning_Cube/Process.lean` passes the literal `1` for its
failure status rather than naming this constant. Pinned here so the two
spellings cannot drift apart silently -- that spike is not this agent's tree to
edit, and a literal in one place with a definition in another is the
arrangement `Grass/ABI/Win64/Convention.lean` records as a hazard. -/
example : failureStatus = (1 : BitVec 32) := rfl

end Tests.Platform.Win32.ExitStatuses
