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

A retraction, recorded here rather than dropped. The first version of this file
carried a fourth example justified by the claim that
`Spikes/5_Spinning_Cube/Process.lean` spells the failure status as a literal `1`
instead of naming this constant, making a second spelling that could drift.
It does contain that literal, and the rest does not follow: `Spikes` is not in
`lakefile.toml`'s `defaultTargets`, nothing under `Grass/` or `Tests/` imports
it, and the `TargetProjection.win10VulkanInteractive` it passes the literal to
does not exist anywhere in the repository. That file is a design sketch which
does not compile, so there is no second spelling and nothing to drift from.
The example it justified was a type-ascribed restatement of the second one
above, so it went with the claim.
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

end Tests.Platform.Win32.ExitStatuses
