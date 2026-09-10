import Grass.Service.Domain

/-!
# Win32 standard-handle values

`GetStdHandle` returns a value the program is then expected to pass back to
`WriteFile`/`ReadFile` to name the same stream. Real Win32 issues one fixed
pseudo-handle per standard device for the life of a process (Microsoft
Learn, "GetStdHandle function",
https://learn.microsoft.com/en-us/windows/console/getstdhandle : the
`nStdHandle` selectors name `STD_INPUT_HANDLE`/`STD_OUTPUT_HANDLE`/
`STD_ERROR_HANDLE`, each resolving to a handle that does not change across
repeated calls within one process). Modeling the mapping as a fixed, static
bijection rather than one allocated on first query is therefore faithful to
the documented behaviour, not a simplifying shortcut.

It is also the only choice available: `Grass.Target.Platform.decode` takes
no `Environment` (`Grass/Target/Platform.lean`), so the mapping `decode`
uses to recover a stream from a `WriteFile`/`ReadFile` handle argument must
already be fixed, independent of any run's history — it cannot be looked up
in state that `GetStdHandle`'s earlier answer would have had to update.
-/

namespace Grass.Platform.Win32.Target.Handles

open Grass.Service

/-- The fixed handle value this platform issues for a standard stream when
`GetStdHandle` reports it available (`Grass/Platform/Win32/Target/Return.lean`).
Distinct across streams, and deliberately neither `0` (`NULL`) nor
`0xFFFFFFFFFFFFFFFF` (`INVALID_HANDLE_VALUE`), which this profile reserves
as its "no such handle" answers
(`Grass/Platform/Win32/Target/Return.lean`, `GetStdHandle`). The concrete
values are this platform's own choice: nothing about a real Win32 handle's
bit pattern is part of the documented contract, so any three distinct
non-reserved values are equally faithful. -/
def value : Stream → UInt64
  | .stdin => 3
  | .stdout => 7
  | .stderr => 11

/-- Recover the stream a Win32 handle value denotes, if any. `none` for a
handle this platform never issued through `GetStdHandle` — including `0`,
`INVALID_HANDLE_VALUE`, and any value a hypothetical `CreateFile` might have
returned, which this profile does not model
(`Grass/Platform/Win32/Target.lean`, "Unsupported"). A `none` here makes
`decode` fail the enclosing `WriteFile`/`ReadFile` call, which is correct:
passing a handle this platform never handed out is a program bug. -/
def streamOf (handle : UInt64) : Option Stream :=
  if handle = value .stdin then some .stdin
  else if handle = value .stdout then some .stdout
  else if handle = value .stderr then some .stderr
  else none

/-- Every issued handle recovers the stream it was issued for. This is the
fact `decode` relies on without restating it: whatever
`Grass/Platform/Win32/Target/Return.lean` hands back for
`GetStdHandle stream`, a later `WriteFile`/`ReadFile` on that exact value
decodes to a request about `stream`. -/
theorem streamOf_value (stream : Stream) : streamOf (value stream) = some stream := by
  cases stream <;> decide

end Grass.Platform.Win32.Target.Handles
