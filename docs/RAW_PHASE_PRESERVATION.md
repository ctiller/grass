# Raw phase preservation

[RawPhasePreservation](../Grass/Platform/Win32/RawPhasePreservation.lean)
extracts local facts from the actual fixed raw relation:

- API entry establishes a checked pending state for the loaded caller and
  selected provider.
- GetStdHandle return establishes checked caller control and removes that
  exact runtime occurrence.
- CPU edges preserve metadata, control and runtime data, including across
  explicit outside-profile outcomes. This does not preserve protocol validity
  of an arbitrary reached machine.
- Bounded actual CPU prefixes retain those same fields. The
  [composition test](../Tests/Platform/Win32RawPhasePreservation.lean) joins an
  actual GetStdHandle return to a CPU suffix at the exact same state and graph.

[RawPrefix](../Grass/Platform/Win32/RawPrefix.lean) reuses
`RelationalSystem.ExecutionPrefix` for finite histories. Its root is computed
from the selected loaded machine, actual grant-supply coverage, fresh protocol
bookkeeping, loaded caller and empty runtime table and graph. Universe lifts
only align the existing carrier with raw choices; each step is the exact raw
relation. Its unused terminal and infinite-consistency fields are false
scaffolding, **not raw completion semantics**. No completion, deadlock, progress
or termination conclusion may be drawn from those fields. Replace this view
with the canonical raw system when complete semantics are available.

These clauses do not prove enabledness or Hello deadlock freedom. Frontend must
retain the actual loader-to-entry prefix; a computed endpoint alone is
insufficient. WriteFile requires the same enclosing history and publication
connection through the lowering adapter. Exit needs an actual terminal edge
with retained status. Neither refusal nor outside-profile execution counts as
successful termination or permitted external waiting.
