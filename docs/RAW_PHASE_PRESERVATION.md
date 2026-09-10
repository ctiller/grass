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

[RawPrefix](../Grass/Platform/Win32/RawPrefix.lean) defines `Raw.system` and reuses
`RelationalSystem.ExecutionPrefix` for finite histories. Its root is computed
from the selected loaded machine, actual grant-supply coverage, fresh protocol
bookkeeping, loaded caller and empty runtime table and graph. Universe lifts
only align the existing carrier with raw choices; each step is the exact raw
relation. A terminal state retains its exit call and status; `Raw.result`
projects that payload. Every pointwise actual infinite step stream is admitted,
with no fairness or responsiveness condition. Infinite service is not silently
identified with a finite wait, and silent CPU divergence remains represented.
This is a relative operational system. A full `BehaviorModel` still needs a
faithful external wait boundary and its public observation mapping.

[RawTerminal](../Grass/Platform/Win32/RawTerminal.lean) proves that any actual
edge into terminal control is a checked ExitProcess completion. Every terminal
loader-rooted prefix therefore retains a preceding run and a final actual exit
edge with the exact process, call, status and event. Terminal control admits no
next raw step; archived bookkeeping need not be empty.

These clauses do not prove enabledness or Hello deadlock freedom. The certificate
fixture at `f9145e4a` now retains the actual 24-edge loader-to-first-WriteFile-entry
prefix; see the [endpoint index](ENDPOINT_INDEX.md#issued-call-resume-status).
WriteFile still requires the original-entry segment and enclosing history/publication
connection through the lowering adapter. Main `0993922c` includes the actual
`RawStep.completedExit` edge, retained status and `terminal_no_step`; this is not
native cleanup or obligation discharge. Neither refusal nor outside-profile
execution counts as successful termination or permitted external waiting.

[RawPrefixSteps](../Grass/Platform/Win32/RawPrefixSteps.lean) decomposes an
existing prefix propositionally into finite state, graph and choice witnesses,
with exactly its recorded events and endpoints. It reuses the generic
[Steps theorem](../Grass/Semantics/ExecutionSteps.lean); the witnesses are not
unique or a canonical choice sequence. No second history carrier is introduced.

[RawPendingService](../Grass/Platform/Win32/RawPendingService.lean) proves that
an actual pending-to-pending edge is service for the same call, caller and
provider, exposing its receipt, action, publication and graph facts. To use the
service-history fold, establish those pending phases for the contiguous segment
being decomposed and retain its original entry witness. Neither arbitrary
prefixes nor equal endpoints supply that entry ancestry. Its `pending_segment`
theorem derives the intermediate controls from the actual entry's pending
control and the indexed slice's internal/publication events. Return and exit
observations are excluded by the slice condition, not reclassified as service.
[RawGetStdHandlePending](../Grass/Platform/Win32/RawGetStdHandlePending.lean)
classifies outgoing choices using exact pending control and the same call's
GetStdHandle runtime entry: every actual outgoing edge is a stdout-result edge
for that call. This excludes CPU work and WriteFile service at that frontier.
It does not establish reply existence for every allowed provider observation,
or permission for permanent nonresponse. Those are separate obligations before
this frontier can supply a full external wait boundary.
