# Bounded Windows provider evidence

[`WriteFile.lean`](../Grass/Platform/Win32/WriteFile.lean) supplies a conditional
pending-prefix evidence layer for the synchronous Hello World provider. It does
not implement a Win32 provider, discharge physical ABI applicability, or extend
the common memory checker with happens-before.

The request carries buffer/count-slot provenance and actual input bytes. Every
frontier resolves both arguments against live CPU allocations, requires initialized
input, and checks an explicit temporary profile: no aliases, nonwrapping placements,
and physical separation of distinct live CPU allocations. The count slot and input
range must be disjoint even within one allocation. This wrapper is intended to
consume the shared state-bound resolver when the backing migration lands; it does
not introduce another backing store.

`History` starts at an actual `CallProtocol.handoff?` with zero accepted bytes and
a valid causal graph. Each extension retains the same pending occurrence and exact
loans, an actual checked step, clean audit, preserved obligations and metadata,
confined count writes, and exact buffer-read/count-write event footprints. Published
bytes are the next suffix segment; their concatenation equals the new cumulative
input prefix. Issuing a loan does not initialize the count slot.

The fixed `Realization` remains an external semantic parameter. In particular,
generic `step?` identifies an agent, not the API occurrence that caused its action.
`executesFor` must connect physical dispatch to that occurrence; sharing an agent
identity is insufficient. Causal graph shape and extension do not establish
Windows/ISA ordering soundness, and `publishes` still needs a connection to the
selected provider-accepted-byte observation. There is no default realization or
proof that these external premises cover all Windows executions. Synchronous
handle rights/mode/lifetime, physical argument values, return, failure outcomes,
physical permanent-wait interpretation and violation envelopes remain downstream work.

[`Win32WriteFile.lean`](../Tests/Platform/Win32WriteFile.lean) exercises initialized
request preparation, exact handoff, and an actual no-memory provider step. It
rejects wrong calls/dispatch, missing loans, substituted or uninitialized bytes,
overlap, repeated prefixes, excessive/backward counts and missing causal edges.
Its actual caller-zero/handoff/provider-zero fixture still receives a denial from
the current checker; the evidence layer rejects that result even though `step?`
returns `some`. It does not claim a conforming provider write exists yet.

## Conditional nonresponse evidence

[`WriteFileNonresponse.lean`](../Grass/Platform/Win32/WriteFileNonresponse.lean)
consumes a reached `History` in two separate ways. `InfiniteContinuation` carries
actual `CommittedStep` evidence at every edge for the same occurrence, record and
realization. `historyAt` recursively extends the exact supplied root history;
it does not choose unrelated histories for later points. `FixedCut` adds the
premise that all accepted counts remain at the reached cut, from which
`FixedCut.output_empty` proves each publication is empty.

`StalledNonresponse` instead takes only a selected observation relation and
evidence at the exact reached realization, call, record, state and accepted
count. It needs no further action or infinite continuation. Any supplied finite
history, including one at a full accepted cut, can serve as this endpoint when
the selected observation is also supplied. This does not assert that possible
reply transitions are disabled.

The relation is fixed by the consumer and receives the realization explicitly;
no default relation or physical witness is supplied. These types consume
conditional evidence rather than prove Windows nonresponse or protocol
permission. Reachability at every output cut, physical adequacy, conforming
return, and eventual stabilization of arbitrary infinite continuations remain
separate obligations. The fixed-cut result alone proves none of them.

[`Win32WriteFileNonresponse.lean`](../Tests/Platform/Win32WriteFileNonresponse.lean)
uses an explicitly synthetic identity relation over the existing reached quiet
history, rejects false and wrong-occurrence relations, and checks endpoint
construction from supplied evidence without any continuation. It does not
fabricate an infinite quiet execution from the fixture's single committed edge.

## External validation

Probe programs are to be authored in Grass and emitted through Hello World's
production PE entry/import/emitter path. The
[semantic probe cases](../Tests/Platform/Win32ProbeCases.lean) currently check
zero/partial/full successes, failure after zero/partial/full output, and rejected
excess counts, count/output disagreement and wrong bytes using the existing Lean
relations. They are not emitted programs. A thin host launcher may supply inherited
stdout fixtures and collect output; it must not replace the API test body or its
model predictions. The [checked PE container path](WINDOWS_PE.md) now has a
complete reader and exact decoded-record round trip. Binding authored Grass code,
static data and imports through that layout remains the dependency before native
Grass probe execution; validation uses that same production writer.

The [auxiliary native campaign](../probes/windows/README.md) builds an MSVC executable
and checks real pipe API outcomes against an independently written comparator.
It is neither a Grass-emitted artifact nor an extraction of the Lean relation.
The comparator's negative controls challenge its count and prefix checks; they
do not prove correspondence between that comparator and Lean.

The source authority is Microsoft's [WriteFile documentation](https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-writefile),
Parameters, Return value, Synchronization and File Position, and Pipes sections,
retrieved 2026-09-09; the reusable URL also appears in [REFERENCES.md](REFERENCES.md).
The allocation, loan, causal and prefix witnesses are Grass modelling choices.
Vendor documentation and native observations challenge their applicability;
neither establishes a kernel-checked physical-model correspondence.

## Checkpoint review, 2026-09-09

The memory-model task reviewed the temporary spatial and causal interfaces.
An independent Terra reviewer inspected the actual Lean/C/Python changes and
surrounding contracts, reran focused Lean elaboration, native probes, Python
compilation and link/whitespace checks, and reported no remaining blocker for
this conditional scope. Review added an explicit external dispatch obligation
and a discriminating complete-record wrong-case harness control.

The universal output theorem uses structural induction over every history
constructor, with the exact incremental publication law at each step. Its scope
does not assert existence or coverage of physical provider executions. Tests
construct a real handoff and quiet checked action and refute wrong occurrence,
uninitialized/substituted input, overlapping arguments, malformed publication,
cyclic graph and absent ordering-edge candidates. The provider-write negative
control checks the entire violation-class list is exactly `conflictingAccess`.

Validation passed: `lake build`, `lake build Tests`, `audit-trust.sh`,
`check-source-input.sh`, `check-spike-sources.sh`, `check-doc-links.sh`, and staged
`git diff --check`. The trust gate audited 75 named declarations and six executable
test modules, including its negative probes. Native validation on Windows build
26200 / Intel family 6 model 186 / MSVC 19.50.35724.0 passed five cases, three
comparator mutations and five timeout/schema controls. Generated binaries and
full environment/hash reports remain under `.lake/windows-probes`.
