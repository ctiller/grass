# Bounded Windows provider evidence

Navigation and supplier snapshot: 2026-09-09, root `1f345e74`, covering Windows
commits `69b72597`, `82cd03ac` and `c0b85ae3`. These supply conditional receipts,
not native export identity, native return correspondence, a complete raw
transition relation, or the Hello certificate. For the whole-program connection,
start at [the facade boundary](HELLO_FACADE_BOUNDARY.md) and
[corpus index](README.md).

## Find the call-to-service boundary

| Need | Defining module and useful declarations |
|---|---|
| Keep all Windows API occurrences in one protocol state | [ApiRequest.lean](../Grass/Platform/Win32/ApiRequest.lean): `ApiRequest`, `ProtocolState`, `embedPending`, `selectPending` |
| Resolve the semantic input/count arguments | [WriteFileArguments.lean](../Grass/Platform/Win32/WriteFileArguments.lean): `Request`, `Prepared` |
| Fix semantic and ABI custody together | [WriteFileCallPlan.lean](../Grass/Platform/Win32/WriteFileCallPlan.lean): `LoanPlan.requests`, `Abi.StackPlan.loanPlan` |
| Issue and retain the exact full batch | [WriteFileHandoff.lean](../Grass/Platform/Win32/WriteFileHandoff.lean): `EntryHandoff.recorded`, `pendingAt`, `initialPrefix` |
| Connect an actual CALL and selected Windows policy | [WriteFileCall.lean](../Grass/Platform/Win32/WriteFileCall.lean): `CallPolicy.ofFactory`, `reachedCall?`, `CallHandoff` |
| Preserve protected storage and actual CALL-saved bytes | [WriteFilePreservation.lean](../Grass/Platform/Win32/WriteFilePreservation.lean), [WriteFileCallPreservation.lean](../Grass/Platform/Win32/WriteFileCallPreservation.lean): `Abi.CallNormal.saved_return_cell_preserved_after_return` |
| Initialize runtime from the reached call | [WriteFileRuntime.lean](../Grass/Platform/Win32/WriteFileRuntime.lean): `CallHandoff.runtime`, `rawAfter`, `runtime_restoredRsp` |
| Continue the same accepted frontier | [WriteFileService.lean](../Grass/Platform/Win32/WriteFileService.lean): `ServiceReceipt`, `after`, `frontier_continuity`, `ServiceEdge` |
| Find raw carrier and edge-signature ownership | [CallRuntime.lean](../Grass/Platform/Win32/CallRuntime.lean), [RawState.lean](../Grass/Platform/Win32/RawState.lean), [RawStepSignature.lean](../Grass/Platform/Win32/RawStepSignature.lean); architecture owns their shared boundary |

`ProtocolState` is the full `CallProtocol.State ApiRequest`, including
GetStdHandle, WriteFile and ExitProcess occurrences. Selecting a WriteFile view
retains the original pending record and loan identities; it does not rebuild a
WriteFile-only table. `LoanPlan.requests` appends ABI custody to the semantic
buffer/count requests. `Abi.StackPlan.loanPlan` fixes the additional return-slot,
writable home-space and fifth-argument loans. The resulting five-loan batch is
issued under the actual `CallId`; any matched return must use that same `CallId`
and the full recorded ID list.
History and service retain that fixed plan rather than choosing another at each
frontier.

`CallPolicy.ofFactory` derives its binding from the actual checked CALL factory
receipt. `reachedCall?` repacks the original metadata against the reached
machine; a failed check stays a refusal, without resetting pending calls or
identity supplies. `CallHandoff` binds the continuation and saved slot to that
CALL before the full handoff. The preservation lemmas trace initialized return
bytes from the actual CALL store through permitted provider writes and modeled
loan return. They do not execute a physical RET or identify a native export.

`CallHandoff.rawAfter` updates an explicitly supplied prior runtime table at the
new call identity. It retains the original return coordinates, saved GPR
snapshot and fifth slot, starting accepted output at zero. `ServiceReceipt`
looks up that exact call, checks the pending control and protocol projection,
and reads its pre-frontier and loan plan from the runtime entry. `rawAfter` is
only a computed table update: fresh-key, `RuntimeLinked` and original-issuance
invariants still need proof at the actual raw-entry boundary; `c0b85ae3` does
not supply that connection. The service receipt's `after` is
computed from the committed action; only the accepted runtime field changes.
Other calls, immutable return data and the whole protocol metadata are preserved.
`frontier_continuity` proves consecutive accepted counts and loan plans agree.

That continuity theorem does **not** equate whole `Prefix` values. A prefix
contains `Prepared` data in `Type`, including resolved argument witnesses;
matching counts, state and plan does not supply equality of those witnesses.
Consumers needing exact prefix identity must retain or establish that connection
explicitly rather than use proof irrelevance for the entire record.

The raw carrier and `Raw.StepSignature` do not themselves install a transition
relation. Factory failures and applicability diagnostics remain distinguishable
from successful receipts or physical outcomes; see the typed failures in
`Raw.Failure` and the underlying factories. A service receipt remains conditional
on the selected `Realization`, not exhaustive raw-step or provider adequacy.

## Conditional prefix evidence

[`WriteFile.lean`](../Grass/Platform/Win32/WriteFile.lean) supplies a conditional
pending-prefix evidence layer for the synchronous Hello World provider. It does
not implement a Win32 provider, discharge physical ABI applicability, or extend
the common memory checker with happens-before.

The request carries buffer/count-slot provenance and actual input bytes. Every
frontier uses the shared state-bound resolver for both arguments, including their
live CPU allocation, provenance, backing identity, origin and bounded range. It
requires initialized input and the temporary dedicated-backing profile. Windows
separately requires nonwrapping placement and physical separation of distinct live
CPU allocations; abstract backing identities do not prove physical separation.
The count slot and input range must be disjoint even within one allocation.

`History` starts at an actual `CallProtocol.handoff?` with zero accepted bytes and
a valid causal graph. Each extension retains the same pending occurrence and exact
loans, an actual checked step, clean audit, preserved obligations and metadata,
confined writes and event footprints under the fixed semantic-plus-ABI loan plan. Published
bytes are the next suffix segment; their concatenation equals the new cumulative
input prefix. Issuing a loan does not initialize the count slot.

The fixed `Realization` remains an external semantic parameter. In particular,
generic `step?` identifies an agent, not the API occurrence that caused its action.
`executesFor` must connect physical dispatch to that occurrence; sharing an agent
identity is insufficient. Causal graph shape and extension do not establish
Windows/ISA ordering soundness, and `publishes` still needs a connection to the
selected provider-accepted-byte observation. There is no default realization or
proof that these external premises cover all Windows executions. Synchronous
handle rights/mode/lifetime, native argument/provider applicability, return and failure correspondence,
physical permanent-wait interpretation and violation envelopes remain downstream
work. The modeled return boundary below supplies conditional return evidence;
it does not close those physical obligations.

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

## Matched return and caller continuation

The [matched-return consumer](../Grass/Platform/Win32/WriteFileReturn.lean)
requires a reached `History`, the exact successful `CallProtocol.return?`, and
explicit physical result correspondence. It preserves the raw 32-bit BOOL:
any nonzero value requires an initialized little-endian DWORD at the count slot,
equal to the accepted prefix length and bounded by the request. False exposes
no trusted count and does not constrain already accepted output. Zero-byte
success remains possible. Typed result failure here means a zero BOOL with no
trusted count; it does not provide a Windows error-code/GetLastError model.
These observations do not execute a caller read.

Return ordering uses the same graph and the exact event suffix derived from
this history's committed edges. Actual protocol effects remove the pending
occurrence and its entire recorded loan batch, including ABI additions, reject
replay and preserve the count observation across
bookkeeping. A separately supplied caller continuation must execute the actual
generic checker and extend that graph. The model does not assert that a return
or caller continuation exists, and graph evidence never bypasses access checks.
Return transport preserves both allocation mappings and backing storage exactly.
These equalities are derived from the actual loan-return effects and preserve the
checked count-slot bytes and their initialization.

Architecture and an independent Terra reviewer approved this conditional
return boundary. The [result fixtures](../Tests/Platform/Win32WriteFileReturn.lean)
cover non-one success, wrong counts and uninitialized slots. The
[matched fixture](../Tests/Platform/Win32MatchedReturn.lean) constructs an actual
handoff/return with a synthetic interpretation and rejects false interpretation
and absent return ordering. Neither fixture asserts physical Windows behavior.

The pending provider-resume connection must combine an actual return-slot read
with fixed endpoint correspondence for the opaque-provider contract. A frame
and read alone do not establish completed control transfer. A modeled full-batch
return is not a physical RET through provider bytes; unchanged Hello contains no
authored RET. The certificate-root effort owns the reusable connection, with
native correspondence still open. In the candidate reviewed by Windows, choosing
policy from the current opaque-provider RIP could spuriously refuse an address
outside the image; reuse of the original CALL policy was the correction under
review, not a completed result at this snapshot.

## Model regressions and external validation

[Win32ApiRequest.lean](../Tests/Platform/Win32ApiRequest.lean) exercises mixed API
occurrences and full-batch custody. The
[service fixture](../Tests/Platform/Win32WriteFileService.lean) exercises five
loans and two consecutive quiet service actions. These are model regressions;
they do not establish native dispatch, provider progress or full Hello execution.
Existing contributor checks are in [CONTRIBUTING.md](../CONTRIBUTING.md).

Probe programs are to be authored in Grass and emitted through Hello World's
production PE entry/import/emitter path. The
[semantic probe cases](../Tests/Platform/Win32ProbeCases.lean) currently check
zero/partial/full successes, failure after zero/partial/full output, and rejected
excess counts, count/output disagreement and wrong bytes using the existing Lean
relations. They are not emitted programs. A thin host launcher may supply inherited
stdout fixtures and collect output; it must not replace the API test body or its
model predictions. The [checked PE container path](WINDOWS_PE.md) now has a
complete reader and exact decoded-record round trip. Native Grass probe execution
must use the corresponding authored code, static data and imports through that
production writer; a container round trip alone does not validate the API body.
This documentation update starts no new native campaign.

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

## Historical prefix checkpoint review, 2026-09-09

The following records the earlier prefix campaign, not validation of the newer
call/runtime suppliers indexed above. Its counts and observed outcomes belong to
that campaign.

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
