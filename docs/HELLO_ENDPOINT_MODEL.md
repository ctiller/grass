# Concrete Win10 console endpoint proposal

Architecture proposal to spikes, 2026-09-09. The directed implementation boundary
is integrated in the certificate checkout (process `04b8e23f`, relative gate
`6b784003`). This document records the next bounded implementation scope; it
claims neither a complete console endpoint nor public verified emission.

Exact presentation/denotation equivalence remains separate from directed
implementation conformance. Every actual implementation behavior must conform;
an abstract error alternative need not occur. API-to-concept correspondence is
an explicit external claim. Authored availability and progress are separate
obligations. No optional-outcome modality or arbitrary theorem transfer is added.

This consolidated document replaces the historical fixed-environment/back-coverage
proposal developed through architecture commit `edc5ea7c`. Its earlier toy choice
experiment is historical context, not a dependency or a Hello proof.

## Concrete directed endpoint proposal

Architecture proposal to spikes, after integration of the directed gate.
Names in this section denote proposed responsibilities, not existing APIs.
Architecture owns the boundary decision and this document; Windows owns provider
semantics and adapters; process owns the behavior model and conformance laws;
spikes owns sequencing and the final fixed target profile. Implement after the
Windows after-prepare checkpoint, without a competing return wrapper.

The smallest useful addition is a concrete `ConsoleEnvironment` state and one
fixed provider transition relation. Its data records process identity, current
standard-handle entries, handle-to-route bindings with lifetime identity, the
exact issued occurrence, accepted output, and pending/completed exit status.
Reuse existing identity types where available; an epoch is needed only where
reuse or mutation requires it. Fields cannot accept arbitrary execution,
publication, return-interpretation, or observation predicates. Instead derive
the existing `WriteFile.Realization` and return interpretation from this one
relation. Keep the same relation across the whole reached history.

The proposed endpoint has three semantic edges, each tied to an actual
checked raw endpoint and its complete pending record:

| Edge | Concrete evidence retained | Authored observation |
|---|---|---|
| GetStd result | Actual selector, table observation, raw RAX, sentinel classification, same call's checked settlement/resume | Sentinel failure selects `stdoutUnavailable` at cut zero; a non-sentinel alone emits nothing and proves no route validity |
| Write provider/return | Request handle resolves at the actual operation to the selected stdout route; exact accepted suffix and causal memory steps; every raw BOOL bit; success count from the initialized slot | Publication advances the same payload cut; false selects `writeFailed`; zero success progress selects `noProgress` on a residual request; full accepted output and actual success path select `success` |
| Completed exit observation | Same process and issued ExitProcess occurrence, exact requested DWORD, actual completed observation, terminal resource disposition | Commit the already selected cause/cut and its corresponding status; invocation alone is not completion |

Use `WriteFile.Publication`, `ReturnResult.Conforms`, `History`,
`MatchedReturn`, and the current shared entry/settlement/resume laws directly.
False BOOL carries no trusted count and does not erase already accepted output.
The hello loop's executed branches establish the selected cause: equal public
status values do not permit exchanging diagnostic causes. No GetLastError value
is invented when the program never reads it. A non-sentinel invalid handle
follows the actual WriteFile failure path, not the GetStd sentinel branch.

The external claim is explicit: for the named Windows/ABI/loader profile and
recorded admitted environment, each native operation and observation is
represented by this fixed relation, including actual failures, output and
nonresponse. This is the API-to-console-concept claim recorded in the target's
TCB, not a new Lean axiom or a proof of Windows internals. Lean proves the
model's directed conformance and artifact connection. Native observations can
challenge the claim but cannot replace those proofs.

Spikes selected the first-profile applicability after reviewing this proposal:
null-OVERLAPPED operation, synchronous mode for resolved live-handle use, a fixed
selected stdout route, no concurrent close/reuse/redirection of the retained handle, and
no foreign or teardown output on the observed route. These conditions belong
in explicit artifact/profile admission and the recorded external claim, never
inferred from guest code or appended to the precious specification. Invalid,
absent or unresolved handle values remain admitted, including their actual
failure paths. A non-sentinel value establishes neither validity nor write
rights. Actual failures, partial writes and pending exit remain modeled.
If the profile cannot yet expose this applicability honestly, Windows delivers
data and edges only with admission still owed; it must not widen certificate
assumptions. The initial implementation is reusable data plus one actual GetStd
edge after Windows preparation, with model/test design sent to root review.

The preconditions and their limits are:

- Synchronous operation with null OVERLAPPED, suitable handle mode, actual
  buffer/count-slot validity and retained ownership. Existing checked loans
  supply memory obligations; they do not establish handle mode or route identity.
- Handle lifetime and route changes are either explicit environment transitions
  with revalidation at use, or excluded by a separately justified admission
  condition. GetStd's returned table value supplies neither stability nor
  writability. Do not infer either from absence of guest mutation instructions.
- The meaning of stdout is explicit: accepted bytes on the selected route,
  not device durability. Foreign or teardown output is represented or excluded
  by an explicit environment scope; it cannot vanish in the projection.
- Exit status is committed only by the completed observation. Pending exit is
  retained; responsiveness and termination remain separate authored demands.
  Successful writes or a nonreturning API signature imply neither.

Microsoft documents that GetStdHandle returns an unvalidated table value,
WriteFile has separate synchronous/asynchronous behavior and raw BOOL results,
and ExitProcess can deadlock during teardown. These constrain the external
claim; they do not supply the proposed route lifetime or output isolation
restrictions. Sources checked 2026-09-09:
[GetStdHandle](https://learn.microsoft.com/en-us/windows/console/getstdhandle),
[WriteFile](https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-writefile),
[ExitProcess](https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-exitprocess).

Process resolved the bounded representation direction. `WriteFile.InfiniteContinuation` can retain
an actual infinite sequence of committed provider steps. The authored console
system advances a bounded cut strictly, then reports and observes; there is no
obvious corresponding infinite transition sequence. Shared `CompleteMatch`
requires infinite-to-infinite matching. Directedness removes reverse error
coverage, not this requirement. Do not silently replace internal divergence by
a permanent wait, drop it in an observation quotient, or add a responsiveness
assumption. Keep shared conformance strict and place an explicit raw-to-caller
boundary interpretation before it. Provider-only activity at the same external
occurrence can represent caller nonresponse only with its actual raw run,
unchanged occurrence and complete publication history retained. Caller-internal
divergence remains infinite; positive publication advances the cut; every reply
and caller-control edge must be accounted for.

Process identifies `RawStep.service_suffix_continuation` and the existing
`Grass.Refinement.Console.WriteFileHistory.Aligned.eventually_fixedNonresponse`
(in `WriteFileEventualNonresponse.lean`) evidence as
support for the bounded provider-only, eventually fixed-cut case. They do not
classify arbitrary mixed raw runs. A raw `WaitBoundary` cannot mark naked
service steps as replies: its `step_reply` law covers every outgoing step.
The caller boundary must therefore be explicit, and every admitted raw execution
category needs a representation argument. Native API meaning can be recorded
at the external claim boundary; a claimed normalization theorem for Grass's raw
model still needs its own proof or explicitly recorded assumption. This is the
remaining implementation obligation, not a new infinite-to-waiting constructor.
Genuine external nonresponse and internal deadlock remain distinct questions.

Craig's subsequent policy decision makes internal deadlock freedom a baseline
requirement alongside safety and conformance: exclude a closed internally stuck
subset even when unrelated work continues. Explicit external waits and intended
idle states remain valid. The obligation needs a compositional proof and
preservation for resources introduced by lowering; it is not the old
`forall history, exists Complete` field. Termination, starvation freedom and
environment responsiveness remain separate. Process and memory own the shared
definition and proof substrate; the general theorem is not yet implemented.
Memory further requires the blocked-set test to respect actual AND/OR enabling
conditions, outside producers, cancellation, timeouts and release transitions.
Spinning or retry steps alone do not establish meaningful progress. Derive
dependencies from exact live participants and resource identities; ordinary
memory safety and loan invariants do not prove this obligation.

Acceptance requires one reached success path and adverse cases for absent or
invalid stdout, raw false BOOL after accepted output, zero progress, short
writes, pending exit, and wrong-route rejection. These exercise the concrete
model; universal conformance still covers every actual admitted behavior. The
third API should add only its semantic edge and external claim, using existing
mechanics rather than copying a proof stack. No DSL build is required.
