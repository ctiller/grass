# Finding the spike endpoint

Navigation snapshot inspected at `f3b69bfa`, 2026-09-09, informed by interviews
with `architecture` and `spikes`. This page routes readers to code and its owning
documents; it does not change their contracts or certify a milestone. Status
describes this revision unless a later inspected delivery or interview report is
explicitly named below.

Latest mechanical connection update: [issued-call resume status](#issued-call-resume-status),
covering `98b9147e`, `ba7b01ec`, `5be3f92e` and `4141cb7f`. Earlier delivery sections explain
the retained carrier, service, dispatch and checked-CPU boundaries.

## Start from the authored output

[Hello Program.lean](../Spikes/1_Hello_World/Program.lean) ends in
`helloVerified : VerifiedProgram spec` and `bytes := emitProgram helloVerified`.
Those are the acceptance surface, still outside the default library build.
Read the paired [annotated spike](SPIKE_1.md) and
[facade boundary](HELLO_FACADE_BOUNDARY.md) for the required connection.
The [spike source index](../Spikes/README.md) routes to all five authored programs.
Spikes reported no completed spike in the 2026-09-09 interview.

The existing [VerifiedProgram implementation](../Grass/Verify/VerifiedProgram.lean)
provides the stratified certificate and `emitProgram`; `loadedBehavior_exact`
connects its selected writer to its modeled artifact behavior. This generic
theorem is not a concrete `helloVerified` construction. The target contract is
owned by [VERIFIED_PROGRAM.md](VERIFIED_PROGRAM.md), while
[HELLO_FACADE_BOUNDARY.md](HELLO_FACADE_BOUNDARY.md) describes the required root
migration. Read the premise types before treating a component theorem as an
endpoint proof.

Architecture confirms that the certificate-root effort owns migration from the
old five-tier gate to the resource-indexed specification and a fixed-target
`RealizationCertificate`, preserving authored `VerifiedProgram spec` and
`emitProgram` syntax. The exact public target-selection type is still being
designed. Missing `Grass.Emit` is therefore more than an import gap. The facade
document's migration section prohibits adapting the new root back through old
finite `accepts` and freely selected `ProgramBehavior`.

## Follow the connections

| Connection | Code to inspect in this checkout | Evidence boundary and next connection | Author to ask |
|---|---|---|---|
| Authored specification and selected demands | [Captured.lean](../Grass/Console/Captured.lean): `CapturedSpecification`, `withLiveness`, `withLiveness_preserves_complete`; [CapturedDemands.lean](../Grass/Console/CapturedDemands.lean) | Captured console components exist; the unchanged public facade and author theorem package remain the requirements in the facade document | process |
| Exact source into image and loaded bytes | [SourceImage.lean](../Grass/Assembly/SourceImage.lean): `CodeSection`, `instruction_bound`; [SourceLoadedImage.lean](../Grass/Assembly/SourceLoadedImage.lean): `entry_rip_exact`, `code_byte_initialized` | Conditional source/image and preferred-base loader facts; not physical loader correspondence or full execution. See [Windows PE](WINDOWS_PE.md) and [loader initialization](WINDOWS_LOADER_INITIALIZATION.md) | spikes, windows |
| Fetched instructions and frame memory | [Execution](../Grass/ISA/X86/Execution/), [LoadedCodeRoot.lean](../Grass/Assembly/LoadedCodeRoot.lean), [loader fixture](../Tests/Platform/Win32LoaderEntry.lean) | Start with [exact Hello coverage](X86_HELLO_COVERAGE.md), [x86 execution](X86_EXECUTION.md), and [frame memory execution](FRAME_MEMORY_EXECUTION.md). Normal receipts have premises; they do not exclude every fault or establish a whole loop | x86, memory-model, lowering |
| Reached CALL into WriteFile custody | [WriteFileCall.lean](../Grass/Platform/Win32/WriteFileCall.lean): `CallHandoff`; [WriteFileHandoff.lean](../Grass/Platform/Win32/WriteFileHandoff.lean); [WriteFileCallPlan.lean](../Grass/Platform/Win32/WriteFileCallPlan.lean) | Actual CALL receipt, saved return slot and ABI custody are connected conditionally. Import-symbol resolution and native provider identity remain separate; see [WriteFile model](WINDOWS_WRITEFILE.md) | windows |
| Provider publication, return and nonresponse | [WriteFileReturn.lean](../Grass/Platform/Win32/WriteFileReturn.lean), [WriteFileNonresponse.lean](../Grass/Platform/Win32/WriteFileNonresponse.lean), [WriteFileProjection.lean](../Grass/Refinement/Console/WriteFileProjection.lean): `history_prefix_exact` | Match the same request occurrence and actual caller history; publication and a return model alone do not prove the global output cut or whole program | windows, lowering |
| Infinite execution and caller waiting | [WriteWaiting.lean](../Grass/Refinement/Console/WriteWaiting.lean), [WriteWaitingGap.lean](../Grass/Refinement/Console/WriteWaitingGap.lean): `no_full_output_wait`, `full_output_wait` | The latter records a mismatch witness, not complete-history coverage. The raw infinite-execution to caller-waiting connection still needs endpoint evidence | process, lowering |
| Whole execution and final emission certificate | [ExecutionState.lean](../Grass/Platform/Win32/ExecutionState.lean): `State`; [VerifiedProgram.lean](../Grass/Verify/VerifiedProgram.lean) | The Windows state is a carrier, not a proof that an instruction, provider transition or terminal run occurred. Locate a concrete whole-execution connection before claiming the authored endpoint closes | architecture, lowering; spikes integrates |

For ownership details and recorded reviews, use
[SPIKE1_BOUNDARY_REVIEW.md](SPIKE1_BOUNDARY_REVIEW.md). For unwind requirements,
use [HELLO_UNWIND_BOUNDARY.md](HELLO_UNWIND_BOUNDARY.md). These documents retain
their own status labels; a reviewed direction is not an implemented declaration.

## Issued-call resume status

Inspected source at `31ad186e`, 2026-09-09. The following are bounded mechanical
connections, not whole-spike completion. Initial linkage and finite service
history are no longer merely extra premises for consumers rooted in these
actual handoff witnesses:

| Connection | Implemented evidence | Boundary still to connect |
|---|---|---|
| Shared checked protocol entry, `5be3f92e` | [ProtocolEntry.lean](../Grass/Platform/Win32/ProtocolEntry.lean): `Entry`, `issue?` and general projection, pending-record, freshness and storage laws. Both [GetStdHandleRuntime](../Grass/Platform/Win32/GetStdHandleRuntime.lean) and [WriteFileHandoff](../Grass/Platform/Win32/WriteFileHandoff.lean) use it through their actual entry producers; duplicated entry construction was removed | API-specific requests, loans and observations remain distinct; this is not a native provider or endpoint certificate |
| Original CALL and initial resume inputs, `98b9147e` | [CallResumeBinding.lean](../Grass/Platform/Win32/CallResumeBinding.lean): both APIs' `CallHandoff.resumeInputs` derive `ProviderResume.PolicyBinding` and `Link` from the same actual CALL, reached plan and computed runtime insertion | Initial linkage does not establish a later return or provider transfer |
| Finite WriteFile service history, `ba7b01ec` | [CallResumeHistory.lean](../Grass/Platform/Win32/CallResumeHistory.lean): `WriteFile.CallHandoff.resumeInputsAfterService` starts at that issued CALL's `rawAfter`, follows the supplied finite same-call `providerService` edges, and derives the original frame link, whole metadata/pending-record agreement, fifth slot and loan plan at the endpoint | It does not include settlement, return-slot read, resumed caller execution, arbitrary non-service edges or infinite-history coverage |

The generic `ProviderResume.Link` remains a data-agreement proposition. These
new consumers derive its relevant issuance/history connection; equal frame
coordinates alone still do not establish that connection for an arbitrary
supplied `Link`.

The separately inspected lowering delivery `4141cb7f` connects **same-issued-CALL
finite history → matched settlement → computed slot read → raw BOOL guard →
source body**, conditionally. Inspect it with
`git show 4141cb7f:Grass/Refinement/Console/WriteFileResume.lean`, theorem
`returned_body`. It transports the original pre-CALL cursor, derives the original
frame, preserves R12/RSP and settled memory, and connects the source load's exact
range and provenance. It still consumes `requestSlot` equating the request's
count slot with `SourceLea.argument`, actual provider BOOL/GPR evidence,
`resumeRan`, the original pre-CALL cursor, and checked guard/body execution
witnesses (including successful BOOL and positive count). It does not install a
raw return edge, restore raw caller control, consume runtime state or establish
physical transfer. Spikes reports integration as `38536c7e`.

[ProviderResume.lean](../Grass/Platform/Win32/ProviderResume.lean)
computes the checked slot read and resume candidate under the original CALL's
policy. Its `resume` still consumes actual reached-state
`PreservesNonvolatile` evidence, and `WriteFileOutput` relates the actual low
32 bits of RAX to the raw BOOL. Neither deriving `PolicyBinding` nor preserving
the frame manufactures those provider observations. The modeled GPR table does
not cover XMM, MXCSR, x87 control state or direction-flag adequacy. Matched
return still needs actual `CallProtocol.return?` settlement with the full
recorded loan IDs; `MatchedReturn.effects` and `consumed` are existing
conditional laws for that evidence. The composition consumes the checked
candidate and source execution witnesses; producing those at the actual endpoint,
including exact-stage slot-read permission and physical provider-transfer
correspondence, remains an obligation. No fetched native RET is claimed.

Windows reports the request/count-slot producer is newly authorized, not yet
implemented or named. [WriteFileArguments.lean](../Grass/Platform/Win32/WriteFileArguments.lean)
(`Request`, `Resolved`, `Prepared`) and
[WriteFileAbi.lean](../Grass/Platform/Win32/WriteFileAbi.lean) (`Abi.Entry`) currently
provide evidence types. The proposed producer starts from the reached post-CALL
state plus canonical provenance-carrying buffer/count arguments, bytes and
fifth slot. It derives the handle from RCX and requested count from the low 32 bits of R8,
checks RDX/R9/stack correspondence, and never reconstructs count provenance from
R9 alone. Existing
[WriteFileStackPlan.lean](../Grass/Platform/Win32/WriteFileStackPlan.lean)
`Abi.StackPlanFactory.deriveLoaded?` consumes an already supplied `Entry` and
derives the shared ReturnHome plan plus WriteFile extensions; it does not fill
that missing request/entry-production step.

The structured Hello fixture at the inspected `31ad186e` had a trust-gate
setup-extraction defect, so that checkpoint is not acceptance evidence.
The repair is integrated as `d7c63bab`, with independent review, the 595-job
root build, and the trust audit of 75 declarations and 8 executable test modules
passing. Source freshness passed for 22 embedding modules. This fixture does not
establish whole Hello.

### Approved semantic correction and relative gate

Process and architecture confirm the latest user-approved boundary: “on error”
is conditional, so an infallible implementation can satisfy that contract.
Generic implementation conformance covers **every actual history, result,
completion and wait**; it does not require producing every abstractly permitted
error. Exact presentation/denotation equivalence remains a separate relation,
and explicitly authored availability and progress requirements remain obligations.
An API implementing a concept is a recorded external correspondence claim, not
a proof of Windows internals. Preserve actual diagnostic causes.

The optional-outcome machinery is stopped; no optional-outcome flags or framework
follow from this decision. Older symmetric back-coverage counterexamples diagnose
an overstrong implementation interface, not an obligation to manufacture errors.
Process's generic relation is delivered as `36ebd13c`, integrated on the
certificate branch as `04b8e23f`: `Grass/Refinement/ImplementationConformance.lean`
defines `DirectedWaitTranslation`, `ImplementationConformance` and the exact-to-directed
adapters `DirectedWaitTranslation.ofExact` and
`BehaviorCorrespondence.toImplementationConformance`. Architecture's relative
gate change `ab646796`, integrated as `6b784003`, uses the directed translation
in `RealizationProfile.waits` and directed conformance in
`RealizationCertificate.correspondence`. Exact artifact binding and admitted-input
entry/safety remain. Inspect these deliveries with `git show <commit>:<path>`;
the gate is in `Grass/Refinement/Realization.lean`.

Spikes reports the combined 245-job focused build and independent Sol review
passed. Expanded scoped audit checkpoint `a5a495f3` covers 2,009 declarations
in 26 modules, including `Realization`. These are **relative certificate
deliveries**, not whole-public-root or trust acceptance: the known legacy
`Grass.Certificate` migration failure remains. Matching covers actual histories,
replies and the existing classified terminal/infinite/wait completions; it adds
no completion-existence field. Internal deadlock classification remains separate
research, with no production policy adopted.

The decision record is available as
`git show 2ae59a56:docs/HELLO_ENDPOINT_MODEL.md`. Its earlier fixed-environment
signatures remain explicitly provisional; do not treat them as an accepted,
implemented complete-correspondence model. This note records the latest decision
without claiming the public verified-emission gate or the Hello endpoint has migrated.

## Deliveries beyond the initial snapshot

Spikes reported a loaded-Hello prologue fixture on main `87fa3e5b`, explicitly
short of full Hello, and relative certificate/loop work on
`codex/certificate-root` at `e8999100`. Those reports are search leads, not
evidence inspected for this page; their newer code is not represented by the
local links above. Use `git show <commit>:<path>` when that commit is available.

### Delivered raw carrier amendment

The scribe inspected these three files directly at architecture commit
`ed231774` on `codex/architecture-raw-execution`. Architecture reports root
consumption as `db6a58de`; that integration is not independently checked here.
They are not yet local files in this page's base revision:

```bash
git show ed231774:Grass/Platform/Win32/CallRuntime.lean
git show ed231774:Grass/Platform/Win32/RawState.lean
git show ed231774:Grass/Platform/Win32/RawStepSignature.lean
```

`CallRuntimeTable` is keyed by the actual `CallId`. `ReturnFrame` retains the
original return coordinates and the selected existing Win64 nonvolatile GPR
snapshot excluding RSP. This is not full Win64 register preservation; XMM and
control-state gaps remain.
`WriteFileRuntime` adds the fifth argument slot and accepted frontier, deriving
its loan plan from those coordinates. Request and loan identities stay in
protocol metadata. `RawState` carries one machine, metadata, control and the
runtime table. `RawState.checked?_raw` round-trips the checked view only with
the original `raw.calls` explicitly retained. `RuntimeLinked` checks matching
pending-call domains and request kinds, not original-call or ABI validity.

`Raw.StepSignature` is
`Graph → RawState → Choice → Event → RawState → Graph → Prop`.
It is a type; the partial implementation delivered later is indexed below.
`Event.Appends` relates edge suffixes to the existing logs; the graph stores
causal edges rather than a duplicate history. `EdgeAgreement` gives necessary
log/graph conditions, not sufficient evidence that an instruction or API ran.

Architecture owns the fixed raw-step composition; x86 owns CPU cases;
Windows owns WriteFile entry, service/initialization
and modeled return; the certificate-root effort owns the reusable provider
resume connection and delegated GetStdHandle/ExitProcess endpoints;
process owns caller normalization; lowering owns loop induction; spikes owns
integration and acceptance. The earlier three-field raw-state proposal is
superseded by this inspected carrier amendment. It is not a completed endpoint.

Provider resume connects the Windows opaque-provider contract to an actual
return-slot read. It does not model a physical RET through provider bytes:
unchanged Hello has no authored RET, and native correspondence remains open.

### Partial raw-step implementation

Inspected architecture delivery `dd4c85d1` on
`codex/architecture-raw-composition` supplies
[RawStep.lean](../Grass/Platform/Win32/RawStep.lean), with a
[direct consumer fixture](../Tests/Platform/Win32RawStep.lean).
`Raw.RawStep` fixes one loaded image and one `WriteFile.Realization` across a
derivation. Its four constructors are three combined actual-CALL/API-entry
cases (`writeFileEntry`, `getStdHandleEntry`, `exitProcessEntry`) and `service`.
This supersedes the signature-only implementation status, not the remaining
whole-execution obligations.

Each entry starts from the exact pre-CALL checked state and prior runtime table,
retains its actual CALL/handoff receipt, and computes the corresponding raw
result. `RawStep.agreement` exposes the event-log suffix and graph obligations
of every installed case. Entry graph constraints are only `EdgeAgreement` at
this delivery; they do not establish the stronger provider causal realization.

The service case retains the committed receipt, actual output, resulting runtime
and exact event kind: empty output is internal; nonempty output is publication
for that call. `Graph.Realizes` equates the selected provider causal order with
the raw graph's transitive closure at the before and after protocol states.
`RawStep.service_receipt` inverts the service choice to recover its record,
action-indexed receipt, output, exact after-state, event kind and both causal
closure facts. The fixture constructs a five-loan quiet service edge and rejects
a wrong observation; it is model evidence, not native reachability or adequacy.

The relation is a partial union, not a public `BehaviorModel`, realization
profile, or exhaustive Windows execution model. At `dd4c85d1`, dispatch
strengthening and CPU/refusal/return/terminal cases were still outstanding;
the later dispatch delivery is described below. In particular,
`exitProcessEntry` is an entry case, not proof of
terminal observation. The supplied realization remains fixed across the
derivation; graph agreement does not discharge native correspondence.

### Computed entry dispatch binding

Inspected architecture delivery `d83bdca1` strengthens all three entry
constructors in `Grass/Platform/Win32/RawStep.lean`. Each now requires successful
`ApiDispatch.select?` at the **same actual CALL** effective address
(`fallthroughRip + displacement`) and target value read by its `CallNormal`
receipt. The selected binding's `MatchesRequest` must match the API constructor
in that entry choice; request payload correctness remains with the endpoint
model. An independently supplied API label is no longer sufficient.

`RawStep.entry_binding` inverts an entry choice to expose an address, target and
binding, its successful computed selection, and matching request. The precise
ties to the CALL receipt reside in the entry constructors; the inversion's
existential conclusion does not separately return that receipt. Existing
service cases and `service_receipt` inversion are unchanged by this delta.

Use `git show d83bdca1:Grass/Platform/Win32/RawStep.lean` and
`git show d83bdca1:Grass/Platform/Win32/ApiDispatch.lean` for the exact inspected
implementation. This is logical dispatch from the loaded import layout, not
native DLL/export adequacy. At that delivery, CPU, refusal, provider-resume and
terminal cases, plus exhaustive public-profile coverage, remained outstanding;
the later CPU delivery is described below. Entry `EdgeAgreement` has not gained the service case's
stronger causal-realization premises.

### Checked CPU execution and CALL provenance

Inspected architecture delivery `0159cb87` adds `EvaluatedCall` to all three
API-entry constructors. It retains the selected `Cpu.policy?`, an actual
`CheckedExecution.normal` result of `some (.ok (.call success))`, and `HEq`
between that success's receipt and the same handoff receipt. A standalone CALL
receipt no longer suffices without this evaluator provenance.

Three new CPU constructors retain actual checked evaluation:

| Case | Required result and retained evidence |
|---|---|
| `cpuCompleted` | Normal evaluation succeeds with the exact `.completed` outcome; CALL is excluded from this case and enters through the API-entry constructors |
| `cpuFailure` | Normal evaluation returns a full typed `CheckedExecution.Failure`, whose mapped outcome supplies the reached state; the event retains `.checked failure`, not only its projected reason |
| `cpuUncovered` | An explicitly non-normal choice evaluates to the exact outside-profile reached state and reason |

All three CPU cases require caller control at the selected policy's context and
retain `EdgeAgreement`. Their result uses `RawState.withMachine`, preserving
the original metadata, control and runtime table even if the reached metadata
cannot pack into the checked protocol view. A refusal diagnostic does not
become a successful physical execution by being retained.

`RawStep.cpu_checked` exposes the selected policy, caller context, checked
evaluator outcome and exact `withMachine` after-state. `RawStep.cpu_rejected`
excludes a CPU edge when evaluation under the selected policy returns `none`;
it does not classify a failure to select a policy. The direct fixture proves
that CALL is not plain completion and constructs an uncovered CPU edge retaining
a failed protocol view and the original runtime table.

Inspect `git show 0159cb87:Grass/Platform/Win32/RawStep.lean`,
`git show 0159cb87:Grass/Platform/Win32/RawStepSignature.lean`, and
`git show 0159cb87:Tests/Platform/Win32RawStep.lean` for this delivery.
Service and its inversion are unchanged. This remains a partial relation,
not a public profile or physical-adequacy theorem: policy-selection failure,
provider refusal, provider-resume/return, terminal observation and exhaustive
coverage are still outstanding at this revision.

## Find a symbol without another inventory

From the repository root:

```bash
rg -n 'helloVerified|emitProgram' Spikes Grass Tests
rg -n 'CallHandoff|history_prefix_exact|no_full_output_wait' Grass Tests
rg --files Grass Tests
```

Use [MODULES.md](MODULES.md) for intended dependency direction, not a promise
that every proposed path exists. Prefer the narrow defining module and its
consumer fixtures over importing the empty `Grass.lean` root. Checks are indexed
by purpose in [CHECKS.md](CHECKS.md).

When a connection lands, update its evidence boundary from the actual declaration
and consumer, folding superseded branch leads into that row. Missing rationale
goes to the named author; routine links and status transcription can go to the
scribe. This is navigation maintenance, not an additional delivery gate.
