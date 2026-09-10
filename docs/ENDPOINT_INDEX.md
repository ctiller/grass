# Finding spike implementations

Navigation snapshot inspected at `f3b69bfa`, 2026-09-09, informed by interviews
with `architecture` and `spikes`. This page routes readers to code and its owning
documents; it does not change their contracts or certify a milestone. Status
describes this revision unless a later inspected delivery or interview report is
explicitly named below.

Current navigation starts with the [cross-stack implementation matrix](#cross-stack-implementation-matrix)
at main `8fc533af`. All five spikes, platforms and targets proceed in parallel.
The older Hello sections below are checkpoint history: deleted fixture evidence
does not establish current implementation or public verification.

## Cross-stack implementation matrix

User direction: all five spikes and all selected platforms/targets proceed in
parallel, with unchanged precious specifications, shared checked mechanisms and
no bespoke program recipes or mock verification. This is capability coverage,
not a Cartesian product: CPU hosts and shader invocations differ; WASI does not
imply native Vulkan. WGSL is a shader language target, not a machine ISA.

Baseline `8fc533af`, supplemented by the owner reports below. **No spike has a
checked public source → verification → emission chain.** A component check applies
only to its named revision and scope, not a fresh full-baseline build. Work in
progress, assignments and authored design files are not checked implementations.
Alternate source syntax must be inherent to the target, not a changed precious spec.

| Spike / owner | Present component evidence | Missing implementation |
|---|---|---|
| [1 Hello](../Spikes/1_Hello_World/) / spikes | Reusable Win32/x86 components below; frontend reports checked generic source capture at `ea0368bc` (`Grass/Assembly/SourceInput.lean`, branch evidence) | Public certificate, general verification/synthesis and emission; deleted 24/14/16-edge fixtures do not count |
| [2 Sort](../Spikes/2_Sort/) / library | [Vec](../Grass/Std/Logical/Vec.lean), [Order](../Grass/Std/Logical/Order.lean) and shared grammar foundations retained | Stable sort, byte-line/order and descriptor representation; Windows input/heap APIs and full chain. Current generic sort transport work is in progress |
| [3 Gzip](../Spikes/3_Gzip/) / grammar | [Grammar](../Grass/Grammar/) typed/prefix/endian/canonical foundations, reviewed `2034833a`, integrated `fb960238`/`e7f6740b`; consumed by PE | No gzip/DEFLATE codec or compiled spike spec; input/heap APIs and full chain. Compression connection is in progress |
| [4 HTTP/2 server](../Spikes/4_Web_Server/) / process | [Process/Network](../Grass/Process/Network/), [Weave](../Grass/Process/Weave/) and [ByteFlow](../Grass/Process/ByteFlow/) transition, invariant and conservation foundations | HTTP/2/HPACK and `Std.Process.Network` surface, actual server/cancellation composition, socket/thread/time APIs and full chain; no server completion evidence |
| [5 Spinning cube](../Spikes/5_Spinning_Cube/) / vulkan | Authored source only for this endpoint; no checked Vulkan or shader artifact at the baseline | Window/callback/message loop, Vulkan lifecycle/device/sync/presentation, shader execution/refinement and full chain |

| Platform / owner | Checked component evidence | Missing / in progress |
|---|---|---|
| Windows / windows | [PE](../Grass/Artifact/PE/) parser/writer/layout and [Win32](../Grass/Platform/Win32/) preferred-base loader, import dispatch, GetStdHandle/WriteFile/ExitProcess, protocol loans and conditional raw return/Exit laws. Owner reports scoped 135 checks after cleanup; no fresh full pass claimed | APIs listed per spike, native/provider applicability and complete programs; wrapper removal exposed a direct-import build repair |
| Linux / linux | No Linux/ELF implementation in the baseline; no checked delta reported | Syscall model/probes and ELF64 parser/writer in progress; actual ISA trap, provider completion, loading and spike closure absent |
| WASI / wasi | No baseline implementation or passed WASI check reported | Preview1 `fd_write`/`proc_exit` decoder/import boundary in progress; provider accesses/results, terminal, artifact/runtime and spike connections absent |
| Bare metal / memory-model | No baseline platform module or checked endpoint evidence | Platform entry/runtime, I/O/terminal and source/artifact connections need concrete owner evidence |

| Target / owner | Checked component evidence | Missing / in progress |
|---|---|---|
| x86 / x86 | [CheckedStep](../Grass/ISA/X86/Execution/CheckedStep.lean) fetch/typed arithmetic, memory, branch, stack and CALL cases retained. Owner's `002c0b65` report: 555-job build, scoped axiom/trust/ledger checks passed | SYSCALL receipt and further spike instruction families; trap/interrupt/abort remain outside-profile, not native adequacy |
| AArch64 / aarch64 | No baseline implementation or checked delta reported | CBZ decode/control and SVC request slice in progress; fetch/exceptions, memory/platform and source connections absent |
| Wasm / wasm | Local `Grass/ISA/Wasm/Types.lean` build reported passed, **uncommitted**; no checked module artifact | Typed source-call/host invocation and WASI consumer in progress; encoding/execution and full spike connections absent |
| SPIR-V / spirv | No baseline implementation or checked shader artifact | Typed composite word/checker/transfer slice in progress; full module/entry/CFG/FP/storage/sync/provider connection absent |
| WGSL / spirv | No baseline implementation or checked shader artifact | Typed composite expression/checker/transfer slice in progress; shader validation/execution and provider/artifact connection absent |

Frontend's structural backend is currently x86/Win32 only. Branch `ea0368bc`
checks generic standalone declaration/range capture, not any spike's public
verification. The old certificate is stale; target-model/deadlock suppliers and
general verification remain open. Authored demand/liveness proofs stay outside
`VerifiedProgram`; they are not a required or optional lowering checklist.
Generic service-path and external-nonresponse support is checked in certificate
commit `07e176f7` (root reports 238 focused tests passed), with the Hello-specific
agency profile removed. Inspect `docs/WAIT_AGENCY_REFINEMENT.md` at that commit;
actual raw wait agency, deadlock and the public gate remain missing.
Use `git show <commit>:<path>` for branch evidence. Owners report scoped checks;
this matrix neither upgrades them to whole-stack assurance nor reinstates deleted
fixtures. Architecture owns cross-target boundaries; spikes integrates evidence.

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
| Authored specification and selected demands | Captured.lean: `CapturedSpecification`, `withLiveness`, `withLiveness_preserves_complete`; CapturedDemands.lean | Captured console components exist; the unchanged public facade and author theorem package remain the requirements in the facade document | process |
| Exact source into image and loaded bytes | SourceImage.lean: `CodeSection`, `instruction_bound`; SourceLoadedImage.lean: `entry_rip_exact`, `code_byte_initialized` | Conditional source/image and preferred-base loader facts; not physical loader correspondence or full execution. See [Windows PE](WINDOWS_PE.md) and [loader initialization](WINDOWS_LOADER_INITIALIZATION.md) | spikes, windows |
| Fetched instructions and frame memory | [Execution](../Grass/ISA/X86/Execution/), LoadedCodeRoot.lean | Start with [exact Hello coverage](X86_HELLO_COVERAGE.md), [x86 execution](X86_EXECUTION.md), and [frame memory execution](FRAME_MEMORY_EXECUTION.md). Normal receipts have premises; they do not exclude every fault or establish a whole loop | x86, memory-model, lowering |
| Reached CALL into WriteFile custody | WriteFileCall.lean: `CallHandoff`; WriteFileHandoff.lean; WriteFileCallPlan.lean | Actual CALL receipt, saved return slot and ABI custody are connected conditionally. Import-symbol resolution and native provider identity remain separate; see [WriteFile model](WINDOWS_WRITEFILE.md) | windows |
| Provider publication, return and nonresponse | WriteFileReturn.lean, WriteFileNonresponse.lean, WriteFileProjection.lean: `history_prefix_exact` | Match the same request occurrence and actual caller history; publication and a return model alone do not prove the global output cut or whole program | windows, lowering |
| Infinite execution and caller waiting | WriteWaiting.lean, WriteWaitingGap.lean: `no_full_output_wait`, `full_output_wait` | The latter records a mismatch witness, not complete-history coverage. The raw infinite-execution to caller-waiting connection still needs endpoint evidence | process, lowering |
| Whole execution and final emission certificate | ExecutionState.lean: `State`; [VerifiedProgram.lean](../Grass/Verify/VerifiedProgram.lean) | The Windows state is a carrier, not a proof that an instruction, provider transition or terminal run occurred. Locate a concrete whole-execution connection before claiming the authored endpoint closes | architecture, lowering; spikes integrates |

For ownership details and recorded reviews, use
[SPIKE1_BOUNDARY_REVIEW.md](SPIKE1_BOUNDARY_REVIEW.md). For unwind requirements,
use [HELLO_UNWIND_BOUNDARY.md](HELLO_UNWIND_BOUNDARY.md). These documents retain
their own status labels; a reviewed direction is not an implemented declaration.

## Issued-call resume status

Historical snapshot: main `a3b4ed9a` and certificate `2b160c4d`.
The Hello prefix template, partial-source gate, and program-specific static/count
and loop/guard adapters described below have since been deleted. They are not
current implementation evidence. See the approved
[removal plan](HELLO_SPECIALIZATION_REMOVAL.md); general full-source verification
and emission remain incomplete. The following records the retired checkpoint.
The retained **24-edge loader-rooted Hello prefix reaches the first WriteFile
entry**. This replaces the earlier missing-initial-prefix status; it is one
checked finite execution, not whole-Hello or public-emission acceptance.
The same authored-source fixture now also retains NULL (14 edges) and INVALID
(16 edges) runs ending at terminal status 1. Spikes reports the full frontend
gate passed; these selected executions do not establish all-run coverage.

| Find | Implemented connection at this snapshot | Remaining boundary |
|---|---|---|
| Hello entry prefix | Certificate `Tests/Frontend/WriteFilePrefix.lean.in`: `Result machineSource stdout`, `inspected`; `Tests/Frontend/check.sh` injects the unchanged authored source and retains the actual `ExecutionPrefix` through GetStdHandle entry/return to first WriteFile entry or the selected sentinel's terminal path | Provider registers are observed inputs and the graph is empty; this fixture does not establish native/causal correspondence, all runs or the certificate suffix |
| Incoming WriteFile arguments | Certificate `Grass/Refinement/Console/WriteFileStaticEntry.lean` composes canonical static buffer/count arguments with the actual CALL and existing checked preparation; count placement uses the original runtime frame | The [incoming-state contract](PLATFORM_ABI.md#incoming-state-contract) requires exact provenance, range, memory and CALL binding, not an executed LEA or another prescribed register recipe |
| Installed returns | RawStep.lean: `getStdHandleReturn`, `writeFileReturn`; GetStdHandleRawReturn, WriteFileRawReturn | The derivation fixes one image, console environment, realization and return interpretation; observed results and the original provider-history connection remain real premises |
| Shared finalization | Both actual return consumers use ProviderResumeFinalization for final state, exact runtime/pending consumption, logs and replay rejection | Dual production adoption is closed; it does not establish native provider identity, full ABI applicability or physical return |
| Completed Exit | ExitProcessCompletion: `complete?`; `RawStep.completedExit`, `exit_result`, `terminal_no_step` | Exact observed process/call/status is checked and archived data cannot enable another raw edge; no native cleanup or blanket obligation discharge follows |
| Finite service/history transport | RawPrefixSteps: `finitePrefix_indexed_witnesses`; RawPendingService: `pending_to_pending_service`; WriteFileReturnHistory: `returnedAfterService` | Extracts actual finite witnesses and same-call pending service edges, then transports matched return to the constructed service history. Connecting the contiguous segment to its original entry in the enclosing execution is still underway |

Certificate-only paths above can be inspected with
`git show 2b160c4d:<path>`. The prefix now uses canonical
Raw.system, its computed loader root,
terminal call/status projection and admission of all pointwise actual infinite
runs. Existing execution interfaces are universe-generalized; the old finite-only
completion scaffolding has been replaced. A faithful wait boundary remains owed.
See [raw phase preservation](RAW_PHASE_PRESERVATION.md) for the exact local clauses
and their limits. In particular, a retained initial prefix does not by itself
supply every subsequent segment's original handoff or prove enabledness.

The canonical synchronization state now participates in
[Op.Step](../Grass/Op/Step.lean)'s conflict check. Actual call handoff and return
propagate the corresponding context frontiers. This fixes the previously
identified ordering omission; it does not complete the program proof.
Hello-specific integration is being removed under the approved
[specialization removal plan](HELLO_SPECIALIZATION_REMOVAL.md).

The next connection is the original-entry service segment and enclosing provider
history, followed by the remaining source/body and certificate composition.
The [selected agency and directed-waiting decision](SEMANTICS.md#selected-agency-and-directed-waiting)
was undelivered at this historical snapshot. Generic support is now checked at
`07e176f7` as recorded in the matrix; actual raw agency remains missing.
Raw deadlock preservation, external/native applicability and the public
`helloVerified`/`emitProgram` endpoint remain open. No spike is complete.
The authored programs and annotated source snapshots remain the acceptance surface.

### Approved semantic correction and relative gate

The [observed process-exit decision](OBLIGATIONS.md#observed-process-exit) requires
exact process/call/status checking, inert terminal archives and rejection of every
subsequent `RawStep`. Exit discharges a duty only under its owning protocol's exact
law; it implies neither empty inventories nor native cleanup. The neutral producer
and terminal no-step machinery are now installed as indexed above; concrete duty
accounting and the public endpoint are separate obligations.

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
no completion-existence field.

The subsequent user-approved direction makes **internal deadlock freedom a
baseline requirement**, alongside safety and specification matching. A closed,
stuck internal subset is disallowed even while unrelated work continues.
Permitted external waiting and intended idle remain valid; termination, starvation
freedom and environment responsiveness are separate requirements. This supersedes
the earlier research-only policy status. A composition theorem and lowering
preservation, including introduced locks, channels and callbacks, are still owed.
Neither this theorem nor its gate integration is implemented by the checkpoints
above; the existing `Complete` classification does not establish this requirement.

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
RawStep.lean, with a
direct consumer fixture (since removed from `Tests/` along with the rest of
its internal-only coverage; see `git show 0159cb87:Tests/Platform/Win32RawStep.lean`).
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
