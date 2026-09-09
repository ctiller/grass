# Finding the spike endpoint

Navigation snapshot inspected at `f3b69bfa`, 2026-09-09, informed by interviews
with `architecture` and `spikes`. This page routes readers to code and its owning
documents; it does not change their contracts or certify a milestone. Status
describes this revision unless a later inspected delivery or interview report is
explicitly named below.

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
profile, or exhaustive Windows execution model. ApiDispatch strengthening,
CPU/refusal/return/terminal cases and exhaustive coverage remain outstanding
at `dd4c85d1`. In particular, `exitProcessEntry` is an entry case, not proof of
terminal observation. The supplied realization remains fixed across the
derivation; graph agreement does not discharge native correspondence.

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
