# Driver handoff — 2026-09-09

**No spike is complete.** Continue toward verified bytes from the original
authored sources, not a structural export or a selected successful execution.
Read this file and `HELLO_SPECIALIZATION_REMOVAL.md` before importing old work.

## User direction

- Work all five spikes in parallel, across Windows, Linux, WASI and bare metal,
  and x86, AArch64, Wasm, SPIR-V and WGSL (a shader language, not a CPU ISA).
- No spike-specific implementation or proof recipes in `Grass/` or `Tests/`.
  Remove discoveries, then report them to the owner. Precious `Spikes/` inputs
  remain unchanged; do not add author proof companions to replace deleted glue.
- Deterministically derivable artifacts must be computed. Intelligence may
  discover implementations/proofs; deterministic checks must establish them.
- When components need an adapter, have their two implementors agree directly
  on their interfaces, including existing adapters. Escalate concrete unresolved
  disagreements to architecture. Do not grow a third bridging layer by default.
- Every final change needs independent agent review. Terra is preferred for
  delegated building; Sol is also authorized. Merge reviewed, checked work to
  main promptly. Credits are low: prioritize the certificate endpoint and
  finishing existing integrations, not new framework or cleanup campaigns.

## Integrated work

Main `baa2094d` passed the full 644-job build, the 33,127-declaration/395-module
axiom audit, source freshness and the full trust script (75 declarations/8 executable
test modules). It contains the recipe deletions, independent API fixtures,
generic source parsing, AArch64 instruction bodies, Wasm source/module binding,
SPIR-V/WGSL primitives, descriptor sorting and the corrected Wasm trap probe.
The separate certificate integration branch merged this at `6ed7c0ba`; its
focused 256-job build passed, but its legacy public certificate migration is
not complete.

Main `34265675` adds shared memory access/read evidence and the first bare-metal
admission/fetch components. Its affected 236-job build and axiom audit passed
(33,393 declarations/402 modules). The citation ledger explicitly retains 362
owed declarations; model proofs do not discharge hardware applicability debt.

Code checkpoint `485ca64d` additionally integrates the reviewed Linux
syscall/ELF-header slice, CRC/gzip trailer accounting, shared endian-law reuse,
and process receive/cancellation/bounded-execution support. Final integration
checks are recorded below. These are prerequisites, not whole
Linux/gzip/server implementations.

## Highest-priority unfinished path

The public certificate migration is on `codex/frontend-certificate-repair`,
based on the resource-indexed canonical semantics in `codex/certificate-root`.
Main still uses the earlier public gate. **Do not merge the entire certificate
branch merely because individual leaves compile.** Complete the coherent gate,
its consumers and trust audit without weakening guarantees.

Frontend and process have agreed to use the existing history-simulation engine
with fixed dual history observers. A separate `Win32TargetBinding` wrapper was
rejected; its exact source-image facts belong in the existing producer/consumer.

The remaining substantive work includes fixed raw state safety, exact provider
wait/agency semantics, and matching actual raw observations to the captured
whole specification. Coverage excluding `outsideProfile` alone is not memory
safety. `FiniteProgress` alone is not general network deadlock freedom. For the
selected single-caller synchronous backend, use its scoped finite-stop rule
together with complete conformance; internal CPU divergence cannot be passed
off as external nonresponse. Future network backends need their own actual
closed-subset deadlock obligation.

Provider response definitions are supplier commit `a35bf24e`, integrated at
`5b063363` with audit enrollment at `af59ee94`, independently reviewed. They
retain the same selected realization and contain no free permanent-wait
permission. ExitProcess `Unit`
indexes terminal settlement only: the consumer must still prove the same-call,
same-status exit observation and actual completed raw path. The selected raw
backend owns its fixed external-service policy, with real occurrence/agency
and upper-wait matching proofs; import-name equality is not policy authority.

The concrete waiting mismatch is now identified. GetStdHandle settlement must
leave the upper output request pending; WriteFile service advances its residual
frontier while the same lower call remains pending. A static rule requiring
every globally allowed result at every later pending cut can demand an earlier
accepted byte count after further publication. Process/frontend are correcting
the existing waiting/conformance engine directly, not adding an adapter or
changing the precious specification. Preserve actual histories, complete-run
obligations and the distinction between external service and internal spin.

## Published work to inspect before implementing anything twice

These hashes identify supplier changes, not blanket permission to merge their
entire branches. Check prerequisites and current main; some may land after this
handoff was written.

| Supplier | Concrete remaining checkpoints |
|---|---|
| Frontend | `a3deb2e5` heterogeneous shared conformance; `d38b3242` canonical tests; `facaba32` dual history observers. Gate WIP is not a verified program. |
| Process | `0bca97ca` fixed raw observation/coverage and finite-progress leaves, on canonical waiting ancestry. Active `RawWaiting`/state-safety work is separate. |
| Lowering | `cb4a720e` and `eb55d7b5` are integrated at `9b90bdbd`/`750f9f63`: actual source-to-checked/raw branch connection. No enabledness or complete source VC claim. |
| Vulkan/memory | `d19e73e6` shared actual access observation; Vulkan `79fe82a6`, `3b438895`, `011ea140`, `0eb19944`, `9068695c`. Preserve the final wrapper deletions and shared-memory prerequisites. |
| x86 | `0e4c5873`, `6f0fe04b`, `7d912e62`: shared-read adoption, AND/MOV/SYSCALL, then deletion of x86 AccessRun and duplicate width records. Breaking references require owner-coordinated migration. |
| AArch64 | `2ed15865`, `ba11a579` boot/body connection; `967f5512` explicit routing and jointly agreed Linux backfill. Not full exception entry. |
| Linux | First slice `3a3866f2` integrated at `ad5f6c41`. Later source-wrapper removal and reached-user/ELF work remain on `codex/linux-syscall-boundary`; coordinate with AArch64. |
| WASI | Original provider slice remains in worktree `2665/grass`; owner task is inactive. Wasm owner found removable duplicate host/type checks. Preserve the uncommitted supplier files; reassign explicitly before editing. |
| Shader | Initial `06024ec1` is integrated. `codex/shader-source-witness` continues actual word/entry witness work with Vulkan. |

## Owner routing

### Late supplier updates after the integration checkpoint

- Frontend published `8e889256`, the reviewed direct-frontier conformance
  change. Process published `a761caba`, reviewed fixed raw waiting laws and
  explicit optional generic reply availability, depending on state/observer
  `24ddb183` and the corrected provider leaf already noted above. These are
  supplier checkpoints, not integrated public certificates.
- **Unresolved provider-domain blocker:** arbitrary `ReturnInterpretation`
  includes `False`. Do not assume whole-program `Raw.WaitLaws` as admission:
  that could exclude malformed caller handoffs instead of rejecting them.
  Frontend, process and architecture must agree on a selected provider domain
  independent of program correctness. Mandatory raw waiting laws remain a
  gate conclusion. Architecture recorded the availability distinction in
  `fd9a4c32`, following `0663456b`.
- Linux published reviewed `ae638bf0` (core `0726d0e8`), covering ELF program
  headers, checked load plans and shared memory installation. Its owner reports
  full local build/trust checks passing; remote CI was pending. Inspect the
  coherent branch and ledger unions before integration.
- Shader published reviewed `0c8150e4`, binding captured source through parsing
  and compilation to canonical words and typed interfaces. Its owner reports
  local gates and `spirv-val` passing; Corpus CI passed and Library CI was still
  running. This does not establish full GPU validity. It is not yet on main.

Use existing tasks, not new standing specialists. Frontend:
`01a0885f-ee7d-77a2-99bd-9b143a7a13ca`; process:
`01a086f1-a780-74e0-9aa4-0a9658d848b0`; architecture:
`01a0873f-dd62-7521-b7c7-e67bc9874c7e`; lowering:
`01a0873c-647a-7961-9b66-c90a41151994`; memory-model:
`01a086e8-33f0-72c1-8724-37ad85dfe287`; CI:
`01a08969-b492-73d3-bf93-1a453c145f62`.

Windows and WASI task sends have returned “no active turn id”; cross-team
messages to root subagents are also rejected. Relay an implementor's exact
message when necessary, without taking over interface design. Root's temporary
provider supplier used `grass-platform-fixture-cleanup` and published the leaf
above. Do not assume an unanswered tool call means work stopped.

Preserve spare-part branch history. The old scribe and shader-primitives branches
were merged with green main: `6a89cfd2` and `c751e95b`, both with exactly the
`baa2094d` tree. Their subsequent CI jobs are CI-owner tracked.

## Final checkpoint verification

The Linux/gzip/process integration passed the full 671-job build. The actual
source-branch connection passed its 277-job integration build; its final source
fixture took 212 seconds and completed successfully. Provider enrollment and
the three target documentation corrections passed another 277-job focused
build. The final axiom audit scanned 34,036 declarations across 415 modules,
with no unapproved axiom, unsafe declaration or compiled override. The citation
ledger reports 791 modeled declarations: 6 cited, 372 owed, 413 reviewed helpers.
The full docstring audit passes after naming the actual enforcing theorems in
six additional Linux/process comments. Source mirrors and documentation links
also passed. Check the newest remote CI run separately; local passing checks
do not claim remote completion or a finished spike.
