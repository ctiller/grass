# Binary evidence and memory-safety verification

Status: proposed feature design for alignment. No command, certificate, or
whole-binary analysis described here is claimed to be implemented. `disasm`
owns feature integration; specialist implementations remain with the fleet.

## 1. Purpose and authority

Given exact executable bytes, produce assembly and structured evidence, then
use Grass's memory model to author and check proofs of memory safety. Begin
with binaries produced by the spikes; later use deliberately safe and unsafe C
programs as described in [DISASM_CORPUS.md](DISASM_CORPUS.md).

The target family is PE and ELF on x86 and ARM. Support is a versioned tuple of
container subset, ISA mode/features, platform, ABI, loader, and external-call
contracts, not a Boolean claim about an entire architecture. The proposed first
tuple is the actual Windows x86-64 PE32+ Hello output accepted by `spikes`.
ELF x86-64 and AArch64 follow available spike outputs. PE ARM and 32-bit x86/ARM
remain in scope for alignment, with their order and exact modes unresolved.
Support for one tuple does not establish support for other combinations.

[FOUNDATION.md](FOUNDATION.md) retains authority over trust;
[ARTIFACTS.md](ARTIFACTS.md) over parsing/loading and exact byte connections;
[INSTRUCTIONS.md](INSTRUCTIONS.md) over instruction semantics;
[MEMORY_MODEL.md](MEMORY_MODEL.md) over memory safety; and
[PLATFORM_ABI.md](PLATFORM_ABI.md) over external boundaries. This proposal adds
an imported-binary consumer of those contracts. It neither redefines them nor
adds an alternate implementation of their semantics.

## 2. What is established

The memory claim covers spatial bounds, live provenance and lifetimes,
initialization, permissions, and applicable authority/concurrency rules from
the selected memory profile. The report lists these properties individually.
Mapping-level accessibility is insufficient evidence of object-level safety.
Resource cleanup or termination is not silently bundled into memory safety;
ledger rules needed to preserve memory authority still apply.

Binary memory safety is separate from C-language definedness. Proving one
compiled artifact does not establish absence of source-language undefined
behavior or correctness of compilation; those require a separate refinement.

Every result names exact bytes, entry scope, admitted initial states, load
bases, external environments, ISA/platform profiles, and model versions. A
whole-image claim covers every entry and execution admitted by that profile,
including loader-triggered entries and callbacks where applicable. A callable
claim states its caller precondition and is visibly narrower.

Results are typed as:

| Result | Required evidence |
|---|---|
| Proved | Kernel-checked theorem for the stated property and scope, with closed coverage and explicit assumptions |
| Violated | Checked feasible execution prefix from an admitted initial state to an operation violating the stated property |
| Unresolved | Residual proof obligation, including missing evidence, unsupported semantics, failed invariant search, or exhausted resources |

Malformed input and tool failures are separate analysis outcomes. They are not
proofs of runtime memory unsafety. An unresolved goal is the location where
safety has not been established; it is not the negation of the desired theorem.
Local proved facts remain useful when the aggregate result is unresolved.
A checked violation refutes the corresponding universal claim even if other
regions remain unresolved. Conflicting checked conclusions for the identical
claim are an integrity failure to investigate, not an aggregation preference.

## 3. Evidence production

The proposed flow is:

```text
exact bytes + explicit target/environment
  -> parsed artifact and loader evidence
  -> decoded instructions and candidate control flow
  -> checked machine behavior coverage
  -> candidate memory annotations and invariants
  -> memory proof obligations
  -> checked proofs / checked violations / residual obligations
```

Each stage retains its input identity and dependencies. Candidate production
can use heuristics, external tools, or agent-authored proposals. Acceptance uses
deterministic checking and kernel-checked connection theorems. JSON, assembly
listings, successful execution, hashes, and external solver answers are review
evidence, not proof authority.

### Artifact and load evidence

Preserve the original bytes. Record file ranges, virtual ranges, zero-filled
storage, mapping permissions, entry sources, relocation actions, imports, and
applicable exception/unwind metadata. Keep file offsets, image-relative
addresses, and loaded addresses distinct. A certificate handles every admitted
load base, not just the preferred base used to print an assembly listing.

Parsing a container does not prove it loadable. Establish nonempty admissible
context/base/import domains independently of successful loading and safety,
and prove loading and initial-state validity as required by the artifact owner.
Unsupported loader behavior prevents that scope from receiving a certificate.

### Instruction and control-flow evidence

For every decoded instruction retain exact consumed bytes, location, mode,
semantic operation identity, successors, and instruction-fetch dependencies.
Decode/encode round-trip alone is not instruction semantic adequacy.
Use the ISA owner's decoder and operation model with their applicability laws.

Recursive traversal, symbols, producer maps, and traces can propose code
boundaries. None proves that all reachable code has been discovered. Every
direct edge, indirect jump, return, external reentry, and applicable exceptional
edge needs a coverage argument. Unresolved targets stay explicit. A bounded
trace or bounded symbolic search cannot close universal reachability.

Unvisited executable bytes are classified as unresolved or proved unreachable
under the entry contract; they are not declared harmless padding by convention.
Overlapping instruction streams or alternative decode modes are either modeled
with all reachable interpretations or excluded by checked profile conditions.
The initial profile should require stable executable bytes. Self-modification,
dynamic code generation, and runtime loading require additional semantics and
coverage before they can enter a proved scope.

### Memory evidence

Associate each memory-affecting instruction or external operation with the
existing ordered access/effect frontier. Include implicit stack accesses,
instruction fetch, partial effects, allocation/lifetime transitions, and
external reads/writes, not only explicit load/store operands.

Recover candidate frame slots, object bounds, provenance, pointer shadow state,
ownership/loans, and loop/call invariants. Track the source of every candidate:
artifact fact, checked producer evidence, inferred invariant, or declared
environment assumption. Symbols and debug types are hints until connected to
actual bytes and behavior.

Numerical addresses do not manufacture provenance. A reconstruction proof
must account for initialization, copying, pointer arithmetic, lifetime changes,
and reuse. It cannot reassign a dangling pointer to the fresh allocation now
at the same address. Similarly, choosing the whole stack or heap as one object
does not establish field/object bounds. Report the exact granularity proved.

The relation between machine states and ghost memory states must establish
initial consistency and preservation, including physical placement, backing
overlap, and nonwrapping address translation. Candidate annotations must not
change executable behavior or narrow its input domain. Failure to reconstruct
such a relation is an unresolved modeling/proof gap, not automatic unsafety.

At the current memory seam, construct the existing `AccessDescriptor` and
consume the owner's preparation/resolution and `Op.step` laws. A single checked
resolution fixes allocation/backing lookups, bounds, and coordinate footprint.
Preparation and `Op.step` use that same certificate for observation, authority
checks, event footprint, and commit; the analyzer must not translate each
independently. Resolution alone does not prove authorization, and preparation
does not prove completion. Actual reached-state single-access receipts connect
the selected prepared access to execution, following the boundary in
[HELLO_UNWIND_BOUNDARY.md](HELLO_UNWIND_BOUNDARY.md).
Reconstruction is consistent across histories, not a fresh convenient choice
of provenance for each access. Current dedicated-backing restrictions remain
applicability requirements; unsupported shared-live mappings are not unsafe
by definition. Exact export names follow the reviewed memory migration.

Quantify over every admitted concrete run before supplying its coherent ghost
witness, and preserve or extend that witness through each step. Tie recovered
object/authority facts to independently stated allocation/ABI contracts and
safety properties; inferred metadata cannot define a conveniently weaker claim.

## 4. Proof boundary

The following are conceptual demands, not proposed compilable Lean signatures:

```text
Loadable(bytes, profile, domain)
EveryLoadedExecutionCovered(bytes, recoveredMachine, profile, domain)
GhostMemoryRelationPreserved(recoveredMachine, annotations, memoryProfile)
EveryReachableMemoryOperationValid(recoveredMachine, annotations, domain)
-----------------------------------------------------------------------
EveryLoadedExecutionMemorySafe(bytes, profile, memoryProfile, domain)
```

Coverage is in the loaded-machine-to-analysis direction: no admitted concrete
behavior may be lost. Conservative additional behaviors may create proof gaps;
a violation found only in that overapproximation needs feasibility checking
against the loaded machine before being reported as demonstrated.

Most importantly, memory audit denial cannot be used to stop the modeled
machine and conclude its remaining executions are safe. Ghost authority checks
are verification obligations. Either prove them before every reachable
concrete access, or retain a failure obligation/violation candidate. The
connection must preserve the concrete operation even where its ghost check
would fail. Architectural faults and committed prefixes remain governed by
their actual ISA/API contracts; faults are not generic safety containment.

Universal safety includes all admitted inputs, allocation choices, API results,
schedules, and finite prefixes of diverging executions. Loop invariants and
recursive summaries require initiation, preservation, and complete successor
coverage. A search timeout or a finite unrolling bound is never such a proof.
Single-threaded applicability must exclude unmodeled concurrent access and
asynchronous entry; it cannot merely omit schedule variables.

Externally supplied call summaries name exact resolved operation/ABI identities
and their memory effects, failure cases, callbacks, and retained pointers.
An unknown external call is a coverage gap. Trusted provider implementations
remain explicit profile assumptions, following existing artifact contracts.

An imported-binary memory certificate is distinct from
[`VerifiedProgram`](VERIFIED_PROGRAM.md): it does not claim correspondence to a
precious functional specification or permission to enter the verified emission
gate. Its checked root is indexed by exact input bytes, claim scope, profiles,
and environment contract. A future promotion requires every missing existing
`VerifiedProgram` demand; no implicit coercion is proposed.

## 5. Proof authoring and diagnosis

Automation computes routine facts and attempts invariants and summaries.
Agents/specialists author the remaining mathematical arguments against the
same generated obligations. All candidate proof terms pass the ordinary Lean
kernel and transitive trust audit; no generated axiom or unchecked solver
promotion is allowed. Reusable facts belong to the narrow owning library.

Here a proof obligation means a proposition to discharge, not a new kind of
linear resource in [OBLIGATIONS.md](OBLIGATIONS.md). Obligations reference
artifact ranges, instruction identity, access substep, assumptions, and prior
facts. Stable keys include the semantic claim and scope, not just an address.

For each residual goal, show what is required, what is known, why it remains
open, and its dependency chain. Distinguish semantic coverage gaps, unavailable
object/provenance evidence, insufficient invariants, resource exhaustion, and
candidate violations. Do not display missing provenance as proved use-after-free.

Preserve model/checker denial as its own diagnostic category under unresolved
results unless a further checked argument connects that denial to the stated
violation. It may reflect insufficient reconstruction or a stricter ownership
policy. Show the exact denied condition without calling it a hardware trap or
concrete corruption.

A violation certificate includes a concrete admissible environment/input and
finite execution prefix, path feasibility, exact failing operation and property,
and the needed object/lifetime connection. Native replay is corroborating
evidence; it is not the certificate. An unreachable invalid instruction does
not demonstrate a runtime violation.

## 6. Outputs, replay, and invalidation

The proposed bundle contains the exact input artifact, target/environment
description, readable assembly, structured evidence graph, proof declarations,
checked claim inventory, residual goals, and optional violation witnesses.
Reuse the report envelope and exact-content identity rules from
[IMPLEMENTATION_RATCHET.md](IMPLEMENTATION_RATCHET.md), with an optional spike
origin. Do not invent a separate trust/reporting architecture.

The check path consumes frozen evidence/proof candidates without invoking the
search engine or trusting cached result flags. Certificates depend on exact
bytes and checked semantic content; digests locate artifacts but do not prove
their identity. Record toolchain, imported model roots, configuration, and
assumptions so the result can be reproduced.

Shard proofs by reusable semantic dependencies and justified block/call
boundaries. A byte change invalidates dependent decode/flow/proof facts; an
entry, relocation, provider, or memory-model change invalidates every dependent
claim. The aggregate root is always rechecked. Timestamps and search durations
do not enter theorem identity. Measure proof-author effort and rebuild cost,
not only the number of decoded instructions.

## 7. Ownership and implementation boundaries

| Owner | Requested responsibility |
|---|---|
| `disasm` | Pipeline integration, evidence provenance, obligation/report presentation, imported certificate and acceptance corpus |
| `architecture` | Review shared interfaces, dependency direction, and cross-domain ownership/interface coordination |
| `spikes` and target spike tasks | Supply exact emitted artifacts and optional checked producer evidence; preserve existing spike acceptance scope |
| `memory-model` | Own ghost reconstruction requirements, access/lifetime semantics, safety predicates, and denial/violation distinction |
| `x86`, `aarch64` | Own instruction decoding/semantics/coverage for the selected ISA profile |
| `windows`, `linux` | Own format/loader/ABI/provider connections for the selected target |
| `lowering` | Guide reuse of raw/ghost correspondence and control-flow contracts |
| `library` | Help extract reusable deterministic machinery and proof laws when demanded |

Local inspection found an x86 subset decoder in
[`Decode.lean`](../Grass/ISA/X86/Decode.lean), a PE container reader in
[`ImageReader.lean`](../Grass/Artifact/PE/ImageReader.lean), and shared access
vocabulary in [`Access.lean`](../Grass/Memory/Access.lean). Their existence does
not establish a completed loader, imported-binary verifier, or arbitrary
compiler-output support. Integration follows reviewed specialist exports rather
than freezing their current internal fields in this proposal.

Before implementation acceptance, resolve with the sibling owners: the exact
first artifact/profile handoff; the machine-to-ghost reconstruction relation;
the memory certificate's narrow checked root; and which existing coverage and
report types can be reused. This design proposes those boundaries for review,
not a ratified change to foundational interfaces.
