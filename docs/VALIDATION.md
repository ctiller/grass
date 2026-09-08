# Citations, validation, and trust ledgers

## 1. Source anchoring

Every modeled instruction, API, ABI rule, binary structure, loader behavior, and
memory-order rule cites an authoritative vendor/standards source. A citation
record contains stable identity, title, publisher, revision/date, retrieval
location, exact anchor, license/cache policy, affected declarations, and review
instructions for locating and checking the source text.

Repository documents may explain derivations and cite one another, but cannot be
the sole authority for external behavior. When vendors disagree, profiles split
or use the weakest cited intersection. Undocumented observations may motivate a
restriction or research item, never a portable guarantee.

Reference drift is reviewed: new revisions do not silently replace the revision
against which a theorem was written. Broken links use a reviewed cached copy or
are a release blocker according to the reference policy.

## 2. Validation layers

Validation challenges the formal/real-world connection at four layers:

1. Structural: parser/writer round-trip, malformed inputs, canonicalization.
2. Differential: compare encoders, decoders, assemblers, disassemblers, loaders,
   emulators, and API observations where independent tools exist.
3. Physical probes: execute generated instruction/API cases on named CPU/OS/GPU
   profiles and compare complete declared effects.
4. Proof gates: prove generators, shrinkers, interpreters, erasure, refinement,
   and artifact connections satisfy their formal interfaces.

Tools and hardware are fallible oracles. Disagreement is preserved as a finding;
majority vote does not establish truth.

## 3. Instruction campaigns

Every instruction profile supplies generators and boundary partitions for:

- every supported encoding and operand class;
- flags and exceptional inputs;
- alignment, page crossing, permissions, and uninitialized state;
- aliasing and overlapping operands;
- feature/mode/privilege applicability;
- faults, traps, restartability, and interruption points;
- atomicity, ordering, and concurrent litmus cases;
- relocation and address-edge cases.

Finite domains are exhaustive where practical. Infinite state spaces require an
explicit coverage partition, randomized/mutation testing, reduced-width
exhaustive models, and retained regression seeds. Claims say exactly what was
covered; “all edge cases” means all reviewed semantic partitions, not an
impossible enumeration of all machine states.

The common x86 profile runs independently on Intel and AMD hardware and records
CPU identification, microcode, OS, virtualization, and test harness version.

## 4. API campaigns

Every API profile probes success, documented failures, boundary sizes, null and
invalid inputs where permitted to call, partial completion, interruption,
cancellation, concurrency, ownership transfer, pointer rights, lifecycle,
callbacks, and teardown. Probe processes are isolated when faults or hangs are
possible. External state is sandboxed and cleanup is independently verified.

## 5. Fuzzing the unsafe layer

`Grass.Unsafe` is intentionally usable without proofs so fuzzers can construct,
encode, parse, decode, and step arbitrary raw programs. Fuzz targets include:

- parser/writer round-trip and canonicalization;
- decoder registry ambiguity and length/dispatch correctness;
- encode/decode semantic equivalence;
- model versus hardware/emulator traces;
- loader/linker/relocation and artifact connection;
- malformed CFG/import/export metadata;
- memory-event descriptors versus actual effects;
- oracle protocol exhaustion and malformed responses.

Crashes, hangs, mismatches, and minimized inputs are retained. A fuzzer success
never closes a theorem obligation.

## 6. Per-profile trust ledger

Each platform/ISA/API profile publishes:

- exact authoritative sources and revisions;
- implemented and rejected feature sets;
- theorem coverage;
- explicit external/profile assumptions and a transitive axiom report for every
  verified theorem, regardless of declaration origin;
- exact use of the reviewed Lean-foundation allowlist and rejection of every
  dependency-defined axiom, `sorryAx`, or equivalent admission constant;
- validation environments and last successful campaigns;
- known discrepancies, errata, and mitigations;
- downstream artifacts whose assurance depends on the profile.

## 7. Ratchet and CI

Every confirmed finding becomes at least one of: a corrected model and theorem,
a regression test, a profile restriction, or an explicit trust-ledger item.
Removing the resulting gate requires review explaining why the original finding
can no longer recur.

CI is sharded by module/profile and separates fast kernel/build checks from
scheduled fuzz/physical campaigns. Ordinary changes must not require enormous
generated files or tens of gigabytes of memory.

Published-corpus lint rejects user-profile absolute paths, account names,
hostnames, device serials, credentials, and private workstation topology.
Validation environments use anonymized stable profile IDs and include only
hardware attributes technically required to interpret results.

CI also validates the mandatory `InvalidationPlan` and `BuildExecutionReport` owned by
[REFINEMENT.md](REFINEMENT.md). Each change-matrix row in Spike 1 and later
milestones has a fixture that mutates only the named reviewed input and asserts
the expected semantic statuses, action sets, and required-reuse subjects.
Unexplained invalidation, re-execution of an unrelated local proof, a missing
causal dependency, or a false reuse is rejection. Reports are retained as small
build artifacts; they may not require a monolithic proof-state snapshot.
Each reviewed module's `LocalityContract` is checked against those reports;
changing a leaf block while touching a forbidden unrelated consumer is a CI
failure even if the full rebuild eventually succeeds.
Periodic clean uncached and differential reconstructions verify the incremental
engine's reuse claims and cache-key sufficiency.

Published-corpus lint also rejects audience/workstation idioms used as evidence,
including “worked on my machine,” in addition to literal private topology.

## 8. Repository tools and staged self-hosting

Correctness-critical repository tooling is production software. A tool is
correctness-critical exactly when a review or nomination cites its output as
evidence, a gate consumes its output in deciding acceptance, or its output
authorizes or performs merge or publication. “Output” includes a decision,
exit status, emitted artifact, or durable state; a command which merely advises
a human and whose output cannot enter any of those uses is outside this
definition. Thus a bus reducer, review gate, linker, emitter, cache validator,
compiler, or audit command can invalidate the evidence chain even when it is
not shipped inside the user's program.

The strongest downstream use fixes the assurance floor. Review or nomination
evidence requires the language-independent contract, reproducible invocation,
and positive and negative fixtures at the public boundary. Gate acceptance also
requires model/state-machine coverage for stateful behavior, fault fixtures for
effectful behavior, and compatibility fixtures for durable data. Merge or
publication authority requires all of those plus the crash, retry,
concurrent-writer, stale-input, exact-effect, and recovery obligations below.
An obligation whose named behavior is absent is inapplicable, not silently
waived; for example, a pure reader has no crash-recovery write obligation. This
output-use ordering, rather than implementation language or a subjective risk
label, is what “proportional to authority” means in this section.

Each such tool has a language-independent behavioral contract covering:

- accepted, rejected, incomplete, stale, conflicting, and unsupported inputs;
- state transitions, durable writes, recovery, idempotence, and replay;
- authority and freshness checks at the operation which needs them;
- bounded local latency and resource use for ordinary read/write paths;
- compatibility and migration across simultaneously deployed versions; and
- exact observable effects at filesystem, Git, process, and network boundaries.

A tool which constructs a proof-bearing object must emit enough exact input and
certificate identity for an independent checker to reject substitution,
truncation, reordering, stale-cache replay, and malformed data. A bootstrap
implementation's successful run is operational evidence only. Acceptance of
its output rests on a parser/checker theorem, Lean kernel check, or another
explicitly recorded trust boundary—not on the producer reporting success.

The contract version also contains a reviewed `ToolTheoremDemand`. It decides
separately for safety, progress, resource use, and exact artifact/output whether
the family is `required` or `inapplicable`. A required family names the public
theorem statement, including its quantified input and environment; an
inapplicable family gives a behavior-specific reason. The record also names any
shared library theorem intended to discharge it. “Appropriate to the tool” is
therefore this reviewed record, not an implementor's or reviewer's unrecorded
judgement. Changing a family, weakening its statement, or attaching a new
universal theorem to the public tool boundary is a design change and receives
the burden review required by [SPIKE_PROOF_BURDEN.md](SPIKE_PROOF_BURDEN.md).
Passing fixtures cannot substitute for a required theorem.

The authoritative per-tool trust-role register lives in this section. A new
persistent correctness-critical tool is registered before its output is cited
as evidence or consumed by a gate. `Role` is a nonempty set drawn from
`evidence-producer`, `gate`, `merge-publisher`, and `foundation-checker`; the
strongest role selects the assurance floor above. `Status` describes the
implementation transition, not proof status.

| Tool | Behavior-contract version | Role | Current implementation | Status | Theorem-demand record |
|---|---|---|---|---|---|
| corpus mirror | `mirror-report-v1`, [IMPLEMENTATION_RATCHET.md §3.1](IMPLEMENTATION_RATCHET.md#31-mirror) | evidence-producer, gate | `check-spike-sources.ps1` | bootstrap active; Grass replacement planned | `mirror-v1-demands` below |
| corpus link lint | `corpus-links-v1`, §7 | gate | `check-doc-links.ps1` | bootstrap active; replacement unscheduled | `pure-finite-lint-v1` |
| axiom audit | `axiom-audit-v1`, §6 and [FOUNDATION.md](FOUNDATION.md) | evidence-producer, gate | `audit-trust.ps1` | bootstrap active; replacement unscheduled | `checked-declaration-audit-v1` |
| agent bus | `agent-bus-schema-v2`, [AGENT_BUS_SCHEMA.md](AGENT_BUS_SCHEMA.md) and [AGENT_REVIEW.md](AGENT_REVIEW.md) | evidence-producer, gate, merge-publisher | `tools/agent-bus` | native implementation active; Grass replacement planned | `durable-authority-tool-v1` |
| spike report commands | `spike-reports-v1`, [IMPLEMENTATION_RATCHET.md](IMPLEMENTATION_RATCHET.md) | evidence-producer, gate | none | planned | one demand record per command before implementation acceptance |
| Lean elaborator/kernel used by the build | pinned `lean-toolchain`, §6 and [FOUNDATION.md](FOUNDATION.md) | foundation-checker | pinned Lean distribution | declared TCB; replacement not claimed | `external-foundation-v1` |

The shared records in this table are templates whose per-tool instantiation is
part of the reviewed row; they are not permission to infer omitted demands.
`pure-finite-lint-v1` requires safety (acceptance implies every declared lint
condition), progress (every finite readable snapshot returns accept, reject, or
an explicit input error), a reviewed finite resource bound, and exact output
(the public verdict and exit status equal the specified scan result; any emitted
report obeys its canonical writer law). `checked-declaration-audit-v1` requires
the same four families and strengthens safety and exact output with exact
correspondence between the audited declaration closure and reported names. The
`durable-authority-tool-v1` record also requires all four families, including
exact durable events/effects, and the crash, retry, concurrency, freshness,
recovery, and migration laws above. `external-foundation-v1` marks all four
Grass theorem families inapplicable to the external checker itself: proving the
checker by accepting that checker's result would be circular. Its exact version,
allowed foundation, validation, and downstream dependence remain explicit trust
ledger entries until a separately reviewed checker transition replaces that
boundary.

`mirror-v1-demands` is the small-tool worked example:

- **Safety:** for every finite repository snapshot, an accepted report iff all
  authored files and classified blocks are in the one-to-one normalized-content
  relation in [IMPLEMENTATION_RATCHET.md §3.1](IMPLEMENTATION_RATCHET.md#31-mirror);
  malformed classifications and I/O failures cannot produce acceptance.
- **Progress:** every finite snapshot whose reads each return data or a named
  I/O failure terminates with accepted, rejected, or that explicit failure. No
  fairness or termination claim is made for an operating-system read which
  never returns.
- **Resources:** the contract supplies reviewed numeric functions
  `mirrorResidentBound(totalInputBytes, fileCount)` and
  `mirrorWorkBound(totalInputBytes, fileCount)`; the theorem bounds peak resident
  bytes and abstract work by those functions for every finite snapshot. The
  functions, units, and overflow behavior are contract data, not chosen by the
  implementation after measurement.
- **Exact output/artifact:** report serialization obeys
  `parse (write report) = .ok report`, emitted report bytes are exactly
  `write (scan snapshot)`, and the promoted Grass executable has the ordinary
  exact source-to-artifact `VerifiedProgram mirrorSpec` connection.

This example is intentionally stronger than “the tool terminated.” It also
shows proportionality: it has no concurrency, recovery, or external-effect
theorem because its contract is a finite pure scan plus one atomic report write;
those properties are fixtures or effect-wrapper obligations, not invented
duties of the pure scanner.

The contract is the durable asset. Rust, another native bootstrap language, and
Grass are replaceable realizations. Implementation-specific structs, exit text,
Git version strings, and cache layouts enter the contract only when an external
consumer genuinely observes them.

A forward-compatibility rule is required for selected mutation capabilities: a
reader which recognizes the base event must not make an append-only history
unreadable merely because it cannot execute a newly selected mutation engine.
It must preserve and reduce the recognized event, report the selection as an
opaque unavailable capability, and make only the affected mutation command fail
closed with an explicit unsupported-capability result. This is not a current
V1 behavior. [AGENT_BUS_SCHEMA.md](AGENT_BUS_SCHEMA.md) deliberately rejects
every unknown field and enum value and has no forward-compatible capability
envelope.

Therefore that rule has an open dependency on a separately reviewed bus-schema
revision and its live reader, writer, reducer, and command implementation. The
schema owner must introduce a bounded, length-delimited capability-selection
envelope whose unknown optional capability identifiers and payloads can be
preserved opaquely. The carve-out is limited to that envelope: unknown base
event kinds, required semantic values, fields outside it, malformed payloads,
and unsupported schema versions remain rejected. Until that schema and tooling
revision is implemented and deployed, readers continue to obey the current V1
strict-rejection rule; this document does not advertise the future rule as an
existing bus capability.

Porting proceeds from small pure boundaries outward:

1. codecs, canonical writers, schema validation, and pure state reduction;
2. local queries and audits over the reduced state;
3. preparation of mutations as explicit plans;
4. filesystem, Git, publication, and integration effects; and
5. the compiler and complete self-hosted toolchain.

Every boundary keeps its normal serialization laws. Pure reducers additionally
have model/state-machine tests for arbitrary valid interleavings and negative
fixtures for every previously escaped corruption class. Effectful commands have
crash-point, retry, concurrent-writer, stale-input, and cross-platform fixtures.
Tests exercise the same public command boundary operators and agents use; a
parallel test-only implementation is not evidence for the production path.

Promotion requires the same reviewed behavior specification and format laws,
every required theorem in the tool's demand record, an exact source-to-artifact
connection, rejecting fixtures, differential campaigns, measured resource and
rebuild evidence, and a reversible deployment interval. None can be replaced by
the bootstrap implementation and Grass implementation merely agreeing.

A Grass replacement first runs in shadow against retained bootstrap traces.
Differential campaigns compare the report schema's declared semantic
projection—not timing, provenance, incidental diagnostics, or other unspecified
details. The projection and its canonicalization are part of the versioned
behavior contract; [IMPLEMENTATION_RATCHET.md](IMPLEMENTATION_RATCHET.md)
defines them for the spike reports. Disagreement is a retained finding. The
Grass realization is promoted only after its refinement theorem, exact emitted
artifact connection, migration proof, negative fixtures, and measured local
cost pass review. During an explicit compatibility window both implementations
can read the same durable format, and mutating dual execution is performed only
in an isolated fixture or through one proved single-commit protocol; two live writers
must not duplicate an external effect merely to compare them.

Self-hosting preserves an explicit induction anchor. Let `T₀` be the reviewed
native seed and `T₁` the first verified Grass implementation built with it. The
claim about `T₁` comes from its checked source-to-artifact proof plus independent
validation of `T₀`'s relevant boundary—not from asking `T₁` to certify itself.
Later `Tₙ₊₁` rebuilds carry forward exact source, proof environment, toolchain,
and artifact identities and may be compared with independently rebuilt outputs.
The current Lean kernel and allowed foundation remain part of the declared TCB
until a separately reviewed theorem and checker transition changes that fact.

For a compiler or another tool capable of rebuilding itself, a fixed-point
build is an additional campaign. Byte-for-byte stability is required only when
the format and build specification demand canonical bytes; otherwise the
declared semantic or artifact projections are compared. No self-build result
discharges a correctness obligation about the compiler which produced it.

Rebuild is the verb. A tooling defect adds the smallest durable specification,
proof, property/state-machine test, mutation, or fault fixture which would have
caught it, with burden review before a new universal proof demand is attached to
the public verified-program or tool boundary. The repair must survive replacing
the implementation rather than merely recognizing one historical code path.
