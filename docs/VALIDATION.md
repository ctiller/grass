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

Correctness-critical repository tooling is production software. A bus reducer,
review gate, linker, emitter, cache validator, compiler, or audit command can
invalidate the evidence chain even when it is not shipped inside the user's
program. Its assurance obligation is proportional to that authority, not to
the language in which its first version happens to be written.

Each such tool has a language-independent behavioral contract covering:

- accepted, rejected, incomplete, stale, conflicting, and unsupported inputs;
- state transitions, durable writes, recovery, idempotence, and replay;
- authority and freshness checks at the operation which needs them;
- bounded local latency and resource use for ordinary read/write paths;
- compatibility and migration across simultaneously deployed versions; and
- exact observable effects at filesystem, Git, process, and network boundaries.

The contract is the durable asset. Rust, another native bootstrap language, and
Grass are replaceable realizations. Implementation-specific structs, exit text,
Git version strings, and cache layouts enter the contract only when an external
consumer genuinely observes them. In particular, a reader must not make an
append-only history unreadable merely because it cannot execute a newly selected
mutation engine; it reduces and reports the selected state, while the affected
mutation command fails closed with an explicit unsupported-capability result.

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

A Grass replacement first runs in shadow against retained bootstrap traces.
Differential campaigns compare classified results, reduced states, intended
effects, and produced bytes—not timing, incidental diagnostics, or other
unspecified details. Disagreement is a retained finding. The Grass realization
is promoted only after its refinement theorem, exact emitted artifact
connection, migration proof, negative fixtures, and measured local cost pass
review. During an explicit compatibility window both implementations can read
the same durable format, and mutating dual execution is performed only in an
isolated fixture or through one proved single-commit protocol; two live writers
must not duplicate an external effect merely to compare them.

Self-hosting preserves an explicit induction anchor. Let `T₀` be the reviewed
native seed and `T₁` the first verified Grass implementation built with it. The
claim about `T₁` comes from its checked source-to-artifact proof plus independent
validation of `T₀`'s relevant boundary—not from asking `T₁` to certify itself.
Later `Tₙ₊₁` rebuilds carry forward exact source, proof environment, toolchain,
and artifact identities and may be compared with independently rebuilt outputs.
The current Lean kernel and allowed foundation remain part of the declared TCB
until a separately reviewed theorem and checker transition changes that fact.

Rebuild is the verb. A tooling defect adds the smallest durable specification,
proof, property/state-machine test, mutation, or fault fixture which would have
caught it, with burden review before a new universal proof demand is attached to
the public verified-program or tool boundary. The repair must survive replacing
the implementation rather than merely recognizing one historical code path.
