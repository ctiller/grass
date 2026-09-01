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
