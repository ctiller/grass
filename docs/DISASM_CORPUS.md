# Disassembly evidence: acceptance corpus

Status: proposed acceptance design for [DISASM.md](DISASM.md). Milestones are
gates for the feature, not claims that spike binaries or commands already exist.

## 1. Begin with actual spike output

Use each spike's exact emitted executable as it becomes available. Preserve
the authored spike and its existing verification requirements. Do not build a
lookalike executable to imply that the real spike pipeline has closed.

Start with the accepted Windows x86-64 PE32+ Hello artifact. If its final byte
connection is still open, record that producer status and exercise available
parser/decoder components without calling the milestone complete. Add ELF
x86-64 and AArch64 targets when the corresponding spike tasks supply them.
Each new platform/ISA combination passes its own load/decode/safety gates.

The producer handoff consists of exact bytes, selected profile, entry and load
contract, reproducible production identity, and optional checked source/raw/
artifact connections. Missing producer proofs are recorded, not invented.
Hashes are inventory keys; the receiving checker binds proofs to exact content.

Run two visibly distinguished analysis modes:

| Mode | Available assistance | Acceptance meaning |
|---|---|---|
| Artifact-only | Executable bytes and explicit platform/environment contract | Measures what disasm can recover and prove without source or producer annotations |
| Producer-assisted | Additionally, byte-connected maps, object/lifetime annotations, and reusable producer lemmas | Measures useful proof reuse and the evidence needed to close artifact-only gaps |

The producer's final safety theorem is a separately labeled comparison or
reused theorem. Replaying it alone does not count as recovery success. Report
which obligations were independently discharged and which consumed producer
lemmas. Removing assistance may expose gaps; it must not leave a stale proved
status. Neither mode silently adds producer facts to environment assumptions.

## 2. Milestone gates

### A. Exact-byte evidence

For the first spike, produce a readable assembly listing and a machine-readable
inventory of container layout, relocation/import/entry facts, instruction bytes,
decode results, and candidate edges. Preserve unknowns. Check the applicable
parser/decoder laws and byte links. No memory-safety claim is required to pass
this evidence-only gate, and its report must say so.

### B. First connected memory proof

Connect the loaded bytes to the recovered machine and the shared memory model.
Cover entry stack conditions, image data, every reachable memory operation,
call/return effects, provider operations, and all permitted partial/failure
outcomes. Close one whole-profile safety claim, or explicitly deliver a narrower
callable claim without calling the whole-image milestone complete.

Run artifact-only and producer-assisted modes. The latter may close first.
Record the smallest reusable assistance required rather than requiring an agent
to maintain a duplicate representation of every instruction. A gap inventory
is a useful intermediate deliverable but does not pass the proof gate.

### C. Growth through the spike family

Follow spike order as their artifacts become available: Hello, sort, gzip,
web server, spinning cube. Use their actual accepted behavior to expose new
proof demands rather than predicting instruction lists in advance. Grow
coverage for loops, allocation/lifetimes, buffers, asynchronous operations,
and concurrency as demanded. Native CPU analysis does not establish safety of
shader/device execution; such dependencies need their own model connections
or explicit provider contracts before a broader claim can be made.

Track new obligations, reusable lemmas, assistance size, manual proof effort,
and rebuild cost at each step. Progress means stronger connected coverage and
lower repeated proof effort, not merely successful decoding of larger files.

### D. Compiler-produced C fixtures

Once the first connected spike proof establishes the seam, add small C fixtures
whose machine behavior isolates one intended memory property. Store source,
compiler/linker versions, target, flags, runtime/linkage choices, and exact
binary identity. Analyze the resulting binary; a C source expectation alone
does not determine the binary verdict.

For each fixture retain a safe control, an intended violating variant, and a
manifest of the expected property and required witness/input. Verify the
relevant operation survived compilation. If a transformation removes or changes
the intended operation, classify that build as unsuitable for that fixture
instead of treating absence of a diagnostic as analyzer success. The compiler
is not proof authority for imported bytes.

Begin with the smallest reviewed runtime/provider surface. CRT startup,
allocators, imported libraries, and loader-triggered execution must be included
or represented by explicit checked/trusted boundaries. A function-only harness
proves a callable claim, not its enclosing executable. Record how input and
environment conditions are established without assuming memory safety itself.

## 3. Discriminating fixture families

| Family | Safe control | Intended failing case | Required distinction |
|---|---|---|---|
| Buffer bounds | Guarded index | Reachable out-of-bounds read/write | Object bounds versus merely mapped pages |
| Stack | Live in-bounds local access | Escaped dead-frame access or reachable overwrite | Frame lifetime and local extent |
| Heap lifetime | Access before release | Access after release, including address reuse | Fresh allocation identity cannot revive old provenance |
| Deallocation | One valid release | Double release or invalid release | Allocator contract violation with feasible call history |
| Initialization | Read after complete write | Read unwritten bytes after partial write | Only committed bytes become initialized |
| Pointer representation | Checked whole-pointer copy/recovery | Partial overwrite or unproved reconstruction | Failed reconstruction may remain a proof gap |
| Size arithmetic | Checked size/index calculation | Wrapping calculation feeding an invalid access | Arithmetic anomaly alone is not the memory violation |
| Permissions | Access with applicable rights | Reachable denied read/write/fetch | Architectural fault versus proof/authority denial |
| External operation | Valid buffer through completion | Invalid extent or premature release | Provider effects and lifetime contract |
| Concurrency, later | Properly synchronized access | Feasible conflicting access | Schedule/order witness and applicable model rule |

Source labels are fixture intentions. Only checked binary evidence determines
the final result. Some memory-model rules require object/authority evidence
unavailable from bytes alone; those fixtures deliberately test unresolved
classification as well as successful proof construction.

Begin with one safe and one violating bounds fixture, plus one honest proof-gap
fixture, rather than making all families prerequisites for first delivery.
Add optimization and compiler variants after this trio passes. Optional debug
metadata and stripped variants test assistance dependence. Include an
unreachable invalid operation so that syntactic pattern matching cannot pass
as a feasible violation proof.

## 4. Mutations and negative controls

For every accepted certificate, exercise changes that should invalidate its
dependencies: alter an instruction byte, operand, relocation, entry point,
section permission, import identity, or attached producer map. The expected
result is rejection of stale evidence or reanalysis; a changed byte is not
automatically unsafe. Preserve both exact original and mutant identities.

Also test semantic incompleteness: unsupported instruction, unresolved indirect
edge, unknown call, missing callback root, and unsupported loader feature.
These prevent universal certification and produce localized gaps, not safe
defaults. Test search timeout separately from a checked counterexample.

Adversarial proof controls include an impossible entry precondition, a
provenance annotation fabricated from an address, an omitted failure branch,
and a memory model that simply refuses an unsafe concrete access. The checker
must reject those shortcuts. A stale result cache and a modified certificate
claim must fail the frozen-bundle check path.

## 5. Reviewable results and acceptance

Each run reports target tuple and supported restrictions; exact artifact and
entry scope; producer status and assistance consumed; reached/decoded/unresolved
regions; checked control-flow coverage; property-level proofs, witnesses, and
residual goals; model assumptions; and reproduction identity. Include tool and
search failures separately. Percentages are descriptive and never certify
complete coverage without its theorem.

Use stable semantic identities to compare runs. Report proof-check time,
evidence-generation time, search budget, proof artifact size, authored invariant
burden, and dependency invalidation. A narrowed environment or property is a
changed claim, not an improvement on the previous result.

Acceptance for a proved case requires exact-byte loading/behavior coverage,
valid non-vacuous domains, memory reconstruction, all scoped safety obligations,
and the ordinary trust audit. Acceptance for a violating case requires a checked
feasible witness to its declared violation. Acceptance for a proof-gap fixture
requires the expected localized residual reason and no false safety/unsafety
claim. Runtime tests, emulators, and independent disassemblers challenge models
and aid diagnosis; they do not substitute for any of these proofs.

Specialists own the underlying ISA/platform/memory tests. `disasm` owns the
connected corpus and reports. Integration remains with the disasm/spikes
drivers under the [semantic review standard](REVIEW.md#implementation-peer-review); consult architecture for changes to
shared boundaries.
No new CLI names are fixed here: extend the existing Grass command/report
family when the first implementation establishes its concrete interface.
