# Linux platform implementation

This support slice starts from `8fc533af`. Linux work is active alongside the
other platforms and spikes. The modules below are reusable boundary components;
they are not a completed Linux program, loader, or `VerifiedProgram` producer.

## Syscall boundary

[`Syscall.lean`](../Grass/Platform/Linux/Syscall.lean) models a bounded selection
of native Linux syscall identities and argument/result decoding. Physical trap
execution belongs to the ISA modules. Linux must connect the exact reached
registers to the selected ABI and provider operation; successful decoding alone
does not establish that an instruction executed, that its memory arguments are
authorized, or that the kernel implements the provider relation.

Direct syscalls and library wrappers are distinct boundaries. Native syscall
number and argument widths, errors, register preservation, signal/restart
behavior and completion must follow the selected profile. A file descriptor's
integer representation is not evidence of its rights, lifetime or resource
identity. Existing common call occurrence, loan and synchronization machinery
remains the owner of custody and ordering; Linux does not introduce a parallel
memory model.

The [native probe harness](../probes/linux/README.md) records external
observations. Its independent comparator can expose disagreements, but is not
an extraction of the Lean definitions or proof of kernel conformance. Test
reports must distinguish a model mismatch, a harness failure, and an outcome
that the campaign did not observe. Native applicability is separate from a
conditional theorem about the modeled boundary.

## ELF header and shared readers

[`Header.lean`](../Grass/Artifact/ELF/Header.lean) provides a complete structural
ELF64 little-endian header reader/writer. Identification bytes, field widths,
file offsets and the virtual entry address are retained. The structural reader
is explicitly selected for this layout; it does not discover arbitrary ELF
classes or byte orders. Its universal writer-to-reader theorem retains an
arbitrary suffix exactly. Its converse reconstructs every successfully consumed
header and proves exact 64-byte consumption. The selected reader additionally
checks the bounded canonical identification, version and header-size profile,
rejects incompatible truncated prefixes, and reports the full header deficit.

This is a header component, not a supported executable format. Program and
section tables, range/overlap checks, architecture flags, relocation,
permissions, load-context inhabitance, and the exact bytes-to-initial-state
connection remain required. In particular the header's machine field does not
establish instruction validity or Linux applicability, and a successful parse
does not establish loadability. Full grammar realization and universal
incomplete/invalid classification laws remain beyond the current success laws.

ELF is the second consumer of
[`Binary.ReaderCore`](../Grass/Artifact/Binary/ReaderCore.lean). The existing PE
readers now use the same sequencing implementation; the historical PE name is
only an abbreviation. Endian readers and their universal laws are reused
unchanged. [Header tests](../Tests/Artifact/ELF/Header.lean) check both machine
values, independent byte offsets, suffix retention, unsupported profiles and
truncation. These checks do not prove loading or execution.

## Source authority

- [System V generic ABI: ELF header](https://gabi.xinuos.com/elf/02-eheader.html)
  defines the field layout and identification; accessed 2026-09-09.
- [Linux syscall interface](https://man7.org/linux/man-pages/man2/syscall.2.html)
  distinguishes the library wrapper and architecture calling conventions.
- [Linux write](https://man7.org/linux/man-pages/man2/write.2.html) describes
  partial writes, errors and signal interactions.
- [Linux exit](https://man7.org/linux/man-pages/man2/_exit.2.html) distinguishes
  the raw thread exit from the library's thread-group behavior and describes
  the observed status domain.

ISA trap receipts, confined provider memory effects and output observation,
return/terminal transitions, and exact loaded-source execution must be connected
before any whole-program Linux assurance claim is made.

## AArch64 request interpretation

[`AArch64.lean`](../Grass/Platform/Linux/AArch64.lean) now consumes the existing
ISA `SupervisorCall.Request word before` directly. `DecodedRequest` adds only
the selected immediate-zero condition and native ABI interpretation, deriving
arguments and the low-32-bit syscall number from the same pretransfer CPU.
The former Linux source-indexed wrapper, second instruction decode and redundant
source-prefix theorem have been removed by agreement with the AArch64 owner.
ISA `SourceWord.bytes_exact` owns source reconstruction, and
`BodyStep.supervisorRequest` projects an existing body receipt without decoding
again. These canonical producer APIs arrived in reviewed checkpoint `967f5512`.

This is a checked source interpretation. SVC-zero is an emitted-profile
restriction, not a claim that Linux rejects all other immediates. The decoded
ISA request supplies no actual instruction fetch, exception admission, Linux
kernel routing or provider result. Those missing connections are not replaced
with caller-selected predicates or a fabricated call occurrence.

[Request tests](../Tests/Platform/LinuxAArch64.lean) exercise the shared source
parser and ISA request producer, and directly consume existing body receipts for
both SVC-zero acceptance and another immediate's refusal. They also check
read/write selection, high number bits, suffixes, unsupported words/numbers and
short source. Native AArch64 execution remains unobserved.

At the historical pre-backfill checkpoint `7c37cb97`, Sol independently reviewed
the source adapter with no blocking semantic findings.
The broader `lake build Grass Tests.Platform.LinuxAArch64
Tests.ISA.AArch64.Control Tests.Platform.LinuxSyscall` check passed 396 jobs.
A fresh citation census passed with 760 definitions, including two additional
explicitly owed adapter definitions (359 total owed, 395 mechanical, 6 cited).
A fresh imported-closure trust audit with the foundation and Linux tests passed
2,479 project declarations; the three adapter theorem roots use only
`propext` and `Quot.sound`.
The full-suite limitation described below remains inherited from the baseline.

## Next AArch64 entry consumer

The proposed next bounded consumer is native A64 EL0 userspace issuing the
selected read, write, exit or exit-group request through SVC-zero, with an
explicitly selected non-VHE kernel-at-EL1 execution profile. The ISA owner
confirmed the bounded regime and supplied an explicit routing checker, while
complete eligibility and transfer remain open;
neither the Linux name nor the decoded word establishes that regime.

The connection requires these pieces of evidence:

- An actual execute-read at the reached user virtual PC, retaining the current
  address-space context, input/output memory state, bytes and failure outcomes.
  The existing fresh physical boot fetch does not provide this evidence.
- Effective execution and control configuration sufficient for the ISA's trap
  checks and destination selection, followed by the actual exception transition.
  The ISA owner determines the required configuration and saved-state, syndrome,
  vector-target and register-framing effects from its architectural sources.
- A Linux request derived from the retained pretransfer registers of that same
  occurrence, using the existing source adapter. Posttransfer state must not
  substitute for the syscall's input state.

The complete reached Linux execution producer is currently missing. The shared
`AccessFactory.access` seam (`d95e4817`) accepts an arbitrary actual predecessor
state; `Op.ReadObservation` (`676c1943`) exposes its completed read bytes and,
under the selected memory oracle, relates them to the resolved backing bytes.
Linux/AArch64 must supply the reached predecessor, address-space context and
virtual-PC descriptor linkage. This consumer introduces no separate Linux
memory model. The image initialization below supplies initial logical segment
placement; it does not prove a later PC is reached or that physical translation
realizes the supplied allocation identities. Other exception regimes require
their own supported profile.

Architectural entry also does not prove Linux provider dispatch. The inspected
[arm64 kernel syscall entry implementation](https://raw.githubusercontent.com/torvalds/linux/master/arch/arm64/kernel/syscall.c)
(accessed 2026-09-09) has asynchronous MTE-fault and syscall-work paths that can
defer, alter or skip invocation. A future kernel/provider connection must retain
the applicable path and its effects. The current native userspace probes cannot
observe the privileged entry state, and supply no evidence for that connection.

## General ELF segment initialization

[`ProgramHeader.lean`](../Grass/Artifact/ELF/ProgramHeader.lean) serializes all
eight ELF64 program-header fields in their specified 56-byte layout. Universal
suffix round-trip, successful-read reconstruction and exact consumption laws
reuse the shared endian parser. The [GABI program-loading specification](https://gabi.xinuos.com/elf/07-pheader.html)
supplies segment layout, alignment, file/zero-fill and permission rules.

[`LoadPlan.lean`](../Grass/Artifact/ELF/LoadPlan.lean) parses the exact input file's
header and program table, then checks a selected fixed-address ET_EXEC profile.
Machine, page size, permitted user-address interval and maximum mapped-byte
count are explicit data. Only PT_LOAD and PT_NULL are supported; interpreter,
dynamic, TLS and other segment types are refused. Extended program counts are
also unsupported. The checker validates table bounds before table recursion,
file/memory extents, nonwrapping virtual placement, alignment, ordered disjoint
logical segments, exact permission flags, aggregate size and executable entry
containment. The loader derives each segment's file slice and zero-filled tail
only after accepting the plan. Public raw byte helpers have conditional laws;
calling them alone does not confer load admission.

[`Loader.lean`](../Grass/Platform/Linux/Loader.lean) installs those computed
segments through the shared initialized-region implementation. It checks complete
fresh identity assignments, represented history, final records, disjoint virtual
placement and a four-byte aligned AArch64 entry range in an executable segment.
The supplied context must already be a thread. Output projections retain that
context, all input general registers/NZCV and non-memory machine fields; the PC
comes from the same parsed ELF header. General laws connect original file bytes
and zero-fill bytes to initialized cells of the final authoritative memory.

Windows and Linux now share
[`InitializedRegion.lean`](../Grass/Memory/InitializedRegion.lean) and
[`ImageInstall.lean`](../Grass/Memory/ImageInstall.lean). Windows keeps compatible
names while both consumers use the same installation, freshness, placement and
record laws. No Windows stack or PE import semantics moved into Linux.

This is logical image initialization, not Linux execve: page tails/page tables,
physical permissions, initial stack/auxv, relocation/interpreter setup, feature
configuration, instruction fetch, exception entry and provider execution are
not established. Configuration is passed separately to the ISA consumer; the
ELF machine tag cannot establish effective EL or feature state. Terra independently
reviewed the segment checker, installation connection and final request backfill
and found no blocking semantic issues in this scope.

Polonius GNU readelf 2.45 independently inspected the exact Lean-emitted segment
fixture: 4,098 bytes, AArch64 ET_EXEC, entry `0x400000`, one PT_LOAD at file
offset `0x1000` and virtual address `0x400000`, file size 2, memory size 4,
read/execute flags and alignment `0x1000`. SHA-256:
`350bdb04b40eb83749f12a9fd695b9b087ecbe2dd98e53b23219ecbf8c550ebd`.
This checks the serialized format independently; the fixture was not executed.

After merging the repaired main baseline `34265675`, the full build passed
671 jobs. The final source-input check rebuilt the test closure (646 jobs) and
re-elaborated its source-embedding module. The whole-library axiom audit passed
34,295 declarations across 413 modules. The full trust audit passed its 4
foundation roots/42,088 project declarations, 75 selected declaration checks,
8 executable test modules and negative controls. These are repository trust
checks, not a Linux whole-program producer claim.

Independent merge review found and required enrollment of the AArch64
control/source/routing cohort in the unified citation ledger. The corrected
fresh census passes: 845 modeled declarations, 6 cited, 409 explicit citation
debts and 430 mechanical definitions. Existing ISA source records do not erase
that debt. Docstring, observation-coverage, source-mirror, relative-link and
diff checks also pass. Reviewed owner comment fixes for AArch64, Wasm and WGSL
were incorporated without semantic changes.

## Historical initial checkpoint evidence

Semantic review separated the syscall decoder, ELF parser and native observer.
Terra reviewed the ELF layout and shared PE sequencing and required successful
parse reconstruction; that law was added and independently inspected. Sol
reviewed selected-prefix rejection and full-header completion hints. Parent
review of the native harness required missing-record EOF handling, exact read
observation, child-PID comparison and a wrong-prefix negative control; the final
campaign includes those fixes. Routine proof corrections were checked by Lean.

The final bounded library/test command passed 398 jobs:

```text
lake build Grass Tests.Artifact.ELF.Header Tests.Artifact.PE.Reader Tests.Artifact.PE.Imported Tests.Artifact.PE.Exceptions Tests.Artifact.PE.ImageWriter Tests.Artifact.PE.LayoutBinding Tests.Artifact.Binary.Primitive Tests.Artifact.Binary.Endian Tests.Platform.LinuxSyscall
```

A fresh `lake env lean Tests/ISA/X86/LedgerAudit.lean` passed. Ten new Linux
API/ABI definitions remain explicit formal citation debt, with primary sources
recorded; the census is not claimed to supply their missing ledger attachment.
The actual census is 758 definitions: 6 cited, 357 owed, 395 mechanical.

A fresh custom audit importing `Tests.Foundation`, both Linux modules and the
Linux syscall test, plus the ELF, PE reader/import/exception/layout and binary
tests, ran `#audit_verified_programs`: 4 foundation producer roots and 9,018
project declarations passed. The named ELF reconstruction/round-trip and Linux
error/register-extraction roots use only the repository's allowed Lean axioms.
This is an imported-closure audit, not the full filesystem audit population.

The full default build and full `audit-trust.sh` are blocked on the inherited
`Tests/Memory/Spike1Reference.lean:93` reference to the
`Grass.ABI.Win64.spike1FrameLayout` definition removed by baseline `8fc533af`.
Dependent test imports consequently cannot be audited. The source-input script
also requires this full Tests build. No production spike-specific frame default
has been restored by this Linux slice. Corpus source consistency and relative
documentation links passed.

Native validation ran on polonius, Linux `6.17.0-41-generic` x86-64, GCC 15.2.0.
Seven read/write/error/number-width observations, two parent-observed exit
cases, five harness controls and three comparator mutations passed. AArch64
native execution, forced partial completion, signals/restarts and arbitrary
failure effects remain unobserved. Final probe SHA-256 identifiers:

| Input | SHA-256 |
|---|---|
| C source | `cf209236787a0e424f88a60d570abeaf6d4589078bd7197ffd0bb7efc9eebfca` |
| Python runner | `fcbae77427834e5c542f77cd7eb5f48e6a8730d11f27722c54ac53bb3340747d` |
| Native binary | `0f94acbaa736e83c0dd77d20e42d52b69da63895822d9ee593f1a95da8bea377` |

GNU readelf 2.45 on polonius independently inspected two exact Lean-emitted
64-byte headers. It reported ELF64, little endian, header size 64, and the
respective x86-64/AArch64 machine fields. These fixtures deliberately have no
program/section tables and are not executable demonstrations. Their hashes are
`b185548fb4f75e7d3ce078bebe14e05ad99167302cfda82273e2c4d389f2a15e`
and `051bf339d2c060ef20ebe3ccfdc7a8cf36d8eb485122f84933c7a355b62217c6`.
