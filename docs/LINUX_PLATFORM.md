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

## Checked checkpoint evidence

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
