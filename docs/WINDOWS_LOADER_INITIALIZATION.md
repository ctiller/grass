# Preferred-base initialization checkpoint

[`LoaderEntry.initialize?`](../Grass/Platform/Win32/LoaderEntry.lean) computes a
bounded initial state for exact checked PE output. Its input is an
instruction-independent `PE.ImagePlan` plus host bytes equal to `writeImage`.
`ImageInput.read_exact` connects those bytes to the independent complete PE
reader. The platform module does not import source assembly.

The result contains the existing `X86.Execution.State`, with one embedded
`Memory.MachineState`. Header and logical section views have derived addresses,
section permissions, and authoritative initialized backing bytes. Every import
target is supplied in the plan's library/symbol order; missing or extra targets
are refused. Eight-byte IAT patches use the plan's derived slot locations.
`patchedByte_outside` frames bytes outside those slots. `LoadedImage.cellAt?`
exposes initialized bytes from the actual final allocation/backing records.

The initializer uses the public backing/allocation doors. It checks represented
identity freshness against allocation/backing tables, grant roots, historical
event roots and captured backing identities, and recorded violation roots.
Successful sequential installation rejects duplicate image identities.
`installRegions?_allocation_preserved` and `installRegions?_backing_preserved`
frame existing storage. `LoadedImage.environment_frame` retains the complete
input machine's history, obligations, faults, violations, contexts and event
supply. The environment is not replaced with an empty disposition inventory.

The input supplies actual stack storage and return bytes. Checks require a live
CPU stack view owned by the entry thread, read/write permission without execute,
entry RSP congruent to 8 modulo 16, the return slot and 32-byte home area, and
the requested frame window below RSP. Future stack accesses still require the
existing memory authority/race checks. Return bytes alone do not establish
pointer provenance or a valid return target. All GPRs and full RFLAGS are input
data; this intermediate ABI condition checks reserved bit 1 and clear DF.
It does not force IF, RF or other unrelated bits to zero.

`entryRip_exact` and `regionPlacement_exact` prove natural address sums before
any modular truncation. The first instruction must still pass x86's actual
initialized execute/fetch check. Entry in an executable section is not a proof
that a complete instruction is fetchable.

## Applicability still owed

This result is a preferred-base initialization subprofile. It is **not** the
canonical Win10 x64 loader/execution profile, ASLR acceptance, runtime safety,
or a `VerifiedProgram` certificate. In particular:

- Loading at other admissible bases needs actual relocation/loader rules or a
  proved reason that the exact image needs no fixups. The public base domain
  must not be narrowed to a singleton to avoid that work.
- Logical payload views do not describe all physical page tails, raw padding,
  gaps or loader storage. Their placement must relate to the actual loaded
  memory; unrepresented CPU behavior must not disappear from execution.
- Physical loader behavior, DLL initialization/callbacks, exact import export
  identities, stack/environment setup and API semantics require correspondence
  evidence. The exact canonical writer leaves the image's TLS and relocation
  directories empty; that does not eliminate imported DLL behavior.
- Freshness outside built-in machine records needs a consistent execution
  identity domain and coverage of protocol-owned references. Opaque protocol
  evidence is not discoverable by scanning `MachineState.obligations`.
- No future progress, interruption behavior or terminal outcome is supplied by
  initialization. Full source frame/stack and instruction-step bridges remain
  separate consumer obligations.

Format and ABI authorities are Microsoft's [PE Format](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format)
and [x64 calling convention](https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention).
Formal citation-ledger coverage remains explicit debt; comments and samples do
not discharge it.

## Validation

[`Win32LoaderEntry`](../Tests/Platform/Win32LoaderEntry.lean) checks missing and
extra import data, reused IDs, context/flags/stack failures, physical aliases,
historical identity reuse and patch framing. It also initializes a PE produced
from the unchanged authored Grass Hello World through `SourceLinkedImage`.
These are executable model tests, separate from universal kernel proofs.

[`run-grass-hello.sh`](../probes/windows/run-grass-hello.sh) launches the same
Grass-authored program as a native PE, with redirected byte streams and a
timeout. The Lean exporter is host plumbing; the binary body is Grass, with no
C/Python implementation. Generated binaries and observations stay under
`.lake/grass-windows-probes`.
The exporter reads authored bytes at runtime and passes those exact characters
to the source linker, avoiding cached source embeddings. It records the input
snapshot whose hash the launcher reports; the supplied static payload is also
recorded as the expected output. Bash owns orchestration, with `--emit-only`
available on Linux and a narrow PowerShell helper for Windows process capture.

The initial 2026-09-09 sample produced a 3,584-byte image with five sections,
entry RVA 4096, exact 15-byte output, empty stderr and exit status zero. The host
reported `Microsoft Windows 10.0.26200`, X64. This is one host observation, not
validation of the complete target Win10 profile, actual load base, memory
mapping contents, general `WriteFile` outcomes or ASLR closure. The generated
result records source/image hashes and raw output for comparison.
