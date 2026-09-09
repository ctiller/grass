# Disassembler development tools

Implemented: a Lean executable that reads real files, uses Grass's canonical
PE field readers and x64 decoder, and reports linear instruction evidence as JSON.
The bounded imported view follows the actual DOS NT-header offset and retains
the stub; the canonical writer/reader contract is unchanged.
`Grass.Disasm.Linear.partition` and `rows_bytes` prove exact byte retention,
including the entire suffix at a refused instruction. No instruction is skipped
to make a listing appear complete. Typed register/stack selectors supply assembly
text where available; other rows retain the decoder's opcode-family diagnostic
and full encoded fields under `encoding-only`.

This is the first implementation slice of [the feature design](../../docs/DISASM.md).
It does not yet recover CFGs, establish loaded execution, or issue memory-safety
proofs or violation certificates. ELF/ARM ingestion and general compiler-output
coverage remain unimplemented. A container/decoder refusal is not a claim that
the input is invalid for its actual platform.

```text
lake build grass-disasm grass-disasm-hello Tests.Disasm.Linear
lake exe grass-disasm-hello Spikes/1_Hello_World/Program.lean payload.bin .lake/hello.exe
lake exe grass-disasm pe .lake/hello.exe
lake exe grass-disasm raw input.bin 4096
python Tools/disasm/check.py
```

The Hello fixture exporter uses `SourceLinkedImage.buildExcept` and `writeImage`
on the actual source's assembly projection plus explicit payload file bytes.
It does not elaborate surrounding Lean declarations, derive data from a source
`def payload`, or claim to emit that complete source program. The smoke test
supplies the Hello CRLF payload explicitly. This exercises the production
composition seam while the accepted end-to-end spike artifact is pending.
Its output is structural evidence, not an accepted `VerifiedProgram`; it is
never executed by these commands.

Raw addresses use decimal input. PE listing addresses are RVAs, not loaded
virtual addresses. Listings cover executable sections' file-backed virtual
extents, retain raw padding separately, and report zero-fill sizes separately.
Imports are absent or present-but-unresolved; opaque remaining directory bytes
are retained without claiming relocation resolution. The fixed per-region
instruction budget is 4096. Budget exhaustion retains the unconsumed suffix.

Exit status 0 means the requested linear decode completed, 3 means a listing
stopped (unsupported/canonical refusal, truncation, PC wrap, or budget), and 2
means argument, I/O, or container failure. Every report states that memory
safety remains unresolved. JSON is a diagnostic projection, not proof authority.

The C pair in [Tests/Disasm/C](../../Tests/Disasm/C) starts the next milestone.
Both use the same callable precondition: a pointer to a live writable eight-byte
object. Their compiled four-byte stores must be recovered from actual bytes.
Source labels and the presence of an out-of-bounds-looking instruction alone
are not violation proofs. No standalone process-entry contract is claimed.

On Windows, build the actual compiler artifacts and an independent dumpbin
listing with the installed MSVC x64 tool directory:

```powershell
./Tools/disasm/build-c.ps1 -CompilerDirectory '<MSVC>/bin/Hostx64/x64'
python Tools/disasm/check.py --compiled-c .lake/disasm/c
python Tools/disasm/observe-c.py .lake/disasm/c
lake exe grass-disasm store .lake/disasm/c/store_oob.dll 4096 5368709120 8192 8 16
```

The generated manifest records source/binary hashes, tool versions and exact
arguments. These are reproducibility metadata, not proof authority. Binaries
and local tool paths remain under `.lake` and are not committed.
The build also retains separate DLL disassembly and export listings. These make
the observed library inspectable, but no checked parser currently binds the
printed `probe` export RVA to its disassembled bytes; that connection remains a
formal artifact/entry obligation.

The optional Windows observation harness calls each generated DLL in a child
process. An eight-byte target array and eight-byte adjacent canary share a
sixteen-byte structure. The safe function changes the target; the bad function
changes the canary. This is native corroboration of a controlled object-boundary
overwrite, not a kernel-checked violation certificate. The separate
`StoreAttempt`/`Spatial` proof components currently establish only conditional
decoded-footprint properties; fetch, entry and coherent caller history still
need to be connected before a formal binary-violation claim.

The `store` command takes decimal RVA, declared image base, declared object
base, object size, and enclosing allocation size. It retains the checked PE
parser result, refuses ambiguous/unmapped/zero-fill entry selection, and binds
the candidate instruction to its exact original file slice. It constructs a
checked, synthetic caller data model with RCX at the object's start and uses
the shared memory checker for the decoded four-byte footprint. Status 0 means
this conditional assessment completed, including an outside-object result;
status 2 means refusal. Neither result establishes whole-binary safety.
The example RVA is specific to the generated fixture and is not an export
resolver. Declared addresses and allocator provenance are assumptions, not
facts inferred from the binary or observed native process.

## Cleanup disposition after checkpoint 0badf267

The checkpoint's independent reviews support these bounded maintenance actions.
They are separate from the functional fetch, execution, history, and ELF/ARM
obligations above.

| Item | Disposition and revisit |
|---|---|
| Temporary C7 address/width model | Move the existing implementation into the x86 execution namespace with a compatibility adapter; retain explicit candidate-only scope. Disasm integrates and x86 reviews. Revisit when x86 exports general operand/attempt semantics, replacing this bounded implementation rather than adding another authority. |
| Imported parser paths | Keep `CheckedImportedImage.readExact` in every entry/fetch consumer. No second raw parser is warranted; the canonical reader and bounded imported reader serve different documented contracts. Revisit when widening the imported container profile. |
| Source-ledger debt | Preserve all new modeled PE/ISA declarations as explicit debt until formal source anchors are reviewed. Namespace migration must transfer coverage without deleting obligations or increasing apparent citation coverage. Revisit at the next ISA-source anchoring change. |
| Corpus maintenance | Keep compiled EXE/DLL files, disassembly, hashes and local paths generated under `.lake`; retain authored C and exact byte-preservation tests. The handwritten MSVC prefix is a fixed parser regression specimen, not a generated golden image; no regeneration is warranted now. Revisit if its provenance or asserted fields change. |

No broad rewrite is warranted by the checkpoint reviews. These actions preserve
the existing proof and refusal boundaries while reducing duplicated ownership.

## Two-store corpus and fetch connection

`sequence_safe.c` and `sequence_oob.c` add a first write to `p[0]` before the
safe `p[1]` or bad `p[2]` write. Volatile stores retain two separate instructions
under the selected optimizing compiler. Build and inspect them with:

```powershell
./Tools/disasm/build-sequence.ps1 -CompilerDirectory '<MSVC>/bin/Hostx64/x64'
lake exe grass-disasm stores .lake/disasm/c-sequence/sequence_oob.dll 4096 5368709120 8192 8 16
python Tools/disasm/check.py --compiled-sequence .lake/disasm/c-sequence
python Tools/disasm/observe-c.py .lake/disasm/c-sequence --family sequence
```

`stores` assesses each supported linear store candidate under the same declared
caller data snapshot. It does not execute preceding stores or prove that the
snapshots form a feasible trace. Every decoded row is assessed independently,
including rows after a refused candidate, with that refusal retained. The linear
decoder itself stops at its first unsupported instruction and retains the
refused suffix; candidate inspection cannot cross that boundary. RET is still
outside the selected decoder, so these examples return status 3 and leave
whole-scope safety unresolved, including the example whose stores fit.

The separate `FetchedEntry.Binding` proof adapter checks agreement between an
imported entry and an actual initialized execute-access `FetchedSite` receipt.
Its `original_event` theorem connects the event's observed instruction to the
original PE bytes. It requires a supplied checked fetch; the CLI does not
construct that receipt, establish an OS loader, or prove a store transition.

## Completed model witness

`StoreCompletion` now joins an actual fetched C7 candidate to a subsequent
completed write, preserving policy/context continuity, exact payload, placed
address, and backing mutation. `CompletedViolation` attaches the original PE
entry and an object in that same caller state, and proves that an actually
committed byte lies outside the declared object. Root-allocation permission
does not discharge object bounds.

`Tests/Disasm/CompletedStore.lean` constructs a closed code/data-backing fixture:
the original C7 bytes are fetched, the root16 byte at offset8 changes from0 to42,
and the narrower object8 witness identifies that committed byte as excluded.
It also checks an enlarged referent and an unrelated-pointer refusal. This
fixture uses the explicitly unproved `FakeIsa` profile package; its theorem is
a declared-model witness, not Windows execution adequacy or recovered C
provenance. The host CLI still reports candidate assessments, not these receipts.
