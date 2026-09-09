# Hello World unwind and PE binding

Status: bounded architecture interpretation, 2026-09-09, independently reviewed
and approved by Windows against the named source and official requirements.
This applies existing [Hello acceptance](HELLO_WORLD.md),
[Spike 1 section 6](SPIKE_1.md), [ABI requirements](PLATFORM_ABI.md) and
[artifact requirements](ARTIFACTS.md); it adds no alternative emission gate.

## Decision

The unchanged Hello image requires generated `.pdata` and `.xdata` for its one
non-leaf function, with a populated exception directory and exact code/metadata
placement connections. Calling `ExitProcess` does not waive those requirements.
Microsoft requires unwind information for functions that allocate stack space,
save nonvolatile registers or call other functions, and requires that it describe
how to undo the prologue. Hello does all three. Its ordinary exit path therefore
does not justify treating it as a leaf.
[Microsoft x64 prolog and epilog](https://learn.microsoft.com/en-us/cpp/build/prolog-and-epilog?view=msvc-170).

The selected Hello profile has no language-specific exception handler, frame
pointer or chained unwind entry. Supplying unwind information is not a new
exception-recovery policy: fault and containment behavior retain their existing
specification/profile meaning. No return epilogue is added to the authored code.

## Exact artifact interface

Root composes metadata derived from the same final source and checked placement
used by the emitted image. Windows owns PE validity and serialization; ABI/source
owners supply the prologue description and its connection to instructions.

| Input or result | Required connection |
|---|---|
| Final code extent | Start of this function's actual prologue through the exclusive end of all its emitted blocks, including containment tails; exclude unrelated alignment padding |
| Prologue result | Exact `SourcePrologue.Result` associated with the emitted source/frame, retaining generated instruction bytes and layout |
| Unwind info | `UnwindInfo` built from that result's layout, no frame pointer and `.noHandler`; no independently maintained Hello byte literal |
| Runtime-function record | Begin/end from final code extent; unwind-info RVA from the placed exact serialized `UnwindInfo` |
| Exception directory | RVA of the serialized runtime-function table and its exact unpadded byte count |
| Loaded connection | Directory and record resolve to those same mapped bytes, with code coverage and read permissions in the admitted loaded image |

Microsoft specifies three image-relative 32-bit fields per runtime-function
entry, DWORD alignment for the entry and unwind information, and ordered
function entries. Unwind codes use descending instruction-end offsets; the
header counts slots, with padding to an even slot count.
[Microsoft x64 exception handling](https://learn.microsoft.com/en-us/cpp/build/exception-handling-x64?view=msvc-170).

For this single-entry profile, the table occupies 12 meaningful bytes. The PE
exception directory is entry index 3 (offset 136 in a PE32+ optional header).
It points to the table, not to the unwind-info record. Section padding must not
inflate the meaningful directory size. PE directories identify tables through
RVA/size, not section-name discovery. Keep the authored profile's `.pdata` and
`.xdata` names and read-only initialized-data permissions while proving actual
RVA resolution.
[Microsoft PE format](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format).

Use checked section locations/extents before narrowing to 32-bit RVA fields.
Reject missing, wrapped, misaligned, out-of-image or wrongly permissioned
placements. Both metadata records must fit in their backed section bytes;
being outside `.text` alone is insufficient. One entry must cover this whole
contiguous function; splitting/reordering blocks would require corresponding
reviewed range handling rather than retaining a stale end address.

If layout is prepared before final metadata bytes, preserve the measured
section lengths and establish that replacing placeholder content with derived
metadata keeps the checked placements and directory locations exact. Reuse the
existing checked-plan binding/invariance pattern. No general linker framework
is required for this bounded composition. Root must not patch header bytes
outside that checked plan. Windows owns the typed directory/layout/writer/reader
extension unless spikes explicitly assigns it otherwise.

## Current implementation and limits

* `Grass/Assembly/SourcePrologue.lean` derives `unwindLayout` from generated
  instruction sizes. `code_offset_naturals`, `stored_prologue_size` and
  `every_instruction_decodes` supply local identity/decoding facts. Its own
  scope excludes physical stack semantics and full body lowering.
* `Grass/ABI/Win64/UnwindBytes.lean` supplies `UnwindInfo.mk?`, serialization,
  `RuntimeFunction.toBytes` and `SearchablePdata`. Its structural checks do not
  prove that a pointer resolves to the actual placed `.xdata` or that the
  serialized record describes the exact source instructions.
* `Prologue.codes_stackDelta` in `Grass/ABI/Win64/Unwind.lean` equates total
  stack-depth arithmetic. Its comment explicitly leaves register restoration
  and ordering separate. It is not a full semantic unwind theorem.
* The inspected Windows PE `OptionalHeader.writeDataDirectories` populates
  imports and leaves other directories absent. Adding metadata as raw sections
  without changing this directory path would not complete the connection.
  The independent reader currently retains the later directory bytes opaquely;
  its expected records and exact roundtrip proofs must track the extension.

The current regression fixture encodes three two-byte pushes of `r12`, `r13`,
`r14`, followed by four-byte allocation of 48 bytes. It expects instruction-end
offsets 2, 4, 6, 10; prologue size 10; four unwind slots; no frame register or
handler; and 12 bytes of unwind information. Those are existing fixture values,
not new caller inputs. Derive them from the realized source and recompute when
its encoding or frame changes.

## Acceptance obligations that remain

1. Extend the PE writer and independent reader/roundtrip to carry the exact
   exception-directory entry, table bytes and unwind bytes. Check malformed
   range, alignment and target cases as well as the successful fixture.
2. Bind the prologue result to the final code prefix and table range after
   source resolution. Code offsets are relative to the function start, not the
   image base or end of the generated prefix.
3. Prove unwind reversal for the realized prologue: saved registers, stack
   contents and caller context, including permitted partial-prologue states.
   Body invariants must preserve the frame needed by that interpretation.
   Microsoft distinguishes prologue, epilogue and body positions when applying
   unwind records; correct serialization and total stack delta alone do not
   establish those cases.
   [Microsoft unwind procedure](https://learn.microsoft.com/en-us/cpp/build/exception-handling-x64?view=msvc-170#unwind-procedure).
4. Connect loader entry/stack assumptions and mapped metadata to the same
   execution and certificate. Parsing a PE and finding an entry is evidence
   about the modeled artifact, not by itself a proof of platform adequacy or
   safe emitted execution.

Spikes owns dispatch and integration of this composition. Windows supplies the
format-validity boundary; source/ABI and lowering supply exact instruction and
frame semantics. Architecture resolves interface conflicts. A format-only
checkpoint can proceed with these remaining obligations explicit; final Hello
acceptance cannot omit them or replace them with a successful normal run.

Validation: Windows independently reviewed the full document and relevant
source declarations with no blocking findings. `check-doc-links.sh` passed for
all 57 Markdown files; the staged diff passed `git diff --cached --check`.
No new implementation or semantic proof is claimed by this document checkpoint.
