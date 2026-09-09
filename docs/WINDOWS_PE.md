# Windows PE container and Grass probe path

Windows validation programs are to be authored in Grass and emitted through the
production PE path. The retained C/Python WriteFile experiment is auxiliary
evidence only; it does not validate Grass code generation. The source-body and
named-static binding work is coordinated by the `spikes` task.

## Checked layout and serialization

`ExecutableImageDescription` contains raw section bytes, named import requests,
and a section-relative entry location. `prepareImage` resolves this into an
`ImagePlan`. Its single proof-linked `ImageLayout` supplies section placement,
entry RVA, import-directory RVA, IAT slots and image size. Import materialization
uses a provisional placement to discover its RVA, then validates that the final
section bytes agree with the final placement. All file offsets are measured
from the beginning of the complete DOS-aware file.

The first section RVA is the section-aligned extent of the complete padded
headers, rather than a fixed page. `ImageLayout.sectionsAfterHeaders` proves
that every mapped section starts after those headers; `headersWithinImage` and
`sectionsWithinImage` prove that the derived image size covers both. Regression
fixtures include 96 section headers, where the headers occupy 4608 bytes and
the first section must start at RVA 8192.

`ImageLayout.Writable` checks names, import resolution, section count, field
widths and exclusive endpoints before serialization narrows natural numbers.
`writeImage` takes only a checked plan. Source instruction encoding and static
symbol binding remain separate consumers of this layout; this module owns no
instruction encoding table.

`ImageLayout.coordinates_eq_of_lengths_eq` compares independently prepared
prototype and final layouts. Equal ordered source payload lengths, imports and
entry location imply equal section spans, entry RVA, image size, import-section
RVA, IAT queries and section-relative resolution. The proof includes import
materialization and its size independence under rebasing. Section bytes remain
those of each actual plan; no equality of payloads or implicit preparation
success is asserted. The source resolver can therefore handle final preparation
failure explicitly and use the theorem once it has the final checked plan.

## Independent reader and exact recovery

`readImage` decodes the DOS/COFF prefix, all optional-header bytes, every section
header field, header padding and all raw section payloads. It checks the selected
AMD64 PE32+ discriminators, the header extent and each declared raw offset against
the sequential file cursor, and rejects trailing bytes. Resource and exception
directory fields are decoded explicitly; twelve later directories are retained
as 96 opaque bytes. `.idata` is retained as section
payload. This reader does not interpret the import subtree.

`readImage_writeImage` proves, for every checked `ImagePlan`, that reading its
serialized image returns exactly `plan.expectedImage` and an empty remainder.
The expected record contains the decoded header fields and exact padded bytes
for every section. The proof uses independently implemented field readers,
endian suffix laws, checked narrowing, and contiguous placement. Reader code
does not compare input against a replay of the writer.

Recovery is to that decoded record, not to the original authoring description:
requested versus generated section ownership and the import-library tree are
not reconstructed. The reader also accepts and retains some reserved-field and
directory values that the writer does not emit.

This is not the converse canonicalization theorem for arbitrary accepted bytes,
a Windows loader-acceptance proof, an import-resolution execution proof, or a
`VerifiedProgram` artifact certificate. The selected DLL characteristics and
zeroed directories also remain subject to loader applicability review before a
production executable claim. Container conformance debt is not discharged by
the structural round-trip proof.

## Exception table binding

`ExecutableImageDescription.exceptionTable` optionally names the actual table
extent and ordered `RuntimeFunctionBinding` values. Each binding supplies a
section-relative code extent, unwind extent and exact unwind bytes. All complete
extents are nonempty and backed by section payload bytes; an exclusive code end
may equal its section's payload end. Address arithmetic is checked before DWORD
narrowing. Code requires readable executable code flags; metadata requires
readable initialized data without write, execute or discardable flags.

Root derives the unwind bytes from the selected source's typed `UnwindInfo` and
retains that ABI validity/source equality. PE treats those bytes as opaque: it
validates their exact placement, length and four-byte alignment, not semantic
unwind reversal. Runtime records must be ordered and disjoint. The final table
must equal every resolved begin/end/unwind triple in order, with no omitted
failed resolution; its meaningful size is exactly twelve bytes per record.

The prototype may reserve same-length table bytes with `exceptionTable := none`.
Use `resolveRuntimeFunctions?` and `writeRuntimeFunctions` to derive final table
bytes from its checked placement, then prepare the final `Some` description.
Final preparation rejects stale table or unwind bytes. Existing coordinate
invariance relates same-length replacements; exception-directory invariance
additionally requires the same table location and size. Hello must retain its
explicit `Some` binding at the final boundary.

The same production writer emits exception-directory index 3 from the actual
table extent. `ImagePlan.exceptionTable_binding` relates its decoded RVA/size
to the checked table slice and `readRuntimeTable`'s independently decoded
records. `readImage_writeImage` still recovers the entire image. These facts
establish container coupling; they do not supply source prologue semantics,
partial-prologue reversal, native loading or platform adequacy.
The record format and alignment authority is Microsoft's
[x64 exception handling](https://learn.microsoft.com/en-us/cpp/build/exception-handling-x64).

## Validation

Lean writer fixtures exercise checked entry rejection, section-count/layout
properties and imports. Reader fixtures exercise complete parsing, invalid MZ,
short header/payload with exact deficits, mismatched raw offsets and trailing
bytes. Those fixtures challenge behavior; the universal theorem supplies exact
writer-image recovery for all checked plans.

The citation audit now walks the PE directory as well as the ISA, ABI and
platform directories. PE constants, field schemas and selected profile checks
are enrolled as explicit citation debt; generic coordinate operations and
projections are separately reviewed. Removing a PE module or a writer's debt
entry is rejected by the audit. Microsoft source comments and structural proofs
do not silently count as confirmed ledger citations.

Grass-authored API probes should report return values, output bytes and count
slot observations against the semantic cases in
`Tests/Platform/Win32ProbeCases.lean`. A host launcher may start the generated
binary and collect observations; its code must not supply the probe body or a
parallel serializer. Native API applicability and execution evidence remain
distinct from container recovery.

The exception-table checkpoint received independent architecture and Terra
review of the actual format path and tests. The
[exception fixtures](../Tests/Artifact/PE/Exceptions.lean) build final table bytes
from provisional resolved coordinates and challenge stale bytes, missing targets,
permissions, overlapping functions, alignment and overflow. The existing image
round-trip theorem and the checked directory/table binding remain distinct from
the source/ABI and native execution obligations.

PE field authority: Microsoft [PE Format](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format),
especially DOS stub, signature, COFF header, PE32+ optional header, section table
and import directory. The restored writer family came from recut commit
`74b88ca7ef6c593adee07b661097e62ec37f0919`; its historical prefix-only reader
was replaced here by complete typed field and payload recovery.
