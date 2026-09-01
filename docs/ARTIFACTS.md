# Serialization, linking, and executable artifacts

## 1. Parser/writer law

Every writer has a reader for the same modeled format. For formats whose source
type is intrinsically writable, it proves:

```lean
parse (write x) = .ok x
```

For formats with separately representable invalid states, the writer accepts a
compact `CanonicalArtifact`/`Writable` value produced once by validated linking,
or the theorem is quantified by `WellFormed x`. It is not an impossible claim
over inconsistent lengths, overlapping sections, or other non-writable values.

Readers that accept noncanonical representations additionally prove, on their
accepted and writable domain:

```lean
parse bytes = .ok x -> write x = canonicalize bytes
```

`canonicalize` is specified and idempotent on accepted input. Parsers follow
their cited format specification, validate lengths and arithmetic before use,
reject malformed/unsupported data, and never rely on successful round-trip as a
substitute for general parser correctness.

Exact byte round-trip is optional when a format intentionally admits multiple
representations, but the two laws above remain at the modeled value level.

## 2. Instruction encoding

Exact encoding objects may prove byte-for-byte decode/encode laws. Semantic
instructions may use the weaker and more important theorem:

```lean
Applicable i ->
  ∃ i', decode (encode i) = .ok i' ∧
        CompleteStepBehaviorEquivalent i i'
```

This prevents redundant prefixes, encoding aliases, or width choices from
making instruction reasoning unnecessarily difficult.

## 3. Artifact connection

Serialization correctness alone does not prove that the executable contains the
program that was verified. Each executable format supplies a connection theorem
covering:

- headers and selected architecture/platform;
- mapped sections and final permissions;
- code bytes and instruction decoding;
- symbols, exports, entry point, and reachable CFG roots;
- imports and their modeled API identities;
- relocations under an arbitrary admissible load base;
- unwind/exception metadata;
- data initialization and provenance roots.

Connection includes loadability, not only conditional behavior: for every
admissible load base and import environment satisfying the artifact's declared
requirements, the exact written bytes parse and the abstract loader relation
produces at least one valid initial machine. The admissible-base and
import-environment domains each have independent inhabitants defined without
reference to loading or execution. Every loader result is proved a valid initial
state and is then subject to execution adequacy and behavioral inclusion. A
theorem quantified only under an uninhabited domain or `Loads` premise is
rejected as vacuous.

For the initial artifact, loading the exact written PE bytes, applying
relocations, resolving imports, and decoding `.text` must produce a raw machine
whose every behavior is included in the `RawProgram` attached to
`VerifiedProgram`. This connection composes with raw-to-ghost inclusion into the
certificate's final loaded-bytes theorem; pairwise equivalence alone is not the
public assurance claim.

## 4. Abstract loader transition

Grass models the necessary Windows loader contract rather than the entire
loader implementation:

1. parse and validate the PE32+ image;
2. choose an aligned abstract ASLR base;
3. reserve/map image sections;
4. apply base relocations using temporary loader-write authority;
5. resolve every derived import to a callable satisfying its API/ABI profile;
6. patch the IAT;
7. establish final section permissions and image provenance;
8. establish unwind metadata and transfer control to the entry point.

The actual Windows loader is a platform trust item challenged by probes.

## 5. PE/COFF and libraries

The first writer/reader covers the canonical subset required for a PE32+ image
and COFF object/library production. All represented structures participate in
round-trip and validation laws, including optional headers, sections, imports,
relocations, symbols/exports, `.pdata`/`.xdata`, and alignment/padding rules.

Imports are derived from realized API operations. Exports are derived from
verified callable declarations. Unused imports and unmodeled entry points are
rejected by the verified artifact gate.
