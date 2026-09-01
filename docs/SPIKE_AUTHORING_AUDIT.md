# Spike authoring cross-view audit

Status: blocking findings open. This audit applies the contract in
[SPIKE_AUTHORING.md](SPIKE_AUTHORING.md) to the current five-spike corpus. Three
independent agents reviewed Spikes 1–3, the HTTP/2 server, and the spinning cube.

## Post-audit repair status

The following findings are now closed in the working corpus:

- every fenced spike block has an immediate machine-readable classification and
  unique identity; the checker validates the entire document rather than only
  its terminal snapshot;
- all authored blocks match the recursively discovered `.lean` files exactly;
- standard artifact, writer/parser, decode/load, and soundness projections were
  removed from all five authored closing modules;
- unused standard process lookups and gzip records were removed; the fixed
  DEFLATE tables now come from one named `Std.Zlib.Fixed32K` static fragment;
- sort's physical failure paths now use its actual four portable outcomes while
  retaining detailed failure causes in the audit trace, and its parser witness,
  statics, and constructor family are explicit closing inputs;
- Web's fragment exit family is well scoped, SETTINGS acknowledgement has one
  owner, and both direct and fragmented HEADERS pass through explicit PADDED /
  PRIORITY normalization before HPACK;
- the cube extent constructor has typed arguments and writes the exact
  `imageCount` consumed by swapchain creation, and irrelevant inputs are
  explicitly accepted as stuttering events; and
- stale prose describing authored `Staged.lean` and `SourceClosure.lean` modules
  was removed.

The central blocking finding remains: raw expansion, certificate reports,
artifact outputs, mutation runs, and build/scale measurements are still **not
generated** or **not measured** because the supporting library is deliberately
out of scope. Several Web/Cube application-specific contracts and the exact
cross-ISA closing junction also remain under author-surface repair.

One Round 19 recommendation is rejected: stability remains precious in Spike 2
because stable ordering was an explicit product requirement. The logical spec
observes occurrence identities even when the selected console projection emits
equal byte strings. The proof factors as stable permutation over ordinal-tagged
occurrences followed by erasure of ordinals during byte serialization; a future
byte-only client may compose the projection theorem and reuse the stronger
implementation, but cannot retroactively weaken this spike's demanded theorem.

## What passes

`./check-spike-sources.ps1` passes for all five spikes. Under the documented
UTF-8/newline normalization, every recursively discovered authored `.lean` path
and its contents match the final exact-source snapshot in the corresponding
annotated document. This proves only snapshot equality.

The high-level file counts are plausible after consolidation: two files for
Hello World, three each for sort and gzip, and six each for HTTP/2 and the cube.
The audits nevertheless found generated plumbing inside several of those files;
a reasonable file count does not make every declaration reasonable author work.

## Corpus-wide blockers

1. Block classification and authored-source equality now pass mechanically.
   This does not make an interface or proof-sketch block generated evidence.
2. The current checker proves classification, identity uniqueness, and
   normalized authored-source equality. It does not reproduce constructor
   expansion, process/CFG extraction, source
   closure, proof reports, artifact layout, or bytes.
3. Generated expansion size, certificate/proof-term size, and clean and
   incremental check costs are not available because the libraries do not yet
   exist. Each spike must say `not generated` and `not measured` explicitly.
4. Ordinary artifact projection, writer/parser, decode/load, source-closure,
   adapter, and binding witnesses still appear in some authored files even
   though the standard closing form is meant to derive them.

## Spike-specific blockers

### Spike 1

The document's purported authored assembly is a different rendered shape from
the exact `Program.lean` source, and the alleged expanded view still contains
symbolic frame fields and wrapper constructs. It needs a labeled generated
rendering plus a separate fully lowered instruction/static/import/relocation
manifest. The standard stdout process/presentation and artifact projection
boilerplate should be tested against the claimed generated closing form.

### Spike 2

The handwritten “exact” `compareRecords` expansion disagrees with the authored
instruction order and opcodes. `bufferAppend` still contains an unexpanded
constructor call and does not show hygienic label allocation. One canonical
generated raw manifest must own all constructor instances, raw instructions,
numeric layout operands, static objects, symbols, imports, relocations, and
source maps; document excerpts must be generated from it rather than copied.

### Spike 3

The document names future exact-expansion theorems but supplies no actual raw
expansion or reproducible generated artifact. Named layout offsets, source
annotations, imports, relocations, tables, and helper labels remain symbolic.
The unused machine-state/round-trip projections and standard process lookup
should not remain authored ceremony. Fixed DEFLATE tables must be either an
explicitly tunable authored choice or a named proved standard-library fragment.

### Spike 4

The six-file snapshot is exact, but the proof boundary is not. Many CFG joins
lack authored typed entry/exit contracts, while generated cancellation meanings
introduce facts absent from block annotations. The local fragment constructor
interface is malformed and leaves HPACK, flow-control, polling, scheduling, and
cleanup algorithms to unexplained lowering. No raw constructor expansion is
printed. Large registries, adapter records, cancellation-combinator trees,
source closure, and artifact wrappers appear mechanically derivable and should
not be charged to the application author. The physical import graph also does
not support the documented invalidation cone.

### Spike 5

The regenerated six-file snapshot is exact, but the document retains stale
prose about nonexistent `Staged.lean` and `SourceClosure.lean` authored files.
Layout, macro registry, static data, and numeric rotation evidence are not
visibly connected as inputs to the final verified construction. The staged
process proof rebuilds scopes from an already-complete realization, and
cube-specific transition/topology facts are hidden behind unexplained names.
Cross-ISA shader/host adjacency is absent from the final constructor. Much of
`Layout.lean` and `Program.lean` is standard generated ceremony, while the
monolithic assembly/import graph contradicts the promised shader-local
invalidation boundaries.

## Required re-review

After repairs, reviewers must begin from the authored directory, reproduce the
annotated views from a clean generated-output directory, and then attempt one
representative change in specification, assembly, layout, and platform policy.
Approval requires both exact views and a believable derivation between them;
neither source mirroring nor a small closing command is sufficient alone.
