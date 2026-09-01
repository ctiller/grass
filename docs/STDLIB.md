# Standard-library foundations

This document owns the shapes and proof contracts of Grass's reusable data
structures. The library begins early because binary formats, traces, CFGs,
memory regions, decoder tables, and user programs otherwise invent incompatible
containers and repeat their proofs.

## 1. `Vec` and `ByteArray`

`Vec α` is the fundamental finite ordered dynamic array of `α` objects.
`Byte` is the canonical eight-bit value type. `ByteArray` is an early public
name for `Vec Byte`:

```lean
abbrev Byte := BitVec 8
abbrev ByteArray := Vec Byte
```

Grass must not introduce a second unrelated byte-container primitive. Adapters
to Lean's host `ByteArray`, OS buffers, or foreign vectors require connection
theorems preserving order, length, and byte values.

`Vec α` itself is a pure finite sequence. Its equality and high-level laws are
extensional over length and indexed elements, independent of capacity, allocator
choice, or address. Physical ownership is a distinct type, conceptually
`OwnedVec profile α vecId bufferId`, connected by:

```lean
Represents : OwnedVec profile α vecId bufferId -> Vec α -> Prop
```

`vecId` is the stable identity of the owning vector resource. `bufferId` is the
fresh generative identity of its current allocation and changes on
reallocation. `OwnedVec` equality never forgets either identity.
Two owned vectors may represent equal `Vec` values while remaining distinct
physical resources with nontransportable provenance, loans, and release
obligations. Physical APIs use `Represents` and logical equivalence, not
propositional equality that erases ownership identity.

An `OwnedVec` realization is an ordered contiguous array for positive-sized
representable objects and has the conceptual shape:

```text
allocator/provider identity
allocation provenance and pointer
length
capacity
element representation/stride/alignment
initialized elements [0, length)
spare uninitialized slots [length, capacity)
ownership and outstanding element/slice loans
element destruction/transfer obligations
```

Required invariants include `length <= capacity`, checked size arithmetic,
correct allocation layout, complete initialization of live elements, no read of
spare capacity, and allocator-compatible release. Empty and zero-sized-element
vectors have explicit profiles and need not allocate.

The design takes inspiration from Rust's explicit pointer/length/capacity and
initialized-prefix guarantees, C++'s contiguous and allocator-aware container
contracts, and Haskell's small algebra of map/fold/traverse operations. Those
libraries are design inputs; Grass owns its exact semantics and proofs.

## 2. Representation separation

`Vec α` is usable at high specification levels even when `α` has no machine
layout. Physical lowering constructs an `OwnedVec` using a selected
`ObjectRepr profile α` describing
size, alignment, initialization, copy/move/drop behavior, byte encoding where
applicable, and memory shape. Thus functional proofs depend on the logical
sequence while lowering proofs depend on one representation profile.

This separation prevents an optimization, allocator change, or target layout
from invalidating map/fold/index proofs. It also prevents treating arbitrary Lean
objects as if they already had a C ABI layout.

The module split is acyclic:

- `Grass.Std.Logical` contains pure `Vec`, `ByteArray`, list/map foundations, and
  algebraic laws; it depends only on `Core`;
- `Semantics`, `Memory`, and `Obligation` may import `Std.Logical`;
- `Grass.Std.Owned` imports those lower semantic layers and implements
  `OwnedVec`, physical slices, allocation, loans, and cleanup;
- no lower memory/obligation module imports `Std.Owned`.

Generic provenance, loans, and obligation transitions remain owned by their
normative modules. `Std.Owned` proves container-specific realizations using them;
it does not duplicate a private ownership model.

## 3. Core safe operations

The pure logical `Vec` interface includes only sequence operations:

- construction: `empty`, `singleton`, `replicate`, `fromList`;
- observation: `length`, `isEmpty`, checked `get?`, bounded `get`, iteration;
- pure structural results: `push`, `pop`, `insert`, `erase`, `truncate`, `clear`;
- composition: `append`, `concat`, `splitAt`, `take`, `drop`;
- pure immutable views/subsequences without loans or capacity state;
- algebra: `map`, `mapM`, `foldl`, `foldr`, `foldMap`, `traverse`, `zipWith`;
- predicates/search: `all`, `any`, `find?`, `contains`, lexicographic comparison;
- conversions with proved order/length preservation.

Physical `OwnedVec` operations are ownership-sensitive families rather than
automatic lowerings of every pure function:

- capacity variants provide fallible `reserve`/`shrink` and expose allocation
  results;
- borrowed variants return immutable/mutable `Slice` values with unique loan
  identities and retain/freeze the source as required;
- mutating variants update initialized length/elements under exclusive authority;
- consuming variants move from and invalidate the source according to their
  dependent result;
- copying/cloning variants require explicit `Copyable`/`Cloneable` laws;
- folds may borrow elements without duplicating ownership;
- physical map/traverse operations state how success and every failure distribute
  source and destination element obligations.

Pure `take`, `drop`, `splitAt`, `append`, `map`, or `traverse` does not authorize
a physical implementation that duplicates uniquely owned elements. A lowering
must select a borrow, consume, or clone contract and prove it represents the
pure result. Operations whose allocation or element operation may fail return an
explicit dependent result. No API silently assumes allocation success.

## 4. Mutation, borrowing, and invalidation

An immutable slice loans shared access to one range. A mutable slice loans
exclusive access to one range. Overlapping mutable slices and mutation through a
vector while incompatible loans live are prohibited by the canonical loan map.

Operations that can reallocate require exclusive vector-growth authority and no
outstanding pointer/slice loan whose contract forbids movement. Initial
`OwnedVec` reallocation permits allocation failure only before element transfer;
that failure leaves the source vector, provenance, elements, and obligations
unchanged. Once transfer begins, the selected element representation must supply
an infallible relocation theorem. Reallocation then:

1. obtains fresh child provenance from the selected allocator;
2. infallibly relocates live elements with the element representation theorem;
3. preserves logical order and length;
4. invalidates old-buffer provenance only after complete successful transfer;
5. releases the old allocation with its original allocator/layout obligation.

The type-level result of reallocation is existential in a fresh buffer identity:

```lean
Σ newWorld newBufferId,
  FreshAllocation oldWorld newWorld newBufferId ∧
  newBufferId ≠ oldBufferId ∧
  OwnedVec profile α vecId newBufferId
```

It consumes the old `OwnedVec ... vecId oldBufferId`, proves old-buffer
provenance invalid, preserves stable `vecId` and `Represents`, and cannot confuse
stale buffer authority with the replacement allocation.

`FreshAllocation` is an allocator/world transition invariant establishing that
the new generative identity has never denoted an earlier allocation in the
relevant provenance history. The inequality is retained as a convenient explicit
consequence; existential packaging by itself is not accepted as freshness.

Representations with fallible element moves are not supported by this basic
reallocation operation. A future operation must choose and expose an explicit
exception-safety profile with a dependent failure result accounting for every
source element, constructed destination element, provenance token, and cleanup
obligation. “Clean up partial construction” alone is not a valid postcondition.

Capacity growth policy is not part of logical equality. Complexity guarantees,
when offered, are separately named profile theorems rather than functional
correctness axioms.

## 5. Required proof package

Reusable proofs include:

- extensionality by length and indexed values;
- get-after-construction/update laws;
- length laws for every structural operation;
- order preservation for append, map, traverse, copy, and serialization;
- fold/map/traverse fusion laws where their premises hold;
- bounds, initialization, provenance, and framing preservation;
- allocation-failure and partial-construction cleanup;
- loan creation, splitting, joining, and invalidation;
- `Represents` preservation across reallocations and allocator providers without
  equating distinct physical resources;
- `ByteArray` writer/reader connection to `Vec Byte`.

Theorems are factored into logical sequence laws, generic representation laws,
and allocator/profile realization laws. User code should not re-prove physical
buffer invariants for routine vector use.

The ownership proof layer supplies checked `grass_frame` and `grass_loan`
automation for routine disjoint framing, loan split/join, unchanged-buffer
transport, and exact loan reconstruction at calls. Diagnostics show the tokens
consumed and returned. Ambiguous aliasing, unusual transfer, or a changed
resource remains an explicit goal; automation may not invent separation.

Whole-element transfers between disjoint `OwnedVec`/`StructLayout` regions
derive occurrence, permutation, and initialization transport from the proved
physical copy. The theorem is instruction-shape independent: scalar, vector,
and macro-expanded copies instantiate the same footprint relation. Overlap,
partial representation writes, or unusual aliasing remains author-supplied.

`OwnedVec` interior access has two explicit shapes. A `PinLoan` makes live
machine pointers legal and disables reallocation until returned. An `OffsetRef`
retains a stable logical position without physical read authority; successful
reallocation returns a `RebaseMap` which converts valid offsets to fresh-buffer
pointers and transports their initialized occurrence facts. Neither route lets
an old raw pointer survive a generative buffer change.

## 6. Standard-library shape

The planned library is layered and demand-driven. Pure shapes live in
`Std.Logical`; resource-bearing realizations live in `Std.Owned`:

### Process and cancellation combinators

Routine serial functions lower as uncancellable process segments without a new
author proof. Reusable `cancelPoint`, `interruptibleCall`,
`withCancellationMask`, `sequence`, `choice`, `loop`, `parallel`, and supervisor
combinators calculate `CancellationSummary` values and export opt-in
`TerminationFacet` instances when their premises are met. The library proves
sequencing associativity, affine pending-request conservation, branch
weakening, loop safe-point coverage, flattening preservation, and standard
deadline/escalation laws once. An interruptible foreign call is available only
when its provider contract names the interrupt operation, race outcomes,
returned custody, and late-result handling; it is never inferred from an
ordinary blocking call.

### Algebraic values

`Unit`, booleans, integers/bit-vectors, products, sums, `Option`, `Result`,
bounded indices, and explicit error types.

### Sequences and text

Persistent `List`, contiguous `Vec`, borrowed `Slice`, `NonEmpty`, `ByteArray`,
and encoding-indexed `String`/text views. Text encoding is explicit at binary and
API boundaries.

UTF-8 conversion of a literal used as a logical constant reduces during kernel
elaboration to the canonical `Vec Byte`, so consumers reason directly about its
bytes and derive its length. Runtime or nonliteral conversion uses the ordinary
law-bearing encoding API and does not borrow this definitional shortcut.

### Associative and ordered structures

`Map`, `Set`, multimaps, ordered maps/sets, and hash-based variants with
separate equality, ordering/hash, allocator, and complexity profiles.

### Worklists

`Deque`, `Queue`, stack, priority queue, and graph worklists used by CFG discovery
and refinement algorithms.

### Ownership and resource wrappers

Unique boxes, shared immutable ownership, atomic sharing where supported,
arena-owned handles, scoped cleanup, and callable/export handles. These reuse the
memory and obligation models rather than inventing library-local ownership.

Only structures demanded by a milestone are implemented, but their common
interfaces and proof package are reviewed before consumers proliferate.

### Physical struct layouts

`StructLayout` describes an ordered physical field sequence, field widths,
alignment, padding policy, and total size. A reviewed layout declaration derives
named field offsets, `sizeof`/alignment theorems, checked array-size arithmetic,
and indexed-address lemmas. It does not choose a program's fields or synthesize
its loads and stores. `OwnedVec` may use a `StructLayout` representation theorem
to connect physical elements to logical values while preserving distinct
allocation and occurrence identities.

For C-ABI records, a transparent `init layout { field := value, ... }` assembly
form may zero the complete object representation and then store the named
nonzero fields. Its expansion is a literal `rep stos*`/store CFG with declared
clobbers; layout proofs establish offsets, padding, initialization, and
non-overlap. The author still chooses every semantic field and may replace the
expansion with hand-tuned literal stores. The form cannot hide allocation,
control flow, API calls, ownership transfer, or an omitted required field.

Layout writers and readers obey the corpus serialization laws: writing a
represented value then reading at the same layout returns it exactly, and every
successful read denotes a value allowed by the layout specification. Padding is
never silently treated as initialized semantic data.

### Effect-policy builders

Reusable total policy values remove boundary boilerplate without inventing
catch-all behavior. `CliWritePolicy.distinctStatuses` covers success,
unavailable, failed-after-prefix, and zero-progress outcomes with author-chosen
statuses. `CliWritePolicy.successOrFailure` deliberately collapses those failure
classes when the specification does not observe the distinction. Both builders
are total over the closed standard effect outcome; extending that outcome forces
the builder and every boundary using it to be reviewed.

Named convenience specifications may pair a standard policy with a standard
liveness intent, for example `CliSpec.writeStdoutResponsive`. Their names expose
the choice and their definitions transparently expand to the ordinary effect,
policy, and liveness fields. Grass does not silently add outcome or liveness
policy merely because an effect was mentioned; applications may use the named
builder or spell bespoke policy as this spike does.

Failure policy can remain binary, map abstract failure classes to structured
application errors/status values, or demand selected provider diagnostics. The
complete audit trace always retains modeled provider causes. Observing
`GetLastError`, `errno`, an HRESULT, or another provider detail is itself an
explicit demand/API operation with all returned values and assembly paths; it is
never conjured by a status macro. Thus production diagnostics are author-
controlled without forcing Hello's minimal public specification to preserve a
platform taxonomy.

Machine-state templates such as `SliceConsumerInvariant` live in the CFG proof
library rather than `Std.Logical`: the pure library owns ordered-sequence and
slice laws, while the CFG layer connects those laws to selected registers,
pointers, provenance, and loans.

### Process composition and flattening

`Std.Process` owns reusable protocol registries, sequential adapters, Hoare
channel patterns, bounded pipelines, worker pools, ring buffers, supervision,
strategy combinators, graph flattening, serial schedulers, and independence/
commutation theorems. Canonical physical representation packages include fixed
worker pools, bounded rings, poll sets, and handle tables; each connects exact
logical occurrences/escrows to physical records and obligations.

`Std.Process.ByteFlow` owns asynchronous ingress and egress protocols. Positive
partial reads produce nonempty ordered chunks; parsers consume their
concatenation independent of chunk boundaries. Positive partial writes commit
exact prefixes and retain the unique unwritten suffix. EOF, pending/readiness,
failure, cancellation, and close are distinct lifecycle events. Its standard
proofs provide completed functional rechunk projection for `ChunkExtensional`
consumers, mapped-cut/capacity relations for asynchronous behavior, prefix
conservation, bounded backpressure, exact terminal disposition, and adapters for blocking calls,
overlapped completion, readiness polling, files, pipes, consoles, and sockets.
Framing and decoding belong above this byte channel rather than inside a
platform provider.

`Std.Process.Resource` owns compositional metrics, capacity-credit channels,
subgraph theorem extraction, and sum/maximum/transfer rules. It derives bounds
for a process together with all of its dynamic descendants, counts shared
regions once, and connects logical holdings to exact physical layout overhead.
Bounded pipeline, worker-pool, parser, codec, and server combinators carry these
certificates, so changing a channel capacity or population bound recomputes the
whole-graph peak instead of reopening every transition proof.
Metrics are generic and product-composable: standard axes cover bytes, Unix file
descriptors, Windows handles, sockets, threads, GPU resources, pending work, and
obligations, with separate provider representation theorems and per-axis
composition laws.

Parser/compiler combinators cover token streams, bounded lookahead,
lexer-parser fusion, structured error/recovery propagation, pass pipelines, and
extensional pass replacement. These constructs build process proof graphs; the
`flatten_correct` and `SerializablePlan` theorems can erase the runtime process
architecture entirely before CFG lowering. Libraries must not require a parser,
compiler, or codec to execute as actors merely because it was proved through a
process graph.
