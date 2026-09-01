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

## 6. Standard-library shape

The planned library is layered and demand-driven. Pure shapes live in
`Std.Logical`; resource-bearing realizations live in `Std.Owned`:

### Algebraic values

`Unit`, booleans, integers/bit-vectors, products, sums, `Option`, `Result`,
bounded indices, and explicit error types.

### Sequences and text

Persistent `List`, contiguous `Vec`, borrowed `Slice`, `NonEmpty`, `ByteArray`,
and encoding-indexed `String`/text views. Text encoding is explicit at binary and
API boundaries.

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
