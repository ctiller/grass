# Standard-library implementation plan

Status: implementation plan owned by the `c-stdlib` implementation agent. This is
a tier-four document under [README.md](README.md) authority ordering: it schedules
work against the normative demands of [STDLIB.md](STDLIB.md),
[MODULES.md](MODULES.md), and [PROTOCOL_STDLIB.md](PROTOCOL_STDLIB.md). It may not
weaken any of them. Where it raises a question outside its ownership — a name
fixed by [STDLIB.md](STDLIB.md), a module root — it says so and names the owner
it has asked.

## 0. Ownership boundary

Owned by this plan:

| Area | Normative owner |
|---|---|
| `Vec`, `ByteArray`, and the pure sequence laws | [STDLIB.md](STDLIB.md) §1, §3, §5 |
| finite maps, sets, multisets, and their framing laws | §6 "Associative and ordered structures" |
| worklists: deque, queue, stack, priority queue | §6 "Worklists" |
| `OwnedVec`, physical slices, loans, reallocation, `RebaseMap` | §2, §4, §5 |
| `StructLayout` and its offset/size/padding derivations | §6 "Physical struct layouts" |
| `Std.Process` combinator packages and `Std.Process.ByteFlow` | §6, [PROCESS.md](PROCESS.md) |
| `Std.Protocol` package shape | [PROTOCOL_STDLIB.md](PROTOCOL_STDLIB.md) |
| effect-policy builders | §6 "Effect-policy builders" |

Not owned, and this plan is blocked on them:

- `Grass.Core` identifiers and their history-indexed fresh supply, owned by
  `g-foundation`. `Std.Owned` cannot state `vecId` or `bufferId` without them.
- Loans, initialization tracking, provenance, allocation, and the obligation
  ledger, owned by `c-mem`. [STDLIB.md](STDLIB.md) §2 is explicit that
  `Std.Owned` "does not duplicate a private ownership model", so every physical
  container waits on that layer rather than routing around it.
- Processes, channels, cancellation, and flattening, owned by `c-process`.
  `Std.Process` is a package of combinators over that vocabulary, not a second
  process model.
- The law-bearing monad interface [MODULES.md](MODULES.md) assigns to
  `Grass.Effect`, which has no owner yet. `Vec.mapM` and `Vec.traverse` wait on
  it; see §3.4.

Not owned and not blocked on this plan: instruction sets, platform profiles,
artifact writers, and the CFG proof library. [STDLIB.md](STDLIB.md) §6 places
machine-state templates such as `SliceConsumerInvariant` in the CFG proof library
deliberately, and this plan does not reach for them.

## 1. Sequencing principle

[STDLIB.md](STDLIB.md) §6 states the default plainly:

> Only structures demanded by a milestone are implemented, but their common
> interfaces and proof package are reviewed before consumers proliferate.

Demand-driven is the right default for a library and it is this plan's default.
It has exactly one exception, and the exception is what orders the work.

[STDLIB.md](STDLIB.md) §1 says Grass "must not introduce a second unrelated
byte-container primitive", and [MODULES.md](MODULES.md) repeats the rule for
ordered buffers generally: consumers "must not introduce competing byte-array or
ordered-buffer foundations". A prohibition on inventing a container is only
enforceable if the container already exists. Waiting for demand would mean every
demand arrives as a layer that has already invented its own, and the cost is then
a migration rather than an import.

The plan therefore orders work in three bands:

1. **Names other layers would otherwise duplicate.** `Vec` and `ByteArray` are
   the whole of this band. They land before their callers, and they are the only
   thing in this plan that does.
2. **Laws a named consumer is currently blocked on.** Written against the
   consumer's actual proof, not against a guess at one. The `FiniteMap` disjoint
   union in §4.3 is the live example: `c-mem` named it, and it is scheduled
   because `c-mem` named it.
3. **Everything else**, on demand, in the order demand arrives.

A structure in band 3 gets nothing — not a stub, not a signature, not a
placeholder — until a consumer exists. A placeholder is a design decision taken
without a use case and then inherited as a constraint, which is the failure
[STDLIB.md](STDLIB.md) §6 is guarding against.

Stages are ordered, not dated. They are lettered `S` so they cannot be confused
with the `M` milestones in
[MEMORY_IMPLEMENTATION_PLAN.md](MEMORY_IMPLEMENTATION_PLAN.md), which they
depend on but do not track.

## 2. S0 — Inherited state

Three pieces of this library were written by agents who did not own it, because
they needed it and no owner existed. All three are declared temporary custody in
source and on the bus. Nothing here is a criticism: each is a correct decision
under [MEMORY_IMPLEMENTATION_PLAN.md](MEMORY_IMPLEMENTATION_PLAN.md) §2, and each
was marked rather than smuggled.

| Path | Custodian | Bus record | Disposition |
|---|---|---|---|
| `Grass/Std/Logical/Byte.lean` | `c-mem` | `c-mem:1`, `coord1:25` | accept as-is; §4.1 |
| `Grass/Std/Logical/FiniteMap.lean` | `c-mem` | `c-mem:1`, `coord1:25` | accept, then extend; §4.3 |
| `Grass/Process/Bag.lean` | `c-process` | `c-process:28`, `coord1:24` | accept and move; §4.2 |

The third row is not visible from this branch. `Grass/Process/Bag.lean` exists
only on `agent/c-process/process-layer`; there is no `Grass/Process/` directory
here. It is tabulated because the handoff is agreed and inbound, not because a
reader can inspect it.

`Grass/Std/Logical/Vec.lean` is new and is this plan's, not custody.

The custody markers stay until each handoff is accepted. Replacing them is part
of accepting, not a precondition for offering: an implementor releasing a file
should not have to rewrite its docstring first.

## 3. S1 — The sequence vocabulary freeze

Goal: an ISA, memory, artifact, or program author can write final source against
an ordered sequence and a byte container without inventing either. This is the
band-1 work of §1 and the only part of this plan that runs ahead of demand.

### 3.1 What landed

`Grass/Std/Logical/Vec.lean` defines `Vec α` with the construction, observation,
update, structural, composition, algebra, and search operations of
[STDLIB.md](STDLIB.md) §3, and the logical slice of the §5 proof package:
extensionality by length and by index, length laws for every structural
operation, get-after-construction and get-after-update laws, order preservation
for `append` and `map`, and `map` fusion. `abbrev ByteArray := Vec Byte`
realizes the §1 name.

Every operation in the module carries at least one law, and the rule that
produced that property is worth stating because it is cheap to violate: an
operation with no law is a name a consumer can call and cannot reason about, so
it will be reasoned about through `Vec.toList` instead, which is precisely the
leak §3.2 pays for the wrapper to prevent. `Vec.pop?` is the case that made the
rule concrete — it was written with no law at all, and `Vec.pop?_push`,
`Vec.length_of_pop?`, and `Vec.pop?_isSome_iff` are what it needed to be usable.
`Vec.mem_iff_exists_get?` is the same rule applied to membership: reaching the
representation is available through `Vec.mem_iff_mem_toList`, but a consumer
should not have to.

The module also carries a prefix/suffix algebra — `IsPrefix`, `take_add`,
`drop_drop`, `take_take`, `drop_eq_empty_iff`, `length_drop_lt_of_pos`, and the
`take_isPrefix` pair. That is band-2 work under §1 with the most-named consumer
in the corpus. [SPIKE_PROOF_BURDEN.md](SPIKE_PROOF_BURDEN.md) carries six
`library-instance` rows, and three of them, spread across three different
spikes, are one shape: `write_all_loop(payload)` in Spike 1,
`buffered_stdout(output_buffer, outUsed, committedPrefix)` in Spike 2, and
`SliceConsumerInvariant(output, consumed, outLen)` in Spike 3. The ledger
describes each as a *standard* partial-write induction or consumer, and that word
is the demand: it expects one reusable theorem, not three authored proofs.

There are three fixtures. Per `Tests.lean` all three establish expressibility
rather than a theorem. `Tests/Std/VecVocabulary.lean` covers the type's own
claims: that a `List Byte` and a host `_root_.ByteArray` are each rejected where
a Grass `ByteArray` is required, that extensionality is usable in the shape a
consumer would use it, and that the update framing law composes the way the
memory layer applies it. `Tests/Std/SpikeSurface.lean` covers the demand side:
every `Vec` operation the authored spike sources call, compiled in the shape they
call it, so that §3.4's "no consumer has demanded it" rests on a reading of the
corpus rather than on an assumption about it.
`Tests/Std/PartialWrite.lean` answers the narrow question the burden ledger
raises — whether the pure half of that standard theorem holds with only this
module — by building the loop state, its conservation, exact-prefix commitment,
monotonicity, and termination laws, and a concrete trace. It does: every proof
there is a `Vec` law applied plus `omega`, with no induction, because the
induction is already discharged inside `Vec.take_add` and `Vec.drop_drop`. What
it deliberately does not do is the other half. [STDLIB.md](STDLIB.md) §6 puts
`SliceConsumerInvariant` in the CFG proof library, since "the pure library owns
ordered-sequence and slice laws, while the CFG layer connects those laws to
selected registers, pointers, provenance, and loans", and no register, handle,
provenance token, or loan appears in that fixture.

### 3.2 The representation decision

`Vec α` is a one-field structure over `List α`, not an `abbrev`. The full
argument is in the module comment; the part that belongs in a plan is the cost
and who pays it. Every law in the module is a wrapper over a `List` law, and
`toList`/`fromList` are the only route between the two, so the wrapper is
perhaps two hundred lines of restatement that buys three things: `ByteArray`
does not reduce to `List Byte`, so §1's prohibition is elaborator-checked rather
than conventional; the representation stays replaceable without touching a
consumer, which §4's separation of capacity policy from logical equality
requires; and the door into the representation is narrow enough to see.

This is reversible in one direction only. Changing `Vec` from a structure to an
abbreviation later is a small edit; changing it the other way after consumers
have leaned on `List` lemmas is not. That asymmetry is the reason for choosing
the stricter option first rather than the cheaper one.

**A fact found after the decision, recorded because it argues against it.** Lean's
own `Array` is, in `Init/Prelude.lean`:

```lean
structure Array (α : Type u) where
  mk ::
  toList : List α
```

That is `Vec`, field for field. The difference is the name, the `@[extern]`
runtime overrides on `Array.mk` and `Array.toList`, and an API in core that is
far larger than the one restated here. So the option this plan never considered —
`Vec α := Array α` — would keep every property §3.2 claims for the structure
(`ByteArray` still would not reduce to `List Byte`, and `Array (BitVec 8)` is
still not Lean's `ByteArray`), while deleting the restatement cost and inheriting
core's proved laws and array-literal syntax.

The argument against it is the same one made above against `abbrev Vec := List`,
transposed: an abbreviation makes Lean's `Array` API, rather than
[STDLIB.md](STDLIB.md) §3, the reviewed surface. Whether that objection has the
same force for `Array` as for `List` is a real question, and the fact that
[MODULES.md](MODULES.md) names `Vec` as a distinct library type does not settle
it, since a `def` with its own API would also satisfy that.

**The criterion neither option was measured against.** Adversarial review raised
a third consideration that this section, the probe branch, and the module comment
all missed: the emitter has to *run*. [HELLO_WORLD.md](HELLO_WORLD.md)'s
acceptance clause requires that `emitProgram helloVerified` yield bytes that
"execute successfully on responsive validation hosts", and
[FOUNDATION.md](FOUNDATION.md) §3 puts the runtime executing the byte writer in
the TCB. `ByteArray` is `Vec Byte`, so the byte writer runs over this type.

Both candidates are quadratic. `Vec.push` is `⟨v.toList ++ [a]⟩` and `Vec.get?`
is `v.toList[i]?` — O(n) per push and O(i) per read, by inspection of the
definitions rather than by benchmark. That is O(n²) to build an artifact and O(n)
to read a byte of it.

Worse, **the probe branch does not fix this and is slower than the status quo.**
`agent/c-stdlib/vec-as-array-probe` changed the type and left every body
List-shaped, so an Array-backed `Vec` round-trips array → list → array on every
push. That is why it came in at a net −2 lines: it is a rename, not a
representation change. This section's earlier claim that adopting `Array` "would
delete the restatement cost and inherit core's proved laws" is therefore wrong as
stated — the probe inherits none of `Array`'s API, because the operations are
still `List` operations.

**A fourth option, now costed.** The three-way framing was itself too narrow.
`Grass/Std/Logical/VecArray.lean` on `agent/c-stdlib/array-backed` is a distinct
one-field structure whose *field* is an `Array` — keeping everything the
structure was chosen for while making `push` an `Array.push` and a read an index.
It is a parallel module named `AVec`; nothing imports it, and it exists to
produce the two numbers this decision should have been taken against.

*Speed.* Building a sequence by repeated `push` and then reading it, in the Lean
interpreter on this machine:

| n | shipped `Vec` (over `List`) | `AVec` (over `Array`) |
|---|---|---|
| 4,000 | 47 ms | 3 ms |
| 8,000 | 155 ms | 2 ms |
| 16,000 | 630 ms | 2 ms |
| 32,000 | 6,488 ms | 20 ms |

The shipped column roughly quadruples per doubling, which is the O(n²) the
definitions predict; the other is flat. At 32,000 elements the difference is
324×, and Spike 5's cube and Spike 4's server are artifacts far larger than that.
A separate attempt to time `push` alone reported zero at every size and is not
reported here: the result was being optimised away, and a benchmark that measures
nothing should not be quoted just because its numbers are favourable.

*Law-porting cost.* Seventeen laws ported. Ten were a native `Array` lemma in one
line. Two round trips were free. Four had to drop to `Array.toList` —
extensionality, `length_take`, `length_drop`, `append_splitAt` — because `Array`
has no `size_take`, `size_drop`, or `take_append_drop`. One, `get?_push_lt`, was
awkward because `Array.getElem?_push_lt` concludes `= some xs[i]` rather than
`= xs[i]?`. So the cost is real, bounded, and concentrated exactly where
`Array`'s own API is thin — which is also where
[SPIKE_PROOF_BURDEN.md](SPIKE_PROOF_BURDEN.md)'s most-named demand lives, so that
work is owed under any representation.

*Type distinction.* `Tests/Std/VecArrayCost.lean` pins that `AByteArray` rejects
a `List Byte`, a host `_root_.ByteArray`, **and** a bare `Array Byte`. The third
is the one `abbrev Vec := Array` gives up, and it is the one §1 most needs: under
the abbreviation any array of bytes from anywhere already is the reviewed
container.

This does not decide anything by itself, and deliberately so — the branch under
review should be reviewed as it stands. What it does is replace an argument with
two measurements and a third option, so that whoever takes the decision is not
choosing between a rationalisation and a rename.

This plan is not changing the decision while the branch is under review. Flipping
a foundational representation underneath a reviewer mid-review is worse than
surfacing the evidence and letting the review weigh it, and the nomination
already asks for exactly this argument to be attacked. It is recorded here so
that the reviewer has the strongest version of the counter-case rather than the
version this owner happened to think of first.

### 3.3 Equality

`Vec` has one representation per length-and-elements, so extensionality is
provable as propositional equality and there is no `Vec.Equiv`. This is
deliberately unlike `FiniteMap`, whose association lists are not normalized and
which therefore needs a separate `Equiv`. A reader moving between the two
modules will meet the difference immediately, so both module comments name it.

The consequence for consumers is worth stating once: `=` is the relation to use
on a `Vec`, and a proof that quantifies over `Vec.Equiv` is a proof that has
copied the wrong pattern from `FiniteMap`.

### 3.4 What S1 deliberately does not contain

[STDLIB.md](STDLIB.md) §3 lists a wider interface than S1 implements. Each
absence is a band-3 item under §1 with a named blocker, not an oversight:

| Absent | Blocked on |
|---|---|
| `mapM`, `traverse` | the `Grass.Effect` law-bearing monad interface. §5 asks for traverse *order preservation*, which is a claim about effect order; writing these over Lean's bare `Monad` now would fix the wrong contract and would have to be rewritten, not extended. |
| `foldMap` | a monoid vocabulary, which no consumer has demanded. |
| lexicographic comparison | an ordering vocabulary, likewise undemanded. |
| indexing laws for `insertAt`/`eraseAt` | a consumer that indexes across an insertion. The operations and their length laws are present; the index-shifting laws are large and are better written against a real proof than guessed at. |
| ~~`Vec` iterators~~ | **Supplied.** §3 lists iteration among the observations and this library had none; adversarial review found that neither the absence list nor the instances fixture had caught it. `Vec` now has `ForIn`, so `for x in v do …` works. |
| fold/map/traverse *fusion* laws beyond `map_map` | a consumer. §5 asks for fusion "where their premises hold"; only `map` fusion exists, and there is no `foldl_map`, `foldr_map`, `foldl_append`, or `foldr_append`. Found by adversarial review; this row is the correction. |
| pure immutable views/subsequences | a consumer. §3 lists them; `take`/`drop` copy instead. Also found by review, also previously unlisted. |
| the `ByteArray` writer/reader connection of §5 | the `Grammar` layer that would write and read one. `HostBytes.lean` supplies §1's *host* adapter, which is a different demand, and conflating the two was this plan's error. |

The absences above are only honest if the corpus was read for demands rather
than assumed to have none, so it was read. `Spikes/` holds the comment-free
expected author source that [SPIKE_AUTHORING.md](SPIKE_AUTHORING.md) makes the
reviewed statement of what an author writes, which makes it the closest thing
this library has to a named consumer. Every `Vec` operation those files call:

| Called by the spike surface | Status |
|---|---|
| `Vec.zipWith f v w` (`5_Spinning_Cube/Macros.lean`) | present, at that argument order |
| `arguments.mapIdx fun index argument => ...` (same file) | **added by this reading**; it was missing |
| `fields.map fun field => ...` through dot notation | present; dot notation reaches `Vec.map f v` |
| `++` on instruction fragments | present |
| array-literal syntax for `Vec` (seven sites) | **absent**; §3.5 |

`Tests/Std/SpikeSurface.lean` compiles each of the first four in the shape the
spike writes it, so "the surface supports this" is checked rather than asserted.
Nothing else in the five spikes calls a `Vec` operation. `List` appears once, in
`4_Web_Server/Process.lean`, and is left alone: [STDLIB.md](STDLIB.md) §6 lists
persistent `List` and contiguous `Vec` as separate offerings, so that is a
choice, not a `Vec` demand.

The spike *sources* are only half the corpus's demand, though, and the weaker
half: they say which operations get called, not which theorems get instantiated.
[SPIKE_PROOF_BURDEN.md](SPIKE_PROOF_BURDEN.md) is the other half, and it is the
more precise one, because its `library-instance` rows are by definition demands
on a library rather than on an author. Six rows carry that classification, and
they divide three ways. Three are the partial-write family answered in §3.1 and
`Tests/Std/PartialWrite.lean`. One, `crc32_prefix(transferred - remaining)`,
shares that prefix indexing but is described as a "standard CRC prefix theorem",
so its residue is a CRC model this library has no reason to own; the sequence
part it would sit on is already here. The last two are classified
`authored-proof/library-instance` rather than `library-instance` outright, and
neither is `Std.Logical`'s: `stable_merge_pass` instantiates a banked stable
merge the ledger pairs with `stableSortModelCorrect`, an `authority-model` entry,
and `bitAccRep` is a physical bit-accumulator representation. None of the three
is scheduled, and each becomes a demand on `Std.Owned` or on an algorithm owner
if it becomes one at all.

### 3.5 Open: `Vec` has no literal syntax, and the obvious fix is harmful

The spike sources write `Vec` literals with array-literal syntax — seven ascribed
sites such as `def deviceExtensionNames : Vec CString := #["VK_KHR_swapchain"]`,
plus `#[]` returned where a `Vec` is expected and `#[...]` as an operand of `++`.
This library provides no such notation, so those lines do not elaborate, and
`Vec.fromList [...]` is what they have to be written as today.

Three mechanisms were tried against a probe covering the spike's shapes. None is
shippable, and the results are recorded because two of them look obviously
correct until measured:

| Mechanism | Result |
|---|---|
| `macro_rules \| \`(#[$elems,*]) => \`(Vec.fromList [$elems,*])` | **Harmful.** It does not overload with Lean's array literal, it shadows it. With the rule in scope, `def c : Array Nat := #[1, 2, 3]` stops elaborating and `let xs := #[1,2,3]` silently becomes a `Vec`. Since `macro_rules` is global once imported, this would break `Array` literals in every module that transitively imports `Std.Logical` — which, through `Memory`, is most of the repository. |
| `instance : CoeTail (Array α) (Vec α)` | **Insufficient.** Ascribed non-empty literals work and `Array` literals are unaffected, but `def b : Vec Nat := #[]` fails, because the element type is a metavariable and the coercion does not fire; and `v ++ #[9]` fails, because the coercion does not reach into `HAppend`. The spike uses both. It also silently converts any `Array` value, not just a literal. |
| `elab_rules : term <= expectedType` deferring to `Array` | **Does not fire.** `#[...]` is expanded by a macro, and macro expansion wins over a term elaborator for the same syntax kind, so the rule never runs. It would also require `import Lean` in `Grass/Std/Logical/Vec.lean`, putting Lean's metaprogramming frontend at the base of the dependency chain that [MODULES.md](MODULES.md) starts with `Core`. |

Two conclusions. First, if notation is added it belongs in a separate module that
consumers opt into, not in `Vec.lean`, because of the `import Lean` cost and
because a global literal rule is not something a library at the bottom of the
chain should impose. Second, the choice is not wholly this library's: the
authored spike surface is governed by [SPIKE_AUTHORING.md](SPIKE_AUTHORING.md),
so "the spikes should write `Vec.fromList [...]`" is as available an answer as
"the library should support `#[...]`", and it is a cheaper one. Breaking `Array`
literals repository-wide to save this library some punctuation is not a trade
this owner takes quietly.

This interacts with §3.2's open question. If `Vec α := Array α` were adopted,
this section would be moot — array-literal syntax would work by construction, as
would `#[]` and `++`. That is the strongest practical argument in that
direction, and it is why the two are recorded as one decision rather than two.

### 3.6 Instances

`Vec` carries `DecidableEq`, `BEq` with `LawfulBEq`, `Repr`, and `GetElem`/
`GetElem?` with `LawfulGetElem`, so `v[i]`, `v[i]?`, `==`, and `decide` work on
one. Each is derived through `toList` rather than restated, which is sound
because `Vec.toList_injective` transports every decision procedure exactly, and
is the one place where routing through the representation is right: an instance
is about how values are compared and displayed, not about what a consumer may
assume of them.

This is completeness work rather than a new demand, and the argument for doing
it is §3.2's own. `Vec` is a private structure precisely so consumers write its
API instead of `List`'s. That trade is only worth making if the API is complete
enough to write against — a container that cannot be compared, indexed with
`v[i]`, or printed pushes its users straight back to `Vec.toList`, which is the
leak the structure was chosen to prevent. An incomplete wrapper is worse than no
wrapper, because it has the cost and not the benefit.

`GetElem` is worth singling out. [STDLIB.md](STDLIB.md) §3 asks for a checked
accessor and a bounded one; Lean's `v[i]?` and `v[i]` are exactly that pair, and
`Vec.getElem?_eq_get?` and `Vec.getElem_eq_get` pin that the notation means those
accessors rather than a parallel implementation.

`Tests/Std/VecInstances.lean` checks the part no theorem states — that the
notation and instances a Lean author reaches for without thinking work on a
`Vec` — and includes the two cases that separate a sequence from a set, since
every other example in it would pass for a container that forgot order or
multiplicity.
### 3.7 Flattening and chunking

`Vec.concat` closes a gap in [STDLIB.md](STDLIB.md) §3's own list — it names
`concat` among the composition operations and this library did not have it — but
what fixes its laws is §6, which gives `Std.Process.ByteFlow` a contract with a
sequence fact inside:

> Positive partial reads produce nonempty ordered chunks; parsers consume their
> concatenation independent of chunk boundaries.

The process half of that waits on `c-process`. The sequence half waits on
nothing, and it is the half that says what "independent of chunk boundaries"
*means*: `Vec.chunk_extensional`, which holds for any consumer expressed as a
function of `Vec.concat`. Its content is entirely in the hypothesis shape — being
chunk-extensional is a property of how a consumer is written, not something it
can be granted, and a parser that inspected the chunk sequence would not have
that type. The theorem is nearly trivial once written, which is the argument for
writing it: "independent of chunk boundaries" reads as a guarantee and is easy to
assume without ever fixing what it quantifies over.

`Vec.AllNonEmpty` and `Vec.length_le_length_concat` are why §6 says *positive*
reads. Without that word a provider could return unboundedly many empty chunks
while a reader waited for input that never arrived, and no length argument would
detect it. This is the read-side counterpart of `Vec.length_drop_lt_of_pos` in
§3.1, and with it the two directions of the ByteFlow contract now have the same
shape: `Tests/Std/PartialWrite.lean` commits exact prefixes of a payload,
`Tests/Std/Chunking.lean` receives one in arbitrary pieces, and neither mentions
a handle.
### 3.8 The crossing to Lean's host `ByteArray`

`Grass/Std/Logical/HostBytes.lean` supplies `Vec.toHostBytes` and
`Vec.ofHostBytes` with the connection theorems [STDLIB.md](STDLIB.md) §1 demands
of an adapter: length by `size_toHostBytes` and `length_ofHostBytes`, order and
byte values at every index by `getElem?_toHostBytes` and `get?_ofHostBytes`, and
losslessness in both directions by `ofHostBytes_toHostBytes` and
`toHostBytes_ofHostBytes`.

This is not band-3 work waiting for a consumer, and the reason is worth stating
because it looks like an exception to §1's rule. `Vec.lean` created a seam —
`Tests/Std/VecVocabulary.lean` pins that a host `_root_.ByteArray` is rejected
where a Grass one is required — and a seam with no sanctioned crossing is not a
boundary but a dead end. The first author who has to hand bytes to an operating
system will cross it regardless; the only question is whether they cross it with
a proved adapter or with an `Array.map` in a module that does not own the
question. Having built the wall, this library owes the door.

It stops at the Lean value. An *OS buffer* — a pointer and a length handed to
`WriteFile` — involves provenance and a pinned loan, which §5 assigns to
`OwnedVec`'s `PinLoan`, and none of that is here.

Two findings from building it, both recorded because they are about the design
rather than the code. First, the naming collision of §3.9 stopped being
hypothetical: `Tests/Std/HostBytes.lean` is the first module in the repository to
mention both byte arrays at once, and a bare `ByteArray` in it is an ambiguity
error. It is now the concrete instance of that question rather than an argument
about one. Second, the crossing lives in the `Vec` namespace and not a
`ByteArray` one, because `ByteArray` is an `abbrev` and dot notation on it
resolves in `Vec`. A first draft got this wrong and the fixture caught it: the
call worked on a value whose declared type was written `ByteArray` and failed on
the same value reached through a type ascription. An operation that resolves
depending on how its argument's type was spelled is worse than one with a longer
name, so the names carry `Bytes`.

### 3.9 Text as bytes

`Grass/Std/Logical/Text.lean` supplies `Text.utf8 : String → Vec Byte` with
`length_utf8`, `toHostBytes_utf8`, `utf8_empty`, and `utf8_injective`.

[STDLIB.md](STDLIB.md) §6 states two demands here and they are different in kind.
The second — "the ordinary law-bearing encoding API" — is the function and its
laws. The first is a *reduction* property: "UTF-8 conversion of a literal used as
a logical constant reduces during kernel elaboration to the canonical `Vec Byte`,
so consumers reason directly about its bytes and derive its length." No theorem
discharges that, because a theorem proved by `simp` would establish that the
equation holds and not that it holds *by reduction*, which is what a consumer
relies on when it writes `decide` or matches on a payload's bytes.
`Tests/Std/Text.lean` therefore closes every literal case by `rfl` and would be
worthless closed any other way. It covers one, two, three, and four-byte
characters, because a length derived from a character count would pass an
ASCII-only fixture and be wrong.

`Spikes/4_Web_Server/Spec.lean` is the consumer that makes this concrete: it
states a response-body equation against an encoded literal, which is checkable
only if the literal's bytes are computable.

**This delegates to Lean's encoder, deliberately.** `Text.utf8` is
`Vec.ofHostBytes ∘ String.toUTF8`. A second encoder would need either a proof
that it agrees with Lean's — against a specification neither this library nor
[STDLIB.md](STDLIB.md) supplies — or two encoders in the trusted base where the
corpus wants one. The trust boundary is worth stating exactly: `String.toUTF8`
carries `@[extern "lean_string_to_utf8"]` over the Lean model `String.toByteArray`,
kernel reduction and every theorem here use the model, and the extern is what
runs. `length_utf8` is therefore a theorem about the model, and a compiled
program's bytes matching it rests on the extern agreeing with its model — a
standard Lean trust assumption already inside the boundary
[FOUNDATION.md](FOUNDATION.md) §3 draws around the toolchain, not one this module
widens.

**Absent: decoding.** Core has `String.fromUTF8` with a validity argument but no
round-trip theorem relating it to `String.toUTF8`, so a `Vec Byte → String` here
could carry no law worth having. Supplying that law means proving UTF-8
correctness against a specification, which is a project rather than a function,
and no consumer has asked — [GZIP.md](GZIP.md) and
[HTTP2_CONSTRAINTS.md](HTTP2_CONSTRAINTS.md) decode bytes as protocol data rather
than as text. Encoding-indexed text *views*, §6's own phrase, are absent for the
same reason: a `Text enc` type should be designed against a consumer with a
second encoding, and UTF-8 is the only encoding any spike uses.

**Found while building it.** The spike surface writes `"...".toUTF8` at three
sites and expects a Grass `ByteArray`. That cannot typecheck: dot notation on a
`String` resolves to core's `String.toUTF8`, which returns the host type, and
this library deliberately rejects a silent crossing. So those three lines need
either a coercion this library argues against, or a different spelling —
`Text.utf8 "..."`. Like the array-literal question in §3.5 this is a change to an
authored surface [SPIKE_AUTHORING.md](SPIKE_AUTHORING.md) owns, not a gap this
plan can close alone.

### 3.10 Permutation, order, and search by position

`Grass/Std/Logical/Order.lean` supplies `Vec.Permutation`, `Vec.Pairwise`,
`Vec.findIdx?`, and `Vec.idxOf?`, with the laws a sort's caller uses and
`Decidable` instances for both predicates.

`Spikes/2_Sort/Spec.lean` is the reason, and it is a stronger reason than the
other spike evidence in §3.4. It is the only place in the corpus where a
*milestone's specification* is written directly over `Vec`, which makes it the
sharpest statement of what this library owes an application author, and its
`stableSorted` uses three `Vec` operations that did not exist.

The division of labour is worth stating because it is easy to get backwards.
[SPIKE_PROOF_BURDEN.md](SPIKE_PROOF_BURDEN.md) makes `stableSortModelCorrect` an
`authority-model` entry and `stable_merge_pass` an `authored-proof/library-instance`
one; neither is this library's. But the vocabulary the specification is *written
in* is, and a sort that shipped its own notion of "same elements rearranged"
would be proving a theorem about itself. [STDLIB.md](STDLIB.md) §5 names the same
vocabulary from the other side, requiring whole-element transfers to "derive
occurrence, permutation, and initialization transport from the proved physical
copy".

The `Decidable` instances are not decoration. `Tests/Std/StableSort.lean`
restates `stableSorted` over a stand-in and discharges it against a concrete
input and output, which needs `decide`; a specification predicate no program can
evaluate is one no fixture can exercise and no implementation can test itself
against. This is the same lesson as §3.6 in a different place, and the fixture is
what found it rather than the design.

**A correction to §3.4.** That section reported the spike corpus as calling five
`Vec` operations, from a survey that matched `Vec.<method>` and therefore saw
only qualified calls. `output.Permutation input` and `output.Pairwise
Occurrence.le` are dot notation on values and were missed entirely. The survey
was rerun over every dot-notation call in `Spikes/`, which is how this section
exists. The lesson is recorded rather than quietly fixed: a grep that matches a
qualified name will miss the idiomatic way the same function is called.

### 3.11 Exit criteria

S1 is complete when all of the following hold. The first four hold today.

1. `lake build` is green with `warningAsError = true`, so no declaration uses
   `sorry`.
2. `lake env lean Tools/AxiomAudit.lean` reports no axiom outside the
   [FOUNDATION.md](FOUNDATION.md) §3 allowlist, with `Grass.Std.Logical.Vec` in
   its coverage set.
3. `python Tools/DocstringAudit.py` reports no unbacked claim.
4. `Tests/Std/VecVocabulary.lean` elaborates, including its `#guard_msgs`
   rejection cases.
5. A reviewer distinct from this agent has merged it, per
   [AGENT_REVIEW.md](AGENT_REVIEW.md).

### 3.12 Open: the `ByteArray` name collides with Lean's

[STDLIB.md](STDLIB.md) §1 fixes the name `ByteArray` for `Vec Byte`. Lean's
prelude already has `_root_.ByteArray`. A module that opens `Grass.Std.Logical`
and writes a bare `ByteArray` therefore gets an ambiguity error naming both
candidates, and must qualify.

This is not a bug in either type, and the ambiguity error is in one sense the
correct outcome: §1 wants the two to stay distinct types related by a connection
theorem preserving order, length, and byte values, and a loud error is a better
realization of that than silent shadowing. But the cost is real, it is paid by
every memory, artifact, decoder, and program module that touches bytes, and it
is paid forever.

The name is fixed by a normative document this plan does not own, so this plan
implements §1 as written and has put the question to the owner of
[STDLIB.md](STDLIB.md) rather than choosing a different name unilaterally. The
options, for whoever rules: keep `ByteArray` and require qualification; rename
Grass's to something with no prelude collision; or state that consumers open a
narrower namespace. This plan has no preference strong enough to justify
pre-empting the ruling, and will implement whichever is chosen.

## 4. S2 — Custody consolidation

Goal: the three inherited pieces of §2 become this library's, and the
`Std.Logical` module tree stops being distributed across three agents' scopes.
Nothing in S2 is urgent and nothing in it blocks another agent; it is scheduled
second because it is cheap and because leaving ownership split invites a fourth
agent to add a fourth piece.

### 4.1 `Byte.lean`

Accept unchanged. `abbrev Byte := BitVec 8` is exactly what §1 specifies.
Accepting replaces the custody note and folds the `ByteArray` declaration back
next to `Byte`, where §1 groups them; it currently sits in `Vec.lean` only
because this agent does not edit a file still under another's custody.

`ByteSeq` does not disappear at acceptance. It is the type the memory layer's
event and state fields use today, and retiring it means editing
`Grass/Memory/**`, which is `c-mem`'s exclusive scope. The two names coexist
until that migration is agreed with `c-mem`; `Vec.lean` records why.

### 4.2 `Bag.lean`

Accept and move to `Grass/Std/Logical/Bag.lean`. `c-process:28` designed the
handover as a rename and a re-export, and the module carries no process
vocabulary, so this should be exactly that.

`c-process:28` flags the representation as one a library owner might revisit:
`Bag α := Quotient (List.isSetoid α)`, hand-rolled rather than mathlib's
`Multiset`. This plan inherits it as a declared fact per `coord1:24` and takes no
position at acceptance. The reason for not ruling immediately is that the choice
is not really about multisets: `lakefile.toml` carries no dependencies, and
[FOUNDATION.md](FOUNDATION.md) §3 puts every selected dependency into the TCB and
build ledgers, so adopting mathlib is a repository-wide reviewed decision that
this plan cannot take on a container's behalf. If that decision is ever taken,
replacing the hand-rolled quotient is a small follow-up; until it is, the
hand-rolled version is the only option, not the worse of two.

### 4.3 `FiniteMap.lean`

Accept, then close the two gaps its author deliberately left:

- **Disjoint union with split and join laws.** `c-mem`'s own M0 requirements name
  these, and the module comment records their absence as waiting for M3. This is
  band-2 work under §1: a named consumer with a named use.
- **A deduplicating count with its own law.** The `domain` docstring records that
  `domain.length` is not a count of bindings, because the entry list may hold
  shadowed duplicates, and explicitly defers a correct count to this owner.
  [MEMORY_MODEL.md](MEMORY_MODEL.md) §3 treats counts as derived caches of the
  authoritative map, so the law must relate the count to `Binds` rather than to
  the representation.

Neither is scheduled ahead of `c-mem` reaching the milestone that needs it.
Writing a disjoint-union split law before seeing the proof that consumes it is
the guessing §1 band 2 exists to prevent.

## 5. S3 — Demand-driven growth

Nothing in this stage is scheduled. It is a register of what exists to be built,
what each is blocked on, and who unblocks it, so that a consumer arriving with a
demand can see whether the demand is buildable.

| Area | Blocked on | Unblocked by |
|---|---|---|
| `Std.Owned`: `OwnedVec`, slices, loans, reallocation | loans, initialization, provenance, allocation | `c-mem` M3 and M6 |
| `StructLayout` and field-offset derivations | a layout consumer; the ABI and artifact layers | whoever owns `Grass.ABI` |
| ordered maps, sets, hash variants | a consumer with a complexity or ordering demand | none named |
| worklists: deque, queue, priority queue | CFG discovery and refinement algorithms | whoever owns `Grass.CFG` |
| `Std.Process` combinators, `ByteFlow` | the process and channel vocabulary | `c-process` |
| `Std.Protocol` packages | `Std.Process`, and [GRAMMAR.md](GRAMMAR.md) formats | `c-process`, and a grammar owner |
| grammar and parser combinators | a `Format` denotation to realize | whoever owns `Grass.Grammar` |
| effect-policy builders | the standard effect outcome type | `g-foundation` |

Two of these have no owner at all today — `Grass.Grammar` and `Grass.CFG` — and
that is worth stating rather than leaving to be discovered. This plan raises an
ownership gap with the coordinator when it becomes a blocker, not before.

## 6. Anti-churn policy

The library sits under almost everything, so a change here is a repository-wide
rebuild. Three rules follow.

**Names before laws.** A declaration's name and signature are what consumers
write down. Adding a law to an existing name costs a rebuild; changing a name
costs a rewrite in every consumer. When a choice is uncertain, this plan prefers
the option that keeps the name stable even if it makes the first proof longer.

**No speculative generality.** A type parameter, a class constraint, or an extra
field added "so it will be there later" is a constraint every consumer pays for
immediately and a design that was never reviewed against a use. Band 3 of §1 is
the mechanism: no consumer, no declaration.

**Deletions are migrations.** `ByteSeq` is the live case. This library will not
delete a name a consumer is using, even a name this plan considers provisional,
without the consumer's owner agreeing to the edit. Publishing a replacement and
leaving the old name until the migration lands is the pattern.

## 7. Risks

**The `Vec`-over-`List` wrapper rots.** Every `List` law a consumer wants has to
be restated. If restatement lags demand, consumers will reach for `toList` and
prove things about the representation, which is exactly what the structure was
chosen to prevent. The mitigation is that `toList` is a visible seam: a proof
that mentions it in a consumer is reviewable as a missing `Vec` law. There is no
mechanical check for this today, and this plan does not claim one.

**`Std.Owned` is the real work and it has not started.** Everything shipped so
far is the pure half of §1 through §5. The ownership half — loans, reallocation
existentials, `FreshAllocation`, `PinLoan`/`OffsetRef`/`RebaseMap` — is where the
difficulty is, and it cannot start until `c-mem` lands loans and allocation. The
risk is that the pure interface, designed without a physical realization in
front of it, turns out to be the wrong thing to represent. The mitigation is §6's
name-stability preference and the fact that `Represents` is a relation rather
than an equality, so a pure `Vec` need not be structurally close to its
realization.

**The `ByteArray` name is settled late.** Consumers written against a qualified
`Grass.Std.Logical.ByteArray` before a rename would need editing after one. The
mitigation is that there are no such consumers yet, which is the argument for
ruling on §3.12 soon rather than at leisure.

## 8. Decisions and open items

Decided by this plan, recorded here because they are the kind of thing a later
reader will want a reason for:

1. `Vec α` is a one-field structure over `List α`, not an abbreviation. §3.2.
2. `Vec` equality is propositional; there is no `Vec.Equiv`. §3.3.
3. `Vec.get` takes a proof of the bound and there is no `Inhabited`-defaulted
   accessor. An out-of-range bounded read is not expressible; `get?` serves a
   caller without the bound.
4. `Vec.truncate` and `Vec.clear` are provided as [STDLIB.md](STDLIB.md) §3's
   names even though they are `take` and `empty` at this level, because the
   `OwnedVec` operations of those names are genuinely different — they must
   account for released elements — and the pure names should not be the ones
   that move.
5. Stages are lettered `S`, not `M`, to avoid collision with
   [MEMORY_IMPLEMENTATION_PLAN.md](MEMORY_IMPLEMENTATION_PLAN.md). §1.

6. **Superseded.** The rule was "every operation carries at least one law", and
   adversarial review broke it twice. It was asserted satisfied on the same page
   where `Vec.truncate` and `Vec.clear` shipped with no law naming either — now
   fixed — and, more importantly, counting laws cannot express what the rule was
   reaching for. A deliberately wrong `insertAt` that ignores its index, and an
   `eraseAt` that always removes the last element, both satisfy the sole length
   law those operations carry; the reviewer compiled both. The rule is now: **the
   laws must determine the operation up to extensional equality.** `set`, `push`,
   `map`, `take`, `drop`, `flatten`, and `zipWith` meet it. `insertAt`, `eraseAt`,
   and `splitAt` do not, and are open item 10 rather than being counted as
   satisfying anything. §3.1.
7. `Vec` carries the instances a Lean author expects — `DecidableEq`, lawful
   `BEq`, `Repr`, `GetElem`/`GetElem?` — derived through `toList`. An incomplete
   wrapper is worse than no wrapper: it has §3.2's cost without its benefit,
   because a container that cannot be compared or indexed sends its users back to
   the representation. §3.6.
8. The crossing to Lean's host `ByteArray` is named rather than a `Coe`, so it is
   visible at the use site, and it lives in the `Vec` namespace with `Bytes` in
   its name because `ByteArray` is an `abbrev` and dot notation on it resolves in
   `Vec`. §3.8.
9. UTF-8 encoding delegates to Lean's `String.toUTF8` rather than being
   re-implemented, and the `@[extern]` trust boundary that creates is stated
   rather than left implicit. §3.9.

Found in a shared tool rather than in this library, and reported rather than
changed: `Tools/DocstringAudit.py` defines `SELF_NAMING` to exempt a theorem's
own docstring — its module comment says "a theorem's own docstring is exempt,
because the theorem beneath it *is* the enforcement" — but the constant is never
used, so that exemption is not implemented and the gate is stricter than it
documents. This plan did not change it. Loosening a gate every agent depends on
is not a unilateral edit, and the workaround is cheap: name the theorem in its
own docstring, which reads better anyway.

Open, with the owner each is with:

1. **The `ByteArray` name collision**, with the owner of
   [STDLIB.md](STDLIB.md). §3.12. Twice sharper than when it was first raised.
   The authored spike sources write bare `ByteArray` in **all five** spikes — an
   earlier count of four was wrong and the correction strengthens the point — so
   "keep the name and qualify at the use site" is a change to the author surface
   and not only to library-internal code. And it is no longer
   hypothetical: `Tests/Std/HostBytes.lean` is the first module to mention both
   byte arrays at once, and a bare `ByteArray` in it is an ambiguity error.
2. **Whether `Vec α` should be `Array α`**, with this branch's reviewer in the
   first instance. Lean's `Array` is the same one-field structure over `List`,
   and adopting it would delete the restatement cost and settle the literal
   syntax below at a stroke. §3.2.
3. **`Vec` has no literal syntax**, which the spike surface needs and which
   interacts with the previous item. Not settled unilaterally, partly because
   the only cheap mechanism breaks `Array` literals repository-wide and partly
   because the authored surface is [SPIKE_AUTHORING.md](SPIKE_AUTHORING.md)'s.
   §3.5.
4. **The spike surface's `"...".toUTF8` cannot typecheck** against a Grass
   `ByteArray`, at three sites, for the same reason and with the same owner as
   the previous item: dot notation resolves to core's `String.toUTF8`, which
   returns the host type. `Text.utf8 "..."` is the available spelling. §3.9.
5. **Resolved, and the reason given was false.** This item said UTF-8 decoding
   was unbuilt because core supplies no round-trip law and closing it "means
   proving UTF-8 correctness against a specification, which is a project rather
   than a function". Adversarial review falsified that: in this toolchain
   `String` is a structure over its own bytes carrying its own validity proof, so
   `String.toUTF8` is a projection and `String.fromUTF8` is the constructor, and
   both round-trip directions are a few lines. `Text.decode`, `Text.decode_utf8`,
   `Text.utf8_decode`, and `Text.isValidUTF8_utf8` now exist. Recorded rather
   than deleted, because a named blocker that was not real is the failure mode
   this plan's band-3 discipline is most exposed to. §3.9.
6. **`Spikes/2_Sort/Spec.lean`'s `stableSorted` does not typecheck**, in two
   further ways beyond the previous items, and both are about totality rather
   than naming. `input[i]` carries no proof that `i` is in range and its binder
   supplies none, and `(output.findIdx? input[i]).get!` panics exactly when the
   substantive claim fails, so the specification is silent about the case a
   wrong sort would hit. `Tests/Std/StableSort.lean` shows the same statement
   written totally. Owner as for the other authored-surface items. §3.10.
7. **The `Bag` representation**, inherited undecided from `c-process:28` and
      genuinely blocked on a dependency question rather than on a container
   judgement — though less blocked than §4.2 says: [MODULES.md](MODULES.md)'s
   final line already permits "mathlib and other reviewed Lean dependencies", so
   what is open is a reviewed addition to `lakefile.toml` and the TCB ledger, not
   a governance question. §4.2.
8. **`Grass.Effect`, `Grass.Grammar`, and `Grass.CFG` have no owner**, which
   blocks `mapM`/`traverse`, the parser combinators, and the worklists
   respectively. Raised with the coordinator when one becomes a blocker. §3.4,
   §5.
9. **`Vec.insertAt`, `Vec.eraseAt`, and `Vec.splitAt` are not determined by
   their laws**, under decision 6's replacement bar. `insertAt` and `eraseAt`
   carry only length laws that a wrong implementation satisfies, and
   `splitAt_eq` is its own definition restated. Either write the index-shifting
   laws or delete the operations until a consumer forces them — which is what
   §1 band 3 says to do anyway. §3.1.
10. **The spike surface calls both `.size` and `.length`** on `Vec`- and
   `ByteArray`-typed values — `.size` at six sites, `.length` at one — so it is
   inconsistent with itself and with [STDLIB.md](STDLIB.md) §3, which fixes
   `length`. `Vec.size` is supplied as an abbreviation so both elaborate, but the
   inconsistency is the spike owner's to settle. §3.6.
11. **[STDLIB.md](STDLIB.md) §3 lists `concat` among the composition
   operations**, and in Lean `List.concat` appends one element while flattening
   is `List.flatten`. This library ships `Vec.flatten` and leaves `concat`
   undefined rather than shipping a name that means the opposite of what a Lean
   author expects. The ambiguity is the [STDLIB.md](STDLIB.md) owner's. §3.7.
12. **There is no TCB ledger.** [FOUNDATION.md](FOUNDATION.md) §3 requires
   external-reality assumptions to be "recorded in the TCB ledger"; no such file
   exists in the repository. This library's `@[extern]` dependencies — at least
   `lean_string_to_utf8`, `lean_array_mk`, and `lean_array_to_list` — are
   recorded in a module comment as a placeholder. `Tools/AxiomAudit.lean` cannot
   see them, since an `@[extern]` is not an axiom, so a green audit is not
   evidence about that boundary. Raised with the coordinator. §3.9.
13. **The `ByteSeq` retirement**, which is an edit to `Grass/Memory/**` and
   therefore `c-mem`'s to make. §4.1.

Items 1, 2, and 3 were all sharpened or found by reading the spike corpus for
demands rather than by reasoning about the library in isolation, which is an
argument for doing that reading earlier next time rather than after a
nomination.
