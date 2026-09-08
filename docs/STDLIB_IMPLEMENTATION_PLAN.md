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
they needed it and no owner existed. Nothing here is a criticism: each was a
correct decision under
[MEMORY_IMPLEMENTATION_PLAN.md](MEMORY_IMPLEMENTATION_PLAN.md) §2, and each was
marked rather than smuggled.

**All three handoffs have been accepted, so this section is history rather than
a queue.**

| Path | Former custodian | Offered | Accepted | Where it went |
|---|---|---|---|---|
| `Grass/Std/Logical/Byte.lean` | `c-mem` | `c-mem:47` | `c-stdlib:19` | stayed put; §4.1 |
| `Grass/Std/Logical/FiniteMap.lean` | `c-mem` | `c-mem:47` | `c-stdlib:19` | stayed put; §4.3 |
| `Grass/Process/Bag.lean` | `c-process` | `c-process:52` | `c-stdlib:15` | `Grass/Std/Logical/Bag.lean`; §4.2 |

`Grass/Std/Logical/Vec.lean` is this plan's own and was never custody.

The custody markers were to stay until each handoff was accepted, because
replacing them is part of accepting rather than a precondition for offering: an
implementor releasing a file should not have to rewrite its docstring first
(`coord1:32`).

**That replacement was owed from 2026-09-07 and was not made until later**, so
for a stretch `Byte.lean` and `FiniteMap.lean` carried a note saying that
`Grass.Std.Logical` "is not owned by the memory agent" and that the module was
"temporary custody", while being owned outright by the agent reading it. The lesson is not "remember
to update docstrings": it is that an accepted handoff has *two* halves, and only
one of them is a bus event, so nothing in the protocol notices the other going
undone.

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

Every operation carries laws that determine it up to extensional equality —
decision 6, arrived at after the weaker rule this paragraph used to state ("every
operation carries at least one law") was broken twice by adversarial review. The
motivation survives the rule that failed to capture it: an operation a consumer
can call and cannot reason about will be reasoned about through `Vec.toList`
instead, which is precisely the leak §3.2 pays for the wrapper to prevent. `Vec.pop?` is the case that made the
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

The fixtures under `Tests/Std/` all establish expressibility rather than a
theorem, per `Tests.lean`. Their number is deliberately not stated: it was
"eight" here and "nine" in §3.11's criterion 4, and both were false within
hours of being written. A count of a set that grows is a stale claim with a fuse
on it.

For the same reason the descriptions below are *illustrative, not exhaustive*:
`Tests/Std/` is the authoritative list, and this section explains only the
fixtures whose purpose is not obvious from their name. Fixtures added since it
was written — the representation probe, the collection-instance bridges, the fold
recursors — are described where they were introduced, in §3.1 and §3.2, rather
than by growing this paragraph every time. `Tests/Std/VecVocabulary.lean` covers the type's own
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
perhaps two hundred lines of restatement that was claimed to buy three things.
Adversarial review refuted two of them and bounded the third, and the retraction
belongs here rather than three paragraphs below.

**Survives, but only against `List`.** `ByteArray` does not reduce to `List Byte`,
so §1's prohibition is elaborator-checked rather than conventional. It does not
distinguish this design from `abbrev Vec := Array`, under which both rejections
still fire — review reproduced them. It *does* distinguish it from that option in
one way the original argument never made: a bare `Array Byte` is rejected here
and accepted there, which §3.2's costing fixture pins.

**Refuted.** "The door into the representation is narrow enough to see" is false.
Lean namespaces are open; review compiled a `Grass.Std.Logical.Vec.unreviewedBackdoor`
from outside `Grass/Std/Logical/` and it appears as dot notation on every
`ByteArray`. `Grass/Std/Logical/HostBytes.lean` sets the precedent itself by
reopening `namespace Vec` from another file. Nothing about the structure narrows
anything.

**Bounded.** "The representation stays replaceable without touching a consumer"
is spent by §3.3: publishing propositional equality hardwires canonicity into the
public contract, so the seam survives only for representations that are also
canonical. The array-backed option is canonical and clears it; a capacity-carrying
one would not, and §1 assigns capacity to `OwnedVec` anyway. The two decisions are
load-bearing on each other in opposite directions and neither module comment said
so.

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

So there is a third option that has been neither costed nor probed: a genuinely
`Array`-backed `Vec` whose `push` is `Array.push` and whose `get?` is `Array`
indexing, with every law re-proved against `Array` lemmas. It is the only one of
the three that can emit a megabyte artifact, and it is the one this plan should
have been comparing against all along.

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

**Read this table against §3.13 before trusting it.** Several rows say a thing is
undemanded, and that is true, but §3.13 measures what "demand" currently means:
of a hundred and five product modules, one can reach `Vec`, and `Spikes/` is not
a build target, so most of the consumers this section reasons about are
prospective. The absences are still right — guessing at a law is worse than
waiting — but "no consumer has demanded it" is weaker evidence here than it
sounds.


| Absent | Blocked on |
|---|---|
| `mapM`, `traverse` | the `Grass.Effect` law-bearing monad interface. §5 asks for traverse *order preservation*, which is a claim about effect order; writing these over Lean's bare `Monad` now would fix the wrong contract and would have to be rewritten, not extended. |
| `foldMap` | a monoid vocabulary, which no consumer has demanded. |
| lexicographic comparison | an ordering vocabulary, likewise undemanded. |
| indexing laws for `insertAt`/`eraseAt` | a consumer that indexes across an insertion. The operations and their length laws are present; the index-shifting laws are large and are better written against a real proof than guessed at. |
| ~~`Vec.filter`~~ | **Withdrawn by the consumer who asked for it.** A review called its absence "startling" in round 1, then wrote six client modules and never once needed it. Recorded because a retracted demand is as useful as a demand, and because band 3 was right. |
| ~~`reverse`, `takeWhile`, `extract`, `foldlM`, `head?`, `tail`, a `Sorted`/sort~~ | Same review, same verdict: never reached for. `Pairwise` plus decidability covered every ordering need including `insertSorted`; `Spikes/2_Sort` specifies sortedness and does not ask this library to perform one. `head?`/`tail` were subsumed by `Vec.recOnCons` — what was wanted was the induction principle, not the accessors. **That last clause holds only while `ByteSeq` is a `List`:** §4.0 records that `Grass/ISA/X86/Decode.lean` consumes a byte sequence with cons patterns, which `recOnCons` does not replace, because a recursor proves and does not compute. The verdict stands today and would not survive the `ByteSeq` migration. |
| ~~`Vec` iterators~~ | **Supplied.** §3 lists iteration among the observations and this library had none; adversarial review found that neither the absence list nor the instances fixture had caught it. `Vec` now has `ForIn`, so `for x in v do …` works. |
| fold/map/traverse *fusion* laws beyond `map_map` | a consumer. §5 asks for fusion "where their premises hold"; only `map` fusion exists, and there is no `foldl_map`, `foldr_map`, `foldl_append`, or `foldr_append`. Found by adversarial review; this row is the correction. |
| pure immutable views/subsequences | a consumer. §3 lists them; `take`/`drop` copy instead. Also found by review, also previously unlisted. |
| the `ByteArray` writer/reader connection of §5 | the `Grammar` layer that would write and read one. `HostBytes.lean` supplies §1's *host* adapter, which is a different demand, and conflating the two was this plan's error. |

The absences above are only honest if the corpus was read for demands rather
than assumed to have none, so it was read. `Spikes/` holds the comment-free
expected author source that [SPIKE_AUTHORING.md](SPIKE_AUTHORING.md) makes the
reviewed statement of what an author writes, which makes it the closest thing
this library has to a named consumer. Every `Vec` operation those files call:

This table has been wrong twice and is now the result of an exhaustive scan of
every declared `Vec`- and `ByteArray`-typed name in `Spikes/`, not of a grep.
Eleven operations, not five:

| Called by the spike surface | Status |
|---|---|
| `Vec.zipWith f v w` (`5_Spinning_Cube/Macros.lean`) | present, at that argument order |
| `arguments.mapIdx fun index argument => ...` (same file) | added by the second reading; it was missing |
| `fields.map fun field => ...` through dot notation | present; dot notation reaches `Vec.map f v` |
| `++` on instruction fragments | present |
| `.size` (six sites) and `.length` (one site) | **absent**, and the surface is inconsistent with itself; open item 10 |
| `output.Permutation input` (`2_Sort/Spec.lean`) | added by the third reading; §3.10 |
| `output.Pairwise Occurrence.le` (same file) | added by the third reading; §3.10 |
| `output.findIdx? input[i]`, applied to an *element* | the operation meant is `Vec.idxOf?`; §3.10 |
| `input[i]` with no bound proof in scope | not expressible; open item 6 |
| array-literal syntax for `Vec` (seven sites) | **absent**; §3.5 |

`Tests/Std/SpikeSurface.lean` compiles each of the first four in the shape the
spike writes it, so "the surface supports this" is checked rather than asserted.
`List` appears once, in `4_Web_Server/Process.lean`, and is left alone:
[STDLIB.md](STDLIB.md) §6 lists persistent `List` and contiguous `Vec` as
separate offerings, so that is a choice, not a `Vec` demand.

**Two corrections, and the second retracts the first.** An earlier version of
this section ended "Nothing else in the five spikes calls a `Vec` operation",
listing five. §3.10 then corrected it to include `Permutation` and `Pairwise`,
and explained the miss as a survey that "matched `Vec.<method>` and therefore saw
only qualified calls". That explanation is refuted by this table's own rows:
`arguments.mapIdx`, `fields.map`, and `++` are unqualified and were found by the
first survey. The real cause was narrower and less flattering — the first survey
read `5_Spinning_Cube`'s `Macros.lean` and `Layout.lean` and did not read
`2_Sort/Spec.lean`, which is the one file in the corpus where a milestone's
*specification* is written over `Vec`. A post-hoc explanation that this document's
own table contradicts is a worse error than the miscount it explains, and it is
recorded rather than quietly replaced.

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

**This delegates to Lean's encoder, deliberately, and delivers less than
"law-bearing encoding API" suggests.** `Text.utf8` is
`Vec.ofHostBytes ∘ String.toUTF8`. Because `String` is byte-backed,
`String.toUTF8` is a projection rather than an algorithm, so `length_utf8` and
`utf8_injective` are consequences of that structure and not of any encoder being
correct — a caller can derive length, injectivity, and validity, and nothing
about which characters map to which bytes. `Tests/Std/Text.lean` exhibits that by
reduction, and [FOUNDATION.md](FOUNDATION.md) §3 is explicit that a fixture is
evidence and never a theorem.

The trust boundary is not where an earlier version of this section put it. It
named `String.toByteArray` as a "model" beneath the extern; in fact
`String.toByteArray` carries the same `@[extern "lean_string_to_utf8"]`, and
`Vec.toHostBytes`/`ofHostBytes` add `lean_array_mk` and `lean_array_to_list`, so
at least three externs sit between these theorems and running bytes.
`Tools/AxiomAudit.lean` cannot see any of them, since an `@[extern]` is not an
axiom — so a green audit is not evidence about this boundary, and §3.11's
criterion 2 must not be read as if it were. Open item 12 raises the missing TCB
ledger that [FOUNDATION.md](FOUNDATION.md) §3 actually asks for.

**And none of those externs is the assumption the spikes actually rest on.** They
run in compiled code. Every literal case — `Tests/Std/Text.lean`'s `rfl`
examples, §6's "reduces during kernel elaboration", and
`Spikes/4_Web_Server/Spec.lean`'s body equation against an encoded literal —
never executes them; the kernel reduces the model. What those rest on is the
*elaborator's construction of the string literal's bytes*: which bytes Lean's
frontend puts into `String.ofByteArray` when it lexes `"Hello, World!"` from a
source file, and the kernel's agreement with that. That is an assumption about
the lexer and about the source file's own encoding. It is not an extern, not an
axiom, and not covered by anything named above — and
`Spikes/1_Hello_World/Spec.lean`'s `message` is the observable the whole first
milestone is specified against.

**Decoding is supplied, and the reason once given for its absence was false.**
This section previously said core supplies no round-trip theorem and that
providing one "means proving UTF-8 correctness against a specification, which is
a project rather than a function". In this toolchain `String` is a structure over
its own bytes carrying its own validity proof, so `String.toUTF8` is a projection
and `String.fromUTF8` is its constructor; both round-trip directions are a few
lines. `Text.decode`, `Text.decode_utf8`, `Text.utf8_decode`, and
`Text.isValidUTF8_utf8` exist. `Text.utf8_append` came with them, after a fixture
was found asserting that the general append law was false. Open item 5 keeps the
record.

Encoding-indexed text *views*, §6's own phrase, remain absent: a `Text enc` type
should be designed against a consumer with a second encoding, and UTF-8 is the
only encoding any spike uses.

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
`Vec.count`, and `Vec.idxOf?`, with the laws a sort's caller uses and `Decidable`
instances for both predicates. An earlier version of this sentence also listed
`Vec.findIdx?`, which does not exist — the module withdrew it under band 3, since
the spike passes an element rather than a predicate, and the module comment
argues that at length. The plan asserted the opposite of what the module said.

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
would be proving a theorem about itself. A note on what does *not* justify this module.
[STDLIB.md](STDLIB.md) §5's sentence about deriving "occurrence, permutation, and
initialization transport from the proved physical copy" was cited here in an
earlier draft; it sits inside the `OwnedVec`/`StructLayout` physical-transfer
paragraph and is about copy footprints in `Std.Owned`, not about a pure sequence
predicate. §3's own enumeration is restrictive — "the pure logical `Vec`
interface includes only sequence operations", with predicates listed as "`all`,
`any`, `find?`, `contains`, lexicographic comparison" — and names none of these.
So this module rests on band 2 alone: `Spikes/2_Sort/Spec.lean` is a named
consumer whose specification does not typecheck without it. That is a strong
argument and it does not need a borrowed one.

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

S1 is complete when all of the following hold. **All five hold today.** The
fifth was the outstanding one and closed when two reviewers distinct from this
agent merged the S1 work; see below for what each criterion actually measured
when it was checked, rather than that it passed.

1. `lake build` is green with `warningAsError = true`, so no declaration uses
   `sorry`.
2. `lake env lean Tools/AxiomAudit.lean` reports no axiom outside the
   [FOUNDATION.md](FOUNDATION.md) §3 allowlist, with **every** module this plan
   owns in its coverage set — `Vec`, `Byte`, `Bag`, `FiniteMap`, `HostBytes`,
   `Order`, and `Text`. The criterion has now been restated twice for the same
   reason: it first named only `Vec`, then the four modules the plan owned at the
   time, and each version stopped tracking the library as it grew. Checked
   directly rather than assumed — all seven are imported by
   `Tools/AxiomAudit.lean`. It is also not evidence about the `@[extern]`
   boundary of §3.9, because an `@[extern]` is not an axiom.
3. `cargo run --release --manifest-path tools/grass-tools/Cargo.toml --bin
   docstring-audit` reports no unbacked claim.
4. **Every** fixture under `Tests/Std/` elaborates, including all `#guard_msgs`
   rejection cases. This criterion previously named one of eight. Checked by
   confirming that *every* file under `Tests/Std/` produces an `olean`, not by
   reading a green build line: `Tools/VecRepresentationProbe.lean` sat outside
   the build for weeks while every gate passed, which is exactly the failure
   this criterion exists to catch and did not.

   No count is given on purpose. An earlier draft of this line said "each of the
   nine files", which was true when written and false two merges later; the
   branch this plan replaced was withdrawn partly for saying "eight" in the same
   place. A count of a set that grows is a stale claim with a fuse on it, and the
   criterion does not need one — "every file" is both stronger and permanent.
5. A reviewer distinct from this agent has merged it, per
   [AGENT_REVIEW.md](AGENT_REVIEW.md). Closed: `e-reviewer` merged the notation
   bridges and their fixture, and `g-reviewer` merged the specification-quote
   repair and the representation probe. Two reviewers rather than one because
   `coord1` alternates this plan's nominations between them.

### 3.12 Settled: the `ByteArray` name collides with Lean's, and stays

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
implemented §1 as written and put the question to the owner of
[STDLIB.md](STDLIB.md) rather than choosing a different name unilaterally.

**It has been ruled on.** Ruled at `g-design:49`, and recorded as
[DECISIONS.md](DECISIONS.md) decision 133: Grass keeps
`Grass.Std.Logical.ByteArray`, a module that can see both representations
qualifies the Grass name or takes a narrow local alias, and host conversion APIs
stay explicitly named and keep their order, length, and value connection
theorems. The reasoning given is the one this section reached from the other
direction — the ambiguity error is a useful guard against silently crossing a
representation boundary — and renaming would abandon already-ratified
vocabulary. The decision names this plan's question as the one it resolves.

Nothing here needs implementing: the ruling is that the current behaviour is the
intended behaviour. `Tests/Std/VecVocabulary.lean` already pins both halves, a
`List Byte` and a host `_root_.ByteArray` each being rejected where a Grass
`ByteArray` is required. This section is kept rather than deleted because the
cost it describes is real and permanent, and a future reader meeting the
ambiguity error deserves to find the reason rather than rediscover the
argument.

### 3.13 Who consumes this library, and which laws anything depends on

Every band judgement in §1 and every "no consumer has demanded it" in §3.4 rests
on a model of who consumes this library. That model had never been measured.

**Two measurements follow. They are independent, they count three different
populations, and neither is evidence for the other.** The populations are
*product reach* — modules under `Grass/` outside this library that can see a
module; *fixture reach* — modules under `Tests/` that can; and *simp-lemma
dependence* — laws some fixture goal is actually routed through. The first two
are properties of the import graph and say nothing about proofs; the third is a
property of the proofs and says nothing about who imports anything. An earlier draft of this
section presented them as one story — "coverage tracks demand" — and `g-reviewer`
refuted it from the section's own tables: `Bag` and `HostBytes` have zero product
consumers and substantial fixture dependence, and `Vec` has fewer product
consumers than `FiniteMap` and three times as many load-bearing laws. The claim
was drawn from the two endpoints while the middle contradicted it. What each
measurement establishes on its own is below; nothing here relates them.

#### Measurement 1: reach, on the import graph

Build the import graph over `Grass/**` and `Tests/**` and ask, for each module of
this library, which modules under `Grass/` *outside* `Grass/Std/Logical/` can
reach it transitively.

There are 105 such product modules and 89 fixture modules, so those are the
denominators of both columns.

| Module | Product modules that reach it (of 105) | Fixtures that reach it (of 89) |
|---|---|---|
| `Byte` | 16 | 32 |
| `FiniteMap` | 6 | 12 |
| `Vec` | **1** | 12 |
| `HostBytes` | 0 | 2 |
| `Text` | 0 | 1 |
| `Order` | 0 | 1 |
| `Bag` | 0 | 1 |

**The flagship type has one product consumer, out of a hundred and five.**
`Grass/Build/Cache/Key.lean` is the only module under `Grass/` outside this
library that can reach `Vec`, and it reaches it for one field's type. `Byte` and
`FiniteMap` are the only two of the seven that more than one product module can
reach, and neither is what §1 spends its argument on.

This is explainable: `Spikes/` is not a build target, so the corpus §3.4 reasons
about does not compile, and the consumers it describes are prospective. It is
worth stating anyway, because "no consumer has demanded it" reads like a
measurement of demand when it is largely a measurement of the corpus not being
built yet. That is the whole of what this measurement supports. It says nothing
about whether the laws are good, whether the fixtures are adequate, or what
should be written next.

`Bag`'s zero is a defect rather than a stage: the process layer still imports its
own `Grass/Process/Bag.lean`, so the library copy has no consumer at all. §4.2
records it and `c-process:120` took the port.

*Procedure.* Collect every `^import <module>` line under `Grass/**` and
`Tests/**`; a file's module name is its path with `/` replaced by `.` and `.lean`
dropped. Then, for each library module, take the transitive closure. The table
was computed twice by different traversals — a forward reachability test from
every module, and a reverse breadth-first expansion from each library module over
the inverted edge set — and the two agree on every cell. That is a check against a
bug in one traversal, not against a wrong edge set: both read the same `import`
lines, so a module reaching another by some means other than a direct `import`
would be invisible to both.

#### Measurement 2: attribute-deletion coverage, on the build

For each `@[simp] theorem` in a module, delete the attribute, rebuild the whole
`Tests` target, and record whether anything fails. Failure means some fixture
goal reached that law.

| Module | Laws a fixture depends on | Total `@[simp]` |
|---|---|---|
| `FiniteMap` | 8 | 9 |
| `Vec` | 25 | 72 |
| `Bag` | 10 | 23 |
| `HostBytes` | 5 | 12 |
| `Order` | 3 | 6 |
| `Text` | 1 | 7 |

`Byte` is absent because it declares no `@[simp]` law at all — it is two
`abbrev`s, and there is nothing to delete. That is also how it can be the
most-reached of the seven and contribute nothing here.

Fifty-two of a hundred and twenty-nine. **This is a statement about the
fixtures, not about consumers.** It says that seventy-seven laws currently have
no fixture goal routed through them; it does not say they are wrong, unwanted, or
unreachable, and it does not say anything about demand.

**`Order`'s row was zero when this section was first written, and moving it is
the best evidence in this document for the criterion below.** The explanation
offered for the zero was mechanical: four of its six laws are `empty` cases
(`count_empty`, `pairwise_empty`, `findIdx?_empty`, `idxOf?_empty`), one is
`pairwise_singleton` and one is `count_push`, while `Tests/Std/StableSort.lean`
built only concrete two- and three-element vectors, which `decide` and `rfl`
reduce without ever reaching a base case.

That explanation was right, and it was also a prediction: if the fixtures were
the reason, then goals written over *general* vectors should reach the base
cases. `c-stdlib:108` added four such goals — sortedness and multiplicity of an
empty vector, a search in one, and multiplicity under a permutation — and three
laws moved from unexercised to load-bearing: `count_empty`, `pairwise_empty` and
`findIdx?_empty`. No law was written, no law was changed, and the total went from
forty-nine to fifty-two.

The three that did not move say the same thing from the other side.
`idxOf?_empty` is an `empty` case like the three that did, and stayed put because
none of the four goals mentions `idxOf?` — the measurement follows the goals
someone happened to write, not the shape of the module. `count_push` and
`pairwise_singleton` need a `push` or a `singleton` in the goal, and a merge sort
states its correctness over `append`, which is the gap `c-stdlib:108` pins
separately.

#### What a law with no fixture behind it does and does not mean

The kernel type-checked every one of the seventy-seven, so none is *false*. What
is unchecked is whether each is the *useful* statement: a law with the wrong
orientation, the wrong side condition, or a normal form nothing else shares will
type-check and then fail to fire, and nothing here would notice.
`Vec.get?_push` is the case that shows the concern is not hypothetical — a real
gap where `simp` could not close a read-after-push, found only when a goal was
written to look for it.

**Not every fixture would add evidence, and this is the criterion rather than a
blanket refusal.** An earlier draft of this section said flatly that fixtures
written against the remaining laws "would measure nothing", which is false as
stated and was corrected by `g-reviewer`. Three shapes, of which one is empty:

- **Law-restating — adds nothing.** The goal is the law's own statement, closed
  by `simp [thatLaw]`. It cannot fail unless the law fails to elaborate. It moves
  the number in the table above without changing what is known.
- **Consumer-shaped — worth writing.** A goal a caller would actually write,
  left for `simp` to discharge by whatever route it finds. It can fail for a
  reason its author did not encode, which is exactly how `Vec.get?_push` was
  found: nobody set out to test that law, because it did not exist.
- **Mutation-killing — worth writing, and stronger.** A goal that breaks when the
  law is perturbed in a plausible wrong direction: orientation reversed, a bound
  off by one, a side condition dropped. Measurement 2 is the crudest instance of
  this — a single mutant per law, "delete the attribute" — and a mutation of the
  *statement* would be strictly stronger evidence than anything reported here.

So the seventy-seven are laws for which no consumer-shaped or mutation-killing
test exists. Writing the first kind against them would raise the number and leave
that sentence just as true.

**That is not a prediction any more.** Four consumer-shaped goals in
`c-stdlib:108` moved three of `Order`'s laws across the line without a single law
being written, and the `Order` paragraph above records which three and why the
other three stayed. A law-restating fixture would have moved all six and
established nothing.

#### A third number, from the gate that already runs

The observation-coverage audit reports its own reach every time CI runs it, and
the line is worth reading beside the two tables: *14 `Vec`-returning operations
each carry a length law and a `get?` law; 9 exempt by clause (ii) or the alias
clause; 44 declarations outside the bar's reach.* Those 44 are operations
returning `Bool`, `Nat`, `Option` or `Prop`, which decision 6's clause (i) cannot
be phrased over, and the audit counts and lists them rather than passing them
silently.

That is a different population again — declarations, not laws, and reachability
of a *rule* rather than of a proof — so it is not addable to anything above. It
is here because it is the same discipline: a checker that states what it cannot
see is worth more than one that reports a clean run over a scope it never names.

#### Reproducing measurement 2 exactly

The first run of this measurement was wrong, and the way it was wrong is the
reason this subsection exists. Matching a declaration by name without a trailing
boundary is a prefix match: the needle for `get?_push` also matched
`get?_push_self`, so three laws were reported unmeasurable when each is declared
exactly once. The number was 22 before that was fixed and 25 after — an error in
the direction that understated the fixtures' reach.

The procedure, in full:

1. **Extract.** Every match of `^@\[simp\] theorem ([A-Za-z_][A-Za-z0-9_'?!]*)`
   over the module source, in file order. Multi-line and non-`theorem` `@[simp]`
   declarations are out of scope and this module family has none.
2. **Confirm the baseline.** `lake build Tests` must succeed before any edit. If
   it does not, stop: every later result would be a false positive.
3. **Isolate one law.** Match `@\[simp\] theorem <name>(?![A-Za-z0-9_'?!])` —
   the negative lookahead is the fix above, and the character class is Lean's
   identifier tail, so `\b` is wrong here. If the pattern matches other than
   exactly once, skip the law and report it as skipped rather than guessing.
4. **Mutate.** Replace that one match with `theorem <name>`, leaving the file
   otherwise byte-identical. One law at a time; never two.
5. **Classify.** `lake build Tests`, no timeout. Non-zero exit means the law is
   depended upon; zero means it is not. No output parsing, so a failure for any
   reason counts — which is conservative in the direction of over-reporting
   dependence.
6. **Restore.** Rewrite the original bytes and rebuild, unconditionally, before
   the next law and on any error path.

Runs must be serial. Two mutations live in one tree at once make every result
after the first meaningless.

#### The tip, and the per-law manifest

Everything above was measured on `7a783b2c`, which is this branch with current
`main` merged in. The manifest below names every law on both sides of the line,
so a rerun can be diffed against it rather than compared against a total.

**This is the third tip this measurement has had, and the second two were
reviewers catching the same mistake in different disguises.** The first version
reported one module from one tip and five from another, with spot checks and a
prediction covering the gap; `g-reviewer:114` refused the prediction and it was
re-run whole. The second version was measured on one tip and then sat while
`c-stdlib:108` merged to `main` — a branch whose entire purpose was to add goals
that reach `Order`'s laws — so the manifest went stale on exactly the module the
section drew its sharpest conclusion from, while the document still asserted the
manifest held because no `Grass/**` or `Tests/**` file had changed since.
`g-reviewer:124` caught that, and the merge-ready gate had already refused the
authorization for the same reason.

The lesson is not to be more careful. It is that a measurement belongs to a
commit, that a long-lived branch will be overtaken, and that "nothing relevant
changed" is a claim about a tree nobody built. `git diff 7a783b2c HEAD --
'Grass/**' 'Tests/**'` is the check that this manifest still describes the branch
tip; it is empty, and it is the check rather than the assurance.

**Two nominations in review will invalidate it again, and naming them now is
cheaper than being told a third time.** `c-stdlib:109` adds
`Vec.toHostBytes_empty` and `Vec.ofHostBytes_empty` with a fixture that exercises
both, which moves the `HostBytes` row. `c-stdlib:113` adds `Vec.get?_isSome_iff`
and puts `Vec.get?_replicate` and `Vec.get?_eq_none_iff` into the `simp` set with
a fixture that exercises all three, which moves the `Vec` row. Whichever of the
three branches lands last owes a rerun; the two rows and the total are the only
things that move, and the procedure above is how.

**`Vec`** — 25 of 72.

*Depended on:* `emptyCollection_eq_empty`, `default_eq_empty`, `length_fromList`, `get_eq_iff_get?_eq`, `length_push`, `get?_push`, `toList_empty`, `toList_append`, `length_append`, `empty_append`, `length_drop`, `take_zero`, `drop_zero`, `drop_drop`, `length_map`, `get?_map`, `get?_mapIdx`, `length_zipWith`, `foldl_push`, `foldr_push`, `foldr_cons`, `foldl_cons`, `not_mem_empty`, `forIn_eq_forIn_toList`, `flatten_singleton`.

*Not depended on:* `toList_fromList`, `fromList_toList`, `get?_fromList`, `length_empty`, `get?_empty`, `length_singleton`, `get?_singleton_zero`, `length_replicate`, `length_ofFn`, `get?_ofFn`, `length_range`, `get?_range`, `length_set`, `get?_set_self`, `get?_push_self`, `pop?_empty`, `pop?_push`, `truncate_eq_take`, `length_truncate`, `clear_eq_empty`, `length_clear`, `append_empty`, `length_take`, `append_splitAt`, `take_append`, `drop_append`, `take_length`, `drop_length`, `isPrefix_refl`, `map_empty`, `map_singleton`, `map_push`, `length_mapIdx`, `foldl_empty`, `foldr_empty`, `mem_singleton`, `mem_append`, `mem_push`, `getElem_eq_get`, `getElem?_eq_get?`, `flatten_empty`, `sum_empty`, `sum_push`, `length_flatten`, `flatten_append`, `flatten_push`, `allNonEmpty_empty`.

**`Bag`** — 10 of 23.

*Depended on:* `empty_eq_zero`, `emptyCollection_eq_zero`, `add_zero`, `card_zero`, `card_singleton`, `card_cons`, `card_add`, `mem_cons`, `mem_singleton`, `mem_add`.

*Not depended on:* `ofList_nil`, `ofList_cons`, `ofList_append`, `card_ofList`, `mem_ofList`, `zero_add`, `mem_zero`, `map_ofList`, `map_zero`, `map_cons`, `map_add`, `card_map`, `mem_map`.

**`FiniteMap`** — 8 of 9.

*Depended on:* `findValue_nil`, `findValue_cons_self`, `findValue_eraseKey_self`, `emptyCollection_eq_empty`, `lookup_empty`, `lookup_insert_self`, `lookup_erase_self`, `isEmpty_empty`.

*Not depended on:* `eraseKey_nil`.

**`HostBytes`** — 5 of 12.

*Depended on:* `ofUInt8_toUInt8`, `toUInt8_ofUInt8`, `getElem?_toHostBytes`, `get?_ofHostBytes`, `ofHostBytes_toHostBytes`.

*Not depended on:* `toNat_ofNat`, `ofNat_toNat`, `size_toHostBytes`, `length_ofHostBytes`, `toHostBytes_ofHostBytes`, `ofHostBytes_append`, `toHostBytes_append`.

**`Order`** — 3 of 6.

*Depended on:* `count_empty`, `pairwise_empty`, `findIdx?_empty`.

*Not depended on:* `count_push`, `pairwise_singleton`, `idxOf?_empty`.

**`Text`** — 1 of 7.

*Depended on:* `decode_utf8`.

*Not depended on:* `length_utf8`, `utf8_empty`, `isValidUTF8_utf8`, `decode?_utf8`, `utf8_decode`, `utf8_append`.
