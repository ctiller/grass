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

There are two fixtures. Per `Tests.lean` both establish expressibility rather
than a theorem. `Tests/Std/VecVocabulary.lean` covers the type's own claims: that
a `List Byte` and a host `_root_.ByteArray` are each rejected where a Grass
`ByteArray` is required, that extensionality is usable in the shape a consumer
would use it, and that the update framing law composes the way the memory layer
applies it. `Tests/Std/SpikeSurface.lean` covers the demand side: every `Vec`
operation the authored spike sources call, compiled in the shape they call it,
so that §3.4's "no consumer has demanded it" rests on a reading of the corpus
rather than on an assumption about it.

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
| `Vec` iterators | a consumer. §3 lists iteration; `foldl`, `foldr`, `map`, and `mapIdx` cover every use in the spike corpus. |

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
| array-literal syntax for `Vec` (seven sites) | **absent**; §3.7 |

`Tests/Std/SpikeSurface.lean` compiles each of the first four in the shape the
spike writes it, so "the surface supports this" is checked rather than asserted.
Nothing else in the five spikes calls a `Vec` operation. `List` appears once, in
`4_Web_Server/Process.lean`, and is left alone: [STDLIB.md](STDLIB.md) §6 lists
persistent `List` and contiguous `Vec` as separate offerings, so that is a
choice, not a `Vec` demand.

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

### 3.6 Exit criteria

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

### 3.7 Open: the `ByteArray` name collides with Lean's

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
ruling on §3.6 soon rather than at leisure.

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

6. Every operation carries at least one law. An operation without one does not
   remove the need to reason about it, it relocates that reasoning to
   `Vec.toList` in the consumer, which is the leak §3.2 pays for. §3.1.

Open, with the owner each is with:

1. **The `ByteArray` name collision**, with the owner of
   [STDLIB.md](STDLIB.md). §3.7. Sharper than when it was first raised: the
   authored spike sources write bare `ByteArray` in four of the five spikes, so
   "keep the name and qualify at the use site" is a change to the author surface
   and not only to library-internal code.
2. **Whether `Vec α` should be `Array α`**, with this branch's reviewer in the
   first instance. Lean's `Array` is the same one-field structure over `List`,
   and adopting it would delete the restatement cost and settle the literal
   syntax below at a stroke. §3.2.
3. **`Vec` has no literal syntax**, which the spike surface needs and which
   interacts with the previous item. Not settled unilaterally, partly because
   the only cheap mechanism breaks `Array` literals repository-wide and partly
   because the authored surface is [SPIKE_AUTHORING.md](SPIKE_AUTHORING.md)'s.
   §3.5.
4. **The `Bag` representation**, inherited undecided from `c-process:28` and
   genuinely blocked on the repository-wide mathlib dependency question rather
   than on a container judgement. §4.2.
5. **`Grass.Effect`, `Grass.Grammar`, and `Grass.CFG` have no owner**, which
   blocks `mapM`/`traverse`, the parser combinators, and the worklists
   respectively. Raised with the coordinator when one becomes a blocker. §3.4,
   §5.
6. **The `ByteSeq` retirement**, which is an edit to `Grass/Memory/**` and
   therefore `c-mem`'s to make. §4.1.

Items 1, 2, and 3 were all sharpened or found by reading the spike corpus for
demands rather than by reasoning about the library in isolation, which is an
argument for doing that reading earlier next time rather than after a
nomination.
