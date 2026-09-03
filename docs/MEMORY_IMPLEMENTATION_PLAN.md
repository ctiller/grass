# Memory, obligation, and resource implementation plan

Status: implementation plan owned by the `c-mem` implementation agent. This is a
tier-four document under [README.md](README.md) authority ordering: it schedules
work against the normative demands of [MEMORY_MODEL.md](MEMORY_MODEL.md),
[OBLIGATIONS.md](OBLIGATIONS.md), and [RESOURCES.md](RESOURCES.md). It may not
weaken any of them. Where it proposes a structural change outside its ownership
(a new module root, a Core interface) it says so and names the owning decision.

## 0. Ownership boundary

Owned by this plan:

| Area | Normative owner |
|---|---|
| provenance, address spaces, regions, pointers | [MEMORY_MODEL.md](MEMORY_MODEL.md) §2, §7.5 |
| the sealed access chokepoint and access descriptors | §1 |
| authority states, loans, pinning, rebasing | §3, §5.1 |
| initialization and permission tracking | §4 |
| allocators, arenas, epochs | §5 |
| stack/frame provenance, call framing, violation envelope | §6 |
| concurrency vocabulary, event graphs, consistency, races, sync | §7 |
| faults and the audit violation ledger | §8 |
| the per-profile required proof package | §10 |
| obligations, ledger law, terminal dispositions | [OBLIGATIONS.md](OBLIGATIONS.md) |
| the generic resource algebra, budgets, envelopes, realization | [RESOURCES.md](RESOURCES.md), [SEMANTICS.md](SEMANTICS.md) tripartite classes |

Not owned, but directly blocked on this plan:

- ISA instruction models (`Grass.ISA.X86`) need the access, event, and fault
  facets before they can declare an instruction's effects.
- `Grass.Std.Owned` needs loans, initialization, and allocation. It must never
  build a private ownership model ([STDLIB.md](STDLIB.md) §2).
- `Grass.ABI.Win64` needs frame provenance and the call-framing theorem.
- `Grass.CFG` needs block-contract obligation sets and memory shapes.
- `Grass.Semantics` cannot state `SpecProcess` without the resource algebra
  classes.
- `Grass.Process.Resource` instantiates the metric and credit primitives here.

Not owned and not blocked on this plan: process scheduling, owned containers,
instruction set architecture, platform profiles.

## 1. Sequencing principle

[DECISIONS.md](DECISIONS.md) explicitly rejects "bolting memory safety on after
an instruction library exists". The consequence is a specific ordering, not a
general urgency: **the vocabulary that appears in an ISA author's source must be
frozen before ISA authoring begins, and the proofs behind it may land after.**

The plan therefore separates three kinds of work that are usually conflated:

1. **Vocabulary** — the record and class shapes an ISA, ABI, or container author
   writes down. Changing these is a repository-wide rebuild and rewrite.
2. **Operational semantics** — the total functions that make those records step,
   and the framing lemmas that make straight-line verification discharge.
   Changing these rebuilds proofs but not source.
3. **Closure** — the per-profile required proof package of §10, race freedom,
   arena epochs, device bridges. Changing these affects only the profile.

Work is ordered vocabulary first, then the semantics needed by the nearest
acceptance fixture, then closure. Milestone M1 is deliberately over-specified
relative to what Spike 1 needs, because under-specifying it is the expensive
mistake.

Milestones are ordered, not dated. Each names its exit criteria and the agent it
unblocks.

## 2. M0 — Ground (prerequisites this plan does not own)

Nothing here can start without a Lake skeleton and two lower layers. Per
[MODULES.md](MODULES.md) the chain is
`Core -> Std.Logical -> Semantics / Memory / Obligation -> Std.Owned`.

Exact requirements this plan places on the lower layers:

- `Grass.Core` identifiers: a nominal identity scheme with decidable equality and
  a **history-indexed** fresh supply. Foundation law 22 forbids numeric reuse
  from reviving stale authority, so a plain incrementing counter with wraparound
  or reset is insufficient. Consumers here are `AllocId`, `LoanId`,
  `ObligationId`, `EventId`, `CallOccurrenceId`, `EpochId`, and `ContextId`.
- `Grass.Std.Logical.FiniteMap K V` with lookup, insert, erase, domain, disjoint
  union, extensionality, and **framing lemmas**: lookup unaffected by an insert
  at a distinct key, and disjoint-union split and join. The loan map and the
  per-allocation byte store are the heavy users, and these framing lemmas are
  what make M2 tractable.
- `Grass.Std.Logical` finite sequences and `ByteArray := Vec Byte` per
  [STDLIB.md](STDLIB.md) §1, so no second byte container is invented here.

`ByteRange` interval arithmetic with decidable overlap is memory-specific and is
owned by this plan (`Grass/Memory/Range.lean`), not by `Std.Logical`.

**Corrected.** An earlier draft of this plan said that arithmetic was over
`BitVec 64`. That conflated two things. A *range* is offsets within one
allocation, bounded by the allocation's size rather than the machine word, and
`Nat` keeps every framing proof free of wraparound reasoning. An *address* is the
machine-level quantity, and it is not always a number at all (§3.4). The two are
connected by `ByteRange.WithinBound` and by a bridge lemma M2 owes: bounded `Nat`
disjointness implies non-aliasing of the corresponding addresses. Without that
bound `⟨2^64 - 1, 16⟩` and `⟨0, 16⟩` are disjoint as offsets while their
addresses would alias, so the bound is not decoration.

The build must also gate on what it claims to check. `warningAsError` is set in
`lakefile.toml`, because without it a declaration using `sorry` is a warning and
`lake build` exits zero; and `.github/workflows/library.yml` runs both the build
and `Tools/AxiomAudit.lean`, which implements the transitive audit
[FOUNDATION.md](FOUNDATION.md) §3 demands over every `Grass` declaration. Before
these, a green build carried no information.

**Decided.** If no agent has claimed Core, `Std.Logical`, or the lakefile when M1
starts, this plan takes **temporary custody** of a minimal `Grass.Core.Id` and
`Grass.Std.Logical.FiniteMap` rather than blocking, because M1 is what every
other agent is waiting on. Custodial declarations are marked in source as pending
transfer and carry no proofs beyond what M1 through M3 consume, so handover is a
rename and re-export rather than a rewrite. This plan does not thereby claim
ownership of those layers, and it must not grow them beyond its own demand.

## 3. M1 — Vocabulary freeze (the ISA unblocker)

Goal: an ISA, ABI, or container author can write final source against these
types. Contents are declarations, notation, and stated laws. Deep proofs are not
required to exit M1; expressiveness is.

### 3.1 Modules

```text
Grass/Memory/AddressSpace.lean   address-space identity, memory type
Grass/Memory/Range.lean          ByteRange, overlap, disjointness, alignment
Grass/Memory/Provenance.lean     AllocId, hierarchical path, epoch, PointerValue
Grass/Memory/Rights.lean         intent, permission triple, alignment demand
Grass/Memory/Ordering.lean       atomicity, portable ordering, scope
Grass/Memory/Fault.lean          fault classes, completion status, restartability
Grass/Memory/Access.lean         AccessDescriptor, AccessOutcome, AccessResult
Grass/Memory/Substep.lean        ordered substeps, commit prefix, fault visibility
Grass/Memory/Event.lean          MemoryEvent, ContextId, ContextKind
Grass/Memory/Audit.lean          AuditRecord, append-only AuditLedger
Grass/Memory/Facet.lean          the operation-facing effect interfaces
Grass/Memory/Profile.lean        MemoryProfile: the §10 package as a record type
Grass/Obligation/Core.lean       ObligationId, kind, existential payload, Obligation
Grass/Obligation/Disposition.lean  the five terminal dispositions
Grass/Obligation/Delta.lean      preserve/create/discharge/split/join/transfer
Grass/Resource/Algebra.lean      ordered partial commutative laws, ResourceModel
Grass/Resource/Axis.lean         ResourceAxisName, HasResourceAxis, HasResourceLimit
```

`AccessDescriptor` carries every field enumerated in
[MEMORY_MODEL.md](MEMORY_MODEL.md) §1, and `MemoryEvent` every field in §7.1,
including the concurrency fields, on day one. See §7 of this plan for why they
are populated before the single-threaded semantics reads them.

`Grass/Memory/Facet.lean` is the seam ISA authors implement. It provides
separated conditional facets rather than one god class, per
[INSTRUCTIONS.md](INSTRUCTIONS.md) §1, and a `MemoryProfileRequirements` value
naming exactly which facets a given profile demands. A reachable operation
missing a demanded facet is rejected; there is no default empty effect.

`Grass/Memory/Profile.lean` ships the §10 required proof package as a record in
M1 even though no instance closes until much later. ISA authors then see the
complete eventual obligation from the first instruction they write, and profile
closure becomes an incremental field-by-field target rather than a surprise.

### 3.2 Reference instruction effects

M1 also delivers, authored by this agent rather than by the ISA agent, declared
memory effects for the exact Spike 1 instruction mix in
[Spikes/1_Hello_World/Program.lean](../Spikes/1_Hello_World/Program.lean):

| Case | What it pins down |
|---|---|
| `push r12` | implicit stack write, frame provenance, stack pointer delta |
| `mov r64, r64`, `mov ecx, imm` | an operation with no memory effect at all |
| `lea r13, [rip + payload]` | address computation is **not** an access; provenance is derived without a read |
| `mov transferred, 0` | typed frame-slot write, produced initialization |
| `lea r9, transferred.addr` | taking the address of a frame slot for a callee, and the loan that authorizes it |
| `call qword ptr [rip + __imp_WriteFile]` | IAT read, return-address stack write, indirect target, call framing entry |
| `mov eax, transferred` | reading a slot the environment wrote; initialization supplied by the provider profile |
| `ud2 @containment_tail(...)` | terminal fault with no obligation discharge |

These are the freeze evidence and the first regression fixtures. If any of them
cannot be expressed, M1 has not exited.

### 3.4 Addresses are not always numbers

Spike 5 declares `OpMemoryModel Logical GLSL450`. Under SPIR-V's Logical
addressing model a pointer has no numeric address at all: it is an `%id` in a
storage class, reached by `OpAccessChain`. A fixed `BitVec 64` address would force
a fabricated number for `%positionsVar`, which is semantic invention
([FOUNDATION.md](FOUNDATION.md) law 1) wearing a representation's clothes, and the
fixture that falsifies it is already in this corpus.

`Address` therefore has two forms, numeric and symbolic, and the address space
declares which it admits. `AddressSpace.Representable` rejects a mismatch rather
than coercing, per law 8. This is an M1 decision precisely because discovering it
at M9 would reopen the freeze.

`Representable` is a necessary condition only. x86-64 canonicality is
sign-extension of bit 47, not an unsigned magnitude bound — a width test both
rejects canonical high-half addresses and admits non-canonical ones — so address
*validity* belongs to the ISA profile and is discharged in its §10 package.

### 3.5 Law 8 needs a mechanism, not a convention

The open nominal names in this layer (address space, memory type, fault class,
allocation source, provenance step kind, obligation kind, observation label) are
what let a profile extend the vocabulary without editing it. They are also, on
their own, a silent-acceptance path: a misspelled address-space name is a
different, perfectly usable address space.

[FOUNDATION.md](FOUNDATION.md) law 8 requires unknown names to be rejected. The
mechanism is `MemoryProfile`, which carries the recognized-name sets for its own
admitted operations, and lookup against it returns an option a consumer must
handle. The profile is the right owner because
[MEMORY_MODEL.md](MEMORY_MODEL.md) §9 already says "Unimplemented behavior is
rejected by profile applicability, never modeled as harmless" — and because
putting a registry in `Core` would be custody over-reach into another owner's
design.

This must land with `MemoryProfile` in M1, not later: retrofitting a registry
changes every one of those name types.

### 3.6 Exit criteria

- All M1 modules elaborate under the pinned toolchain.
- Every reference case above is expressible without an escape hatch.
- A published `MEMORY_VOCABULARY.md` note lists, declaration by declaration,
  which shapes are frozen under the §7 anti-churn policy and which are
  explicitly provisional. Known provisional entries so far: `ByteSeq`, which
  becomes `Vec Byte` when `Std.Logical` lands `Vec`; and `AddressSpace`, which
  will gain fields as device and GPU profiles arrive at M9.
- The ISA agent has reviewed the freeze against a worst-case candidate list
  (§9 risk 1) and confirmed the seam is sufficient.

Unblocks: ISA instruction authoring, `Std.Owned` type design, and the
`Semantics` statement of `SpecProcess`.

### 3.7 Freeze status: the seam is the acceptance criterion

The M1 vocabulary is **not** frozen, and the condition for freezing it is no
longer "the vocabulary looks sufficient". It is that a fake ISA module *outside*
`Grass/Memory/` can be written cleanly. That fixture is
`Tests/Op/FakeIsa.lean`, and it must be able to:

1. introduce a new operation type without modifying a master sum or a registry;
2. package it existentially;
3. declare read, write, read-modify-write, allocation, release, atomic, fault, and
   obligation facets;
4. have the generic transition relation consume those facets;
5. reject invalid provenance, ranges, ledger effects, and alias conflicts;
6. preserve partial effects when a compound operation faults;
7. coexist with a second, independently defined operation family.

All seven now hold. What that means is narrower than "M1 is done": it means the
seam is real, and the remaining §3.8 gaps are about depth rather than about
whether an ISA author can start.

### 3.8 Where the seam lives, and why not in the profile

`MemoryProfile` describes a target's memory policy and holds no operation facets.
Putting them there would make the memory model depend on a closed operation
universe: every new instruction family would edit `Memory`, and `Memory` would
import ISA definitions, inverting the dependency direction
[MODULES.md](MODULES.md) fixes. It also fights the existential packaging that
`docs/INSTRUCTIONS.md` §1 requires.

Three pieces stay separate:

```text
MemoryProfile          memory policy; knows nothing about operations
HasOperationFacets Op  supplied independently by each operation family
SomeOperation          the family erased, so stepping consumes facets blindly
```

`Grass/Op/Step.lean` imports Memory and Obligation, consumes facets, and updates
both state machines. Memory does not import operations. A new ISA family
participates by declaring an instance; nothing below it changes.

`StepPolicy.requiredFacets` lives with the stepper rather than on the profile, for
the same reason: which facets an operation must supply is a fact about operations.

### 3.9 What review closed, and how

Four rounds of adversarial review, each with fresh context. The pattern in every
round was the same and is worth stating once: **a docstring asserted a property
the code did not have, and the reviewer found it by executing rather than
reading.** Closed since the vocabulary was first written:

- an identity type colliding with Lean's `Id` monad, and freshness that was
  convention rather than mechanism;
- a `BitVec 64` address falsified by Spike 5's own `OpMemoryModel Logical GLSL450`;
- `IsAligned addr 0` universally true, so an unpopulated field accepted everything;
- a descriptor carrying its own `AddressSpace`, able to choose a representation
  that made its own guards vacuous;
- no clause relating `requiredPermission` to `intent`, leaving `Permission.Permits`
  dead code;
- an empty provenance path making every range condition vacuous — a sixteen-exabyte
  write was well formed against the honest 64-bit space;
- `div [mem]` inexpressible, because its faulting step performs no access and a
  list of accesses had no index to name it;
- `visibleEffects?` guessing the `priorEffectsVisible` answer for a profile-owned
  rule;
- `LedgerDelta` able to drop and fabricate duties, and `PreservesIdentity` holding
  for the obligation a transfer had just re-owned;
- `Conflicts` requiring `SameStorage`, so aliased mappings never conflicted;
- a faulted read-modify-write unable to record the read it performed;
- the resource laws admitting `max` as a parallel composition, and then — after
  that was fixed — forbidding `max` as a temporal aggregation, where it is correct;
- the axiom audit silently covering six fewer modules than the build;
- `lake build` exiting 0 on a `sorry`.

Two claims were **withdrawn** rather than fixed, because they could not be made
true as stated:

- the audit violation ledger cannot be append-only *by construction*. `records?`
  reads the list out and `append` folds it back in, so laundering is three lines
  whatever the constructor's visibility, and no arrangement of a type with a
  readable projection avoids that. The property belongs to the transition
  relation; `AuditViolationLedger.Extends` states it and
  `Op.performAccess_extends_violations` proves the stepper preserves it.
- `FreshSupply` cannot guarantee supply uniqueness. `initial` is public and must
  be, so threading one supply per domain is the execution model's obligation.

### 3.10 Docstring discipline

Every public docstring that says "ensures", "prevents", "cannot", or
"append-only" must point to either a theorem or a named transition invariant.
Mechanism-shaped prose reads as verification and is not; this corpus produced four
rounds of evidence for that. Where a property genuinely cannot be enforced by the
type, the docstring says so and names what does enforce it.

### 3.11 Closure properties for the freeze

Nine properties are required before M1 is called frozen. Each names what enforces
it, per §3.10; where a type makes the failure unrepresentable that is recorded
instead of a theorem, because it is the stronger form.

| Property | Enforced by |
|---|---|
| step extends the violation ledger | `Op.step_extends_violations` |
| step emits only well-formed events | `Op.step_events_wellFormed`, and `ValidMemoryEvent` makes a malformed trace unrepresentable: `mk` is private and `MemoryEvent.ofOutcome` is the only producer. As strong as its fields and no stronger — two went uncompared until review found an event whose status contradicted its own counts |
| denial prevents undeclared later effects | `Op.runAccesses_stops_at_refusal` for the access list, `Op.runStep_stops_at_refusal` for the faulting branch. The second was missing and the branch was wrong: `runStep` performed the faulting substep's access whether or not a survivor had been refused, so a denial was followed by a committed write. Found by local adversarial review after the property had already been declared closed and merged; `Tests/Op/FakeIsa.lean`'s `denial_stops_the_operation_on_the_fault_path` is the regression. |
| fault choices are structurally in range | `Op.FaultPlan` carries a `Fin`; the bad case is unrepresentable |
| partial RMW retains its completed read | `Committed` counts reads and writes separately; `faulted_rmw_keeps_its_read` |
| ledger mutation occurs iff the delta is applicable | `Op.obligations_unchanged_unless_committed`; `LedgerDelta.Applicable` requires a typed `ProtocolAuthority`, and `Op.LedgerEffectApplicable` checks each delta against the ledger the previous ones left |
| a fault the operation reached is never discarded | `Op.runStep_records_the_fault`, with `Op.performAccess_preserves_faults`. **The property is weaker than the row used to claim.** A fault reported for a substep the operation never reached, because an earlier one was denied, is not recorded: `Op.runStep_records_no_fault_after_refusal`. That is a semantic decision and it is provisional — see §4.3. |
| failed ledger mutation is recorded and non-mutating | `Op.ledger_refusal_is_recorded`, `Op.refused_preserves_everything_but_the_ledger` |
| every emitted violation class is declared | `Op.refusalOf_class_declared`, over `Op.AuthorityProvider.emittedClasses` — the set grows with the provider list, so an authority's own nominal class is covered too; `Tests/Op/FakeIsa.lean`'s `undeclared_provider_class_cannot_form_a_policy` and `custom_violation_class_is_usable` are the two sides |
| external operation families require no Grass edits | `Tests/Op/FakeIsa.lean`, and reproduced independently by a reviewer building three families outside the repo |

The last is evidence rather than a theorem, and is labelled so. A fixture cannot
prove that *no* family would require an edit; what it establishes is that the ones
tried did not, which is what the seam claim rests on.

### 3.12 Authority evidence extends the seam

The remaining precondition was one synthetic loan or frame authority provider
carried through the seam — not the M3 and M4 models, but enough to show that
authority evidence extends without redesigning operation packaging.

`Grass/Memory/Authority.lean` supplies the grant table
[MEMORY_MODEL.md](MEMORY_MODEL.md) §3 describes, `MemoryState` holds it, and
`Grass/Op/Step.lean`'s `AuthorityProvider` is the extension point `refusalOf`
consults. `Tests/Op/FakeIsa.lean` then defines **two** authority kinds — a loan
and a stack frame — entirely in the fixture, with no edit under `Grass/`, and
proves each refuses without its grant and admits with it.

What that establishes, precisely: `AccessDescriptor`, `OperationFacets`,
`HasOperationFacets`, `SomeOperation`, and the shape of `step` are unchanged by
adding an authority kind. An access does not name the grant it relies on, so the
descriptor gains no field; returning a grant is a ledger operation and already
goes through `LedgerDelta` with its typed `ProtocolAuthority`.

What it does **not** establish: there is no loan or frame *model* here. No split,
join, freeze, exclusivity-iff-empty, pinning, rebasing, or call-framing theorem —
M3 and M4 own those, and a grant is simply live while it is in the table. Adding
the table was itself an edit under `Grass/`; the claim is that the *seam* absorbed
a new authority kind, not that nothing anywhere changed.

**Still not a freeze.** §3.13 lists what remains open. The seam is a clearly
versioned **provisional** interface, and an ISA author starting against it should
expect additive change.

### 3.13 Gaps that remain open

- `Address.symbolic` is an atom where §1 asks for an address *expression*. A
  SPIR-V `OpAccessChain` derives a pointer from a base and a runtime index, and
  nothing relates a symbolic address to its provenance.
- `lock cmpxchg16b` still cannot declare its compare and swap operands. The
  *outcome* now carries values, which was the blocking half; the intent does not,
  so an operation whose behaviour depends on a comparison against a supplied
  operand has nowhere to put it.
- The descriptor carries a `ContextId` but no `ContextKind`, though §7.1 requires
  identity *and* kind; the stepper supplies the kind out of band, and now also
  takes the operation's executing context so that a fault on a substep with no
  descriptor still has one.
- `address` is unconnected to `range`. Two writes declaring the same address with
  different ranges are judged non-conflicting. `Access.lean` defers this to M2,
  but `ConflictsWithHistory` is now live and decides aliasing on a field the
  alignment check does not constrain.
- Five open-name axes have no registry: the `profileSpecific` cases of ordering,
  scope, restartability, and fault visibility, plus `ObservationLabel`.
- `xchg`'s implicit `LOCK` cannot be declared as a demand rather than a choice.
- An operation declaring `onFault := .profileSpecific` cannot be stepped by the
  generic relation at all. Refusing beats guessing, but it means a profile with
  split-store semantics owes a stepper extension before it can express one.

### 3.14 What the seam does *not* yet demonstrate

Worth stating separately from the gaps, because it bears on when M1 can freeze.
`Tests/Op/FakeIsa.lean` shows an externally authored family reaching memory
events, authority checks, obligations, the violation ledger, and — since §3.12 —
two externally authored authority kinds. It does not show that family reaching an
*emitted artifact*, and it does not exercise the loan, frame, or arena **models**,
which remain M3, M4, and M6. The claim the fixture supports is that the facet
interface carries an operation through the transition and absorbs new authority
evidence, not that the transition is complete.

## 4. M2 — Executable single-thread memory semantics

Goal: straight-line assembly verification actually discharges. This is the gate
for a Spike 1 block certificate, and it is what
[INSTRUCTIONS.md](INSTRUCTIONS.md) §5 calls the bounded decidable forward
fragment.

```text
Grass/Memory/State.lean   MemState: per-allocation byte store, init map,
                          permissions, liveness, epoch, provenance table
Grass/Memory/Step.lean    applyAccess : AccessDescriptor -> MemState ->
                          AccessResult x MemState (total)
Grass/Memory/Framing.lean disjointness, read-after-write, init monotonicity
Grass/Memory/Shape.lean   typed shaped read/write over StructLayout footprints
```

Required laws, chosen because the symbolic verifier consumes them directly:

- denial preserves the state immediately before the denied substep (§1) and
  emits an audit record;
- a write initializes exactly the bytes it completes (§4), and a faulted or
  partial access commits exactly the prefix its declared visibility policy
  permits;
- reads and writes to disjoint ranges commute and frame;
- permission and alignment failures produce the declared fault, never a silent
  success;
- typed shapes expand soundly to byte facts for partial access, padding, and
  external writes (§4).

The audit ledger closes here: append-only, non-erasable, with the emptiness
predicate `VerifiedProgram` consumes (§8).

Two constraints on M2 are already settled and should not be rediscovered.

**The byte store is not an association list.** `Grass.Std.Logical.FiniteMap` has
the right framing lemmas but the wrong cost model: `lookup` is a linear scan and
`insert` rebuilds. A 4 KB frame would be quadratic list surgery, and
`applyAccess` has to be total *and* executable to serve the bounded decidable
forward fragment of [INSTRUCTIONS.md](INSTRUCTIONS.md) §5 without violating
[FOUNDATION.md](FOUNDATION.md) law 12. M2 selects a run-based or sorted
representation behind the same extensional API. `FiniteMap` remains right for the
loan map, which is small.

**The offset-to-address bridge is owed here.** `ByteRange` disjointness is `Nat`
arithmetic; addresses are `BitVec 64` or symbolic. M2 must prove that for ranges
satisfying `WithinBound`, offset disjointness implies address non-aliasing.
Without it every framing lemma proves something about offsets that no one has
connected to memory.

### 4.1 What is built

Three of the four files above exist, under different names than the sketch.

`Grass/Memory/Addressing.lean` proves the bridge arithmetic. `addressOf` places an
offset in an allocation based at a `MachineAddress`, and
`disjoint_ranges_do_not_alias` is the lemma the section above records as owed.
It is wired now, and the section above's debt is discharged.
`AllocationRecord.base` places an allocation, `MemoryState.addressAt?` reads the
address of an offset, and `MemoryState.addressAt?_ne_of_disjoint` connects `Nat`
disjointness to distinct machine addresses for a state the model builds. The base
is optional because §7.5's logical spaces have allocations with no machine address.
An earlier version of this sentence added "and it is not authority: `denialOf` reads
none of it", which stopped being true when `denialOf` gained the `placementWraps` and
`addressDisagreesWithPlacement` clauses — both read `record.base`. The half that is
still true is narrower and is the half the model relies on: two allocations sharing a
base are distinct storage unless `aliases` says otherwise, which is §2's
provenance-not-address direction. The *converse* — same space, same address, therefore
same bytes — has no counterpart anywhere in `Grass/Memory/`, and §4.4.1 records what
review demonstrated with it. It is conditioned on `FitsAllocation`:
the allocation's own bytes do not wrap. That is not a convenience — an allocation
whose last byte wraps past `2^64` has two offsets at one address, so no
disjointness argument about it could be sound, and a profile admitting one has
already lost.

`Grass/Memory/ByteStore.lean` is the store, and it is a journal: a write prepends
a run, nothing is merged. Writes are constant time and framing is one case split.
The cost is that reads scan runs and degrade over a long program, and **that cost
is not paid off here.** What makes it acceptable rather than deferred forever is
that every lemma is stated over `cellAt?`, never over `runs`, so a compacting
store agreeing pointwise satisfies all of them unchanged. Compaction is owed.

A run carries `initializes` as well as bytes. `AccessDescriptor.producesInitialized`
lets a completed write decline to credit initialization, and a value-only store
would have reported those bytes as initialized because it held values for them —
the permissive direction [FOUNDATION.md](FOUNDATION.md) law 8 forbids.
`not_initializedAt_write_false` is the theorem. Newest wins for initialization as
it does for value, so a non-initializing write over initialized bytes leaves them
uninitialized; the corpus does not settle that case, and this is the reading that
cannot admit a program a stricter model would refuse.

`AllocationRecord.initialized : List Nat` is gone. Initialization is read off the
store, so `RangeInitialized` cannot drift from what was written.
`MemoryState.write_preserves_metadata`, `write_preserves_other_allocation`,
`rangeInitialized_write_of_other_allocation`, `rangeInitialized_write_of_disjoint`,
and `rangeInitialized_write` are the state-level framing set.

`Op.Oracle.ofMemory` is what fixtures now use; `Oracle.zeroed` remains, unused,
because a profile may still want a machine that reads zeros. It and `Tests/Op/FakeIsa.lean` now
runs the whole M1 seam over it unchanged, which is the evidence that the store
did not cost a redesign. It takes what a store writes *and* what an indeterminate
read observes as parameters. The second is the one worth naming: bytes that are
not initialized have no value the model can read off the store, a profile that admits an
indeterminate read owes what it observes. Defaulting it to zero would be law 8's permissive fallback wearing a
plausible number.

`Grass/Memory/Apply.lean` is `applyAccess`, total and executable, with the laws
stated as equations over it rather than as claims about a transition's branches.
It is not what `Grass/Op/Step.lean` calls — `performAccess` remains the
transition's own path — but both write memory through `MemoryState.commit` and
nothing else, so the framing results are results about the transition.
`Op.performAccess_frames_untouched` and `Op.runAccesses_frames_untouched` state
them for `performAccess` and `runAccesses`, and `Op.runStep_frames_untouched` and
`Op.step_frames_untouched` for a whole operation. The last two were owed for
several rounds while four documents claimed they existed; they quantify over
`sequence.accesses` rather than the survivor list, because `visibleEffects?`
excludes the faulting substep and framing over survivors alone would miss the byte
that substep writes. An earlier version of this section said `applyAccess`
had been factored out of `performAccess`; it had been written alongside it, with
two write paths and framing proved about one. Review found it and `commit` is the
repair.
`applyAccess_refused_preserves_state` is §4's first required law.
`applyAccess_frames_other_allocation` and `applyAccess_frames_disjoint_range` are
the framing half of "reads and writes to disjoint ranges commute and frame";
`applyAccess_comm` is the state half of commutation and `applyAccess_result_comm`
the result half — the same access gets the same refusal decision and observes the
same bytes on either side of a disjoint one. Both are for two accesses within one
allocation. `applyAccess_comm_of_other_allocation` and
`applyAccess_result_comm_of_other_allocation` are the cross-allocation pair, where
disjointness is free: §2 makes distinct `AllocId`s distinct storage by
construction, so coinciding offsets are not the same bytes.

Commutation is stated as `MemoryState.AgreesOn` — agreement at every offset, in
byte and in initialization — and not as state equality. That is forced rather than
chosen: a journal records two writes in whichever order they arrived, so the two
orders leave different write histories and no proof could make those states equal.
`AgreesOn` compares cells rather than bytes because `denialOf` reads
initialization: a values-only agreement would let two orders disagree about
whether a later access is refused, which review demonstrated with a concrete pair
before it was fixed.

Commutation needed a second half that is easy to miss. Bytes agreeing is not
enough if the *decision* can move: were a write elsewhere able to change whether
an access is refused, one order could refuse what the other committed.
`denialOf_write_of_disjoint` rules that out, and it rests on
`ByteStore.initialized_write_iff_of_disjoint` being an `iff` — framing has to
carry a lack of initialization across a write as well as its presence, or an
`uninitializedRead` could be laundered by writing somewhere else.

`Grass/Memory/Shape.lean` is the `Shape.lean` row, and it is deliberately only
half of it. `StructLayout` is a `Std.Owned` facility per [STDLIB.md](STDLIB.md):
it chooses field order, widths, alignment, and padding policy and carries an ABI
profile, and none of that is the memory layer's. What the memory layer owes is
the other side of the interface — given *some* aggregate's field ranges, what is
true of the bytes — and a `Footprint` is exactly that and nothing more.

The obligation is [STDLIB.md](STDLIB.md)'s: "Padding is never silently treated as
initialized semantic data." `padding_uninitialized_after_writing_fields` is the
theorem, proved for any list of the aggregate's fields in any order with any
data, rather than for one convenient write schedule. The reason it matters is
concrete: without it, writing every field of a struct would make the struct read
as fully initialized when part of it was never written, and a typed shape could
launder an `uninitializedRead` that `denialOf` catches on the raw bytes.

The converse half is proved too — `byteAt?_writeField` for
[STDLIB.md](STDLIB.md)'s serialization law and `initializedAt_writeField` for the
field's own bytes — so the two together partition the aggregate rather than making
a one-sided claim. `Tests/Memory/Padding.lean` applies both, and
`cellAt?_writeField_of_other_field` besides, over a struct that pads for a real
reason: a one-byte field followed by a four-byte field its alignment
puts at offset four. Padding there holds no byte at all, not merely an
uninitialized one, so a store that quietly zero-filled the gap would fail even if
it kept the initialization flags right.

The exit criterion is that the framing set discharges a straight-line block
*without a bespoke local lemma*. `runBlock` runs a list of accesses in order and
`byteAt?_write_survives_block` is the discharge: a store's bytes are still there
at the end of a block, provided no later step's declared range covers them.
Everything a caller checks is decidable from the descriptors, which is what
`Touches` is for, so discharging a block is checking ranges rather than reasoning
about the store.

The hypothesis is each step's *declared* range rather than the bytes it actually
wrote. That is deliberate: a caller knows ranges from descriptors and does not
know how much data each store carried, and `applyAccess` only ever writes inside
the declared range, so the stronger hypothesis would buy nothing and cost every
caller an obligation.

`Tests/Memory/StraightLineBlock.lean` is the check, and it is symbolic rather
than concrete on purpose. A fixture that fixed the allocation, the data, and the
offsets and closed everything by `decide` would prove the arithmetic and say
nothing about the lemma set — the kernel would be doing the work the theorems are
supposed to do. There the state is universally quantified, the data arbitrary,
and every proof a single application of a named exported theorem. One local
declaration exists and is a wrapper, not content.

`Tests/Memory/Spike1Block.lean` runs that discharge on the Spike 1 descriptors.
It runs `runBlock`, the memory-level executor, and not `Op.step`; the framing
carries because both write through `MemoryState.commit`, but the sequence executed
is not literally the one the machine executes. The instructions are: `mov transferred, 0`, then the two accesses inside
`call [rip + __imp_WriteFile]`, then `mov eax, transferred`. The claim the
spike's correctness argument turns on is that the reload observes what the store
wrote, and the `call` in between reads a different allocation and writes a part of
this one thirty-two bytes below.

The split between what is decided and what is proved is the point. The side
conditions — allocation live, epoch and space match, range in bounds, permission
allows the write, no intervening declared range covers the slot — are `decide`d,
because those are exactly what a front end computes and deciding them is their
intended use. The framing is not decided: it is one application of
`byteAt?_write_survives_block`. A proof that closed the whole thing by `decide`
would compute the answer from that particular state and would still compile if
every framing theorem were deleted.

The file also carries the control the claim needs: the same reload *is* refused
as an `uninitializedRead` against the state before the store, so
`the_reload_is_not_refused` is evidence the initialization check ran rather than
evidence it was skipped.

One lemma fell out that is worth naming: `applyAccess_state_indep` and
`runBlock_state_indep` say what memory looks like afterwards does not depend on
what an indeterminate read would have observed. The `indeterminate` answer stays
in the observation and never reaches memory, so a profile choosing differently
changes what a program sees and never what it leaves behind.

### 4.2 What M2 still owes

Recorded rather than implied, and expanded twice after adversarial review. The
first round found three of these stated as done; the second found three more, and
one outright defect that had already merged — see §3.11's denial row.

- **Trace agreement between `runBlock` and `step`.** They agree on memory, through
  `MemoryState.commit`. Nothing proves they agree on the recorded trace, so a
  straight-line argument over `runBlock` is an argument about memory and not about
  what a program's event log says.
- **`MemoryProfile.vocabularyVersion` is never checked.** A profile states which
  vocabulary version it assumes and nothing compares that to what the transition
  implements. There is one version and no migration theorems, so there is nothing
  yet to compare against; this becomes real when a second version exists.
- **`AccessDescriptor.observations` is never read.** §3.13 recorded that
  `ObservationLabel` has no registry, which understates it: the field has no reader
  at all. §7.5's device completion and fence signals are what would consume it, and
  those are causal edges in the event graph, so the consumer is plausibly M8 — but
  no milestone in this plan claims it, which is why it stays here rather than being
  reclassified.

  `AccessIntent.isDevice` was in this list and is now **removed from the
  vocabulary** rather than owed. Its docstring read "performed by, or targets, a
  device rather than the CPU", which is two different facts in one `Bool` with
  neither recoverable from it, and both are already carried by mechanisms that
  *are* consulted: who performs an access is `ExecutionContext.kind`, which §7.1
  requires every event to carry and which `step` checks against
  `MachineState.contexts`; what it targets is its `AddressSpaceId`, which
  `denialOf` checks and which §7.5 makes non-interchangeable precisely so the
  identity carries the fact. A third, unconsulted source for a fact two consulted
  ones already carry is the defect shape this branch has found eight times.
- ~~**`InitializationDemand.permitsUninitialized`'s justification names nothing**~~
  Closed together with `FaultVisibility.transactional`'s and
  `FaultVisibility.profileSpecific`'s. `AdmittedVocabulary` carries
  `initializationJustifications`, `atomicityJustifications` and
  `faultVisibilityRules`; `Admits` requires the first and `step` requires the other
  two (`onFaultRuleNotRegistered`). Three registries and not one, because a rule
  permitting an uninitialized read is not a proof that a two-substep store is
  all-or-nothing, and a shared namespace would let either name satisfy the other.

  Registration is not discharge. A registered name says the profile owns the claim;
  §10's package is where it is proved, and that remains M10's.
- ~~**The operation-level `faults` facet is consumed by nothing.**~~ Closed.
  `OperationFacets.supplied` read only `isSome`, so an operation declaring
  `faults = some []` closed the facet and then page-faulted through a substep that
  admitted one. `step` now cross-checks it in both directions before running
  anything: every class a substep may raise must appear in the operation's list
  (`operationFaultsIncomplete`), and every class the operation names must be
  recognized by the vocabulary (`operationFaultNotRecognized`) — the third place a
  fault class could be named and the only one no registry saw. Statically, on every
  step rather than only on a faulting one, because two declarations that disagree
  are refused rather than reconciled ([FOUNDATION.md](FOUNDATION.md) law 8).

  An **absent** facet is still not a declaration of no faults; whether it may be
  absent is `Closes`'s question. Eighteen of `Tests/Op/FakeIsa.lean`'s own
  operations were inconsistent when the check went in, which is the measure of how
  little a declaration nobody reads constrains.
- **Ordering modes are checked against a registry; the refinement theorem is still
  owed.** `AdmittedVocabulary` now carries `orderingModes` and `orderingScopes`, and
  `Admits` requires a `profileSpecific` mode or scope to be a name the profile
  registered (`AdmitsOrder`, `AdmitsScope`, and the two `not_admits_of_unregistered_*`
  theorems). `MemoryOrder.IsPortable` gained its consumer in
  `admitsOrder_of_isPortable`: a portable mode needs no entry, since
  [MEMORY_MODEL.md](MEMORY_MODEL.md) §7.1 fixes those five. Before this, an access
  declaring `profileSpecific` with any name at all stepped and minted an event
  carrying it.

  What remains owed is §7.1's actual demand: an ordering request may be used "only
  where it has a proved target meaning", and mapping a portable order onto an ISA or
  API operation requires a refinement theorem. Registration says the profile owns
  the name. It does not say the name means anything on a target, and nothing here
  can — the refinement obligation belongs to an ISA owner, and the strength relation
  it would be proved against is M8's `ConsistencyProfile`.
- **`SubstepSequence.ClaimsAtomicity` still has no consumer.** The justification
  *names* are registered now (above), but `RequiresJustification` and
  `ClaimsAtomicity` exist so a §10 package can enumerate outstanding claims and
  nothing under `Grass/` enumerates them. `StepPolicy.unregisteredOnFaultRule?`
  consults the registries directly rather than through `RequiresJustification`, so
  that predicate's only consumer is `unregisteredOnFaultRule?_priorEffectsVisible`,
  a theorem.
- **§10's proof package is closable by triviality, and its docstring calls that the
  mechanism.** `RequiredProofPackage`'s eleven fields are bare `Prop`s the profile
  owner chooses; nothing relates a field to the profile, to its admitted operations,
  or to any theorem in the tree. `Holds` is their conjunction, so a profile supplying
  `True` eleven times *closes* §10 and `Holds` is `trivial` —
  `Tests/Op/FakeIsa.lean` does exactly that and says so, but the honesty is the
  fixture's, not the type's. The docstring says a `MemoryProfile` "cannot be
  constructed with one missing — which is the mechanical content of" §10's gate; what
  is enforced is that eleven propositions are *named*.

  This is the last gate between a profile and `VerifiedProgram`. Closing it means each
  field's *statement* mentioning the profile — `accessDescriptorSoundness` quantifying
  over what the vocabulary admits, and so on — which is corpus work spanning this
  layer and `VerifiedProgram`'s, and it is a design question rather than a repair.
  §4.2.1 considered `MemoryProfile.package` and answered a different question: who
  consumes it. Nobody asked whether its content is constrained.
- **§8's second conjunct is half-stated.** "`VerifiedProgram` proves the ledger
  remains empty **and that only spec-allowed fault outcomes occur**."
  `MachineState.FaultsRecognized` is the half this layer can state — every recorded
  fault is of a class the profile declared — and it had no predicate at all until
  review found that `MachineState.faults` was appended to by `runStep` and read by
  nothing under `Grass/`. What "spec-allowed" means at a given point is
  `docs/SEMANTICS.md`'s, not this layer's, and no milestone owns the rest.
- **§7.1's `fence` event kind cannot be minted, and there is no fence intent.**
  `kindOf` yields only read, write and read-modify-write; `ofOutcome` is the only
  producer of a `ValidMemoryEvent`; and `AccessIntent` has no fence form, because an
  intent that neither reads nor writes is refused by `WellFormedIn.notInert`. So
  §7.4's "release establishes the profile's causal edge" has no event to carry the
  edge. A theorem stated over `EventKind.fence` was consequently vacuous and is now
  stated over `touchesMemory`.
- **`Grass/Core/Generational.lean` is dead, and it makes law 22's second half look
  discharged.** Nothing imports it; it builds only through the `Grass.+` glob. Every
  identity in the tree — `AllocId`, `GrantId`, `EpochId`, `EventId`, `ContextId`,
  `ObligationId` — is a bare `Uid`, never a `Generational`, so the externally-recycled
  numeric case that module exists for is unaddressed. `ExecutionContext` carrying an
  OS thread identity is the concrete instance.
- **`FreshSupply` is fabricable, rewindable and observable through its recursor.**
  Its docstring claimed the private constructor prevented all three; review compiled
  all three from outside the module and re-minted an identity a rewound supply had
  already issued. The docstring is corrected. What actually protects `never_reissued`
  is its `Reachable` hypothesis, and nothing type-enforces that a caller mints from a
  forward-reachable supply.
- **`MemoryState.Exclusive` and `outstandingLoans` are defined on the raw entry
  list**, which `Grass/Std/Logical/FiniteMap.lean` says is "never the right relation
  to use" — two `Equiv` maps can differ under a filter. Unexploitable only because
  `MemoryState.mk` and the `grants` field are private, so the map is only ever built
  by `insert` and `erase`. That is an invariant holding because no code exercises the
  case, protected by an unrelated privacy decision in another module with no theorem
  linking the two.
- ~~**A duty can be transferred to a context that names no live context**, after which
  it can never be discharged, since discharge requires the actor to own it.
  `LedgerDelta.Applicable`'s transfer clause ignores `newOwner` entirely.
  `Grass/Op/Step.lean` has `MachineState.contexts` and could check it there.~~ Closed
  the way this entry said to: `Applicable` takes the context set and the transfer
  clause requires `newOwner ∈ contexts`, which `Grass/Op/Step.lean` supplies from
  `MachineState.contexts.domain`.

  **What the machine knows is what has executed.** `contexts` is populated by
  `noteContext`, so a context that has never stepped is not a destination, and handing
  a duty to a thread before it runs is refused. That is the conservative reading and
  the cost is real; [FOUNDATION.md](FOUNDATION.md) law 8 prefers it to a permissive
  default, and a profile needing the other behaviour has to say so. The two fixtures
  are the pair: a transfer to a context the machine has never seen is refused and the
  duty survives with its owner unchanged, and the same transfer to the device engine
  goes through once the engine has stepped.
- **`Grass/Memory/Shape.lean`'s `writeField` is unbounded by the allocation.** It
  truncates to the field's size and checks nothing about `base + field.range.start`
  against the extent, and `MemoryState.write` writes into an unbounded journal. Not
  reachable today — `writeFields` has one caller, a padding fixture, and it is not
  the access path — which is the point: it is a facility whose only safety is having
  no users.
- **`FacetName` is open nominal in shape and closed in effect.** It carries a `Name`,
  so a profile may name a facet this layer has never heard of; `OperationFacets` is a
  closed four-field record and `supplied` can only return those four. A profile-invented
  name in `requiredFacets` therefore makes `Closes` unsatisfiable and rejects every
  operation of every family. It fails safe, and §3.5's rationale for open nominal
  names — extension without editing — is not true of this one.
- **`MemoryState.Granted` is vacuously true on an empty range**, in every state, since
  it quantifies over the range's bytes. `not_granted_empty` had to gain a
  `¬ range.IsEmpty` hypothesis to stay true. Safety rests on
  `AccessDescriptor.WellFormedIn.rangeNonEmpty` two layers up, and the invariant moved
  out of the predicate without being written into it.
- **`AdmittedVocabulary.admissibilityFailures` collapses `WellFormedIn`'s fourteen
  named conditions into one anonymous `notWellFormedInSpace`.** The list exists so a
  rejection says which clause failed, and `WellFormedIn` is a structure of named
  fields so a failing condition names itself; the first clause throws both away. A
  zero-length read and a write that under-declares its permission produce the
  identical value.
- **The layer cannot carry Spike 1, and the reason is not a missing convenience.**
  `WriteFile` is a second execution context, and `Grass/Op/Step.lean`'s
  `ConflictsWithHistory` refuses any cross-context access whose event conflicts with
  an earlier one — `StepPolicy.compatible` defaults to refusing every pair, which the
  comment there names as "the conservative direction" pending M8's happens-before.
  Review built a Spike 1 `StepPolicy` and stepped it: the program's
  `mov transferred, 0` runs clean, and the API agent's write to the slot it was lent
  is refused and recorded, which [MEMORY_MODEL.md](MEMORY_MODEL.md) §8 requires to be
  empty for a `VerifiedProgram`.

  The conservative direction is right; what was not recorded is its consequence. M8
  is scoped to Spike 4 in §5 and described as additive. It is not: the single-context
  assumption is violated by the *first* acceptance program, so the M2 and M3–M5
  acceptance criteria cannot close without either M8's ordering or a profile-supplied
  `compatible` relation that says what an external API agent's write is ordered
  against. That is a design question and it is the largest one on this list.
- ~~**Nothing steps the M1 reference instruction set.**~~ `Tests/Memory/Spike1Policy.lean`
  does: a `MemoryProfile`, an `AdmittedVocabulary` populated from what the reference
  descriptors actually name, and a `StepPolicy` adopting the standard loan rule. Every
  program-thread reference case steps and records what it should — the store, the
  implicit stack write, the `call`'s two events from one instruction, the three
  effect-free operations, and the reload refused before the store and admitted after.

  **The criterion is met for the program's instructions and not for Spike 1.** The
  API agent's write to the slot the program lent it steps, records a violation, and
  mints no event, because `ConflictsWithHistory` refuses every cross-context conflict
  — `the_agent_write_is_refused` is that, stepped. So the M8 entry above is not a
  worry about a future milestone; it is the reason this criterion cannot fully close,
  stated as a theorem rather than as a claim in this document.
- ~~**`Tests/Memory/Spike1Block.lean` proves the wrong data flow.**~~ Fixed. The
  block now applies the API agent's write to the slot it was lent, between the `call`
  and the reload, and `the_reload_observes_the_agents_count` is Spike 1's actual data
  flow: `mov eax, transferred` reads the byte count `WriteFile` wrote, not the zero
  the program stored. `the_agents_count_is_not_the_stored_zero` is the control, and
  `the_initialization_came_from_the_agent` discharges `movEaxTransferred`'s declared
  justification with the fact it declares rather than with the program's own store.

  The agent's write appears in a `runBlock` fixture and not in a `Grass.Op.step` one,
  and that is the M8 problem above rather than a choice: `runBlock` is the
  `applyAccess`-level executor and asks no cross-context question, so it can say what
  the program does while the transition cannot yet admit it.
- ~~**`MEMORY_VOCABULARY.md` does not exist**~~ It does now, and it says what M1's
  exit criterion asks: declaration by declaration, which shapes are frozen and which
  are provisional. It reads "frozen" narrowly — a shape a consumer may depend on, not
  a claim that the declaration is correct — and its closing section says the freeze
  is stable in practice and not yet frozen by the process §3 describes, because two
  of §9 risk 1's mandatory fixtures are still absent and the ISA agent's review has
  therefore not happened.
- ~~**Two of §9 risk 1's five mandatory pre-freeze fixtures are absent.**~~ Written:
  `Tests/Memory/RiskOneCases.lean` has `rep movsb` and `lock cmpxchg16b`. Both are
  expressible, and writing them found two things the frozen shape cannot say, which is
  what risk 1 asked for.

  **`rep movsb` is a family, not a descriptor.** The count is a runtime register and
  `AccessDescriptor.range` is fixed, so `substeps` is a function of the operation
  value — which `HasOperationFacets` already allows. The cost is that a proof about
  `rep movsb` for all counts is an induction over that family, so the `decide`-based
  side-condition idiom in `Tests/Memory/Spike1Block.lean` does not carry to it. The
  zero-count branch is separate: `rangeNonEmpty` refuses an empty access, so a
  zero-count string operation has no memory effect at all and an ISA model must
  case-split.

  **`lock cmpxchg16b` cannot say its write is conditional.** §3.13 said it "cannot
  declare its compare and swap operands", and that turns out to be about *values*,
  which this layer does not model. What it genuinely cannot express is that a failed
  comparison writes nothing: `intent.writes` is `true` either way, and `Committed` is
  about a *faulting* access's prefix, not a write that lawfully did not happen. Safe
  for authority — the access demands write authority it may not use — and wrong for
  §7.3's conflict rule, where a non-writing access does not conflict.

  What remains of the criterion is the ISA agent's review of the freeze against this
  list, which is that agent's and has not happened.
- **Aliased allocations have independent byte stores.** `MemoryState.SharesBytes`
  says two allocations name the same bytes, and the whole authority layer believes
  it: `grantsOver`, `AuthorizedBy` and `MemoryEvent.Conflicts` all key on it. But
  `MemoryState.write` writes `record.bytes` of the *named* allocation only, so a
  store through a mapped view leaves the file's bytes unchanged and a read of the
  file afterwards sees the old value. "Same storage" is an authority-level fiction
  with no byte-level counterpart, which means `Tests/Op/StandardLoan.lean`'s
  `a_loan_cannot_be_bypassed_through_an_alias` guards a relation the memory
  semantics does not implement.

  This is the largest thing on this list, and it is now visible in the test suite
  as well as here: `Tests/Op/StandardLoan.lean`'s
  `the_alias_is_not_yet_a_byte_level_fact` stores through the view and reads the old
  value from the buffer.

  Two shapes close it, and the choice is a design decision rather than a repair:

  1. **`MemoryState.write` propagates across the alias set.** Smallest diff to the
     data, largest to the proofs — every framing lemma keyed on `id ≠ other` becomes
     keyed on `¬ SharesBytes id other`, in `Grass/Memory/State.lean`,
     `Grass/Memory/Apply.lean` and `Grass/Op/Step.lean`. It also needs the offset
     question below answered, because propagation has to know where to write.
  2. **Allocations share one byte store by identity.** `AllocationRecord` carries a
     storage identity rather than a `ByteStore`, and the stores live in a map beside
     the allocations. Writes are shared because there is one store, `SharesBytes`
     becomes equality of storage identity — decidable in one comparison instead of a
     bounded transitive closure — and `SharesAfter`, `AliasHop` and the fuel bound
     disappear. Larger diff to the data, and it makes the offset question explicit
     rather than assumed, because a view onto a store at a non-zero offset has to say
     so somewhere.

  The second is the better shape. Neither should be taken without the design owner,
  because both change `MemoryState`.
- **`MemoryState.aliases` records no offset mapping.** `AuthorizedBy` and
  `grantsOver` compare `ByteRange`s across aliased allocations with `Contains` and
  `Meets`, which assumes aliased allocations agree offset for offset. A view mapped
  at a non-zero file offset — the ordinary `MapViewOfFile` case — does not.
- ~~**`AccessDescriptor.WellFormedIn.rangeInProvenance` is self-certifying.**~~ Half
  closed. `denialOf` compares `provenance.rootExtent` to the allocation record's
  `extent` and records `provenanceExtentMismatch` when they differ, so a descriptor
  no longer supplies the bound it is checked against. It remains a recorded violation
  rather than a rejection, which is `denialOf`'s shape for every access-time failure.

  Provenance `path` step extents are still unchecked: nothing requires a `field` step
  at `⟨2048, 64⟩` to correspond to anything, and `Provenance.Nested` relates the
  steps to each other and to `rootExtent` only.
- **`ByteRange.Contains` and `ByteRange.Meets` disagree about one past the end.**
  `Contains` places `empty r.stop` inside `r`, which is what a bounds check wants;
  `Meets` places it outside, which is what an authority check wants. Both cite §5.1.
  `AccessDescriptor.WellFormedIn.rangeNonEmpty` makes the position unreachable from
  an access and therefore from `step`, but `denialOf` still returns `none` for a
  zero-size descriptor, so a consumer on the `applyAccess` path — which
  `Grass/Memory/Apply.lean` contemplates — still meets it. The predicates are not
  reconciled; the access gate routes around them.
- **No policy in the tree requires the `.ordering` facet**, so omitting it skips the
  agreement check entirely. `Tests/Op/FakeIsa.lean`'s policy requires
  `[.memoryEffects, .faults, .restartability]`. Whether a facet is required is
  `OperationFacets.Closes`'s question and a profile's to answer, but the pressure the
  strictness creates is toward not declaring, and nothing records which facets a
  profile *should* require.
- **`OperationFacets.ordering` is single-valued.** `step` now requires it to equal
  every access substep's ordering, which is the only relation this layer can state:
  `Grass/Memory/Ordering.lean` deliberately defines no strength order, because the
  one that matters is M8's. An operation whose substeps genuinely differ in ordering
  — a store with an implicit fence — cannot declare that and is refused. The facet
  needs to become per-substep, or the check needs M8's relation.
- **`InitializationDemand` is per-access.** §4 asks for initialization "tracked at
  the granularity required to justify every read", and a struct copy with three
  padding bytes must declare `permitsUninitialized` for the whole range, turning the
  check off for every byte. The registry added for the justification name gates the
  name and not the granularity, and §4 does not describe the escape at all.
- **`AdmittedVocabulary.faultVisibilityRules` holds names, and the transition needs
  an answer.** `SubstepSequence.visibleEffects?` returns `none` for
  `FaultVisibility.profileSpecific` and `step` rejects, so registering a rule name
  unblocks only the path on which the rule is never consulted — a sequence that does
  not fault. `Tests/Memory/Spike1Reference.lean`'s `splitPageStore` is the corpus's
  own example and an ordinary x86-64 event. The registry should map a name to a
  survivor rule, not to nothing; the danger of leaving it is that someone later makes
  `visibleEffects?` consult it, find a bare name, and fall back to
  `priorEffectsVisible`, which `Grass/Memory/Substep.lean`'s module comment calls the
  worst available behavior.
- ~~**`SubstepSequence.ClaimsAtomicity` requires more than one substep.**~~ Closed;
  the conjunct is gone. A single-access sequence declaring `transactional` says its
  commit is all-or-nothing, which for a page-crossing store is a substantive claim
  and false by default on x86-64, and calling it claimless meant a §10 package
  enumerating outstanding claims would not have seen it while `step` required a
  registered justification for it regardless.
- **`WritableByAnother` is the only rights-sensitive predicate in `authorityOf`.** A
  grant permitting `execute` but not `write` reads as read-only, and `AuthorityState`
  has no state for execute-only sharing. Nothing exploits it today.
- **`Restartability` is declared and never read.** A profile can require the facet
  and a descriptor carries a value, but nothing in the transition consults it, so
  [MEMORY_MODEL.md](MEMORY_MODEL.md) §7.4's retry rules have no mechanism here.
- **`runStep_records_the_fault`'s `hreached` has no abstract discharge.** A caller
  can close it by `decide` on a concrete fixture. There is no lemma taking "no
  survivor is refused" to it, because that has to thread state through the
  `runAccesses` recursion. The theorem is not vacuous and is currently only usable
  concretely.
- **Byte-store compaction is partial.** `ByteStore.compact` drops runs a newer run
  covers everywhere, which is the degenerate case, and `cellAt?_compact` proves it
  answers every offset identically — so the "a compacting store is a drop-in"
  argument the module was designed around is now discharged rather than promised.
  It does not merge adjacent runs or clip partial overlaps, which needs splitting a
  run against a range. Reads are bounded by distinct live regions plus
  unnormalised overlaps rather than by write count. Nothing calls it automatically,
  because calling it per write restores the cost it avoids; when to call it belongs
  to whoever owns the allocation lifecycle.
- **`ByteStore` structural equality observes the journal.** Every exported
  *theorem* is representation-independent, but the derived `DecidableEq` is not:
  two pointwise-identical stores built by different write sequences are provably
  distinct. A compacting store is a drop-in for the theorems and not for `=`.
  Nothing in the layer's reasoning depends on that equality — the framing and
  commutation laws are over `AgreesOn` and `cellAt?` precisely because it does not
  — but it is a limit rather than an oversight, and compaction will change it.


One more defect this milestone found in already-merged code, recorded because a
closure property depended on it. `FaultVisibility.transactional` declares "no step
is visible unless all are". `visibleEffects?` returned `[]` for it, which answers
for the substeps *before* the failure — and nothing answered for the faulting
substep's own partial write, so `runStep` committed it. A transactional sequence
therefore discarded its completed substeps and kept the faulting one's prefix,
which is the reverse of what it declares.
`Grass/Memory/Substep.lean`'s `faultingEffectVisible` is the missing question, and
`Tests/Op/FakeIsa.lean`'s `transactional_exposes_nothing` is the regression. The
fault is still recorded: nothing being visible is a claim about committed effects,
not about whether the machine faulted.

A fourth adversarial round, aimed at the fault model because both live defects
so far were there, found four more and the same shape twice again — a property
enforced for the substeps before a failure with the failing one exempt, or an
input the transition took on trust.

- **The reported fault class was checked against nothing.** `FaultPlan` carried a
  `FaultClassId` that no registry saw: not `Substep.faults`, not
  `AccessDescriptor.admittedFaults`, not `AdmittedVocabulary.faultClasses`. An
  undeclared class was recorded into `RaisedFault` and into a `ValidMemoryEvent`'s
  status, since `MemoryEvent.WellFormed` constrains counts and lengths but not
  fault identity. This is `AuthorityProvider.violationClass`'s hole in a second
  place, in a module claiming every registry is consulted.
  `StepRejection.faultClassNotDeclared` closes it.
- **Every completed load and store reported `partialCommit`.**
  `AccessOutcome.status` demanded reads *and* writes both cover the range,
  unconditionally on intent, and a write-only access has `readCount = 0` by
  construction. So `AccessStatus.completed` was reachable only for a full-width
  read-modify-write, and `IsComplete` — the predicate written to answer "did the
  whole access take effect" — was false for every load and store. The test is
  intent-relative now.
- **A faulting read-modify-write could not keep its read without its write.**
  `Committed` counts reads and writes separately and this document's own module
  motivates that with an `xadd` that observed its operand and faulted before
  storing. The transition truncated both lists by one shared count, so that
  outcome was the one thing the fault path could not express, and the fixture
  asserting the read survived never checked the write. `FaultPlan.before` carries
  both counts now.
- **A faulted access applied its obligation ledger effect in full**, at any commit
  count including zero: a `reserve` that faulted having written nothing created its
  duty, and a `release` that faulted having written nothing discharged one. The
  second is a leak. The asymmetry review named is the sharp part: the alias check
  treats a zero-byte faulted access as having touched nothing, while the ledger
  treated the same access as fully performed, and both cannot be right. See §4.3.

A fifth round, aimed at the fourth round's own fixes because they were new code
written fast. Nine findings; three were live defects and two of those are on main.

- **An access could declare a context other than the one running it.**
  `MemoryEvent.ofOutcome` took the event's identity from
  `AccessDescriptor.context` and its kind from `step`'s argument, and nothing
  compared them. `ConflictsWithHistory` keys on that identity, so
  [MEMORY_MODEL.md](MEMORY_MODEL.md) §7.3's race rule was defeated by one field: a
  device write naming the program thread aliased the thread's bytes and committed,
  and the event it minted paired thread identity with engine kind, which §7.1
  forbids. `StepRejection.contextMismatch` closes it.
- **A `.compute` substep's fault classes were checked against no registry.** The
  round-four fix closed the access case; a compute substep has no descriptor, so
  `MemoryProfile.Admits` never saw it and the only thing checked about one was that
  its fault list is non-empty. `faultClassNotDeclared` was validating a plan
  against a list that was itself unvalidated — and `.compute` is the constructor
  the `div` case exists for. `StepRejection.computeFaultNotRecognized` is the
  sibling clause.
- **The read/write separation stopped at `Committed`.** `AccessStatus` still
  carried one number, the `max`, so the very outcome round four added — an `xadd`
  that read eight bytes and wrote none — recorded `faulted 8`, `committedBytes`
  answered eight for an access that wrote nothing, and `committedRange` mapped it
  onto the whole range. `AccessStatus` carries both counts now and
  `committedWriteRange` is named for what it means.
- `FaultPlan`'s commit counts are bounded by `StepRejection.faultCommitOutOfRange`
  rather than saturating silently, which is what `faultPointOutOfRange` did for the
  index.
- `faultWithUndeclaredLedgerEffect` fired on `transactional` sequences, where
  `faultingEffectVisible` proves the faulting access is never performed and the
  effect cannot apply. Now gated on it.

A sixth round, on the fifth round's repairs and on a systematic field census.
Four more live defects, two of them on main and two in the previous round's fixes.

- **`MemoryState.SharesBytes` compared a single alias hop.**
  [MEMORY_MODEL.md](MEMORY_MODEL.md) §7.5 makes mapping and sharing typed
  transitions and those compose, so a file aliased to a view and that view to a
  second view means all three name the same bytes. The two ends of such a chain
  were declared non-conflicting and a cross-context write to the far end committed
  — the same defect `SharesBytes` was introduced to fix, one hop out. It is the
  bounded transitive closure now.
- **`Obligation.owner` was consulted by nothing**, so any context could discharge
  any duty. [OBLIGATIONS.md](OBLIGATIONS.md) opens by making an obligation a duty
  of its holder. `LedgerDelta.Applicable` takes the acting context now and checks
  ownership on every delta kind, including `create`, since a context may not
  fabricate a duty in another's name either.
- **The read/write split stopped at `AccessStatus.completed`**, which still
  answered "the whole range" for both counts — and the intent-relative
  completeness test means every ordinary load and store lands there. A completed
  load claimed to have written its whole range. `completed` carries its counts now.
- **`MemoryEvent.WellFormed` never related `status` to the counts**, so an event
  saying it observed nothing while `readCommitted` said eight discharged every
  clause and wrapped in a `ValidMemoryEvent`. Two records of one fact with nothing
  tying them, inside the structure that exists to prevent that.
- **The context *kind* was still unchecked** after `contextMismatch` closed the
  identity half: one `ContextId` could be a thread in one step and a device engine
  in the next. `MachineState.contexts` is the single source of truth now.
- `faultCommitOutOfRange` bounded both counts by the range, so an impossible read
  count on a write-only access was approximated to zero rather than refused, while
  the same impossible claim on a compute substep was refused. The bound is
  intent-relative now.

### 4.2.1 A gate for the defect class, because review was not converging

Six adversarial rounds found eight defects that had already passed a merge review.
All but one had the same shape — the model carries a fact and nothing consults it
— and rounds four, five and six each found defects in the immediately preceding
round's repairs. A process that finds a fixed fraction of a population per pass,
and adds to the population with each repair, is not converging, and running a
seventh round would have been the same bet again.

A field whose name is never projected is a *lexical* property, so
`Tools/ConsultedAudit.py` checks that directly and CI runs it, with an allowlist
where each entry states why a field is carried anyway. An unlisted one fails the
build, so the judgement is made once rather than rediscovered.

**It is a net, not a proof, and the difference matters** because this section used
to present it as closing the class. It keys on the field name rather than the
declaring structure, so two structures sharing a field name are indistinguishable
without elaborating Lean. A clean run means no declared field name is entirely
unprojected across `Grass/` and `Tests/` — not that every field is meaningfully
consumed. Review corrected the overstatement, and also two false negatives it did
have: comments and string literals are stripped before scanning, and a
construction `name := value` no longer counts as a read. `--self-test` seeds each
of those classes and fails if the scanner stops discriminating; it also asserts
the same-named-field blind spot is still a blind spot, so that cannot quietly
become a silent pass mistaken for coverage.

It reported six fields six review rounds had not. **On inspection only two were
gaps**, and the first version of this section called all six defects — the same
overstatement the tool itself was corrected for, made in the paragraph announcing
the tool. What the audit finds is a field nothing projects; deciding whether that
is a defect still takes reading the corpus, and I skipped that step.

Checked one at a time: `AddressSpace.memoryType` and `coherence` are **not** gaps,
because §7.1 requires the *event* to carry address space and memory type and
`MemoryEvent.space` does; the rules that would consume them are §7.2's
`ConsistencyProfile`, which is M8's. `MemoryProfile.package` is not a gap either:
§10 names `VerifiedProgram` as what the package gates, and that composition is
outside this layer. `ProtocolAuthority.issuer` is already recorded in its own
docstring as M10 profile-closure work. `TerminalOutcome`'s fields await the
terminal-accounting mechanism, which is a later milestone.

That leaves `vocabularyVersion`, above, and the three device and retry fields
below — `AccessIntent.isDevice`, `AccessDescriptor.observations`, and
`Restartability` — which have a corpus requirement, no consumer, and no milestone
that owns them.

Limits, stated rather than discovered later. It cannot see a field consumed by
pattern matching rather than projection, so those are allowlisted structurally and
it under-reports. It says nothing about whether a field *should* be read — that is
what the allowlist reasons are for. And it was itself wrong on first run: an early
version treated a field docstring as the end of a structure, saw almost no fields,
and reported a clean tree. Probing it against a field already known to have no
reader is what caught that, which is why the self-test exists.

### 4.3 A semantic decision this milestone made and does not own

Two questions, both forced by fixing defects and neither answerable from the
corpus.

**First: when a denial stops an operation before the substep the machine reported
a fault at, is that fault recorded?**

M2 answers *no*, on the reasoning that a denied substep did not complete, the
model has declined to follow the execution past it, and attaching a fact about
substep *n* to a state frozen at substep *k < n* would be inventing history. The
opposite reading is arguable and was argued in review: a `RaisedFault` is
diagnostic rather than an effect, keeping it commits nothing, and `FaultPlan` is
documented as a fact the stepper is *given* rather than one it predicts, so
discarding it is the model overruling its own input.

**Second: what becomes of an obligation ledger effect when the access carrying it
faults?** [OBLIGATIONS.md](OBLIGATIONS.md) §1 makes cancellation and fault
behaviour part of an obligation's form and §2 requires a transition to state how
it transforms the ledger; neither says what a partial or zero-byte faulted access
does. The conservative answer differs by delta kind, which is why it cannot be
guessed: applying a `create` is conservative, because a spurious duty causes a
verification failure rather than an unsound accept, while applying a `discharge`
is a leak. M2 refuses instead — `StepRejection.faultWithUndeclaredLedgerEffect` —
because refusing is law 8's answer to a rule nobody wrote. That is strict: it
rejects operations a ruling might well admit.

This plan is tier four and cannot settle either. Both behaviours are implemented
and tested, §3.11 is stated to match, and both are provisional until
[MEMORY_MODEL.md](MEMORY_MODEL.md) §1, [OBLIGATIONS.md](OBLIGATIONS.md), or
[DECISIONS.md](DECISIONS.md) rules. Raised with the design owner rather than left
in code comments, which is where the first one sat when review found it.

Exit criteria: the M1 reference instruction set steps end to end over a
hand-built `MemState`; the framing lemma set is sufficient to discharge a
straight-line Spike 1 block without a bespoke local lemma; and the bridge lemma
above is proved.

Unblocks: the `verify_assembly` owner, and Spike 1 block certificates.

## 4.4 M3 begun: loans

`Grass/Memory/Loan.lean` implements the part of [MEMORY_MODEL.md](MEMORY_MODEL.md)
§3 that every later authority law rests on, and `Tests/Memory/Loans.lean` checks
it.

`AuthorityState` names **three and a half** of the five canonical states §3 lists.
Closing it as a sum is this module's decision and **not** §3's requirement: §3 says
the canonical states "include" these, which is an open enumeration, and an earlier
version of the code and of this paragraph claimed otherwise.

The closure is also **not** the safe direction, which the next sentence here used to
claim while citing [FOUNDATION.md](FOUNDATION.md) law 8 for it. `authorityOf` is a
total function into these four: a situation they do not describe is not rejected, it
is classified as the nearest one, and law 8 demands rejection. The closure is kept
because an open sum with a permissive default is worse and because extending means
editing the module in the open with the laws re-proved — not because it fails
loudly, which it does not. A new *kind* of authority remains a `GrantKind`, which is
open nominal so that is the usual road, and `grantsOver` sees every kind so that
road does not lead past the freeze.

The half is §3's fifth entry, "transferred **or** unavailable authority":
`unavailable` derives from liveness and epoch and covers the second half only.
Nothing represents a transfer, and §4.4.1 records it. The count was "four of five"
for one round, which read as coverage of a bullet half-delivered.

§3's third entry, atomic shared access under an ordering profile, is **not** named.
There was an `atomicShared` constructor and a theorem putting §3's "atomics do not
grant ordinary non-atomic access" beyond it, and nothing built the constructor:
`AuthorityGrant` carries `kind`, `holder`, `provenance`, `range` and `rights`, and
no ordering. The theorem held of an unreachable case, which reads as coverage
without being any. Both are deleted and §4.4.1 records the law as owed, with where
it could bite today — the earlier claim that "the rule has nothing to constrain" was
false, since `AccessIntent.isAtomic` and `OrderingDemand.atomicity` exist and
`WellFormedIn.atomicityAgrees` ties them.

Every remaining constructor is built by `authorityOf`: `sharedImmutable` and
`unavailable` were built by nothing, so every theorem about them was vacuous.
`authorityOf` derives all four from state that already exists — `unavailable` from
liveness and epoch, `exclusive` and `frozen` from the grant map, and
`sharedImmutable` from the rights on the outstanding grants, since §7.3 makes a
conflict require a writer and §3 lists shared immutable access separately. Nothing
*enforces* that every constructor stays reachable; four fixtures exhibit it and a
future author must extend them, which §4.4.1 records.

`PermitsIntent` is written out per constructor with no wildcard, so a fifth
constructor fails to compile there. `permitsOrdinaryWrite_iff_exclusive` does
**not** break under one — a wildcard would send the new case to `False` and the
equivalence would still hold — and this paragraph claimed it did.

Three laws are proved. A return consumes that exact identity, which
`returning_one_of_two_leaves_the_other` earns by returning one of two loans
identical in range, rights and holder — a map keyed by shape fails there and
nothing else in the fixture would notice. Exclusivity is the emptiness of the
relevant map, defined as that rather than checked against a stored number. And
counts are derived: `outstandingLoans` computes from the map and no field records
one, which is the discipline that removed `AllocationRecord.initialized` and
`AccessIntent.isDevice` after each turned out to be a second source of truth.

`authorityOf` is the freeze: while another context's write grant is outstanding the
lender holds `AuthorityState.frozen`, and
`not_permitsOrdinaryWrite_of_writableByAnother` is the borrow discipline that
follows. It too is a function of the state, so lending freezes, returning thaws,
freeing revokes and an epoch bump revokes, without a field to keep in step, and
`lending_the_head_leaves_the_tail_writable` shows the freeze is per-fragment rather
than per-allocation.

It takes the context, and an earlier version did not — a context that had lent to
itself was reported frozen while `Grass/Op/LoanAuthority.lean` let its write
through, which is the two halves of the model contradicting each other.

It reads **every kind of grant**, not only loans. §7.3's conflict is about
authority, and filtering to `GrantKind.loan` meant a `.frame` grant — or one of a
kind a profile invented, which `GrantKind` is open nominal to allow — carried write
authority that froze nobody and conflicted with nothing (`a_frame_grant_freezes`).
`loansOver` is that list narrowed to loans, for §3's laws, which really are about
loans; `a_frame_grant_is_not_a_loan` is the two questions kept apart.

It reads the **epoch**. §2 says address reuse never revives old pointers, and
`Live` compared only the `live` flag, so a provenance minted before a
free-and-reallocate was reported exclusive over the storage that replaced it, with
an ordinary write permitted (`a_stale_provenance_is_unavailable`). The same
blindness ran the other way: a grant issued under a defunct epoch froze the live one
permanently. Both are now unreachable, because `MemoryState.allocate?` refuses the
reallocation that would produce the state — `reallocating_under_a_loan_is_refused`.

`Exclusive` is **not** authority, and `authorityOf` used to read it as though it
were: over the empty state, which has an empty loan map and no allocations, it
reported exclusive ownership to whoever asked. `AllocationRecord.live`'s own
docstring says a dead allocation authorizes nothing whatever provenance is
presented, so `Live` is now a conjunct of the exclusive case and
`a_freed_allocation_is_exclusive_and_unavailable` holds both halves side by side.
`permitsOrdinaryWrite_of_unheld` takes `¬ HeldByAnother` and not `Exclusive`, for
the same reason.

`loansOver` matches on `ByteRange.Meets`, not on `¬ Disjoint`. An empty range covers
no offset, so every range is `Disjoint` from one — and asking what authority the
owner held over offset 4 while `[0, 8)` was lent for writing returned exclusive,
with an ordinary write permitted. §5.1 makes one-past-the-end and invalidated
offsets meaningful as positions, so a query about a position has to be answered
about one. `Meets` is asymmetric on purpose: the grant's range is the extent, the
query is the position, so a loan over no bytes still freezes nothing
(`a_grant_of_no_bytes_is_refused` (a zero-byte grant is refused at issue now, rather than issued and freezing nothing)) and one past the end of a loan is not frozen
(`one_past_the_end_of_a_loan_is_not_frozen`).

`MemoryState.issue?` refuses to *issue* conflicting authority — a reissued identity,
or a grant conflicting with a live one — and `LoanConflicts` is §7.3's test at issue
time. §7.3's rule is between *distinct* contexts, and a missing holder clause made a
second grant to the same holder a conflict, which is exactly the "declare a loan to
yourself" idiom `Grass/Op/LoanAuthority.lean` endorses; the clause is there now
(`a_second_loan_to_the_same_holder_is_accepted`).

Issuing is not the guarantee, and a comment here said it was. `MemoryState.grant`
installs a grant with no checks at all, and two grants that do not conflict when
issued become conflicting when an alias is declared afterwards — §7.5 makes that a
real transition and nothing re-examines what was already issued. Review reached both
states and watched the write commit with no violation recorded.

`Grass/Op/LoanAuthority.lean` is the rule as a provider a profile adopts rather
than reinvents, and it has two halves. Lent bytes are reachable only through a loan
— a holder test over the loan map. **And** the state `authorityOf` reports must
permit the intent, which is the half that reads the map it is handed rather than
trusting how the map was built, and which is what refuses both states above
(`the_conflicting_pair_cannot_be_issued`,
`an_alias_declared_after_issue_is_refused`).

The two halves are not the same test and neither implies the other. Refusal is
strictly wider than `frozen`: a context holding no covering loan is refused a read
of bytes another context holds only a read loan over, while `authorityOf` calls that
`sharedImmutable` and permits reads (`a_self_loan_bounds_its_holder`). An
earlier version of this section cited `loan_refuses_only_the_frozen` as the bridge
between the two; that theorem's statement mentioned neither `authorityOf` nor
`frozen`, its proof was a projection of the provider's own definition, and the
"exactly" was false in both directions. Three independent reviewers found it.
`loan_refuses_the_frozen` was the direction that carries the guarantee, stated — and
it is deleted with the provider it was about. The guarantee is `refusalOf`'s own
`authorityOf` clause now, and `refusalOf_refuses_the_unauthorized` is the theorem,
quantified over the policy.

`returnLoan?` refuses a return by a context that does not hold the loan. §3 says
which loan a return consumes, not who may return it, and the unchecked version let
any context return any loan and then write the thawed bytes — an authority check
defeated by calling the function that removes it
(`a_stranger_cannot_return_the_loan`).
`Tests/Op/StandardLoan.lean` drives it through `step`, which is the part that
matters — a rule proved about a map the transition does not consult is the defect
this branch has found repeatedly, so the fixture checks refusal and restoration
end to end rather than at the map.

Three of its cases exist because the obvious provider gets them wrong. A *read* of
lent bytes is refused, not only a write, since "lending stops the owner writing" is
the intuitive half and a provider enforcing only that would pass everything else.
Lending the tail leaves the head reachable, so the freeze is per-fragment rather
than per-allocation — without it, lending one field of a struct would lock the
struct. And an unlent store commits, so the refusals are not a provider that
refuses everything.

### 4.4.1 What M3 still owes

- ~~**Split and join of loans**, which §3 requires and which the identity discipline
  above is the foundation for.~~ Done. `MemoryState.splitGrant?` and
  `MemoryState.joinGrants?` are the doors, in the module that owns the map, and three
  decisions are worth recording.

  **Binary, at an offset, with the parts derived rather than supplied.** A
  list-of-parts door needs a predicate saying the parts cover the source's range and
  lie inside it, and this branch has learned what a satisfaction condition with room
  to be empty is worth — §10's proof package is closable by `True` eleven times. Two
  parts either side of an offset need no coverage check: coverage is arithmetic, and
  `AuthorityGrant.covered_by_part` is three lines of `omega`. An *n*-way split is
  *n* − 1 of these.

  **Neither door re-runs `issue?`, and a theorem says why that is safe.** Re-running
  it would refuse correct splits, because `MayLend`'s unheld disjunct is false once
  the source is outstanding and its lender-lends-again disjunct fails when the source
  coexists with another lender's grant over the same bytes. So the justification is
  `splitGrant?_creates_no_authority` and `joinGrants?_creates_no_authority` — the
  result authorizes nothing the sources did not — with
  `splitGrant?_preserves_authority` and the two `joinGrants?_preserves_*_authority`
  for the other direction. Every one is over an arbitrary state; the fixtures in
  `Tests/Memory/Loans.lean` are the concrete round trip.

  **The join compares whole grants.** `lowGrant = { highGrant with range := … }` is
  one `decide` over `DecidableEq`, so a field added to `AuthorityGrant` later is
  compared without this door being edited. A door listing the fields it cares about
  is precisely the shape that let `LedgerDelta.Applicable` relabel a duty: it pinned
  protocol and owner because those were the fields someone thought of. Adjacency is
  checked for the same reason — a gap would join authority over bytes neither source
  covered, and `joinGrants?_creates_no_authority` would be false without it.

  What is *not* stated is an `↔` between the two maps' `Granted`, because `Granted`
  ranges over the raw entry list and a map carrying a shadowed duplicate under the
  source's identity would lose that duplicate to the `erase`. No such map can be
  built, for the same privacy reason §4.4.1 records below for `Exclusive`, and that is
  again an invariant with no theorem. Both directions above hold of every map,
  shadowed or not.

  `Grass/Std/Logical/FiniteMap.lean` gained `mem_of_mem_eraseKey`,
  `mem_entries_insert` and `mem_entries_erase` for this: bounding a modified map's
  entry list from above is what a no-new-authority theorem needs, and without them
  the proof has to unfold the association list at the call site.
- **Lifetime and conditions on a grant.** §3's map carries them and
  `AuthorityGrant` does not. Adding fields nothing consults is the shape this layer
  has been bitten by three times, so they wait for M4's frames, where a bounded
  lifetime has something to mean.
- ~~**Atomic shared authority, and §3's rule that atomics do not grant ordinary
  non-atomic access.**~~ Closed, after two wrong turns worth recording.

  `AuthorityState.atomicShared (ordering : OrderingDemand)` and a theorem stating
  §3's rule about it existed, and nothing built the constructor, so the theorem held
  of an unreachable case. Both were deleted — right, because a vacuous theorem reads
  as coverage. The reasoning given for the deletion was wrong: it said the rule had
  nothing to constrain, and `Permission.Permits` is the sole rights gate on the
  chain `MemoryState.AuthorizedAt` → `MemoryState.Granted` → `refusalOf` → `step`,
  so the rule had a gate and no clause there. (This sentence named the deleted
  `Authorizes` function and `MemoryState.GrantedOfKind` until review checked the
  chain: the first is deleted and the second has no caller under `Grass/` at all —
  the transition's clause asks kind-blind `Granted`, deliberately, because *any*
  authority over the bytes freezes them and the kind distinction is a provider's
  business. `Grass/Memory/Rights.lean` had already been corrected; this had not.) `Permission.atomicOnly` is that clause, and `authorityOf` derives
  `atomicShared` from it. The constructor carries no ordering: that was a second
  place to say what `AccessDescriptor.ordering` says.

  The second wrong turn took minutes and is the reason to distrust a repair that
  builds. `WritableByAnother` probed `rights.Permits AccessIntent.write`, which an
  atomic-only grant fails, so a context updating a word atomically stopped freezing
  another context's ordinary write. §7.3's "at least one writer" asks who may change
  the bytes, so the probe is `rights.write`. A fixture written at the same time as
  the field caught it.

  §7.3's issuance sentence is "unique loans prevent **ordinary** conflicting
  authority from being issued", and `LoanConflicts` had no ordinary/atomic
  distinction, so `lend?` prevented all conflicting authority and two contexts could
  not share a word atomically at all. It exempts two atomic-only grants now, and
  only those.

  What remains owed is §3's second clause: atomics "must follow the ISA/platform
  ordering model". Nothing relates a grant to `AccessDescriptor.ordering`, and
  nothing here can — that needs §7.1's refinement theorem, which an ISA owner owes,
  and the strength relation M8's `ConsistencyProfile` induces.
- ~~**The transition reads the authority map and never writes it.**~~ Closed by
  `AuthorityDelta`, and this was the largest instance of this branch's own recurring
  defect: `issue?`, `returnGrant?`, `splitGrant?`, `joinGrants?` and `transferGrant?`
  were five checked doors whose only callers were fixtures, so every law proved about
  them was a law about a map no transition changed. §6's ABI call lends buffer and
  slot authorities and consumes the same identities on return, and §7.4's acquire
  operations transfer authority; both are things an *operation* does, and nothing an
  operation carried could do them.

  An `AccessDescriptor` now carries an `authorityEffect` beside its `ledgerEffect`,
  `refusalOf` refuses an access whose declared changes the map will not accept, and
  the committing branch applies them. `Tests/Op/FakeIsa.lean` steps five of them,
  including the pair that separates the two rules: the same `splitLoan` operation
  lands from a state where the acting context holds the grant and is refused from one
  where another context does.

  **One function, not a predicate and an applier.** `applyAuthorityEffect?` returns
  `Option`, and `refusalOf` decides applicability by running the very function the
  commit branch runs. The obligation ledger is the other shape —
  `LedgerDelta.Applicable` is a `Prop` and `applyDelta` is a separate function, with
  nothing tying them together — and two sources of truth is how a clause gets added
  to one and forgotten in the other. That is not hypothetical: `Applicable` was found
  missing a clause twice on this branch, the output `kind` and then the transfer
  destination, with `applyDelta` unaffected both times and neither miss caught by the
  shape.

  The ledger is unified now. `performAccess` installs `applyLedgerEffect?`'s result
  and the unconditional fold is deleted, so there is no longer a third description of
  what a delta does: `applyLedgerDelta?` gates `applyDelta` behind the very predicate
  `refusalOf` asks about, and `ledgerEffectApplicable_iff_isSome` says the two are the
  same rule. The `none` branch on the committing path is unreachable and recorded
  rather than fallen back from, exactly as the authority effect's is, with
  `ledger_effect_applies_when_nothing_refuses` as the proof.

  **Authority is not data**, which the transition's framing law needs: the effect is
  applied to the pre-access map and the bytes are written on top, so
  `allocations_applyAuthorityEffect?` and `cellAt?_applyAuthorityEffect?` are what
  keep `performAccess_frames_untouched` true. Every door changes `grants` and nothing
  else, and now there is a theorem saying so rather than an inspection.

  **The actor rules and the invariant checks are in different places**, because
  `issue?` reads the lender from the grant it is given and has no actor. "The acting
  context must be the lender it names" lives in `applyAuthorityDelta?`, as does "only
  the holder may split or join", so a caller reaching `issue?` directly can still
  name any lender: `MayLend` bounds what that named lender can lend, so nothing is
  conjured out of nothing, but one context could strip another's exclusivity by
  lending that other's bytes to itself.

  The commit that introduced this said the fix was an `actor` parameter on `issue?`
  and ninety-odd call sites, and that it was next. **That is wrong, and the reason is
  worth keeping.** A caller of `issue?` holds the grant, so it can satisfy
  `actor = grant.lender` by passing `grant.lender` — the parameter would be a gate
  the caller closes with the thing being gated, which is the empty-satisfaction-
  condition defect this document records against §10's proof package. An actor check
  has content only where the actor comes from somewhere the caller does not choose,
  and the only such place is the transition's `d.context`. That is where the check
  is. So the rule holds on every path an operation can take, and `issue?`'s
  unverified `lender` is a claim rather than a hole — a fixture asserting "I am
  lending as this context" while building a state, which is what a fixture is for.
  What was genuinely owed was narrower: nothing stopped a *future* non-fixture caller
  under `Grass/` from reaching a door outside an authority effect. `Tools/DoorAudit.py`
  is that guard — it fails on any application of one of the five doors from a
  `Grass/` module other than the two that own the map, and it does not scan `Tests/`,
  where calling a door directly is what a fixture is for. Negative-tested by adding a
  real call to `Grass/Op/LoanAuthority.lean` and watching it fail, not only by its
  own self-test.
- ~~**`GrantKind` is an open nominal name with no registry.**~~ Closed by
  `AdmittedVocabulary.grantKinds`, and the timing is the point: it did not matter
  while only a fixture could mint a grant, and it mattered the moment
  `AccessDescriptor.authorityEffect` let an *operation* mint one. Every other open
  nominal name in this layer that reached an operation acquired a registry — fault
  classes, allocation sources, provenance step kinds, obligation kinds, ordering
  modes and scopes, and three justification registries — and this is the same shape.

  What made it worth closing rather than recording is that `MemoryState.AnyGrantOver`
  is kind-blind: every rule that asks whether anything is held over some bytes counts
  a grant of any kind, so a grant of an invented kind freezes bytes while no
  provider's `GrantedOfKind` can ever match it. The rejection is `accessNotAdmitted`
  with `AdmissibilityFailure.grantKindNotRecognized`, before any question of whether
  the map would accept the lend, and `an_invented_grant_kind_is_refused` is it
  stepped, with a companion showing the declared kind runs.

  Two things this cost, recorded because they are the kind of thing that gets left
  out. Every profile must now declare its grant kinds, which is a breaking change to
  `AdmittedVocabulary` — both fixture profiles gained a line, and Spike 1's says
  `loan` only, because `frame` is M4's and its reference set models no frame grant.
  And appending a clause to `admissibilityFailures` cost one `Or.inl` in each of
  seven existing proofs, because the clause list is a left-associative `++` chain;
  that is a real maintenance tax on adding the *next* clause, and the honest fix is a
  `List (List AdmissibilityFailure)` joined once, which is not done here.
- ~~**Three of `AuthorityDelta`'s five constructors were declared and never
  built.**~~ `returnGrant`, `join` and `transfer` had no fixture two commits after
  the type arrived, and `Tools/ReachabilityAudit.py` was silent on all three: it is
  namespace-blind, so `LedgerDelta.join` and `LedgerDelta.transfer` satisfied two of
  them, and `transferredHead.returnGrant? owner firstLoan` reads as a construction of
  the third because the scan matches the name and not the `?`. Found by reading the
  commit rather than by a gate, which is what that tool's docstring says to expect.
  `Tests/Op/FakeIsa.lean` now steps all five, each with a refusal beside it.

  The same reading found that every new step fixture is of the form
  `∀ s, (step …).state? = some s → P s`, which `cases hs` closes vacuously when the
  step is *rejected* — a trap this branch fell into once already.
  `the_authority_effect_steps_run` asserts all eleven stepped states exist, which
  closes the class rather than one instance.
- ~~**§5's arena reset requires returning all live use loans, and there is no bulk
  operation.**~~ `MemoryState.tearDown?` is the bulk operation, and the reason it is
  one operation rather than a loop with a tidy name is the all-or-nothing fixture: a
  loan over the buffer refuses a teardown that names the scratch block *first*, and
  the scratch block is still live afterwards, because there is no afterwards. A
  hand-written walk over `allocate?` would have torn the scratch block down and then
  failed, leaving an arena half dead with no record that it had stopped.

  The grant check is `allocate?`'s, which is the point of routing through it: a
  teardown is a metadata change, so §5.1's precondition is the refusal it already
  was. `tearDown?_kills_every_name` is the law a walk could not state — not "each
  call succeeded" but "every allocation named is dead in the state that came out" —
  and it needed `allocate?_lookup_self`, `allocate?_lookup_ne` and
  `tearDown?_lookup_of_not_mem`, which are framing lemmas the layer lacked. An
  identity the table does not hold refuses the teardown rather than counting as
  already gone, and a repeated name is harmless.

  **What is still owed is the arena itself.** The list comes from the caller, so
  nothing knows it names *every* allocation of the arena being reset: a caller that
  forgets one tears down the rest and leaves it live, and this operation cannot tell.
  That needs an arena identity on `AllocationRecord`, and §5's model owes it. The
  bulk operation does not close that gap and does not claim to.
- ~~**Transferred authority.** §3's fifth entry is "transferred or unavailable";
  `unavailable` derives from liveness and epoch and nothing represents a transfer.
  §7.4 makes transfer real ("acquire operations may transfer protected memory
  authority") and M3's own scope table in §5 lists `transfer` as a loan-map
  operation.~~ `MemoryState.transferGrant?` is the door.

  **The identity is kept, unlike a split's**, because §6 has the lender consuming the
  identity it lent on a conforming return: a transfer that reissued under a fresh
  identity would strand the lender's return. `the_transfer_keeps_the_lender` checks
  the lender can still return it afterwards. A split consumes its source precisely
  because what comes out is not the same authority.

  **Only the holder may transfer**, which is what the `actor` parameter is for. The
  lender's power over an outstanding grant is `returnGrant?`; nothing in §3 or §6
  lets a lender redirect a live loan to a third party.

  **The conflict re-check is the clause with content.** `LoanConflicts` requires
  distinct holders, so one context may hold two write grants over the same bytes and
  `issue?` is right to accept the second — a context does not conflict with itself.
  Transfer either to a third context and that legal pair becomes a §7.3 conflict, so
  a door that only asked whether the actor held the grant would create one.
  `transferGrant?_leaves_no_conflict` is the guard read back out, and
  `transferring_into_a_conflict_is_refused` is the state, with a companion showing
  the same transfer out of a singly-held state is accepted.

  What this does *not* add is an `AuthorityState` constructor. "Transferred" is not a
  state of the bytes — after a transfer the bytes are lent exactly as before, to
  somebody else — and a constructor for it would be a second encoding of the holder
  field. `authorityOf` already answers "who holds this" from the map.
  `transferGrant?_creates_no_authority` says a context that is not the recipient
  gains nothing; it deliberately does not say the old holder *lost* the bytes, since
  it may hold other grants over them, and `Tests/Memory/Loans.lean` has the concrete
  case where it holds none and the authority really is gone.
- **`LoanConflicts` is a second encoding of §7.3.** `MemoryEvent.Conflicts` is §7.3's
  sentence with the atomic clause as a `compatible` parameter, and `step` consumes it
  through `ConflictsWithHistory`. Two Lean encodings of one corpus sentence in one
  layer is what [FOUNDATION.md](FOUNDATION.md) law 11 forbids. Stating `LoanConflicts`
  through `MemoryEvent.Conflicts` would fix this and give the atomic clause above a
  home in M3; it is not done, because the two currently differ in what they range
  over (grants versus events) and reconciling that is a design question.
- **"Registration is not discharge" is maintained in prose only.** Once
  `onFaultRuleNotRegistered` passes, `SubstepSequence.visibleEffects?` gives a
  `transactional` sequence full all-or-nothing semantics on the strength of a
  registered string, and `denialOf` skips `uninitializedRead` for any
  `permitsUninitialized _`. No type, predicate or theorem separates a claimed
  justification from a discharged one — §10's package is where discharge would live
  and nothing enumerates outstanding claims. `FaultVisibility.RequiresJustification`
  and `SubstepSequence.ClaimsAtomicity` exist for that enumeration and have no
  consumer under `Grass/`.
- ~~**Three admissibility failures report one rejection.**~~ Closed.
  `StepRejection.accessNotAdmitted` carries an `AdmittedVocabulary.AdmissibilityFailure`
  with ten distinct reasons, `Admits` is that failure list's emptiness so the two
  cannot drift, and `the_three_refusals_are_distinguishable` is the fixture the old
  shape could not have. This bullet stayed on the owed list for two commits after the
  work landed, which is the same failure as an overclaim pointing the other way.
- ~~**A context could lend bytes it neither held nor lent.**~~ Closed by
  `MemoryState.MayLend`, and worth recording because of how long it survived. `issue?`
  had grown seven checks — reissue, emptiness, liveness, nestedness, extent agreement,
  containment, conflict — and not one of them related the *lender* to the storage,
  while `LoanConflicts` requires distinct holders, so the first grant over any bytes
  conflicted with nothing. Review had one context issue itself a whole-buffer write
  loan over an allocation another exclusively owned: the owner went `frozen`, its
  counter-grant was refused as conflicting, it could not return a grant it neither held
  nor lent, and it could not free or re-epoch the allocation because a grant was
  outstanding. Permanent seizure, in one accepted call, and reachable through `step`.

  `MayLend` has three ways to be satisfied — nothing is held over the bytes, the
  lender holds covering authority that `Permission.Grants` what it is lending, or every
  grant over those bytes was lent by this lender — and each is a fixture in
  `Tests/Op/StandardLoan.lean`. The first is the one that still admits a claim: seizing
  bytes *nothing* is held over is indistinguishable from a legitimate owner's first
  loan, and stays so until `AllocationRecord` records an owner, which is the same gap
  the bullet below records from the other side.
- **Two live allocations may occupy the same machine address without being aliases.**
  `allocate?` refuses a metadata change under an outstanding grant and checks nothing
  about placement, and `AuthorizedAt` keys on `SharesBytes`, which is the declared
  alias relation and has no placement input. Review added a seventh allocation to the
  fixture state — same space, same extent, same `base := some 0x1000` as the buffer,
  no alias declared — gave the engine an exclusive write loan over the buffer, and
  proved all four of: the allocation is accepted; `addressAt?` agrees at offset 0 and
  at offset 63; `SharesBytes` is false; and the thread's write through the other
  identity is admitted, undenied, unrefused by the loan rule, with `authorityOf`
  reporting `exclusive`.

  Latent today, because only a fixture places allocations and M6 owns the allocator.
  Latent is how the grant doors were before `authorityEffect` gave an operation a way
  to reach them.

  The fix is not a check in `allocate?`: two live allocations at one base is exactly
  what an alias *is*, and the fixture state declares its alias after `allocateAll?`
  runs, so an allocation-time refusal would reject the model's own legitimate states.
  What is owed is a state-level coherence property — overlapping placement in one
  space implies a declared alias — asserted where a profile builds its allocation
  table, which is M6's shape rather than this milestone's.
- ~~**`MemoryState.alias` was an unchecked mutator outside every gate.**~~ It changes
  which allocations name the same bytes, which is an authority question — every rule
  in the layer keys on `SharesBytes` — and `Tools/DoorAudit.py`'s first version left
  it out. Review added a real definition calling it to `Grass/Op/LoanAuthority.lean`
  and the audit printed its green line. It is a door now, negative-tested the same
  way.

  It stays unchecked, and that is a decision rather than an omission. Declaring an
  alias can put two grants into conflict that did not conflict when issued, and the
  tempting fix is to refuse such an alias — which would be a lie in the other
  direction, because if the platform mapped two views of one file then the alias
  exists and a model that cannot record it cannot describe the machine. What makes
  the unchecked form safe is that both halves of §3's rule are asked at access time
  now, so in the conflicting state each holder is frozen by the other: the state is
  stuck rather than unsound.
- **§7.5's unmapping has no representation.** `alias` adds a pair and nothing removes
  one, so a mapping the platform tears down stays declared forever — and since the
  conflicting state above is *stuck*, an arena that is unmapped and remapped cannot
  recover the authority it had. M6 owns the allocator; this is owed with it.
- ~~**`MemoryProfile.Admits` was dead and wrong about itself.**~~ Deleted. Its
  docstring called it "deliberately not decidable" and the body was a list-emptiness
  test with a `Decidable` instance three definitions above — review wrote the instance
  in one line and decided a real case with it. It had no call site either: everything
  that checks admissibility goes through `AdmittedVocabulary.whyNotAdmitted?` or
  `StepPolicy.Admits`. Six docstrings across four modules named it as the thing that
  enforces a rule, which is the part that bites: a reader auditing "who checks the
  fault classes" was sent to a dead function that could drift from whatever actually
  checks them. All six now name `AdmittedVocabulary.Admits`.

  A `def` under `Grass/` that nothing uses falls between two gates —
  `Tools/FixtureAudit.py` scans `Tests/` only and `Tools/ReachabilityAudit.py` looks
  at inductive constructors — which is worth knowing and is not closed here.
- **`AddressSpace.owner` is carried and unread**, and its docstring claimed the owner
  is "part of the space's identity", which is false: `AddressSpaceTable.find?` matches
  on `id` and `WellFormed` requires the ids to be `Nodup`, so two externally owned
  buffers with different owners and one id are indistinguishable. Corrected in place.
  `Tools/ConsultedAudit.py` could not have found it — `owner` is projected freely as
  `Obligation.owner`, which is the same-name blind spot its own docstring documents.
  Kept rather than deleted because §7.5's distinction is real and a device authority
  will need it.
- **`AdmittedVocabulary.WellFormed` constrains the address-space table and nothing
  else.** Eleven registries, no coherence condition between them. The two
  justification registries are split so that one name cannot satisfy the other's
  claim, and nothing stops a well-formed vocabulary listing one name in both, which
  re-creates the collapse at the profile level. Minor — a profile listing a name in
  both is arguably making two honest claims — but it means the split is a convention
  rather than a guarantee.
- ~~**The loan rule was a provider a profile could decline to list.**~~ The largest
  finding of round ten, and the same shape as the round before it one level up.
  `StepPolicy.authorities` defaults to `[]`; the grant map was read by
  `AuthorityProvider.loan` and by nothing else — `denialOf` reads the allocation
  table and never `grants` — so a profile that declared no providers got no authority
  enforcement at all. Review took the fixture profile, changed that one field to the
  structure's own default, and stepped the fixture's own operations: `lendSlot` minted
  a grant *through `step`*, and the next ordinary store walked over it with an event
  minted, no violation, and the byte overwritten. Every law in
  `Grass/Memory/Loan.lean` was conditioned on a policy field a profile author gets
  wrong by writing nothing.

  §3's rule is `refusalOf`'s now, ahead of the provider search, so no provider list
  can remove it and a provider may only add its own refusals.
  `refusalOf_refuses_the_unauthorized` is the law and it quantifies over `policy`,
  which is the point; `refusalOf_allows_the_unheld` is the companion that stops it
  refusing everything. `Tests/Op/StandardLoan.lean` steps the whole path under a
  policy listing no providers at all: a store to lent bytes refused, a grant minted by
  one operation enforced against the next, and an unlent store still committing.

  **The first version of this fix carried only half the rule, and the commit message
  claimed it carried all of it.** It moved the holder question — is anything held
  here that you are not authorized for — and said `AuthorityProvider.loan` was now "a
  strict subset of the transition's own refusal". That was wrong, and the case that
  breaks it is one this document already describes: two grants that did not conflict
  when issued, made to conflict by an alias declared afterwards. In that state each
  holder is `Granted` by its own grant, so the holder clause passes for both. Only
  `authorityOf` sees the other holder, and it reports `frozen`. A probe written while
  closing the *next* finding stepped `aliasedAfterIssue` under a policy with no
  providers and watched the thread's write commit over bytes the engine held.

  Both halves are in `refusalOf` now, in the provider's own order, and
  `an_alias_declared_after_issue_is_refused_without_a_provider` is that state with the
  second half in place. The lesson is the one this branch keeps relearning: a repair
  that builds is not a repair, and a claim that one check subsumes another is a
  theorem, not an observation — stated as an observation, it was false within the
  hour.

  `AuthorityProvider.loan` is deleted, with `Grass/Op/LoanAuthority.lean`. Both its
  clauses were in `refusalOf` verbatim, which is two encodings of one rule and
  [FOUNDATION.md](FOUNDATION.md) law 11 forbids it; nineteen citations across eight
  files are repointed at `refusalOf`, and `Tests/Op/StandardLoan.lean` — which existed
  to drive the standard provider — now drives a policy with *no* providers, which is
  a better demonstration than the one it replaced: every theorem in it holds for a
  profile that asked for nothing.

  Its seven theorems went with it. They were about a provider's `refuses` returning
  `true`; what replaced them is `refusalOf_refuses_the_unauthorized`, which is
  quantified over the policy and so says something the seven could not.

  The deeper half of review's finding stands and is not closed: `AuthorityProvider` is
  `refuses : MachineState → AccessDescriptor → Bool` with no locality, monotonicity or
  soundness condition attached, and `StepPolicy` carries a proof obligation about a
  provider's *class* and none about its behaviour. A provider keyed on
  `state.events.length` is well formed. Making refusal monotone in the state, or
  local to the access, is a design question this branch has not answered.
- ~~**A faulting substep applied its whole authority effect.**~~ The first real
  soundness defect an adversarial round found in the authority-effect work, and it
  was a gate that was not extended rather than a rule nobody wrote.
  `StepRejection.faultWithUndeclaredLedgerEffect` refuses a fault on a substep
  carrying an obligation effect, because the corpus does not say what becomes of that
  effect; `AccessDescriptor.authorityEffect` arrived a milestone later and the gate
  beside it was not extended. `performAccess` applies the authority effect in full on
  the committing branch however little the access committed, so review drove a store
  that wrote *zero bytes* to lend the buffer's head to the device engine, a faulting
  return to consume its identity, and a faulting transfer to move a grant.
  `faultWithUndeclaredAuthorityEffect` is the second gate, a separate constructor
  rather than a rename because which effect was undeclared is the useful half of the
  report, and three fixtures step the lend, the return and the transfer.
- **The `refusalOf` clause for the authority effect is not what refuses.** Review
  deleted it and the whole build stayed green. Both paths refuse — `performAccess`'s
  "unreachable" branch records `authorityEffectRefused` and commits nothing — so this
  is not a hole, but the commit that introduced it framed the branch as the
  unreachable one and the clause as the gate, and that is backwards. What the clause
  buys is *ordering*: the class is recorded ahead of an `AuthorityProvider`'s and
  ahead of `ConflictsWithHistory`, which `refusalOf`'s own docstring promises
  ("the recorded class names the first thing that was wrong"). No fixture pins that
  ordering, and constructing one needs an access that fails two rules at once.

  What review's deletion did expose is real and is closed: the fallback branch sits
  outside `refusalOf_class_declared`'s reach, so nothing said the class it records is
  one the profile declared. `transition_own_classes_declared` says it for that class
  and for `wrongAddressSpace`. It does *not* say it for the third append site —
  `AccessOutcome.violation?` carries a class the profile's machine oracle chose, and
  nothing in this layer bounds it. That is an open gap and it is stated in the
  theorem's own docstring.
- ~~**The `.join` actor rule had no fixture.**~~ Removing "only the holder may join"
  from `applyAuthorityDelta?` left the whole build green, while its `.split` twin is
  caught immediately. `a_non_holder_may_not_join` is the fixture, and it is stated on
  the map rather than through `step` for a reason worth recording: the actor of an
  authority effect is the descriptor's context, and a descriptor whose context is not
  the stepping context is rejected by `contextMismatch` before the actor rule is
  reached. A fixture on this branch was once written that way and proved the wrong
  thing. The discriminating shape is a triple — the door accepts, the actor rule
  refuses, the holder succeeds — and `a_non_holder_may_not_split` and
  `the_forged_lend_is_refused_on_the_map` now have it too.
- ~~**`Tools/DoorAudit.py` did not guard the function its own failure message names.**~~
  The argument that an `actor` parameter on `issue?` is worthless applies verbatim to
  `applyAuthorityDelta?`'s `actor`, which is caller-chosen everywhere except the one
  `performAccess` site. Review added three real map-changing definitions to
  `Grass/Op/LoanAuthority.lean`, one routed through the applier, and the audit printed
  its green line. Both appliers are doors now, with the transition as an allowed
  caller.

  Four scanner defects came with it, each now covered by a seeded case: reports
  numbered the *stripped* source, so every line number from a real file was wrong;
  `unfold X at h` was reported as a call, which the docstring denied; a `|>` call and
  a call whose arguments wrap were both missed. And the first repair for the third
  introduced a fifth — matching a naming tactic anywhere on the line let an argument
  named `delta` silence a real call — caught by the self-test the same minute.
- ~~**Nothing said the authority map changes only by declaration.**~~
  `performAccess_preserves_authority_of_no_effect` and
  `runAccesses_preserves_authority_of_no_effects` say it, over an arbitrary policy,
  state, descriptor and outcome. [FOUNDATION.md](FOUNDATION.md) law 6 forbids ambient
  provider choice and this is the same reading applied to authority: a grant may not
  appear or disappear because an access happened, only because an access said it
  would. Every other fact about the authority effect was a point check through a
  fixture's `step`, which is exactly what `e-reviewer:18` asks reviewers not to accept
  as domain coverage.

  It needed `MemoryState.grantEntries_write` and `grantEntries_commit` — the other
  half of "authority is not data", since the committing branch applies the effect and
  then writes bytes on top.

  `runStep` is covered too, once the missing lemma was written. Its faulting branches
  run `SubstepSequence.visibleEffects?`, and nothing related a survivor list to the
  sequence's own accesses, so the hypothesis could not be discharged for the surviving
  prefix. `mem_accesses_of_mem_visibleEffects?` is that relation — both branches are
  `⊆`, since `priorEffectsVisible` takes a prefix and `transactional` takes nothing —
  and `mem_accesses_of_substep` is its companion for the faulting substep's own
  descriptor, which the branch that commits a partial write needs.
  `runStep_preserves_authority_of_no_effects` holds for every fault plan: no plan, a
  profile-owned visibility rule where the step does nothing, survivors that stop at a
  denial, and a faulting substep that commits.
- ~~**A fixture could outlive the claim it was built for.**~~ `Tools/FixtureAudit.py`
  is the eighth gate, over the one place `ConsultedAudit.py` and
  `ReachabilityAudit.py` do not look: a `def` under `Tests/` that nothing uses. Two
  existed — `lentThenReused`, a state built by reallocating under an outstanding loan
  from before that reallocation was refused, whose `.getD` silently returned the
  *unreallocated* state; and `currentProv` from the same commit. Both are deleted.

  Its `ALLOWED` list has two entries and they are the interesting part:
  `Tests/Foundation.lean`'s `aliasedVerified` and `inferredVerified` are consumed by
  an environment-walking audit rather than by name, so no lexical scan can see their
  consumer.
- **`denialOf`'s `Permits` clause is unreachable for every page this layer can
  describe.** The clause rejects an access whose intent the *page's* permission does
  not permit, and it sits behind the `Grants` clause, which rejects an access whose
  declared permission the page does not grant. `AccessDescriptor.WellFormedIn` already
  requires the descriptor's declared permission to permit its own intent, so a
  descriptor reaching the `Permits` clause has a permission the page grants and which
  permits the intent — and `Permission.permits_of_grants_of_permits` is that
  implication, proved. The clause is retained because it is the sentence §1 states and
  because `Grants` is the newer of the two, but no fixture can distinguish it and none
  claims to.
- **`MemoryEvent.ofOutcome`'s space guard cannot fail from `step`.** `ofOutcome`
  refuses to mint an event whose `AddressSpace` disagrees with the descriptor's
  `provenance.space`, which is `ValidMemoryEvent.WellFormed`'s
  `spaceAgreesWithProvenance` at the door. `step` resolves the space *from* the
  provenance, so the two never disagree there, and the refusal is reachable only for a
  direct caller of `ofOutcome`. That makes the guard a door-check on an unreachable
  path rather than a demonstrated rejection, and it is the shape this branch has
  learned to distrust: a mismatch becomes a silent absence of an event rather than a
  violation. Making it a rejection means `runStep` distinguishing "no event because
  nothing to record" from "no event because minting failed", which is `Grass/Op/`
  work.
- ~~**The `AuthorizedAt` negatives yield no `¬ Granted`.**~~ Closed.
  `not_authorizedAt_of_other_holder` and its three siblings say a specific grant does
  not authorize a specific byte; `Granted` quantifies existentially over
  `grantEntries`, so refuting it needs every entry refuted, and nothing composed the
  two. `granted_of_covering` had the same shape from the other side: its
  `entry ∈ grantEntries` hypothesis was discharged by `decide` for a concrete map and
  by nothing for an abstract one, because `Grass/Std/Logical/FiniteMap.lean` had no
  lemma taking `lookup id = some v` to `(id, v) ∈ entries`. Every fixture in `Tests/`
  is concrete, which is exactly why the gap was invisible: the lemmas had a use, and it
  was the only one they had.

  `FiniteMap.mem_entries_of_lookup` is the missing step, `MemoryState.granted_of_grantAt`
  the bridge from an identity, and `MemoryState.not_granted_of_no_authorizing_entry`
  the composition of the negatives — whose `¬ range.IsEmpty` hypothesis is where
  `Granted`'s vacuity on an empty range becomes visible in a signature.
  `Tests/Memory/Loans.lean` states both over an arbitrary state with no `decide` in
  sight, since a fixture that could `decide` it would not be testing the bridge.
- **The lender of a read-only loan is refused the read of its own bytes.** The loan
  provider's holder half asks whether *anything* is held over the bytes, and if so
  requires the accessor to hold covering authority. `AllocationRecord` records no
  owner, so the lender and a context that never held anything are the same context to
  that rule. Permitting the lender permits the stranger, and permitting the stranger
  is how a context that was never let in joined an atomic protocol — review
  demonstrated two contexts atomically writing the same live bytes with one holding
  no grant. The over-refusal is the safe half of that trade and is recorded rather
  than argued away; closing it properly needs an owner, which §5's arena model owes.
- **An unplaced allocation opts out of the address check.** `denialOf` compares the
  declared address to the placement only when the allocation has a base, which is
  right for a logical address space — §7.5's SPIR-V `Private` storage class has no
  machine addresses — and wrong for an allocation in a numerically addressed space
  that simply forgot to say where it sits. `denialOf` reads the space's *identity*
  and not its representation, so it cannot tell the two apart; the check belongs
  where the `AddressSpace` is in hand.
- **`MemoryState.Granted` composes grants byte by byte, and nothing composes their
  *rights*.** A context holding a read grant and a write grant over the same byte is
  authorized for a read-modify-write only if one grant permits both. That is the safe
  direction and it is not stated anywhere.
- ~~**A stale-epoch grant freezes the next epoch's storage and only its holder or
  lender can clear it.**~~ Closed at the source. `MemoryState.allocate?` refuses to
  replace an existing record while any grant is outstanding over that storage, which
  is §5.1's "reallocation requires the return of all live use loans" as a refusal
  rather than a sentence. A fresh identity is always accepted, and so is re-writing a
  record with the metadata it already has, so an idempotent registration still works
  — `allocate?_isSome_of_same_metadata` is that.

  An earlier version of this refusal, and of this paragraph, limited it to an epoch
  change or a teardown and said in as many words that "a permission, liveness or
  placement change is not a reallocation". Review took the sentence at its word:
  narrowing the buffer's `extent` under a live grant left the grant's range outside
  the allocation it was issued against, and moving its `base` left the grant naming
  bytes that had moved — both while the holder kept authority the record no longer
  supported. Any metadata difference is now the refusal, because the property that
  matters is that the record a grant was checked against is still the record in the
  table, and `AllocationRecord.Metadata` is exactly the part `denialOf` reads.

  The state that skipping it produced was the one three rounds kept circling — a
  grant that freezes the storage that replaced it, authorizes nothing, and blocks a
  replacement grant — and removing the state is better than accommodating it.
- ~~**Nothing enforces that every `AuthorityState` constructor stays reachable.**~~
  Closed by `Tools/ReachabilityAudit.py`, which reports any inductive constructor
  nothing outside its own declaration appears to build. It is lexical, like the other
  three, and its docstring says what it cannot see — namespace-blind dot notation, a
  construction in dead code, a constructor produced by a generic function. On its
  first run it named ten deliberate cases, each now in an allowlist with the
  milestone that owes the builder: `EventKind.control`, the two terminal
  `Disposition` constructors §5 needs, and the seven resource-policy constructors
  built ahead of M7 and M9.

## 5. M3–M5 — The Spike 1 acceptance path

These three run in the order given and, together with M2, close everything
Spike 1 demands from this ownership area.

### M3 — Loans and authority

```text
Grass/Memory/Authority.lean  exclusive, shared immutable, atomic shared,
                             frozen fragment, transferred
Grass/Memory/Loan.lean       LoanId, LoanRecord, LoanMap, split/join/return/
                             transfer, exclusivity-iff-empty, derived counts
```

Counts are proved to be caches of the map, never the authority
([DECISIONS.md](DECISIONS.md) rejects "one sharing count without loan
identities"). Pinning, `OffsetRef`, and `RebaseMap` are deliberately **not**
here; they are M6, and no Spike 1 line depends on them landing early.

Unblocks: `Std.Owned` slice loans, and M4.

### M4 — Frames, calls, and the violation envelope

```text
Grass/Memory/Frame.lean       stack reservation provenance, frame create/destroy,
                              frame-loan resolution before destruction
Grass/Memory/CallFrame.lean   the reusable ABI call-framing theorem of §6: lend
                              exact slot authority, retain disjoint residual,
                              construct the pending frontier state and completion
                              obligation, and consume the same loan identities on
                              a conforming return
Grass/Memory/Violation.lean   ViolationReturnEnvelope: affine, indexed by call
                              occurrence, pre/post worlds, call ID, loan IDs, and
                              boundary-step witness
```

`Grass/Memory/CallFrame.lean` is generic; `Grass.ABI.Win64` instantiates it. That
split is the coordination point with the ABI agent: this plan owns the theorem
shape and the loan accounting, and the ABI agent owns shadow space, alignment,
nonvolatile register classes, and unwind correspondence.

The envelope is required by Spike 1's `@violation_edge(.excessWriteCount)` and
must be affine at the exact occurrence — equal request and result values at a
second call site cannot reconstruct it. Per [DECISIONS.md](DECISIONS.md) 35 it is
optional hardening, so the conforming theorem must not depend on it.

### M5 — Obligation ledger and terminal dispositions

```text
Grass/Obligation/Ledger.lean    the ledger and its transition law
Grass/Obligation/Contract.lean  allowed and forbidden sets on CFG block entry and
                                exit, and call/jump ledger compatibility
Grass/Obligation/Terminal.lean  the disposition-to-specification theorem
```

The terminal theorem is indexed by the specification and its result/observation
mapping ([OBLIGATIONS.md](OBLIGATIONS.md) §3): for every terminal execution it
connects the concrete final ledger and each disposition to the exact declared
success, failure, abort, or unknown result. A platform's permission to abandon
does not by itself prove the program reports abandonment, and successful exit
must not leave an external obligation in an abnormal disposition.

Exit criteria for M3–M5: Spike 1's handle acquisition, frame-slot lending across
`WriteFile`, partial-write loop, provider-violation edge, and `ExitProcess`
teardown adoption all typecheck against these modules, with no obligation
introduced or discharged outside a protocol theorem.

Unblocks: the `VerifiedProgram` owner, the `Platform.Win32` process-exit
contract, and Spike 1 end to end.

## 6. M6–M10 — Refinement stages

Each stage is gated by the acceptance fixture that first needs it, so nothing is
built speculatively and nothing arrives late.

### M6 — Allocation, arenas, epochs, rebasing (Spikes 2 and 3)

```text
Grass/Memory/Alloc.lean   allocator source profiles, generative freshness,
                          address reuse never revives a pointer
Grass/Memory/Arena.lean   arena ownership, child provenance, borrowed lifetime,
                          teardown requiring exclusive authority and returned
                          loans, destructor obligation processing, epoch advance
Grass/Memory/Rebase.lean  OffsetRef, RebaseMap, PinLoan, stable-address profiles
```

Sort needs allocation failure observable before any output byte (the
`sort.alloc.output` mutation). Gzip needs input-length-independent resident
memory and arena-held dictionary state (`gzip.rep.dictionary`).

### M7 — Resource algebra depth (Spike 4)

```text
Grass/Resource/Metric.lean    ResourceMetric: axis-indexed valuation with empty,
                              monotone, disjointUnion, attribution, affineTransfer
Grass/Resource/Credit.lean    AffineCreditToken, ProductCreditHolding,
                              ChannelCapacityLedger, capacity transition law
Grass/Resource/Budget.lean    SemanticBudget
Grass/Resource/Envelope.lean  ExecutionEnvelope, RealizesSemanticBudget
Grass/Resource/Framing.lean   unrelated-axis preservation, and independent
                              subsystem envelope replacement
```

`NetworkResourceState` and `NetworkResourceCertificate` belong to the process
agent ([PROCESS.md](PROCESS.md)); this plan supplies the algebra, metric, and
credit primitives they instantiate. The affine credit token is the mechanism that
makes `h2.credit.double` fail rather than silently double count, so it is not an
optional convenience.

The classification rule of [RESOURCES.md](RESOURCES.md) §3 is enforced
structurally: `Budget.lean` may not import `Envelope.lean`.

### M8 — Concurrency: event graphs and consistency (Spike 4)

```text
Grass/Memory/Graph.lean        sequenced-before, reads-from, modification order,
                               synchronizes-with, happens-before, dependency;
                               graph witness; monotone prefix extension; limits
Grass/Memory/Consistency.lean  the ConsistencyProfile predicate and the §7.2
                               well-formedness obligation list
Grass/Memory/Race.lean         conflict, race, race freedom from unique loans
Grass/Memory/Sync.lean         acquire/release authority and matched obligation,
                               spawn/join/detach, masking restoration, ranking
```

The load-bearing deliverable is the **coincidence theorem**: the degenerate
single-context profile admits exactly the executions M2's operational
`applyAccess` produces. Without it, every instruction model written between M2
and M8 is at risk; with it, M8 is additive. Infinite consistency is checked on
the limit graph, not inferred from individually plausible finite choices (§7.2).

Ownership is settled (§10): this plan owns the framework — the relations, the
graph witness and prefix/limit discipline, the §7.2 well-formedness obligation
list, the race definition, and the synchronization laws — and ISA and platform
agents own the instances. The x86-64 consistency predicate is the ISA agent's,
expressed over this vocabulary. The rule that keeps this honest is that a profile
supplies a predicate; it may not extend or reinterpret the common relations, per
[MEMORY_MODEL.md](MEMORY_MODEL.md) §7.1.

### M9 — Address spaces and devices (Spike 5)

Device and GPU agents as graph participants, noncoherent profiles requiring
explicit visibility operations, mapping/pinning/sharing/cache-maintenance/queue
ownership as typed transitions with obligations, and lawful heterogeneous bridge
composition (§7.5).

### M10 — Profile closure

Per-profile discharge of every field of `MemoryProfile` (§10) for the Win64
x86-64 profile: access-descriptor soundness, range/provenance and initialization
preservation, permission enforcement and fault fidelity, loan laws, consistency
well-formedness, race-freedom consequences, synchronization and obligation
transfer laws, allocator freshness and epoch invalidation, frame lifetime
preservation, ghost erasure preservation, and validation metadata. The profile is
not usable by `VerifiedProgram` until this closes for all of its admitted
operations.

Closure is incremental: each earlier milestone discharges the fields it can, and
M10 is the audit that no field is left open rather than one large final proof.

## 7. Anti-churn policy

Later milestones must not rewrite earlier ISA source. Four binding rules:

1. **Concurrency fields are populated from M1.** `ContextId`, atomicity,
   requested ordering, scope, address space, and memory type appear in
   `AccessDescriptor` and `MemoryEvent` before M2 reads any of them. Paying the
   field cost in M1 is cheaper than a repository-wide rewrite at M8.
2. **Extension is additive.** An ISA-facing record grows by adding a field with a
   default or by gaining a profile-supplied component. An existing field's type
   never changes. Foundational vocabularies are versioned (§9), and each
   `MemoryProfile` records its `MemoryVocabularyVersion`.
3. **Every deepening comes with a coincidence theorem.** M8 proves the trivial
   consistency profile agrees with M2; M6 proves the trivial single-allocation
   arena agrees with M2's flat store. A stage that cannot state its coincidence
   theorem is a redesign, not a refinement, and reopens review.
4. **Signature and implementation separation from the first module.** Per
   [OLEAN_SHARDING.md](OLEAN_SHARDING.md), consumers import exported theorems,
   not bodies. Framing and step lemmas are exported explicitly; nothing outside a
   module recovers a fact by unfolding `applyAccess`. This is what allows M2's
   implementation to be replaced without invalidating ISA certificates.

## 8. What ISA authors get, and when

| After | An ISA author can |
|---|---|
| M1 | write final instruction models with declared memory, event, fault, ordering, and obligation effects |
| M2 | step those models, and have straight-line block goals discharge from library lemmas |
| M3 | model instructions that lend or consume authority |
| M4 | model call and return instructions against the ABI framing theorem |
| M8 | write the x86-64 consistency predicate, and model atomics and fences |

Source written after M1 is expected to survive M2 through M10 unchanged, under
the §7 policy. Proofs about it are expected to be rebuilt.

## 9. Risks

1. **Seal sufficiency.** [MEMORY_MODEL.md](MEMORY_MODEL.md) §1 calls the access
   interface sealed. If the first genuinely awkward instruction cannot be
   expressed, M1 reopens and every downstream file rebuilds. Mitigation: before
   the M1 freeze, the ISA agent supplies a worst-case candidate list — at minimum
   repeated string operations, locked read-modify-write, an instruction with a
   divide fault between two memory effects, an implicit-stack operation, and a
   misaligned crossing access — and each is expressed as an M1 fixture. This is an
   explicit dependency on another agent, not an assumption.
2. **Monotone freshness.** Foundation law 22 requires identities fresh over a
   monotone history, including infinite executions. If Core supplies only a
   counter, this plan must build the history-indexed supply itself, which moves
   work into M0.
3. **Resource algebra placement.** Settled in §10: the algebra is built at a new
   `Grass/Resource/` root. The residual risk is procedural, not technical — the
   corresponding [MODULES.md](MODULES.md) edit is owned by another agent, and
   until it lands the tree and the normative module document disagree.
4. **`Std.Owned` boundary.** `Std.Owned` is the largest consumer of loans and is
   not owned here. If its author needs loan lemmas this plan did not anticipate,
   they are added here rather than reimplemented there
   ([STDLIB.md](STDLIB.md) §2 forbids a private ownership model). M3's exit
   criteria should be reviewed by that agent before M3 closes.
5. **M8 scope.** The event graph is the largest single body of work in this plan
   and the least constrained by an early fixture. If Spike 4 slips, M8 should
   still land its degenerate profile and coincidence theorem early, because that
   theorem is what protects everything written between M2 and M8.

## 10. Decisions and open items

Three boundary questions were referred to the repository owner and are settled.
They are recorded here because they are outside this plan's ownership, and each
carries a consequence for another agent:

1. **The generic resource algebra is built at a new `Grass/Resource/` root**,
   ordered between `Std.Logical` and `Semantics`. `Grass/Process/Resource/`
   remains the process agent's owned metrics and capacity credit and continues to
   sit above `Semantics`; it instantiates this root rather than duplicating it.
   Consequence: [MODULES.md](MODULES.md) needs a corresponding edit from its
   owner (risk 3).
2. **This plan takes temporary custody of the M0 layers if they are unclaimed**,
   under the limits in §2. Consequence: whichever agent later owns `Core` and
   `Std.Logical` inherits declarations it did not write, and should review them
   at the point of transfer.
3. **The `ConsistencyProfile` framework is owned here; ISA and platform agents
   own the instances.** Consequence: the ISA agent writes the x86-64 predicate
   over this vocabulary and does not define a competing event model (M8).

One item remains open, and it is the one worth the most care:

- the resource-class defect filed against the Semantics owner in
  [DEFECT_SEMANTICS_RESOURCE_CLASSES.md](DEFECT_SEMANTICS_RESOURCE_CLASSES.md);
- the reviewer identity that will take the M1 freeze under
  [AGENT_REVIEW.md](AGENT_REVIEW.md). The freeze is the highest-cost irreversible
  step in this plan, and §9 risk 1 makes its sufficiency a claim about
  instructions this agent does not own. It should not be self-reviewed.
