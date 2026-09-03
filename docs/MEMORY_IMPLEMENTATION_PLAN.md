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
is optional because §7.5's logical spaces have allocations with no machine address,
and it is not authority: `denialOf` reads none of it, and two allocations sharing a
base are still distinct storage unless `aliases` says otherwise. It is conditioned on `FitsAllocation`:
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
- **`InitializationDemand.permitsUninitialized`'s justification names nothing**,
  like `FaultVisibility.transactional`'s, and unlike that one it was not recorded.
- **The operation-level `faults` facet is consumed by nothing.**
  `OperationFacets.supplied` reads only `isSome`, so an operation declaring
  `faults = some []` can still raise one. The substep-level lists are checked now;
  the operation-level declaration is not cross-checked against them.
- **Ordering modes are unchecked.** `MemoryOrder.IsPortable` and
  `MemoryScope.IsPortable` have no consumer, `AdmittedVocabulary` has no ordering
  registry, and an access declaring `profileSpecific` with an unregistered name
  steps and mints an event carrying it. [MEMORY_MODEL.md](MEMORY_MODEL.md) §7.1
  says unsupported mappings are rejected.
- **`FaultVisibility.transactional`'s `justification` names nothing.**
  `RequiresJustification` and `SubstepSequence.ClaimsAtomicity` exist so a §10
  package can enumerate outstanding claims, and nothing under `Grass/` consults
  either; no registry holds justification names. A sequence gets all-or-nothing
  fault semantics by declaring a string. `FaultVisibility.profileSpecific`'s name
  is likewise unchecked.
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

- Compaction for the byte store, per §4.1.

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

`AuthorityState` names the five canonical states §3 lists, closed because §3 names
them as the canonical list — a profile needing another does not add a constructor,
since `atomicShared` carries the profile's own ordering and a new *kind* of
authority is a `GrantKind`, which is open nominal so this does not have to be.
`PermitsOrdinaryWrite` holds only of `exclusive`, which puts §3's "atomics do not
grant ordinary non-atomic access" in a theorem.

Three laws are proved. A return consumes that exact identity, which
`returning_one_of_two_leaves_the_other` earns by returning one of two loans
identical in range, rights and holder — a map keyed by shape fails there and
nothing else in the fixture would notice. Exclusivity is the emptiness of the
relevant map, defined as that rather than checked against a stored number. And
counts are derived: `outstandingLoans` computes from the map and no field records
one, which is the discipline that removed `AllocationRecord.initialized` and
`AccessIntent.isDevice` after each turned out to be a second source of truth.

`ownerAuthority` is the freeze: an owner with a loan outstanding holds
`AuthorityState.frozen` and `not_permitsOrdinaryWrite_of_not_exclusive` is the
borrow discipline that follows. It too is a function of the map, so lending
freezes and returning thaws without a field to keep in step, and
`lending_the_head_leaves_the_tail_writable` shows the freeze is per-fragment rather
than per-allocation.

`Grass/Op/LoanAuthority.lean` is the rule as a provider a profile adopts rather
than reinvents: lent bytes are reachable only through a loan.
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

- **Split and join of loans**, which §3 requires and which the identity discipline
  above is the foundation for.
- **Lifetime and conditions on a grant.** §3's map carries them and
  `AuthorityGrant` does not. Adding fields nothing consults is the shape this layer
  has been bitten by three times, so they wait for M4's frames, where a bounded
  lifetime has something to mean.

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
