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

### 3.7 Freeze status: not yet

The M1 vocabulary is **not** frozen, and two rounds of adversarial review are the
reason. Recording why, because the freeze is the step this plan exists to get
right on the first try.

Round one found three type-level defects — an identity type colliding with Lean's
`Id` monad, a `BitVec 64` address falsified by Spike 5's own
`OpMemoryModel Logical GLSL450`, and an alignment predicate that accepted
everything at its default value. Round two, run with fresh context, found that
the sealed descriptor did not seal:

- a descriptor carried its own `AddressSpace`, so it could choose a
  representation that made its own alignment and range checks vacuous;
- nothing related `requiredPermission` to `intent`, so a store could declare it
  needed only read-only permission, and `Permission.Permits` was dead code;
- `alignment` and `requiresInitialized` had permissive defaults;
- a `div [mem]` could not be expressed at all, because its `#DE` is raised by a
  step that performs no access and a list of accesses had no index to name it;
- the audit violation ledger could be erased in one line, and the axiom audit had
  already stopped covering six modules.

All of those are closed, with negative fixtures for the ones that were
constructible. The lesson worth carrying is narrower than "review works": in
every case the docstring already asserted the property. Prose describing a
mechanism is not the mechanism, and the reviews found the gap by executing rather
than reading.

A third round, again with fresh context, confirmed the round-two fixes that were
checkable by execution and refuted two of them, plus found holes neither earlier
round reached. Closed since:

- **An empty provenance path made every range condition vacuous.** A sixteen-
  exabyte write was well formed against the honest 64-bit CPU space, because
  `Provenance.extent?` was `none` for a path-free provenance and the condition was
  stated over the `Option`. Provenance now carries a `rootExtent`, `extent` is
  total, and the condition is unconditional.
- **The corpus's own `WebServerResources` sketch does not elaborate.**
  [SEMANTICS.md](SEMANTICS.md) writes it as
  `extends HasResourceLimit R .residentBytes, HasResourceLimit R .connections, …`;
  Lean deduplicates parent structures by head constant, so every axis after the
  first is silently dropped — and under `warningAsError` it is a hard error. A
  multi-axis specification now holds `ResourceLimit R axis` values as fields. This
  is a finding about the specification, not only about this implementation, and
  the Semantics owner needs it.
- **The resource laws admitted `max`.** Commutativity, associativity, identity,
  monotonicity and the order laws are all satisfied by an algebra reporting that
  one socket combined with one socket is one socket — a double count running in
  the under-counting direction. `combineCancel` and `combineEqLeft` rule it out,
  and `max` now fails them by construction.
- **The audit ledger's append-only claim was still false**, and cannot be made
  true of the type: `records?` reads the list out and `append` folds it back in,
  so a laundered ledger is three lines. The property belongs to the transition
  relation, not the type. `Extends` states it and M2's step relation owes the
  proof; the docstring now says so instead of claiming a guarantee it cannot give.

Gaps that remain open, and must be closed or accepted before the freeze:

- **`WellFormedIn d space` takes the space as a free parameter**, so it can be
  applied to a fabricated space. The real seal is at `Substep.WellFormedIn` and
  `AdmittedVocabulary.Admits`, which resolve through a table — but
  `AdmittedVocabulary` and `MemoryProfile` still have no well-formedness of their
  own, so a vocabulary can declare one id twice with different representations.
  `AddressSpaceTable.WellFormed` now exists; requiring it is not yet wired.
- **The facet seam is unwired.** `OperationFacets.Closes` and
  `MemoryProfile.requiredFacets` have no consumer, `MemoryProfile` is not
  parameterized by the operation type, and an ISA author cannot register anything
  with a profile today.
- **`LedgerEffect.WellFormed` is enforced nowhere**, so the split/join laws have
  no consumer.
- **Two registries are dead and five open-name axes have none.**
  `obligationKinds` and `auditViolationClasses` are never consulted, and the
  `profileSpecific` cases of ordering, scope, restartability and fault visibility,
  plus `ObservationLabel`, have no registry at all.
- **`Conflicts` requires `SameStorage`**, which excludes aliased mappings — a
  host-visible device buffer and a file view over the same bytes are declared
  non-conflicting.
- **A faulted read-modify-write cannot record the read it performed**, because
  read and write share one committed count.
- **`Address.symbolic` is an atom, not an expression**; **the descriptor carries
  no values**, so `lock cmpxchg16b` cannot declare its operands; **`WellFormedIn`
  is not decidable**; **`ObligationPayload` is write-only**; and **the descriptor
  carries no `ContextKind`** though §7.1 requires identity *and* kind.

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

Exit criteria: the M1 reference instruction set steps end to end over a
hand-built `MemState`; the framing lemma set is sufficient to discharge a
straight-line Spike 1 block without a bespoke local lemma; and the bridge lemma
above is proved.

Unblocks: the `verify_assembly` owner, and Spike 1 block certificates.

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

- the reviewer identity that will take the M1 freeze under
  [AGENT_REVIEW.md](AGENT_REVIEW.md). The freeze is the highest-cost irreversible
  step in this plan, and §9 risk 1 makes its sufficiency a claim about
  instructions this agent does not own. It should not be self-reviewed.
