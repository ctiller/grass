# Historical memory vocabulary assessment

This is a retained implementation assessment from before the spike-first reset.
Its tables preserve concrete compatibility concerns and proof debts for review
when the active spike reaches them. They are not a current freeze, work assignment,
or certification that every description still matches the tree. Internal
interfaces may be rebuilt to meet the reviewed spike, with explicit treatment of
consumers and proof dependencies.

The former memory implementation plan and its numbered sections are available in
Git history. References below to its milestones or review rounds are historical.
The named Python audits below are not available current checks; use the actual
commands in CONTRIBUTING.md and inspect the relevant declarations. Status claims
must be revalidated against code before using them as evidence.

This note cannot override FOUNDATION.md, MEMORY_MODEL.md, or DECISIONS.md.

## Previously assessed stable shapes


### Identity and naming

| Declaration | Shape | Note |
|---|---|---|
| `AllocId`, `EpochId`, `GrantId`, `EventId` | `Uid` over a phantom tag | A supply never reissues. `DECISIONS.md` rejects sharing counts without loan identities, and this is why the map is keyed by identity. |
| `AllocationSourceId`, `ProvenanceStepKind`, `FaultClassId`, `AuditViolationClass`, `MemoryTypeId`, `AddressSpaceId`, `GrantKind`, `ObservationLabel` | one `Name` field | Open nominal by design: a profile adds its own without editing this layer. Each has a registry in `AdmittedVocabulary` that must recognise it. |
| `NameRegistry`, `Recognized` | `recognized : List α`, and a bundled proof | The registry pattern the open nominal identities are checked against. |

### Ranges, bytes, addresses

| Declaration | Shape | Note |
|---|---|---|
| `ByteRange` | `start`, `size` | Offsets, not addresses. `Meets` was added; the two fields are frozen. |
| `ByteStore` | private `runs` | A journal. The representation is *private* and consumers reason through `cellAt?`; the module comment records honestly that `ByteStore.rec` defeats the seal for structural observation. |
| `MachineAddress` | `BitVec 64` | Frozen for the CPU profiles this project targets. A profile with a different address width is not expressible; §9's risk list does not name one. |
| `Address` | `numeric`, `symbolic` | Both constructors are load-bearing: `AddressRepr.symbolic` exists for SPIR-V's Logical addressing, where an allocation has no machine address at all. |
| `AddressRepr`, `Coherence` | as declared | Vocabulary `MEMORY_MODEL.md` §7.5 fixes. |

### Access and permission

| Declaration | Shape | Note |
|---|---|---|
| `AccessIntent` | `reads`, `writes`, `executes`, `isAtomic` | `isDevice` was removed: it was two facts in one `Bool`, both already carried by `ExecutionContext.kind` and `AddressSpaceId`. |
| `Permission` | `read`, `write`, `execute`, `atomicOnly` | `atomicOnly` was added to give §3's "atomics do not grant ordinary non-atomic access" a gate; it narrows a *grant* and a page never sets it. |
| `AccessDescriptor` | as declared | Every field group `MEMORY_MODEL.md` §1 names. Frozen since M1 and unchanged by six review rounds, which is the evidence the seam is right. |
| `AccessDescriptor.WellFormedIn` | as declared | Gained `rangeNonEmpty`. A clause added here is not a churn cost to a consumer, since the structure is a proof bundle. |
| `InitializationDemand` | `allBytesInitialized`, `permitsUninitialized`, `readsNothing` | See *provisional* — the demand is per access and §4 asks for per-byte granularity. |

### Provenance

| Declaration | Shape | Note |
|---|---|---|
| `Provenance` | `space`, `root`, `epoch`, `source`, `rootExtent`, `path` | §2's "provenance, not address, authorizes". `rootExtent` is now compared to the allocation table by `denialOf`. |
| `ProvenanceStep` | `kind`, `label`, `extent` | |
| `PointerValue` | `address`, `provenance` | A pointer cannot be manufactured from an address: constructing one demands the provenance. |

### State

| Declaration | Shape | Note |
|---|---|---|
| `AllocationRecord` | `extent`, `epoch`, `space`, `source`, `owners`, `permission`, `live`, `bytes`, `base` | `initialized` was removed as a second source of truth. `base` is an `Option` because a logical address space has unplaced allocations. This row omitted `source` and `owners`, both load-bearing: `source` feeds `provenanceSourceMismatch` and `owners` feeds `refusalOf`'s owner exemption. |
| `AllocationRecord.Metadata` | the seven fields a decision reads | Kept in step with what `denialOf` reads; `base` joined it when the address check landed. |
| `MemoryState` | `allocations`, `aliases`, private `grants` | The constructor and the grant field are private. Five doors change the grant map -- `issue?`, `returnGrant?`, `splitGrant?`, `joinGrants?`, `transferGrant?` -- and the historical door audit was intended to check that no other path did. |
| `MachineState` | as declared | |
| `AuditViolation`, `AuditViolationLedger` | as declared | The ledger's records are private; `records?` is the read view. |

### Substeps, faults, events

| Declaration | Shape | Note |
|---|---|---|
| `Substep`, `SubstepSequence` | `access`/`compute`; `substeps`, `onFault` | The commit-prefix model §1 requires. |
| `FaultVisibility` | `priorEffectsVisible`, `transactional`, `profileSpecific` | See *provisional*: the profile-specific rule is a name with no way to say what it means. |
| `AccessStatus`, `Restartability` | as declared | `Restartability` is declared and read by nothing; recorded in plan §4.2. |
| `MemoryEvent`, `ValidMemoryEvent`, `EventCause`, `EventKind` | as declared | §7.1's event vocabulary. `ValidMemoryEvent.mk` is sealed so a malformed trace is unrepresentable. |
| `Committed`, `CompleteCommitted`, `AccessOutcome` | as declared | `CompleteCommitted` exists so an oracle cannot silently short-commit. |

### Authority

| Declaration | Shape | Note |
|---|---|---|
| `AuthorityGrant` | `kind`, `holder`, `lender`, `provenance`, `range`, `rights` | `lender` was added for §6's conforming return. Lifetime and conditions are **not** here — see *provisional*. |
| `AuthorityState` | `exclusive`, `atomicShared`, `sharedImmutable`, `frozen`, `unavailable` | A closed sum over §3's open list. Closing it is this module's decision, and §4.4.1 records that it is not the safe direction — `authorityOf` is total and classifies rather than rejects. |

### Profile

| Declaration | Shape | Note |
|---|---|---|
| `AdmittedVocabulary` | thirteen registries plus the address-space table | See *provisional*: registries have been added five times and will be again. |
| `AdmissibilityFailure` | twelve constructors | Tracks `admissibilityFailures` exactly; a clause can only be added in one place, because `Admits` is that list's emptiness. |
| `MemoryProfile`, `RequiredProofPackage` | as declared | §10's eleven items, as fields. The package is a checklist of propositions, not evidence for them. |

### Shapes

| Declaration | Shape | Note |
|---|---|---|
| `FieldFootprint`, `Footprint` | as declared | The byte-side half of layout. The type-side half is `Std.Owned`'s and does not exist. |

---

## Provisional

| Declaration | What is expected to change | Owner / milestone |
|---|---|---|
| `ByteSeq` | Still `List Byte`. `Vec` has landed, so this is due rather than waiting; `c-stdlib:97` measures the siting cost as one import line in five modules, and reports the abbrev does not have to move down after all. Recorded since M1. | stdlib owner |
| `AddressSpace` | Gains fields as device and GPU profiles arrive. | M9 |
| `AdmittedVocabulary` | Gains a registry whenever a new open nominal identity is introduced, and has five times already: ordering modes, ordering scopes, and three justification registries. A profile constructing one positionally will break. | this layer, ongoing |
| `AuthorityGrant` | Gains `lifetime` and `conditions`, which §3's map carries and this does not. Deliberately deferred: a field nothing consults is the defect this layer has removed three times, and a bounded lifetime has something to mean once frames exist. | M4 |
| `AuthorityState` | May gain a constructor if §3's open list grows, and `authorityOf` must build it — the historical reachability audit was intended to check this. | this layer |
| `FaultVisibility.profileSpecific` | The registry holds a *name* and `visibleEffects?` still refuses to guess, so registering a rule unblocks only the non-faulting path. The registry must eventually map a name to a survivor rule. | this layer, recorded in §4.2 |
| `InitializationDemand` | Per access, where §4 asks for granularity "required to justify every read". A struct copy with padding must currently turn the check off for the whole range. | this layer, recorded in §4.2 |
| `OperationFacets.ordering` (in `Grass/Op/`) | Single-valued, so an operation whose substeps differ in ordering cannot say so. | this layer, recorded in §4.2 |
| `MemoryState.aliases` | Records no offset mapping, and `MemoryState.write` does not propagate across it — so `SharesBytes` is an authority-level fact with no byte-level counterpart. §4.2 names the two shapes that would close it and says neither should be taken without the design owner. | design decision, open |
| `Grass/Resource/*` | Built ahead of its consumers. Ten constructors and nine fields are declared and unbuilt or unread, each recorded in the two audits' allowlists. | M7, M9 |

---

## What this note does not certify

M1's other exit criteria are separate. `Tests/Memory/RiskOneCases.lean` now has the
two §9 risk 1 fixtures that were missing, and both are expressible — but writing them
found two things the shapes above cannot say, recorded in §4.2: `rep movsb` is a
*family* of descriptors rather than one, so proofs about it are inductions rather than
`decide`s; and `lock cmpxchg16b` cannot declare that its write is conditional, so a
failed compare-and-swap is described as a write.

What remains is the ISA agent's review of the freeze against that list, which is that
agent's and has not happened. So the shapes above are stable *in practice* — seven
adversarial review rounds moved mechanism and not fields — and are not yet frozen *by
the process §3 describes*.
