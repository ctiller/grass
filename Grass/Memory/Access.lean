import Grass.Core.Context
import Grass.Memory.AddressSpace
import Grass.Memory.Audit
import Grass.Memory.Fault
import Grass.Memory.Ordering
import Grass.Memory.Provenance
import Grass.Memory.Range
import Grass.Memory.Rights
import Grass.Obligation.Delta

/-!
# The access descriptor

`docs/MEMORY_MODEL.md` §1 makes this the sealed chokepoint: every
memory-affecting instruction, API, macro, loader, allocator, DMA or device
operation, and external call declares its memory events here, and raw mutation
outside this interface is prohibited.

`AccessDescriptor` carries exactly the nine field groups §1 enumerates. Three
choices in it are worth stating, because they are the ones a later milestone
would otherwise force an ISA author to revisit.

**The concurrency fields are present now.** `context`, `ordering`, and the
address space's memory type are declared by every access, including the ordinary
single-threaded ones that milestone M2's semantics will not read. Milestone M8
introduces the event graph that does read them. Populating them from the start
is the anti-churn rule in `docs/MEMORY_IMPLEMENTATION_PLAN.md` §7: an instruction
model written today should survive M8 unchanged.

**Initialization is declared in both directions.** §4 requires reads to be
justified and requires a write to initialize "only the bytes it actually
completes". A descriptor therefore states what it needs initialized and what it
leaves initialized, and the second is a claim about the *committed* bytes, not
about the range it named.

**Denial is not a fault.** §1 distinguishes an authority or audit check, which
happens before the substep commits and preserves the prior state, from an
architectural fault, which is modelled behavior with its own committed prefix.
`AccessResult` keeps them apart, and there is no constructor that lets a denial
report committed bytes.

This module is vocabulary. `applyAccess`, the state it runs over, and the framing
lemmas are M2.
-/

namespace Grass.Memory

open Grass.Core Grass.Obligation

/--
The identity of an observation an access may emit.

`docs/SEMANTICS.md` §3 owns the observation trace and the projection that selects
from it; an access only declares which labels it emits. The label is nominal so a
specification can select on it without this module knowing the specification.
-/
structure ObservationLabel where
  /-- The label's nominal name. -/
  name : Name
deriving DecidableEq, Repr

/--
What an access demands of the initialization of the bytes it reads.

`docs/MEMORY_MODEL.md` §4: "Initialization is tracked at the granularity required
to justify every read." The demand is therefore total and has no default. A
`Bool` defaulting to `false` would mean a forgotten field silently authorized an
uninitialized read, which is the permissive default law 8 forbids in the one
place it costs most.

`permitsUninitialized` exists because §4 also requires typed shapes to "expand
soundly for partial access, padding, unions, serialization, or external writes".
A typed copy that moves padding is a real case. It carries the name of what
justifies it, so the exception is cited rather than assumed.
-/
inductive InitializationDemand where
  /-- Every byte read must already be initialized. -/
  | allBytesInitialized
  /-- Some bytes read may be uninitialized, justified by the named rule. -/
  | permitsUninitialized (justification : Name)
  /-- The access reads nothing, so it demands nothing. Distinct from
  `permitsUninitialized`: a write-only store is not an access that tolerates
  uninitialized bytes, it is one with no reads to justify. -/
  | readsNothing
deriving DecidableEq, Repr

/--
One declared memory access.

Every field group of `docs/MEMORY_MODEL.md` §1 is present: address and range,
intent, provenance and bounds, initialization required and produced, permission
and alignment, atomicity and ordering, context identity, admitted faults and
partial completion, and observation and obligation effects.
-/
structure AccessDescriptor where
  /-- The context performing the access. -/
  context : ContextId
  /-- The computed address of the first byte. Numeric or symbolic according to
  the space; see `Grass/Memory/AddressSpace.lean`. -/
  address : Address
  /-- The address space the access is performed in, by name. The properties of
  that space come from the profile's `AddressSpaceTable`, not from here: an
  access that described its own space could switch off its own guards. -/
  space : AddressSpaceId
  /-- The provenance the access must present to be authorized. -/
  provenance : Provenance
  /-- The byte range accessed, relative to the provenance's root allocation. -/
  range : ByteRange
  /-- What the access does to those bytes. -/
  intent : AccessIntent
  /-- The page or section permission the access requires. -/
  requiredPermission : Permission
  /-- The alignment the access requires of `address`. No default: `1` means "no
  demand" and would accept every address, which is the permissive default
  `docs/FOUNDATION.md` law 8 forbids. An access that genuinely has no alignment
  demand says `1` deliberately. -/
  alignment : Nat
  /-- What this access demands of the initialization of the bytes it reads. No
  default, for the same reason. -/
  initialization : InitializationDemand
  /-- Whether the committed bytes are initialized afterwards. -/
  producesInitialized : Bool := false
  /-- The atomicity, ordering, and scope the access requests. -/
  ordering : OrderingDemand := .plain
  /-- The architectural faults this access may raise. A fault outside this list
  is a model discrepancy, not an admitted outcome. -/
  admittedFaults : List FaultClassId := []
  /-- Whether the access may be restarted after interruption. -/
  restartability : Restartability := .notRestartable
  /-- The observations this access emits. -/
  observations : List ObservationLabel := []
  /-- How this access changes the obligation ledger. -/
  ledgerEffect : LedgerEffect := []
deriving DecidableEq, Repr

namespace AccessDescriptor

/--
`d.AlignmentSatisfied` holds when a numeric address meets the declared alignment.

Written as a match rather than a guarded universal so that it is decidable. A
symbolic address has no numeric value to align; SPIR-V alignment is a property of
types, and a profile that needs it states it there.
-/
def AlignmentSatisfied (d : AccessDescriptor) : Prop :=
  match d.address with
  | .numeric value => IsAligned value.toNat d.alignment
  | .symbolic _ => True

instance (d : AccessDescriptor) : Decidable d.AlignmentSatisfied := by
  unfold AlignmentSatisfied; split <;> infer_instance

/--
`d.RangeFitsSpace space` holds when a numerically addressed access does not name a
range wider than its space.

This is what rules out a `Nat` range whose machine addresses would wrap and alias
a disjoint one; see the module comment in `Grass/Memory/Range.lean`. The tighter
bound, the allocation's own size, is a state fact and is checked by the transition
relation.
-/
def RangeFitsSpace (d : AccessDescriptor) (space : AddressSpace) : Prop :=
  match space.repr with
  | .numeric bits => d.range.WithinBound (2 ^ bits)
  | .symbolic => True

instance (d : AccessDescriptor) (space : AddressSpace) :
    Decidable (d.RangeFitsSpace space) := by
  unfold RangeFitsSpace; split <;> infer_instance

/--
The intrinsic well-formedness of a descriptor.

`space` is the resolved address space, obtained from a profile's
`AddressSpaceTable`. It is a parameter rather than a field of the descriptor
because a descriptor that carried its own space could pair the id `cpu.virtual`
with `repr := .symbolic` and make both the alignment and range-bound clauses
vacuous — every numeric guard would be optional in practice.

The remaining conditions are checkable from the descriptor alone. Whether the
provenance is live, whether the named bytes are actually initialized, and whether
the address really is the allocation base plus `range.start` are facts about a
memory state, and belong to M2's `applyAccess` rather than here.

Stated as a structure of named fields rather than a conjunction so that a failing
condition names itself, and so that the §10 profile package can cite conditions
individually.
-/
structure WellFormedIn (d : AccessDescriptor) (space : AddressSpace) : Prop where
  /-- The supplied space is the one the descriptor names. A caller obtains it by
  resolving `d.space` through a profile's table, and cannot substitute another. -/
  spaceResolved : space.id = d.space
  /-- An access that reads, writes, and executes nothing is not an access.
  `docs/FOUNDATION.md` law 8 forbids treating it as a harmless no-op. -/
  notInert : ¬ d.intent.IsInert
  /-- The declared space is realizable by this vocabulary version. -/
  spaceWellFormed : space.WellFormed
  /-- The address has the form the space's representation requires. A numeric
  address in a symbolic space, or the converse, is rejected rather than coerced. -/
  addressRepresentable : space.Representable d.address
  /-- The provenance belongs to the space the access names. Without this, an
  offset match across two address spaces could authorize an access
  (`docs/MEMORY_MODEL.md` §7.5). -/
  spaceAgrees : d.provenance.space = d.space
  /-- The provenance path is nested, so it designates something. -/
  provenanceNested : d.provenance.Nested
  /-- The accessed range lies inside what the provenance designates.

  Unconditional, because `Provenance.extent` is total. It used to be stated over
  an `Option` that was `none` for an empty path, which made it vacuous for every
  descriptor rooted directly in an allocation — a sixteen-exabyte write was well
  formed against the honest 64-bit CPU space. -/
  rangeInProvenance : d.provenance.extent.Contains d.range
  /-- A numeric address satisfies the declared alignment. A symbolic address has
  no numeric value to align; SPIR-V alignment is a property of types, and a
  profile that needs it states it there rather than here. -/
  aligned : d.AlignmentSatisfied
  /-- In a numerically addressed space the accessed range fits the space itself.
  This is what rules out a `Nat` range whose machine addresses would wrap and
  alias a disjoint one; see the module comment in `Grass/Memory/Range.lean`. The
  tighter bound, the allocation's own size, is a state fact and belongs to M2. -/
  rangeFitsSpace : d.RangeFitsSpace space
  /-- An atomic intent declares atomic ordering, and conversely. A `lock`-prefixed
  operation that declared `nonAtomic` would be checked by the wrong rules. -/
  atomicityAgrees : (d.intent.isAtomic = true) ↔ (d.ordering.atomicity = .atomic)
  /-- The access requires the permission its intent needs. Without this clause
  `Permission.Permits` is dead code and `docs/MEMORY_MODEL.md` §4's demand that
  read, write, and execute be distinct is unenforced: a write could declare it
  needs only read-only permission and be well formed. -/
  permissionSufficient : d.requiredPermission.Permits d.intent
  /-- An access reads exactly when it makes a demand about what it reads. A
  reading access must choose between requiring initialization and citing a
  justification for not requiring it; a non-reading one says `readsNothing`. -/
  initializationMatchesIntent :
    (d.intent.reads = true) ↔ (d.initialization ≠ .readsNothing)
  /-- Only an access that writes can produce initialization. -/
  producesInitializedOnlyIfWrites :
    d.producesInitialized = true → d.intent.writes = true

instance (d : AccessDescriptor) (space : AddressSpace) :
    Decidable (d.WellFormedIn space) :=
  if h : space.id = d.space ∧ ¬ d.intent.IsInert ∧ space.WellFormed ∧
      space.Representable d.address ∧ d.provenance.space = d.space ∧
      d.provenance.Nested ∧ d.provenance.extent.Contains d.range ∧
      d.AlignmentSatisfied ∧ d.RangeFitsSpace space ∧
      ((d.intent.isAtomic = true) ↔ (d.ordering.atomicity = .atomic)) ∧
      d.requiredPermission.Permits d.intent ∧
      ((d.intent.reads = true) ↔ (d.initialization ≠ .readsNothing)) ∧
      (d.producesInitialized = true → d.intent.writes = true) then
    .isTrue
      { spaceResolved := h.1, notInert := h.2.1, spaceWellFormed := h.2.2.1
        addressRepresentable := h.2.2.2.1, spaceAgrees := h.2.2.2.2.1
        provenanceNested := h.2.2.2.2.2.1, rangeInProvenance := h.2.2.2.2.2.2.1
        aligned := h.2.2.2.2.2.2.2.1, rangeFitsSpace := h.2.2.2.2.2.2.2.2.1
        atomicityAgrees := h.2.2.2.2.2.2.2.2.2.1
        permissionSufficient := h.2.2.2.2.2.2.2.2.2.2.1
        initializationMatchesIntent := h.2.2.2.2.2.2.2.2.2.2.2.1
        producesInitializedOnlyIfWrites := h.2.2.2.2.2.2.2.2.2.2.2.2 }
  else
    .isFalse fun w =>
      h ⟨w.spaceResolved, w.notInert, w.spaceWellFormed, w.addressRepresentable,
        w.spaceAgrees, w.provenanceNested, w.rangeInProvenance, w.aligned,
        w.rangeFitsSpace, w.atomicityAgrees, w.permissionSufficient,
        w.initializationMatchesIntent, w.producesInitializedOnlyIfWrites⟩

/-- A descriptor for an ordinary aligned single-context load. -/
def IsPlainRead (d : AccessDescriptor) : Prop :=
  d.intent = .read ∧ d.ordering.IsPlain

/-- A descriptor for an ordinary aligned single-context store. -/
def IsPlainWrite (d : AccessDescriptor) : Prop :=
  d.intent = .write ∧ d.ordering.IsPlain

/--
The bytes a given outcome commits, as a range.

`docs/MEMORY_MODEL.md` §4: "A write initializes only the bytes it actually
completes." The committed range is therefore a prefix of the named range, and
this is the function every initialization and framing argument goes through.
-/
def committedRange (d : AccessDescriptor) (status : AccessStatus) : ByteRange :=
  d.range.take (status.committedBytes d.range.size)

@[simp] theorem committedRange_completed (d : AccessDescriptor) :
    d.committedRange .completed = d.range := by
  simp [committedRange]

/--
The committed range never escapes the named range.

Unconditional, because `committedRange` saturates through `ByteRange.take`. Even
a status claiming more committed bytes than the access covered cannot describe an
effect outside the access's own range.
-/
theorem committedRange_contained (d : AccessDescriptor) (status : AccessStatus) :
    d.range.Contains (d.committedRange status) :=
  d.range.contains_take _

/-- For a well-formed status the committed range is exactly the claimed prefix,
with no saturation. -/
theorem committedRange_size (d : AccessDescriptor) {status : AccessStatus}
    (h : status.WellFormed d.range.size) :
    (d.committedRange status).size = status.committedBytes d.range.size := by
  rw [AccessStatus.WellFormed] at h
  simp [committedRange, Nat.min_eq_left h]

/-- A faulting access commits its declared prefix, which may be nonempty. Nothing
here permits a proof to assume a fault committed no bytes. -/
theorem committedRange_faulted (d : AccessDescriptor) (fault : FaultClassId)
    {committed : Nat} (h : committed ≤ d.range.size) :
    d.committedRange (.faulted fault committed) = ⟨d.range.start, committed⟩ := by
  simp [committedRange, AccessStatus.committedBytes, ByteRange.take, Nat.min_eq_left h]

end AccessDescriptor

/--
What happened when an access was attempted.

`performed` covers every modelled architectural outcome, including a fault with a
committed prefix. `denied` covers an authority or audit check that rejected the
access before it committed anything.

`docs/MEMORY_MODEL.md` §1 requires denial to preserve "the state immediately
before the denied substep", so `denied` carries no committed count. There is no
way to express a partially committed denial.
-/
inductive AccessResult where
  /-- The access was performed, with this architectural status. -/
  | performed (status : AccessStatus)
  /-- The access was denied before committing, and this violation was recorded. -/
  | denied (violation : AuditViolation)
deriving DecidableEq, Repr

namespace AccessResult

/-- `result.IsDenied` holds when an authority or audit check rejected the access. -/
def IsDenied : AccessResult → Prop
  | .denied _ => True
  | .performed _ => False

instance : (result : AccessResult) → Decidable result.IsDenied
  | .denied _ => .isTrue trivial
  | .performed _ => .isFalse (fun h => h)

/--
The bytes this result committed.

A denial commits nothing, by construction rather than by convention.
-/
def committedBytes : AccessResult → Nat → Nat
  | .performed status, size => status.committedBytes size
  | .denied _, _ => 0

@[simp] theorem committedBytes_denied (violation : AuditViolation) (size : Nat) :
    (AccessResult.denied violation).committedBytes size = 0 := rfl

/-- A denial commits nothing whatever the access named. This is the statement
that denial preserves the pre-substep state. -/
theorem committedBytes_eq_zero_of_isDenied {result : AccessResult}
    (h : result.IsDenied) (size : Nat) : result.committedBytes size = 0 := by
  cases result with
  | denied _ => rfl
  | performed _ => exact absurd h (fun h => h)

end AccessResult

end Grass.Memory
