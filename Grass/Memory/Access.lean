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
One declared memory access.

Every field group of `docs/MEMORY_MODEL.md` §1 is present: address and range,
intent, provenance and bounds, initialization required and produced, permission
and alignment, atomicity and ordering, context identity, admitted faults and
partial completion, and observation and obligation effects.
-/
structure AccessDescriptor : Type 1 where
  /-- The context performing the access. -/
  context : ContextId
  /-- The computed address of the first byte. Numeric or symbolic according to
  the space; see `Grass/Memory/AddressSpace.lean`. -/
  address : Address
  /-- The address space the access is performed in. -/
  space : AddressSpace
  /-- The provenance the access must present to be authorized. -/
  provenance : Provenance
  /-- The byte range accessed, relative to the provenance's root allocation. -/
  range : ByteRange
  /-- What the access does to those bytes. -/
  intent : AccessIntent
  /-- The page or section permission the access requires. -/
  requiredPermission : Permission
  /-- The alignment the access requires of `address`; `1` demands nothing. -/
  alignment : Nat := 1
  /-- Whether the accessed bytes must already be initialized. -/
  requiresInitialized : Bool := false
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

namespace AccessDescriptor

/--
The intrinsic well-formedness of a descriptor.

These are the conditions checkable from the descriptor alone. Whether the
provenance is live, whether the named bytes are actually initialized, and whether
the address really is the allocation base plus `range.start` are facts about a
memory state, and belong to M2's `applyAccess` rather than here.

Stated as a structure of named fields rather than a conjunction so that a failing
condition names itself, and so that the §10 profile package can cite conditions
individually.
-/
structure WellFormed (d : AccessDescriptor) : Prop where
  /-- An access that reads, writes, and executes nothing is not an access.
  `docs/FOUNDATION.md` law 8 forbids treating it as a harmless no-op. -/
  notInert : ¬ d.intent.IsInert
  /-- The declared space is realizable by this vocabulary version. -/
  spaceWellFormed : d.space.WellFormed
  /-- The address has the form the space's representation requires. A numeric
  address in a symbolic space, or the converse, is rejected rather than coerced. -/
  addressRepresentable : d.space.Representable d.address
  /-- The provenance belongs to the space the access names. Without this, an
  offset match across two address spaces could authorize an access
  (`docs/MEMORY_MODEL.md` §7.5). -/
  spaceAgrees : d.provenance.space = d.space.id
  /-- The provenance path is nested, so it designates something. -/
  provenanceNested : d.provenance.Nested
  /-- The accessed range lies inside what the provenance designates. An empty
  path designates the whole root allocation, whose size is a state fact. -/
  rangeInProvenance :
    ∀ extent, d.provenance.extent? = some extent → extent.Contains d.range
  /-- A numeric address satisfies the declared alignment. A symbolic address has
  no numeric value to align; SPIR-V alignment is a property of types, and a
  profile that needs it states it there rather than here. -/
  aligned : ∀ value, d.address.value? = some value → IsAligned value.toNat d.alignment
  /-- In a numerically addressed space the accessed range fits the space itself.
  This is what rules out a `Nat` range whose machine addresses would wrap and
  alias a disjoint one; see the module comment in `Grass/Memory/Range.lean`. The
  tighter bound, the allocation's own size, is a state fact and belongs to M2. -/
  rangeFitsSpace :
    ∀ bits, d.space.repr = .numeric bits → d.range.WithinBound (2 ^ bits)
  /-- An atomic intent declares atomic ordering, and conversely. A `lock`-prefixed
  operation that declared `nonAtomic` would be checked by the wrong rules. -/
  atomicityAgrees : (d.intent.isAtomic = true) ↔ (d.ordering.atomicity = .atomic)
  /-- Only an access that reads can require its bytes initialized. -/
  requiresInitializedOnlyIfReads :
    d.requiresInitialized = true → d.intent.reads = true
  /-- Only an access that writes can produce initialization. -/
  producesInitializedOnlyIfWrites :
    d.producesInitialized = true → d.intent.writes = true

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
