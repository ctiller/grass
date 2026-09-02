import Grass.Memory.Audit
import Grass.Memory.Authority
import Grass.Memory.Event
import Grass.Memory.Profile
import Grass.Std.Logical.FiniteMap

/-!
# The memory state a transition acts on

The minimum state needed to decide whether a declared access is permitted: what
allocations exist, how big they are, what permission they carry, which of their
bytes are initialized, and which of them alias each other.

This is deliberately not the full M2 state. It exists because the seam cannot be
demonstrated without it — an operation's facets have to be consumed *by something*
that checks provenance, ranges, and aliasing, or the facet interface is untested
prose. What is here is what the vertical needs; the byte-level store, the
representation choice, and the framing lemma set remain M2.

## Aliasing is state, not provenance

`docs/MEMORY_MODEL.md` §7.5 contemplates mapping and sharing: a host-visible
device buffer, a file view, and a physical/virtual pair are distinct allocations
over the same bytes. Provenance cannot tell you they alias — that is exactly what
distinct `AllocId`s mean — so the state carries the relation, and the conflict
test consults it.

Without this, `Conflicts` required `SameStorage` and declared every aliased pair
non-conflicting: a write through a mapped view and a write through the file it
maps would not conflict, and every race-freedom theorem downstream would have
inherited that.
-/

namespace Grass.Memory

open Grass.Core Grass.Obligation Grass.Std.Logical

/-- What the state records about one allocation. -/
structure AllocationRecord where
  /-- The allocation's extent, in bytes. -/
  extent : ByteRange
  /-- The current reuse generation of its storage. -/
  epoch : EpochId
  /-- The address space it lives in. -/
  space : AddressSpaceId
  /-- The permission its storage carries. -/
  permission : Permission
  /-- Whether it is live. A dead allocation authorizes nothing, whatever
  provenance is presented. -/
  live : Bool
  /-- The offsets currently initialized. A list rather than a byte store, because
  the vertical needs to decide initialization, not to model byte values; M2 owns
  the store. -/
  initialized : List Nat
deriving DecidableEq, Repr

/--
The memory state.

`aliases` is symmetric by convention and `SharesBytes` closes it, so a profile
declares each aliased pair once.
-/
structure MemoryState where
  /-- The live and dead allocations. -/
  allocations : FiniteMap AllocId AllocationRecord
  /-- Pairs of allocations whose bytes are the same storage. -/
  aliases : List (AllocId × AllocId)
  /-- The authority grants currently live.

  `docs/MEMORY_MODEL.md` §3 makes this map the authoritative borrowing state.
  What is here is the map and nothing else: the split, join, freeze, and
  exclusivity-iff-empty laws are M3's, and the frame lifetime discipline is
  M4's. It exists a milestone early so that `Grass/Op/Step.lean`'s
  `AuthorityProvider` has a real table to check against, which is what shows a
  new authority kind needs no change to operation packaging. -/
  grants : FiniteMap GrantId AuthorityGrant

namespace MemoryState

/-- The state with nothing allocated. -/
def empty : MemoryState := { allocations := .empty, aliases := [], grants := .empty }

/-- Record a grant of authority. -/
def grant (state : MemoryState) (id : GrantId) (record : AuthorityGrant) : MemoryState :=
  { state with grants := state.grants.insert id record }

/--
`state.Granted context provenance range intent` holds when some live grant
authorizes that access.

Existentially quantified over the grant, because an access does not name the one
it relies on; see `Grass/Memory/Authority.lean`. Decidable because the grant table
is finite.
-/
def Granted (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) : Prop :=
  ∃ entry ∈ state.grants.entries,
    entry.2.Authorizes context provenance range intent

instance (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) :
    Decidable (state.Granted context provenance range intent) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- `state.GrantedOfKind` additionally requires the authorizing grant to be of a
particular kind, which is how one provider distinguishes itself from another over
the same table. -/
def GrantedOfKind (state : MemoryState) (kind : GrantKind) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) : Prop :=
  ∃ entry ∈ state.grants.entries,
    entry.2.kind = kind ∧ entry.2.Authorizes context provenance range intent

instance (state : MemoryState) (kind : GrantKind) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) :
    Decidable (state.GrantedOfKind kind context provenance range intent) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A state with no grants authorizes nothing. Authority is held, not assumed. -/
theorem not_granted_empty (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) :
    ¬ empty.Granted context provenance range intent := by
  rintro ⟨entry, hmem, -⟩
  simp [empty, FiniteMap.empty] at hmem

/-- `state.SharesBytes a b` holds when two allocations name the same storage,
either because they are the same allocation or because the profile declared them
aliased. -/
def SharesBytes (state : MemoryState) (a b : AllocId) : Prop :=
  a = b ∨ (a, b) ∈ state.aliases ∨ (b, a) ∈ state.aliases

instance (state : MemoryState) (a b : AllocId) : Decidable (state.SharesBytes a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem sharesBytes_refl (state : MemoryState) (a : AllocId) : state.SharesBytes a a :=
  .inl rfl

theorem SharesBytes.symm {state : MemoryState} {a b : AllocId}
    (h : state.SharesBytes a b) : state.SharesBytes b a := by
  rcases h with rfl | h | h
  · exact .inl rfl
  · exact .inr (.inr h)
  · exact .inr (.inl h)

/-- Record a new allocation. -/
def allocate (state : MemoryState) (id : AllocId) (record : AllocationRecord) :
    MemoryState :=
  { state with allocations := state.allocations.insert id record }

/-- Declare that two allocations name the same storage. -/
def alias (state : MemoryState) (a b : AllocId) : MemoryState :=
  { state with aliases := (a, b) :: state.aliases }

/-- Mark a range initialized. -/
def setInitialized (state : MemoryState) (id : AllocId) (range : ByteRange) : MemoryState :=
  match state.allocations.lookup id with
  | Option.none => state
  | some record =>
      { state with
        allocations := state.allocations.insert id
          { record with
            initialized := record.initialized ++
              (List.range range.size).map (range.start + ·) } }

/-- `state.RangeInitialized id range` holds when every offset of `range` is
initialized in `id`. -/
def RangeInitialized (state : MemoryState) (id : AllocId) (range : ByteRange) : Prop :=
  match state.allocations.lookup id with
  | Option.none => False
  | some record =>
      ∀ offset ∈ (List.range range.size).map (range.start + ·),
        offset ∈ record.initialized

instance (state : MemoryState) (id : AllocId) (range : ByteRange) :
    Decidable (state.RangeInitialized id range) := by
  unfold RangeInitialized; split <;> infer_instance

end MemoryState

/--
The whole machine state a transition threads.

The three ledgers are separate because they answer different questions and have
different laws: memory is checked, obligations are transferred, and violations
only ever grow. `events` is the trace the consistency model of M8 will read.
-/
structure MachineState where
  /-- What is allocated and what is initialized. -/
  memory : MemoryState
  /-- The obligations currently outstanding, by identity. -/
  obligations : FiniteMap ObligationId Obligation
  /-- The append-only violation ledger. -/
  violations : AuditViolationLedger
  /-- The memory events performed so far, most recent last.

  `ValidMemoryEvent`, not `MemoryEvent`: the trace cannot contain a malformed
  event, so "every event in the trace is well formed" holds by construction rather
  than by a check something could forget. An earlier trace held bare events beside
  a predicate nothing consulted, and every event the transition minted violated
  it. -/
  events : List ValidMemoryEvent
  /-- The supply that mints event identities. -/
  eventSupply : FreshSupply EventTag

namespace MachineState

/-- The state a program starts in. -/
def initial (memory : MemoryState) : MachineState :=
  { memory := memory, obligations := .empty, violations := .empty
    events := [], eventSupply := .initial }

/-- `state.OutstandingObligations` are the identities still owed. -/
def outstanding (state : MachineState) : List ObligationId := state.obligations.domain

/--
Every event in the trace is well formed.

A projection, not a check. `docs/MEMORY_MODEL.md` §7.1's field requirements hold
of the whole trace because `ValidMemoryEvent` carries the proof, and the only
producer is `MemoryEvent.ofOutcome`.
-/
theorem events_wellFormed (state : MachineState) :
    ∀ valid ∈ state.events, valid.event.WellFormed :=
  fun valid _ => valid.wellFormed

end MachineState

end Grass.Memory
