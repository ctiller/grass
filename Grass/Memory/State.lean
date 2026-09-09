import Grass.Memory.Addressing
import Grass.Memory.Backing
import Grass.Memory.Audit
import Grass.Memory.Authority
import Grass.Memory.Event
import Grass.Std.Logical.FiniteMap

/-!
# The memory state a transition acts on

Allocations are provenance and permission carrying views. Each view names one
`StorageId` and an origin; `MemoryState.backings` owns the unique capacity and
`ByteStore` for that identity. `resolveAccess?` validates provenance, liveness,
nesting, the allocation binding, backing existence, and whole-view bounds once,
then supplies one derived `BackingSpan` to authority, bytes, and events.

The portable representation can describe shared and shifted views. The temporary
runtime profile is stricter: `DedicatedBackings` requires every live allocation to
have a bounded backing and distinct live allocations to name distinct backings.
Operation entry checks that invariant while translated shared-authority laws are
completed. Candidate invalid or shared records remain expressible inputs to checked
doors and are rejected rather than acquiring executable meaning.
-/

namespace Grass.Memory

open Grass.Core Grass.Obligation Grass.Std.Logical

/-! ## Membership bounds on the grant map

Five theorems that were added to `Grass/Std/Logical/FiniteMap.lean`, which is
c-stdlib's module. `coord1:245` says implementors work within their assigned roles,
`e-auditor:5` reported this branch not doing so, and `e-reviewer:121` gave the two
ways out: c-stdlib's explicit agreement, or moving them here. This is the second.

Specialised to `GrantId`/`AuthorityGrant` rather than carried over polymorphic. They
were written for one caller and generality was never the point; stating them at the
type they are used at also keeps them out of the way of whatever c-stdlib may want
`FiniteMap`'s membership API to look like. A sixth, `entries_eq_nil_of_isEmpty`, was
added at the same time and used by nothing; it is dropped rather than moved.

`findValue`, `eraseKey` and `findValue_cons_self` are
c-stdlib's and already on main, so proving these here asks nothing of that module.
-/

/-- A found value is one of the entries.

Proved by induction on the entry list, which is why `findValue` operates on
the raw list rather than on the map. -/
theorem mem_of_findValue {entries : List (GrantId × AuthorityGrant)} {key : GrantId}
    {value : AuthorityGrant} (h : findValue entries key = some value) :
    (key, value) ∈ entries := by
  induction entries with
  | nil => simp [findValue] at h
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    by_cases hk : k = key
    · subst hk
      rw [findValue_cons_self] at h
      cases h
      exact List.mem_cons_self
    · rw [findValue, if_neg hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Erasing removes entries and adds none. -/
theorem mem_of_mem_eraseKey {entries : List (GrantId × AuthorityGrant)} {key : GrantId}
    {entry : GrantId × AuthorityGrant}
    (h : entry ∈ eraseKey entries key) : entry ∈ entries := by
  induction entries with
  | nil => simp [eraseKey] at h
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    by_cases hk : k = key
    · rw [eraseKey, if_pos hk] at h
      exact List.mem_cons_of_mem _ (ih h)
    · rw [eraseKey, if_neg hk] at h
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- A binding is one of the entries.

The missing half of a bridge review found broken: `granted_of_covering` takes an
`entry ∈ state.grantEntries` hypothesis, which `decide` discharges for a concrete map
and nothing discharged for an abstract one, so no general theorem about authority
could be stated from a `lookup`. The converse fails on a map with shadowed
duplicates, which is why this direction only. -/
theorem mem_entries_of_lookup {m : FiniteMap GrantId AuthorityGrant} {key : GrantId}
    {value : AuthorityGrant} (h : m.lookup key = some value) :
    (key, value) ∈ m.entries :=
  mem_of_findValue h

/-- The entries of a map after an insert, bounded from above.

`mem_entries_of_lookup` says what a map holds; this and `mem_entries_erase` say what
it does *not* hold, which is what a no-new-authority theorem needs: every entry of
the new map is the one just inserted or an entry of the old map. Without them a
theorem about a modified map has to unfold the association list at the call site. -/
theorem mem_entries_insert {m : FiniteMap GrantId AuthorityGrant} {key : GrantId}
    {value : AuthorityGrant} {entry : GrantId × AuthorityGrant}
    (h : entry ∈ (m.insert key value).entries) :
    entry = (key, value) ∨ entry ∈ m.entries := by
  rcases List.mem_cons.mp
    (show entry ∈ (key, value) :: eraseKey m.entries key from h) with h | h
  · exact Or.inl h
  · exact Or.inr (mem_of_mem_eraseKey h)

/-- And after an erase. -/
theorem mem_entries_erase {m : FiniteMap GrantId AuthorityGrant} {key : GrantId}
    {entry : GrantId × AuthorityGrant}
    (h : entry ∈ (m.erase key).entries) : entry ∈ m.entries :=
  mem_of_mem_eraseKey h


/-- What the state records about one allocation. -/
structure AllocationRecord where
  /-- The allocation's extent, in bytes. -/
  extent : ByteRange
  /-- The current reuse generation of its storage. -/
  epoch : EpochId
  /-- The address space it lives in. -/
  space : AddressSpaceId
  /-- Which allocator or mapping produced it.

  The counterpart to `Provenance.source`, and it exists because there was none.
  `docs/MEMORY_MODEL.md` §2 asks a profile to distinguish `VirtualAlloc`, process
  heap, `malloc`, page-table mapping, kernel heap, bump allocator, stack, mapped
  file and device memory; a descriptor recorded which of those it claimed and
  nothing could compare the claim to the storage, so two provenances differing only
  in `source` were the same storage to every rule in the layer. `denialOf` compares
  them now, as `provenanceSourceMismatch`.

  No default, for the same reason `base` has none: a profile says where an
  allocation came from. -/
  source : AllocationSourceId
  /-- The contexts that hold the allocation's own authority.

  `docs/MEMORY_MODEL.md` §3 lists "exclusive read/write ownership" among the
  canonical authority states, and until this field existed the layer could not say
  whose. `MayLend`'s lender disjunct -- the one a first loan needs -- was therefore
  the same rule a stranger's first loan needed, so a context could lend out bytes it
  had no relation to; `MayLend`'s own docstring named that as what it could not stop.
  Ownership is the missing half.

  A list, not a single context: §3's shared states and §7.4's synchronization both
  need storage several contexts own outright, and a profile that means one owner
  writes one. Empty is legal and means *no* context owns it -- storage reachable only
  through grants issued when it was made.

  Not a right and not a loan. Owning storage does not say what the permission
  allows, and `Permission.Grants` is still the question `denialOf` asks. -/
  owners : List ContextId
  /-- The permission its storage carries. -/
  permission : Permission
  /-- Whether it is live. A dead allocation authorizes nothing, whatever
  provenance is presented. -/
  live : Bool
  /-- The backing store this allocation views. Bytes live in `MemoryState.backings`. -/
  backing : StorageId
  /-- The allocation-local zero point in backing coordinates. -/
  origin : Nat
  /-- Where the allocation sits in its address space, if it sits anywhere.

  `Option`, and not because placement is optional bookkeeping. `docs/MEMORY_MODEL.md`
  §7.5 makes address spaces non-interchangeable and a logical space — a SPIR-V
  `Private` storage class, say — has allocations with no machine address at all, so
  a mandatory base would force every profile to invent one. Placement is also not
  authority in §2's sense: provenance decides what an access may touch, and the
  allocation's backing/origin binding decides which stored bytes it denotes. It is
  *not* invisible to `denialOf`, which reads this field in `placementWraps` and
  `addressDisagreesWithPlacement`; this docstring said "nothing in `denialOf` reads
  this" for two milestones after those clauses landed, thirty-two lines above its own
  retraction below, and review found it with three copies elsewhere. It is here so `Grass/Memory/Addressing.lean`'s bridge can
  be instantiated, which §4.2 recorded as owed for as long as no allocation carried
  an address.

  No default. A profile placing an allocation says where; a profile that does not
  place it says `none` deliberately. -/
  base : Option MachineAddress
deriving DecidableEq, Repr

/--
The fields a denial decision depends on.

Not "everything except the bytes", which is what this said before `owners` existed:
`denialOf` does not read `owners` and must not, because ownership is an authority
question and `Grass/Memory/Loan.lean` is where it is asked. Leaving it out is the
claim that adding an owner cannot change whether an access is *denied* -- only
whether it is *authorized* -- and `denialOf_congr_of_agrees` is that claim proved.

`denialOf` reads exactly these seven fields plus initialization, so this is the
view a decision depends on. Naming it lets a framing argument say "the metadata
did not move" without asserting the bytes did not, which is the whole point of a
write.
-/
structure AllocationRecord.Metadata where
  /-- The allocation's extent. -/
  extent : ByteRange
  /-- Its reuse generation. -/
  epoch : EpochId
  /-- Its address space. -/
  space : AddressSpaceId
  /-- Which allocator or mapping produced it. Here because `denialOf` reads it; a
  metadata view missing a decision input would make `denialOf_congr_of_agrees`
  false. -/
  source : AllocationSourceId
  /-- The permission its storage carries. -/
  permission : Permission
  /-- Whether it is live. -/
  live : Bool
  /-- The backing binding used by spatial resolution. -/
  backing : StorageId
  /-- The allocation-local zero point in backing coordinates. -/
  origin : Nat
  /-- Where it sits, if it sits anywhere.

  Added when `denialOf` began checking the access's declared address against the
  allocation's placement. `AllocationRecord.base`'s docstring said "nothing in
  `denialOf` reads this", and that was true and was the problem: the address field
  on a descriptor could say anything. The moment it became a decision input it had
  to be in this view, or `denialOf_congr_of_agrees` would be false — two states
  agreeing on metadata and on every byte could refuse differently. -/
  base : Option MachineAddress
deriving DecidableEq, Repr

/-- The metadata view of a record. -/
def AllocationRecord.metadata (record : AllocationRecord) : AllocationRecord.Metadata :=
  ⟨record.extent, record.epoch, record.space, record.source, record.permission,
   record.live, record.backing, record.origin, record.base⟩

/-- The coordinate projection of an allocation record. Its extent remains on the
record and is supplied separately to the pure coordinate checker. -/
def AllocationRecord.mapping (record : AllocationRecord) : Coordinates.Mapping :=
  ⟨record.backing, record.origin⟩

/-- The memory state: allocation views, authoritative backing storage, and grants. -/
structure MemoryState where
  private mk ::
  /-- The live and dead allocations. -/
  allocations : FiniteMap AllocId AllocationRecord
  /-- One authoritative capacity and byte store per backing identity. -/
  backings : FiniteMap StorageId BackingRecord
  /-- The authority grants currently live. **Private**: see below.


  `docs/MEMORY_MODEL.md` §3 makes this map the authoritative borrowing state.
  What is here is the map and nothing else: the split, join, freeze, and
  exclusivity-iff-empty laws are M3's, and the frame lifetime discipline is
  M4's. It exists a milestone early so that `Grass/Op/Step.lean`'s
  `AuthorityProvider` has a real table to check against, which is what shows a
  new authority kind needs no change to operation packaging. -/
  private grants : FiniteMap GrantId AuthorityGrant

namespace MemoryState

/-- The state with nothing allocated. -/
def empty : MemoryState := { allocations := .empty, backings := .empty, grants := .empty }

/-! ## The grant map is sealed

`grants` is `private`, and the mutators live in this module, because deleting the
unchecked door was not enough twice running.

First there was `MemoryState.grant` — `grants.insert`, no checks — described as the
door providers of kinds other than `loan` use, with a theorem arguing it was safe
because the access-time rule reads whatever map it finds. `FiniteMap.insert`
*erases* any existing binding, so installing a grant under an identity another
context already holds deletes that context's grant, and the map the access-time rule
then finds no longer contains the victim. Review wrote that attack and the write
committed with no violation.

Deleting `grant` and adding `issue?` did not close it: `grants` was a public field,
so `{ state with grants := state.grants.insert id g }` *is* the deleted function,
available to every caller — and two of this project's own fixtures used it. Review
wrote the same attack again through the field. A comment saying "there is no second
door" was in the file at the time.

So the field is private and the five operations that change it are here: `issue?`,
`returnGrant?`, `splitGrant?`, `joinGrants?` and `transferGrant?` — which is the door
set `Tools/DoorAudit.py` guards, and this sentence said two for as long as there have
been five. `Grass/Memory/Loan.lean` states §3's laws over
them and adds the loan-specific refusals; `grantEntries` and `grantAt?` are the
read-only views everything else uses.

**And `mk` is private too**, which is the third time this hole was closed — and the
checks live here rather than a module up, which is the fourth. Marking the *field*
private privatised the projection and left the constructor alone, so
`MemoryState.mk allocations backings ⟨…⟩` still built any map at all; review rebuilt
`Tests/Op/StandardLoan.lean`'s own lent state with the loan filtered out of
`grantEntries`, and the thread's store committed. Sealing `mk` closed that, and left
a low-level `issueGrant?` public in this module that ran the identity check and none
of the others, so review installed a four-kilobyte grant over a sixty-four-byte
allocation through it and froze an honest store. There is one door now and it is the
checked one.
Marking the *field* private privatises the projection and leaves the constructor
alone, so `MemoryState.mk allocations backings ⟨…⟩` still built any map at all —
review rebuilt `Tests/Op/StandardLoan.lean`'s own lent state with the loan filtered
out of `grantEntries`, and the thread's store committed. That is the same failure
`Grass/Memory/ByteStore.lean`'s comment records for `ByteStore.rec`, and this module
had it while claiming there was no second door. `MemoryState.rec` cannot construct,
so with `mk` private the map is reachable only through the five mutators above.
-/

/--
`state.RootExtentAgrees provenance` holds when the provenance's recorded root extent
is the extent of the allocation it names.

`Provenance.rootExtent` is what `AccessDescriptor.WellFormedIn.rangeInProvenance`
bounds an access against and what `Provenance.extent` computes a grant's bound from,
and nothing compared it to the allocation table -- so both were self-certifying, and
review issued a grant over four kilobytes of a sixteen-byte allocation and watched it
authorize and freeze. `denialOf` records `provenanceExtentMismatch` for an access;
`MemoryState.issue?` refuses the grant.
-/
def RootExtentAgrees (state : MemoryState) (provenance : Provenance) : Prop :=
  (state.allocations.lookup provenance.root).any
    (fun record => decide (record.extent = provenance.rootExtent)) = true

instance (state : MemoryState) (provenance : Provenance) :
    Decidable (state.RootExtentAgrees provenance) :=
  inferInstanceAs (Decidable (_ = _))

/--
`state.RootIdentityAgrees provenance` holds when the allocation the provenance names
is in the address space and from the allocator the provenance claims.

The other two comparisons `denialOf` makes for an *access* -- `wrongAddressSpace` and
`provenanceSourceMismatch` -- asked at the authority layer, where `issue?` asks
`RootExtentAgrees` and asked nothing else about the root. A grant is a claim about
storage in the same way a descriptor is, and it reached the map without either
question: review issued a grant whose provenance put `bufferAlloc` in
`device.hostVisible`, and the map held it and froze the thread's own bytes with it.

Deliberately *not* about the grant versus the access. `MemoryState.AuthorizedAt` drops
its space conjunct on purpose, because a device engine's grant over a host-visible
buffer is the case §7.5 exists to describe; this compares the grant's provenance with
the allocation that provenance names, which in that case agree.
-/
def RootIdentityAgrees (state : MemoryState) (provenance : Provenance) : Prop :=
  (state.allocations.lookup provenance.root).any
    (fun record => decide (record.space = provenance.space) &&
      decide (record.source = provenance.source)) = true

instance (state : MemoryState) (provenance : Provenance) :
    Decidable (state.RootIdentityAgrees provenance) :=
  inferInstanceAs (Decidable (_ = _))

/-- The grants outstanding, as a read-only view. -/
def grantEntries (state : MemoryState) : List (GrantId × AuthorityGrant) :=
  state.grants.entries

/-- The grant an identity names, if it names one. -/
def grantAt? (state : MemoryState) (id : GrantId) : Option AuthorityGrant :=
  state.grants.lookup id

/-- Stable capacity metadata for one backing identity. -/
def backingCapacity? (state : MemoryState) (id : StorageId) : Option Nat :=
  (state.backings.lookup id).map BackingRecord.capacity

/-- The backing named by an allocated view. -/
def backingOf? (state : MemoryState) (id : AllocId) : Option StorageId :=
  (state.allocations.lookup id).map AllocationRecord.backing

/-- Two allocated views share storage exactly when they name one backing. Identity
is retained as the reflexive case so existing authority statements remain total;
live execution additionally passes through `resolveAccess?`. -/
def SharesBytes (state : MemoryState) (a b : AllocId) : Prop :=
  a = b ∨ ∃ backing, state.backingOf? a = some backing ∧ state.backingOf? b = some backing

instance (state : MemoryState) (a b : AllocId) : Decidable (state.SharesBytes a b) :=
  inferInstanceAs (Decidable (_ ∨ ∃ _backing, _ ∧ _))

@[simp] theorem sharesBytes_refl (state : MemoryState) (a : AllocId) :
    state.SharesBytes a a := Or.inl rfl

theorem sharesBytes_symm {state : MemoryState} {a b : AllocId}
    (h : state.SharesBytes a b) : state.SharesBytes b a := by
  rcases h with rfl | ⟨backing, ha, hb⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨backing, hb, ha⟩

theorem sharesBytes_trans {state : MemoryState} {a b c : AllocId}
    (hab : state.SharesBytes a b) (hbc : state.SharesBytes b c) :
    state.SharesBytes a c := by
  rcases hab with rfl | ⟨ab, ha, hb⟩
  · exact hbc
  · rcases hbc with rfl | ⟨bc, hb', hc⟩
    · exact Or.inr ⟨ab, ha, hb⟩
    · rw [hb] at hb'
      cases hb'
      exact Or.inr ⟨ab, ha, hc⟩

theorem sharesBytes_of_backing_eq {state : MemoryState} {a b : AllocId}
    {ra rb : AllocationRecord} (ha : state.allocations.lookup a = some ra)
    (hb : state.allocations.lookup b = some rb) (hbacking : ra.backing = rb.backing) :
    state.SharesBytes a b := by
  right
  refine ⟨ra.backing, ?_, ?_⟩
  · simp [backingOf?, ha]
  · simp [backingOf?, hb, hbacking]


/--
`state.CurrentEpoch provenance` holds when the root allocation exists and is in the
epoch this provenance names.

`docs/MEMORY_MODEL.md` §2: address reuse never revives old pointers, and §5:
same-address objects in a new epoch have new provenance. `AllocationRecord` carried
the epoch and nothing compared it, so a provenance minted before a
free-and-reallocate was treated as naming the storage that replaced it.
-/
def CurrentEpoch (state : MemoryState) (provenance : Provenance) : Prop :=
  (state.allocations.lookup provenance.root).any
    (fun record => decide (record.epoch = provenance.epoch)) = true

instance (state : MemoryState) (provenance : Provenance) :
    Decidable (state.CurrentEpoch provenance) :=
  inferInstanceAs (Decidable (_ = _))

/--
`state.Live provenance` holds when the root allocation exists, is live, and is in
the epoch this provenance names.

Authority over storage that is gone is not weak authority, it is none — which is
`AllocationRecord.live`'s own rule ("a dead allocation authorizes nothing, whatever
provenance is presented") read at this layer.
-/
def Live (state : MemoryState) (provenance : Provenance) : Prop :=
  (state.allocations.lookup provenance.root).any
    (fun record => record.live && decide (record.epoch = provenance.epoch)) = true

instance (state : MemoryState) (provenance : Provenance) : Decidable (state.Live provenance) :=
  inferInstanceAs (Decidable (_ = _))

/-- Live storage is current-epoch storage. -/
theorem currentEpoch_of_live {state : MemoryState} {provenance : Provenance}
    (h : state.Live provenance) : state.CurrentEpoch provenance := by
  unfold Live at h
  unfold CurrentEpoch
  cases hm : state.allocations.lookup provenance.root with
  | none => rw [hm] at h; simp at h
  | some record =>
      rw [hm] at h
      simp only [Option.any_some] at *
      exact ((Bool.and_eq_true _ _).mp h).2

/-! ## Checked backing resolution -/

/-- Why a provenance/range could not be resolved to authoritative backing bytes.
The constructors are deliberately more precise than the temporary profile-level
`backingLayoutUnsupported` audit class so rejection tests can distinguish malformed
state from an ordinary bounds or provenance error. -/
inductive ResolveFailure where
  | provenanceNotAllocated
  | deadProvenance
  | staleEpoch
  | wrongAddressSpace
  | provenanceSourceMismatch
  | provenanceExtentMismatch
  | provenanceNotNested
  | rangeOutsideProvenance
  | backingNotAllocated
  | mappingOutOfBounds
deriving DecidableEq, Repr

/-- `ResolvedAccess` is the complete result of resolving one access. Its
`allocationLookup`, `backingLookup`, and `coordinates` fields bind later consumers to
the checked mapping, capacity, and span. -/
structure ResolvedAccess (state : MemoryState) (provenance : Provenance)
    (requested : ByteRange) : Type where
  allocation : AllocationRecord
  backing : BackingRecord
  allocationLookup : state.allocations.lookup provenance.root = some allocation
  backingLookup : state.backings.lookup allocation.backing = some backing
  allocationLive : allocation.live = true
  epochAgrees : allocation.epoch = provenance.epoch
  spaceAgrees : allocation.space = provenance.space
  sourceAgrees : allocation.source = provenance.source
  extentAgrees : allocation.extent = provenance.rootExtent
  provenanceNested : provenance.Nested
  rangeInProvenance : provenance.extent.Contains requested
  coordinates : Coordinates.ResolvedRange allocation.mapping allocation.extent
    backing.capacity requested

namespace ResolvedAccess

/-- The one backing span derived from the checked lookup and mapping. -/
def span {state : MemoryState} {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) : Coordinates.BackingSpan :=
  access.coordinates.span

/-- A checked prefix keeps the same allocation and backing lookups. Prefixing is
only spatial; fault-plan and atomicity checks remain at the operation boundary. -/
def «prefix» {state : MemoryState} {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (count : Nat) :
    state.ResolvedAccess provenance (requested.take count) :=
  { access with
    rangeInProvenance := access.rangeInProvenance.trans (requested.contains_take count)
    coordinates := access.coordinates.prefix count }

/-- Restrict a prepared access to a contained local subrange without repeating any
state lookup or mapping decision. -/
def restrict {state : MemoryState} {provenance : Provenance} {outer inner : ByteRange}
    (access : state.ResolvedAccess provenance outer) (h : outer.Contains inner) :
    state.ResolvedAccess provenance inner :=
  { access with
    rangeInProvenance := access.rangeInProvenance.trans h
    coordinates :=
      { withinView := access.coordinates.withinView.trans h
        viewWithinBacking := access.coordinates.viewWithinBacking } }

/-- Containment of local requests is preserved by their single stable mapping. -/
theorem span_contains_of_contains {state : MemoryState} {provenance : Provenance}
    {outer inner : ByteRange}
    (outerAccess : state.ResolvedAccess provenance outer)
    (innerAccess : state.ResolvedAccess provenance inner)
    (h : outer.Contains inner) : outerAccess.span.Contains innerAccess.span := by
  have ha : outerAccess.allocation = innerAccess.allocation := by
    apply Option.some.inj
    exact outerAccess.allocationLookup.symm.trans innerAccess.allocationLookup
  unfold span Coordinates.ResolvedRange.span
  rw [ha]
  exact (Coordinates.Mapping.span_contains_iff _ _ _).2 h

@[simp] theorem prefix_span {state : MemoryState} {provenance : Provenance}
    {requested : ByteRange} (access : state.ResolvedAccess provenance requested)
    (count : Nat) :
    (access.prefix count).span.range = access.span.range.take count :=
  Coordinates.ResolvedRange.prefix_span access.coordinates count

/-- Transport a resolution across a transition that changes neither allocation
bindings nor backing records. Authority effects use this exact form. -/
def transport {before after : MemoryState} {provenance : Provenance}
    {requested : ByteRange} (access : before.ResolvedAccess provenance requested)
    (hallocations : after.allocations = before.allocations)
    (hbackings : after.backings = before.backings) :
    after.ResolvedAccess provenance requested :=
  { access with
    allocationLookup := by rw [hallocations]; exact access.allocationLookup
    backingLookup := by rw [hbackings]; exact access.backingLookup }

/-- Read a covered local offset from the backing snapshot retained by this
resolution. An offset outside the prepared request fails closed. -/
def cellAt? {state : MemoryState} {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (offset : Nat) :
    Option (Byte × Bool) :=
  if requested.Covers offset then
    access.backing.cellAt? (access.allocation.origin + offset)
  else none

/-- The byte component of `cellAt?`. -/
def byteAt? {state : MemoryState} {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (offset : Nat) : Option Byte :=
  (access.cellAt? offset).map Prod.fst

/-- Initialization of the exact prepared backing span. -/
def RangeInitialized {state : MemoryState} {provenance : Provenance}
    {requested : ByteRange} (access : state.ResolvedAccess provenance requested) : Prop :=
  access.backing.bytes.Initialized access.span.range

instance {state : MemoryState} {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) :
    Decidable access.RangeInitialized := by
  unfold RangeInitialized
  infer_instance

end ResolvedAccess

/-- Resolve provenance and a requested local range exactly once. Every lookup and
arithmetic failure is explicit; in particular, a missing backing never behaves as
an empty byte store. -/
def resolveAccess? (state : MemoryState) (provenance : Provenance)
    (requested : ByteRange) :
    Except ResolveFailure (state.ResolvedAccess provenance requested) :=
  match hrecord : state.allocations.lookup provenance.root with
  | none => .error .provenanceNotAllocated
  | some record =>
      if hlive : record.live = true then
        if hepoch : record.epoch = provenance.epoch then
          if hspace : record.space = provenance.space then
            if hsource : record.source = provenance.source then
              if hextent : record.extent = provenance.rootExtent then
                if hnested : provenance.Nested then
                  if hrange : provenance.extent.Contains requested then
                    match hbacking : state.backings.lookup record.backing with
                    | none => .error .backingNotAllocated
                    | some backing =>
                        if hbound : (record.extent.shift record.mapping.origin).WithinBound
                            backing.capacity then
                          .ok
                            { allocation := record
                              backing := backing
                              allocationLookup := hrecord
                              backingLookup := hbacking
                              allocationLive := hlive
                              epochAgrees := hepoch
                              spaceAgrees := hspace
                              sourceAgrees := hsource
                              extentAgrees := hextent
                              provenanceNested := hnested
                              rangeInProvenance := hrange
                              coordinates :=
                                { withinView := by
                                    rw [hextent]
                                    exact (Provenance.extent_within_root hnested).trans hrange
                                  viewWithinBacking := hbound } }
                        else .error .mappingOutOfBounds
                  else .error .rangeOutsideProvenance
                else .error .provenanceNotNested
              else .error .provenanceExtentMismatch
            else .error .provenanceSourceMismatch
          else .error .wrongAddressSpace
        else .error .staleEpoch
      else .error .deadProvenance

/-- Public failure classifier for a checked lookup of a dead allocation. -/
theorem resolveAccess?_eq_deadProvenance {state : MemoryState}
    {provenance : Provenance} {requested : ByteRange} {record : AllocationRecord}
    (hlookup : state.allocations.lookup provenance.root = some record)
    (hdead : record.live = false) :
    state.resolveAccess? provenance requested = .error .deadProvenance := by
  unfold resolveAccess?
  split
  · rename_i hrecord
    rw [hlookup] at hrecord
    contradiction
  · rename_i found hrecord
    have hfound : found = record :=
      Option.some.inj (hrecord.symm.trans hlookup)
    subst found
    simp [hdead]

/-- Public failure classifier for an allocation generation mismatch. -/
theorem resolveAccess?_eq_staleEpoch {state : MemoryState}
    {provenance : Provenance} {requested : ByteRange} {record : AllocationRecord}
    (hlookup : state.allocations.lookup provenance.root = some record)
    (hlive : record.live = true) (hstale : record.epoch ≠ provenance.epoch) :
    state.resolveAccess? provenance requested = .error .staleEpoch := by
  unfold resolveAccess?
  split
  · rename_i hrecord
    rw [hlookup] at hrecord
    contradiction
  · rename_i found hrecord
    have hfound : found = record :=
      Option.some.inj (hrecord.symm.trans hlookup)
    subst found
    simp [hlive, hstale]

/-- Public failure classifier for a provenance source mismatch after the preceding
identity checks have succeeded. -/
theorem resolveAccess?_eq_sourceMismatch {state : MemoryState}
    {provenance : Provenance} {requested : ByteRange} {record : AllocationRecord}
    (hlookup : state.allocations.lookup provenance.root = some record)
    (hlive : record.live = true) (hepoch : record.epoch = provenance.epoch)
    (hspace : record.space = provenance.space)
    (hsource : record.source ≠ provenance.source) :
    state.resolveAccess? provenance requested = .error .provenanceSourceMismatch := by
  unfold resolveAccess?
  split
  · rename_i hrecord
    rw [hlookup] at hrecord
    contradiction
  · rename_i found hrecord
    have hfound : found = record :=
      Option.some.inj (hrecord.symm.trans hlookup)
    subst found
    simp [hlive, hepoch, hspace, hsource]

/-- Public failure classifier for a missing backing after provenance checks pass. -/
theorem resolveAccess?_eq_backingNotAllocated {state : MemoryState}
    {provenance : Provenance} {requested : ByteRange} {record : AllocationRecord}
    (hlookup : state.allocations.lookup provenance.root = some record)
    (hlive : record.live = true) (hepoch : record.epoch = provenance.epoch)
    (hspace : record.space = provenance.space)
    (hsource : record.source = provenance.source)
    (hextent : record.extent = provenance.rootExtent)
    (hnested : provenance.Nested) (hrange : provenance.extent.Contains requested)
    (hbacking : state.backings.lookup record.backing = none) :
    state.resolveAccess? provenance requested = .error .backingNotAllocated := by
  unfold resolveAccess?
  split
  · rename_i hrecord
    rw [hlookup] at hrecord
    contradiction
  · rename_i found hrecord
    have hfound : found = record :=
      Option.some.inj (hrecord.symm.trans hlookup)
    subst found
    simp only [hlive, hepoch, hspace, hsource, hextent, hnested, hrange,
      ↓reduceDIte]
    split
    · rfl
    · rename_i foundBacking hfoundBacking
      rw [hbacking] at hfoundBacking
      contradiction

/-- Public failure classifier for a live view whose translated full extent exceeds
the installed backing capacity. -/
theorem resolveAccess?_eq_mappingOutOfBounds {state : MemoryState}
    {provenance : Provenance} {requested : ByteRange} {record : AllocationRecord}
    {backing : BackingRecord}
    (hlookup : state.allocations.lookup provenance.root = some record)
    (hlive : record.live = true) (hepoch : record.epoch = provenance.epoch)
    (hspace : record.space = provenance.space)
    (hsource : record.source = provenance.source)
    (hextent : record.extent = provenance.rootExtent)
    (hnested : provenance.Nested) (hrange : provenance.extent.Contains requested)
    (hbacking : state.backings.lookup record.backing = some backing)
    (hout : ¬ (record.extent.shift record.mapping.origin).WithinBound backing.capacity) :
    state.resolveAccess? provenance requested = .error .mappingOutOfBounds := by
  unfold resolveAccess?
  split
  · rename_i hrecord
    rw [hlookup] at hrecord
    contradiction
  · rename_i found hrecord
    have hfound : found = record :=
      Option.some.inj (hrecord.symm.trans hlookup)
    subst found
    simp only [hlive, hepoch, hspace, hsource, hextent, hnested, hrange,
      ↓reduceDIte]
    split
    · rename_i hfoundBacking
      rw [hbacking] at hfoundBacking
      contradiction
    · rename_i foundBacking hfoundBacking
      have hbackingEq : foundBacking = backing :=
        Option.some.inj (hfoundBacking.symm.trans hbacking)
      subst foundBacking
      simp [← hextent, hout]

/-- A value carrying all resolver evidence is the resolver's unique successful
result; proof fields are propositionally irrelevant. -/
theorem resolveAccess?_eq_ok {state : MemoryState} {provenance : Provenance}
    {requested : ByteRange} (access : state.ResolvedAccess provenance requested) :
    state.resolveAccess? provenance requested = .ok access := by
  unfold resolveAccess?
  split
  · rename_i hrecord
    have : (none : Option AllocationRecord) = some access.allocation :=
      hrecord.symm.trans access.allocationLookup
    contradiction
  · rename_i record hrecord
    have hrecordEq : record = access.allocation :=
      Option.some.inj (hrecord.symm.trans access.allocationLookup)
    subst record
    repeat' split
    all_goals simp_all [access.allocationLive, access.epochAgrees,
      access.spaceAgrees, access.sourceAgrees, access.extentAgrees,
      access.provenanceNested, access.rangeInProvenance,
      access.backingLookup]
    case h_2.isTrue =>
      rename_i backing hlookup _
      have hbackingEq : access.backing = backing :=
        Option.some.inj (access.backingLookup.symm.trans hlookup)
      cases hbackingEq
      congr
    case h_2.isFalse =>
      rename_i backing hlookup hbound
      cases hlookup
      exact hbound (by simpa [access.extentAgrees, AllocationRecord.mapping] using
        access.coordinates.viewWithinBacking)

/-- The temporary executable profile: every live allocation resolves to an existing
bounded backing, and two distinct live allocation identities never name one backing.
The portable representation remains capable of describing candidate shared layouts;
operation entry rejects them until the translated authority law suite is complete. -/
def DedicatedBackings (state : MemoryState) : Prop :=
  state.allocations.entries.all (fun entry =>
    !entry.2.live ||
      ((state.backingCapacity? entry.2.backing).any
        (fun capacity => decide
          ((entry.2.extent.shift entry.2.origin).WithinBound capacity)) &&
       state.allocations.entries.all (fun other =>
        !other.2.live || other.1 = entry.1 || other.2.backing ≠ entry.2.backing))) = true

instance (state : MemoryState) : Decidable state.DedicatedBackings :=
  inferInstanceAs (Decidable (_ = true))

@[simp] theorem dedicatedBackings_empty : empty.DedicatedBackings := by
  simp [DedicatedBackings, empty, FiniteMap.empty]

private theorem mem_allocation_of_findValue
    {entries : List (AllocId × AllocationRecord)} {key : AllocId}
    {value : AllocationRecord} (h : findValue entries key = some value) :
    (key, value) ∈ entries := by
  induction entries with
  | nil => simp [findValue] at h
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    by_cases hk : k = key
    · subst hk
      rw [findValue_cons_self] at h
      cases h
      exact List.mem_cons_self
    · rw [findValue, if_neg hk] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem mem_allocation_entries_of_lookup
    {m : FiniteMap AllocId AllocationRecord} {key : AllocId}
    {value : AllocationRecord} (h : m.lookup key = some value) :
    (key, value) ∈ m.entries :=
  mem_allocation_of_findValue h

/-- Distinct live allocation views name distinct backings in the temporary runtime
profile. This is the semantic projection used by allocation-relative framing. -/
theorem DedicatedBackings.backing_ne_of_live_lookup {state : MemoryState}
    (hdedicated : state.DedicatedBackings)
    {a b : AllocId} {aRecord bRecord : AllocationRecord}
    (ha : state.allocations.lookup a = some aRecord)
    (hb : state.allocations.lookup b = some bRecord)
    (halive : aRecord.live = true) (hblive : bRecord.live = true)
    (hne : a ≠ b) : aRecord.backing ≠ bRecord.backing := by
  unfold DedicatedBackings at hdedicated
  have haEntry : (a, aRecord) ∈ state.allocations.entries :=
    mem_allocation_entries_of_lookup ha
  have hbEntry : (b, bRecord) ∈ state.allocations.entries :=
    mem_allocation_entries_of_lookup hb
  have haCondition := (List.all_eq_true.mp hdedicated) (a, aRecord) haEntry
  have hothers : state.allocations.entries.all (fun other =>
      !other.2.live || other.1 = a || other.2.backing ≠ aRecord.backing) = true := by
    have haCondition' := haCondition
    simp only [halive, Bool.not_true, Bool.false_or, Bool.and_eq_true] at haCondition'
    exact haCondition'.2
  have hbCondition := (List.all_eq_true.mp hothers) (b, bRecord) hbEntry
  have hba : b ≠ a := Ne.symm hne
  have : bRecord.backing ≠ aRecord.backing := by
    simpa [hblive, hba] using hbCondition
  exact Ne.symm this

/-- Install one fresh backing. Existing backing identities are immutable: neither
capacity nor bytes can be replaced through this door. -/
def installBacking? (state : MemoryState) (id : StorageId) (record : BackingRecord) :
    Option MemoryState :=
  match state.backings.lookup id with
  | some _ => none
  | none => some { state with backings := state.backings.insert id record }

@[simp] theorem allocations_installBacking? {state next : MemoryState} {id : StorageId}
    {record : BackingRecord} (h : state.installBacking? id record = some next) :
    next.allocations = state.allocations := by
  unfold installBacking? at h
  split at h
  · contradiction
  · injection h with h; subst h; rfl

@[simp] theorem grantEntries_installBacking? {state next : MemoryState} {id : StorageId}
    {record : BackingRecord} (h : state.installBacking? id record = some next) :
    next.grantEntries = state.grantEntries := by
  unfold installBacking? at h
  split at h
  · contradiction
  · injection h with h; subst h; rfl

/-- `DedicatedBackings.installBacking?` proves that installing a fresh backing preserves
an existing dedicated layout. A live view cannot already name the fresh identity,
because `DedicatedBackings` requires its backing to exist. -/
theorem DedicatedBackings.installBacking? {state next : MemoryState} {id : StorageId}
    {record : BackingRecord} (hdedicated : state.DedicatedBackings)
    (h : state.installBacking? id record = some next) : next.DedicatedBackings := by
  unfold MemoryState.installBacking? at h
  cases hlookup : state.backings.lookup id with
  | some existing => rw [hlookup] at h; contradiction
  | none =>
      rw [hlookup] at h
      injection h with hnext
      subst next
      unfold DedicatedBackings at hdedicated ⊢
      apply List.all_eq_true.mpr
      intro entry hentry
      have hold := List.all_eq_true.mp hdedicated entry hentry
      by_cases hlive : entry.2.live = true
      · have hne : entry.2.backing ≠ id := by
          intro heq
          subst id
          simp [hlive, backingCapacity?, hlookup] at hold
        have hcapacity :
            ({ state with backings := state.backings.insert id record } :
              MemoryState).backingCapacity? entry.2.backing =
              state.backingCapacity? entry.2.backing := by
          unfold backingCapacity?
          rw [FiniteMap.lookup_insert_ne _ hne]
        simpa [hlive, hcapacity] using hold
      · have hliveFalse : entry.2.live = false := by
          cases hvalue : entry.2.live
          · rfl
          · exact False.elim (hlive hvalue)
        simp [hliveFalse]

/-- Resolve an installed grant's declared range through the same state-bound spatial
gate used by accesses. -/
def grantSpan? (state : MemoryState) (grant : AuthorityGrant) :
    Except ResolveFailure Coordinates.BackingSpan :=
  (state.resolveAccess? grant.provenance grant.range).map ResolvedAccess.span

/-- Two successfully resolved grants with the same provenance preserve local range
containment in backing coordinates. -/
theorem grantSpan?_contains_of_same_provenance {state : MemoryState}
    {outer inner : AuthorityGrant} {outerSpan innerSpan : Coordinates.BackingSpan}
    (hprovenance : outer.provenance = inner.provenance)
    (hrange : outer.range.Contains inner.range)
    (houter : state.grantSpan? outer = .ok outerSpan)
    (hinner : state.grantSpan? inner = .ok innerSpan) :
    outerSpan.Contains innerSpan := by
  unfold grantSpan? at houter hinner
  cases ho : state.resolveAccess? outer.provenance outer.range with
  | error failure =>
      rw [ho] at houter
      contradiction
  | ok outerAccess =>
      rw [ho] at houter
      injection houter with houter
      subst outerSpan
      rw [← hprovenance] at hinner
      cases hi : state.resolveAccess? outer.provenance inner.range with
      | error failure =>
          rw [hi] at hinner
          contradiction
      | ok innerAccess =>
          rw [hi] at hinner
          injection hinner with hinner
          subst innerSpan
          exact ResolvedAccess.span_contains_of_contains outerAccess innerAccess hrange

/-- `grantSpan?_eq_ok_transport` transports a successful grant span across equal
allocation and backing tables. -/
theorem grantSpan?_eq_ok_transport {before after : MemoryState}
    {grant : AuthorityGrant} {span : Coordinates.BackingSpan}
    (h : before.grantSpan? grant = .ok span)
    (hallocations : after.allocations = before.allocations)
    (hbackings : after.backings = before.backings) :
    after.grantSpan? grant = .ok span := by
  unfold grantSpan? at h ⊢
  cases hr : before.resolveAccess? grant.provenance grant.range with
  | error failure => rw [hr] at h; contradiction
  | ok access =>
      rw [hr] at h
      injection h with hspan
      let transported := access.transport hallocations hbackings
      rw [resolveAccess?_eq_ok transported]
      change Except.ok transported.span = Except.ok span
      congr

/-- Grants meeting an already-resolved backing span. A malformed installed grant is
included conservatively rather than disappearing from the freeze set. -/
def grantsOverSpan (state : MemoryState) (span : Coordinates.BackingSpan) :
    List (GrantId × AuthorityGrant) :=
  state.grantEntries.filter fun entry =>
    match state.grantSpan? entry.2 with
    | .ok grantSpan => decide (grantSpan.Meets span)
    | .error _ => true

/-- Provenance-facing compatibility wrapper. Invalid query resolution fails closed
by reporting every installed grant as potentially relevant. Runtime code should use
`grantsOverSpan` with its prepared access. -/
def grantsOver (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    List (GrantId × AuthorityGrant) :=
  match state.resolveAccess? provenance range with
  | .ok access => state.grantsOverSpan access.span
  | .error _ => state.grantEntries

/-- The loans among them. §3's laws — exclusivity, counts, return by identity — are
about loans, so they are stated over this; the access-time conflict rule is about
authority, so it is stated over `grantsOver`. -/
def loansOver (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    List (GrantId × AuthorityGrant) :=
  (state.grantsOver provenance range).filter (fun entry => entry.2.kind = GrantKind.loan)

/-- `state.AnyGrantOver provenance range` holds when *some* context holds authority
over those bytes, of any kind.

The question the transition's holder test should be asking, and it took three tries
to arrive at.

It was `Exclusive` — the *loan* map empty of everyone's loans — which is §3's
sentence about exclusive authority and not a question about this access. A lender
that had lent read-only could not read its own bytes, and a context following this
layer's own "declare a loan to yourself" idiom with a read-only self-loan could not
write those bytes even after every other loan was returned.

Then it was `LoanHeldBySelf`, which fixed the self-loan case and opened a worse one:
a context holding *nothing* was asked nothing, so when others held atomic-only
grants and `authorityOf` reported `atomicShared`, any context at all could join the
protocol atomically. Review demonstrated two contexts atomically writing the same
live bytes with one of them holding no grant. It also keyed on `GrantKind.loan`
while the state half did not, so two grants identical but for `kind` gave opposite
answers about whether their holder may write.

So: if anything is held over these bytes, an accessor needs authority of its own.

That over-refused, and the cost was stated here for two milestones: the lender's read
of its own shared-immutably-lent bytes was refused along with a stranger's, because
nothing recorded who owned an allocation and the two were indistinguishable to the
rule. `AllocationRecord.owners` distinguishes them, and `Grass/Op/Step.lean`'s clause
exempts an owner that holds no grant of its own -- `HeldBySelf` being the second half,
since an owner that took a narrower grant over its own bytes is bound by it. The
predicate here is unchanged and still asks only what is outstanding; the exemption is
where the refusal is narrowed, which is the layer that knows who is accessing. -/
def AnyGrantOver (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    Prop := state.grantsOver provenance range ≠ []

instance (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    Decidable (state.AnyGrantOver provenance range) :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- Prepared-span form used by operation authority checks. -/
def AnyGrantOverResolved {state : MemoryState} {provenance : Provenance}
    {range : ByteRange} (access : state.ResolvedAccess provenance range) : Prop :=
  state.grantsOverSpan access.span ≠ []

instance {state : MemoryState} {provenance : Provenance} {range : ByteRange}
    (access : state.ResolvedAccess provenance range) :
    Decidable (state.AnyGrantOverResolved access) :=
  inferInstanceAs (Decidable (_ ≠ _))

/--
Two grants issue conflicting authority.

`docs/MEMORY_MODEL.md` §7.3 defines a conflict as overlapping live bytes with at
least one writer *from distinct concurrent contexts*, and says "unique loans
prevent ordinary conflicting authority from being issued". This is that test
applied at issue time.

**Distinct holders.** §7.3's rule is about distinct contexts, and without the
clause a context could not hold two grants over its own bytes — which is the
idiom the access-time rule endorses for "the owner may still read", and
which was therefore mutually exclusive with any other grant on those bytes.

**`Meets` in both directions**, because `Meets` is asymmetric and neither grant is
the query here. `loansOver` moved off `Disjoint` and this did not, which left one
module with two answers to what "overlapping" means.

That sentence says why the directions differ and not what the second one adds, and
review found nothing discriminating it. `ByteRange.meets_comm_of_nonempty` is the
boundary stated: on two non-empty ranges the directions agree, so the reverse one is
reached only where the *installed* grant covers no bytes and the new grant covers
where it sits. `issue?_eq_none_of_empty` refuses an empty grant at the door, so no
state reached through `issue?` has one installed — which is the shape of `MayLend`'s
epoch conjunct, and it is kept for the same reason: this is a safety rule, refusing is
the narrowing direction, and §7.3 is not a place to widen on a reachability argument.
Unlike that conjunct it is not unreachable at this layer, because `LoanConflicts` takes
both grants as arguments rather than reading them out of the map, and
`an_empty_installed_grant_still_conflicts` decides the case the reverse direction
exists for.

That fixture is what the two docstrings were standing in for. This paragraph cited the
asymmetry, `issue?_eq_none_of_empty` cited this paragraph, and neither named a state
either direction catches.

Two read-only grants over one range do not conflict, which is `sharedImmutable`
being a real state rather than a name. Nor do two **atomic-only** grants, which is
`atomicShared` being one: §7.3's issuance sentence is "unique loans prevent
*ordinary* conflicting authority from being issued", and this had no
ordinary/atomic distinction, so `issue?` prevented all conflicting authority and two
contexts could not share a word atomically at all.

The write probe is `rights.write`, the capability, not `rights.Permits .write`.
An atomic-only grant may modify the bytes and does not permit an ordinary write, and
§7.3's "at least one writer" is the first question.

**Refusing at issue is not the whole rule, and an earlier version of this comment
said it was.** "The point of uniqueness is that the conflicting pair never exists" is
false, and it was false for two reasons. One is closed: there was a second, unchecked
door, and review used it twice — once through a `grant` function and once through the
public field that function was deleted in favour of. `issue?` is the only way in now
and `MemoryState.mk` is private.

The other is not closable at issue time, and `Grass/Op/Step.lean`'s `refusalOf`
access-time rule is what covers it. Declaring an alias *after* two
non-conflicting grants are issued makes them conflict, with nothing re-examined, and
§7.5 makes declaring one a real transition. The pair that must never *act* is stopped
at access time by `Grass/Op/Step.lean`'s `refusalOf`, which is where the guarantee lives;
this is the cheaper check that stops the honest caller earlier.
-/
def LoanConflicts (state : MemoryState) (a b : AuthorityGrant) : Prop :=
  a.holder ≠ b.holder ∧
    (match state.grantSpan? a, state.grantSpan? b with
      | .ok aSpan, .ok bSpan => aSpan.Meets bSpan ∨ bSpan.Meets aSpan
      | _, _ => True) ∧
    (a.rights.write ∨ b.rights.write) ∧
    ¬ (a.rights.atomicOnly ∧ b.rights.atomicOnly)

instance (state : MemoryState) (a b : AuthorityGrant) :
    Decidable (state.LoanConflicts a b) :=
  by
    unfold LoanConflicts
    cases state.grantSpan? a <;> cases state.grantSpan? b <;> infer_instance

/--
`state.OwnedBy context provenance` holds when the context is one of the contexts the
provenance's root allocation was declared to belong to.

Reads the allocation table and not the grant map, which is the point: ownership is
not a grant, so it leaves no entry, and a rule that asked only the map could not
distinguish an owner with nothing lent from a stranger. Absent storage is owned by
nobody -- `List.any` on a missing lookup is `false` -- so this is not a door onto the
empty state.

Says nothing about liveness or epoch on purpose. `Live` is a separate question that
`authorityOf` asks first, and folding it in here would hide which of the two refused.
-/
def OwnedBy (state : MemoryState) (context : ContextId) (provenance : Provenance) : Prop :=
  (state.allocations.lookup provenance.root).any
    (fun record => record.owners.contains context) = true

instance (state : MemoryState) (context : ContextId) (provenance : Provenance) :
    Decidable (state.OwnedBy context provenance) :=
  inferInstanceAs (Decidable (_ = _))

/-- A lender passes on only a resolved backing span it owns or holds.
Candidate and source grants use the same whole-range resolver as access authority. -/
def MayLend (state : MemoryState) (grant : AuthorityGrant) : Prop :=
  match state.grantSpan? grant with
  | .error _ => False
  | .ok candidate =>
      state.grantEntries.any (fun entry =>
        entry.2.holder = grant.lender &&
          (match state.grantSpan? entry.2 with
          | .error _ => false
          | .ok held => decide (held.Contains candidate)) &&
          decide (entry.2.rights.GrantsAsGrant grant.rights)) = true ∨
        (state.OwnedBy grant.lender grant.provenance ∧
          (state.allocations.lookup grant.provenance.root).any
            (fun record => decide (record.permission.GrantsAsGrant grant.rights)) = true ∧
          (state.grantsOverSpan candidate).all
            (fun entry => entry.2.lender = grant.lender) = true)

instance (state : MemoryState) (grant : AuthorityGrant) : Decidable (state.MayLend grant) := by
  unfold MayLend
  split <;> infer_instance

/-- A malformed candidate grants no lending authority. -/
theorem not_mayLend_of_unresolved {state : MemoryState} {grant : AuthorityGrant}
    {failure : ResolveFailure} (h : state.grantSpan? grant = .error failure) :
    ¬ state.MayLend grant := by
  simp [MayLend, h]


/--
Issue a grant, or refuse.

`Option`, because every way of getting this wrong is silent otherwise, and review
found four of them.

**Reissue.** An earlier version was `grants.insert`, and `FiniteMap.insert` erases
any existing binding — so issuing twice under one identity returned the first grant
with no return, and exclusivity came back for bytes still borrowed. §3 says a return
consumes that exact identity; a reissue is a return nobody asked for. Worse, there
was a second, wholly unchecked door (`MemoryState.grant`) with the same erasing
behaviour, so one context could delete another's grant and write the bytes. That
door is gone: this is the only way a grant enters the map.

**Conflict.** §7.3 says unique loans prevent conflicting authority from being
issued. Nothing prevented issuing two overlapping write grants to different holders,
and each satisfied the access rule, so both could write the same bytes. The scan
covers **every kind of grant**: a `.frame` or profile-invented write grant is
conflicting authority on §7.3's terms, and scanning only loans applied
`LoanConflicts` — which has no kind clause of its own — to a strict subset of the
pairs it describes.

**A grant over nothing.** A grant whose range is empty conflicts at issue (both
`Meets` directions are tried there) and freezes nobody once installed, because an
empty extent meets no position. It is decoration with a refusal attached, so it is
refused instead — the same rule `AccessDescriptor.WellFormedIn.rangeNonEmpty`
applies to accesses.

**A grant over storage that is not there.** Review lent a write loan over a
provenance whose root the allocation table does not hold, aliased to a live one:
`issue?` accepted it, `grantsOver` did not see it, and the store committed. A grant
must be over live current-epoch storage, and its range must lie within the extent
its own provenance claims.

What this is **not** is the guarantee that no conflicting pair can act. Declaring an
alias after two non-conflicting grants are issued makes them conflict with nothing
re-examined, and §7.5 makes that a real transition. `Grass/Op/Step.lean`'s `refusalOf`
reads the map it finds; this is the cheaper check that stops the honest caller
earlier.

Refusing rather than overwriting or ignoring is `docs/FOUNDATION.md` law 8's
direction. Eight of the nine refusals are stated — `issue?_eq_none_of_reissued`,
`issue?_eq_none_of_empty`, `issue?_eq_none_of_not_live`,
`issue?_eq_none_of_not_nested`, `issue?_eq_none_of_wrong_extent`,
`issue?_eq_none_of_wrong_identity`, `issue?_eq_none_of_nothing_to_lend` and
`issue?_eq_none_of_conflict` — so a caller that cannot issue finds out which rule
stopped it. **The containment clause is the one with no theorem of its own**; it is
checked and not stated.

This sentence named the *extent* clause, which is the one gate here that does have a
theorem, and it went on naming it after the count beside it was repaired from "four of
the five" to "eight of the nine". A reviewer following it checked a clause that was
already covered and did not check the one that is not — which is why the enumeration
is now complete rather than partial: a list of four under a claim about eight leaves
the reader to guess which four are missing, and guessing wrong is the whole defect.
-/
def issue? (state : MemoryState) (id : GrantId) (grant : AuthorityGrant) :
    Option MemoryState :=
  if (state.grants.lookup id).isSome then Option.none
  else if grant.range.IsEmpty then Option.none
  else if ¬ state.Live grant.provenance then Option.none
  else if ¬ grant.provenance.Nested then Option.none
  else if ¬ state.RootExtentAgrees grant.provenance then Option.none
  else if ¬ state.RootIdentityAgrees grant.provenance then Option.none
  else if ¬ grant.provenance.extent.Contains grant.range then Option.none
  else if ¬ state.MayLend grant then Option.none
  else if state.grantEntries.any
      (fun entry => decide (state.LoanConflicts entry.2 grant))
    then Option.none
  else some { state with grants := state.grants.insert id grant }

/-- **A grant whose provenance misdescribes its storage is refused.** The two
comparisons `denialOf` makes for an access, at the door a grant comes through. -/
theorem issue?_eq_none_of_wrong_identity (state : MemoryState) (id : GrantId)
    (grant : AuthorityGrant) (h : ¬ state.RootIdentityAgrees grant.provenance) :
    state.issue? id grant = Option.none := by
  unfold issue?
  by_cases hfresh : (state.grants.lookup id).isSome = true
  · rw [if_pos hfresh]
  · rw [if_neg hfresh]
    by_cases hempty : grant.range.IsEmpty
    · rw [if_pos hempty]
    · rw [if_neg hempty]
      by_cases hlive : state.Live grant.provenance
      · rw [if_neg (by simpa using hlive)]
        by_cases hnest : grant.provenance.Nested
        · rw [if_neg (by simpa using hnest)]
          by_cases hext : state.RootExtentAgrees grant.provenance
          · rw [if_neg (by simpa using hext), if_pos (by simpa using h)]
          · rw [if_pos (by simpa using hext)]
        · rw [if_pos (by simpa using hnest)]
      · rw [if_pos (by simpa using hlive)]

/-- **A lender with nothing may not lend over held bytes.** -/
theorem issue?_eq_none_of_nothing_to_lend (state : MemoryState) (id : GrantId)
    (grant : AuthorityGrant) (h : ¬ state.MayLend grant) :
    state.issue? id grant = Option.none := by
  unfold issue?
  by_cases hfresh : (state.grants.lookup id).isSome = true
  · rw [if_pos hfresh]
  · rw [if_neg hfresh]
    by_cases hempty : grant.range.IsEmpty
    · rw [if_pos hempty]
    · rw [if_neg hempty]
      by_cases hlive : state.Live grant.provenance
      · rw [if_neg (by simpa using hlive)]
        by_cases hnest : grant.provenance.Nested
        · rw [if_neg (by simpa using hnest)]
          by_cases hext : state.RootExtentAgrees grant.provenance
          · rw [if_neg (by simpa using hext)]
            by_cases hid : state.RootIdentityAgrees grant.provenance
            · rw [if_neg (by simpa using hid)]
              by_cases hin : grant.provenance.extent.Contains grant.range
              · rw [if_neg (by simpa using hin), if_pos (by simpa using h)]
              · rw [if_pos (by simpa using hin)]
            · rw [if_pos (by simpa using hid)]
          · rw [if_pos (by simpa using hext)]
        · rw [if_pos (by simpa using hnest)]
      · rw [if_pos (by simpa using hlive)]

/-- An owner may lend a resolved range when no grant is outstanding over it. -/
theorem mayLend_of_unheld_of_owned {state : MemoryState} {grant : AuthorityGrant}
    {access : state.ResolvedAccess grant.provenance grant.range}
    (hresolve : state.resolveAccess? grant.provenance grant.range = .ok access)
    (h : ¬ state.AnyGrantOver grant.provenance grant.range)
    (howns : state.OwnedBy grant.lender grant.provenance)
    (hrights : (state.allocations.lookup grant.provenance.root).any
      (fun record => decide (record.permission.GrantsAsGrant grant.rights)) = true) :
    state.MayLend grant := by
  have hspan : state.grantSpan? grant = .ok access.span := by
    simp [grantSpan?, hresolve, Except.map]
  have hempty : state.grantsOverSpan access.span = [] := by
    simpa [AnyGrantOver, grantsOver, hresolve] using h
  unfold MayLend
  rw [hspan]
  exact Or.inr ⟨howns, hrights, by simp [hempty]⟩

/-- `not_mayLend_of_unheld_of_unowned` rules out lending a nonempty, unheld range
by a context that does not own it. -/
theorem not_mayLend_of_unheld_of_unowned {state : MemoryState} {grant : AuthorityGrant}
    (h : ¬ state.AnyGrantOver grant.provenance grant.range)
    (howns : ¬ state.OwnedBy grant.lender grant.provenance)
    (hne : ¬ grant.range.IsEmpty) : ¬ state.MayLend grant := by
  cases hresolve : state.resolveAccess? grant.provenance grant.range with
  | error failure => simp [MayLend, grantSpan?, hresolve, Except.map]
  | ok access =>
      have hspan : state.grantSpan? grant = .ok access.span := by
        simp [grantSpan?, hresolve, Except.map]
      unfold MayLend
      rw [hspan]
      rintro (hheld | ⟨howned, _, _⟩)
      · obtain ⟨entry, hmem, hcond⟩ := List.any_eq_true.1 hheld
        cases hentry : state.grantSpan? entry.2 with
        | error failure => simp [hentry] at hcond
        | ok held =>
            simp only [hentry, Bool.and_eq_true, decide_eq_true_eq] at hcond
            have hcontains : held.Contains access.span := hcond.1.2
            have hnonempty : ¬ access.span.range.IsEmpty := by
              change ¬ grant.range.IsEmpty
              exact hne
            have hmeets : held.Meets access.span :=
              ⟨hcontains.1, ByteRange.meets_of_contains hcontains.2 hnonempty⟩
            have hpresent : entry ∈ state.grantsOverSpan access.span := by
              apply List.mem_filter.2
              refine ⟨hmem, ?_⟩
              simp [hentry, hmeets]
            apply h
            simpa [AnyGrantOver, grantsOver, hresolve] using List.ne_nil_of_mem hpresent
      · exact howns howned

/-- **A grant over no bytes is refused.** It would conflict at issue with a live one
— `LoanConflicts`'s *forward* direction asks whether an installed grant covers the new
grant's start, which an empty range inside a live one satisfies — and freeze nobody
once installed, because an empty extent meets no position. Decoration with a refusal
attached.

This named "both directions", which is the wrong half of the rule: the reverse
direction is about an *installed* grant of no bytes, and this theorem is what makes
that state unreachable through the door. The two docstrings cited each other for why
the reverse direction exists, and `ByteRange.meets_comm_of_nonempty` is the fact
neither of them stated. -/
theorem issue?_eq_none_of_empty (state : MemoryState) (id : GrantId)
    (grant : AuthorityGrant) (h : grant.range.IsEmpty) :
    state.issue? id grant = Option.none := by
  unfold issue?
  by_cases hfresh : (state.grants.lookup id).isSome = true
  · rw [if_pos hfresh]
  · rw [if_neg hfresh, if_pos h]

/-- **A grant over dead, absent or stale-epoch storage is refused.** -/
theorem issue?_eq_none_of_not_live (state : MemoryState) (id : GrantId)
    (grant : AuthorityGrant) (h : ¬ state.Live grant.provenance) :
    state.issue? id grant = Option.none := by
  unfold issue?
  by_cases hfresh : (state.grants.lookup id).isSome = true
  · rw [if_pos hfresh]
  · rw [if_neg hfresh]
    by_cases hempty : grant.range.IsEmpty
    · rw [if_pos hempty]
    · rw [if_neg hempty, if_pos (by simpa using h)]

/-- **A grant whose provenance path is not nested is refused**, which every access
already had to satisfy through `AccessDescriptor.WellFormedIn.provenanceNested` and
no grant did — a single unnested step was a second way to claim any extent at all. -/
theorem issue?_eq_none_of_not_nested (state : MemoryState) (id : GrantId)
    (grant : AuthorityGrant) (h : ¬ grant.provenance.Nested) :
    state.issue? id grant = Option.none := by
  unfold issue?
  by_cases hfresh : (state.grants.lookup id).isSome = true
  · rw [if_pos hfresh]
  · rw [if_neg hfresh]
    by_cases hempty : grant.range.IsEmpty
    · rw [if_pos hempty]
    · rw [if_neg hempty]
      by_cases hlive : state.Live grant.provenance
      · rw [if_neg (by simpa using hlive), if_pos (by simpa using h)]
      · rw [if_pos (by simpa using hlive)]

/--
**A grant whose provenance misdescribes its allocation is refused.**

The clause that was self-certifying: `issue?` bounds a grant by
`grant.provenance.extent`, which the provenance itself supplies, and nothing compared
that to the allocation table. Review issued a write grant over four kilobytes of a
sixty-four-byte allocation, and it both authorized accesses and froze a context that
legitimately owned the larger storage it was aliased to.
-/
theorem issue?_eq_none_of_wrong_extent (state : MemoryState) (id : GrantId)
    (grant : AuthorityGrant) (h : ¬ state.RootExtentAgrees grant.provenance) :
    state.issue? id grant = Option.none := by
  unfold issue?
  by_cases hfresh : (state.grants.lookup id).isSome = true
  · rw [if_pos hfresh]
  · rw [if_neg hfresh]
    by_cases hempty : grant.range.IsEmpty
    · rw [if_pos hempty]
    · rw [if_neg hempty]
      by_cases hlive : state.Live grant.provenance
      · rw [if_neg (by simpa using hlive)]
        by_cases hnest : grant.provenance.Nested
        · rw [if_neg (by simpa using hnest), if_pos (by simpa using h)]
        · rw [if_pos (by simpa using hnest)]
      · rw [if_pos (by simpa using hlive)]

/-- **Conflicting authority is refused at issue.** -/
theorem issue?_eq_none_of_conflict (state : MemoryState) (id : GrantId)
    (grant : AuthorityGrant)
    (h : state.grantEntries.any
      (fun entry => decide (state.LoanConflicts entry.2 grant)) = true) :
    state.issue? id grant = Option.none := by
  unfold issue?
  by_cases hfresh : (state.grants.lookup id).isSome = true
  · rw [if_pos hfresh]
  · rw [if_neg hfresh]
    by_cases hempty : grant.range.IsEmpty
    · rw [if_pos hempty]
    · rw [if_neg hempty]
      by_cases hlive : state.Live grant.provenance
      · rw [if_neg (by simpa using hlive)]
        by_cases hnest : grant.provenance.Nested
        · rw [if_neg (by simpa using hnest)]
          by_cases hext : state.RootExtentAgrees grant.provenance
          · rw [if_neg (by simpa using hext)]
            by_cases hid : state.RootIdentityAgrees grant.provenance
            · rw [if_neg (by simpa using hid)]
              by_cases hin : grant.provenance.extent.Contains grant.range
              · rw [if_neg (by simpa using hin)]
                by_cases hlend : state.MayLend grant
                · rw [if_neg (by simpa using hlend), if_pos h]
                · rw [if_pos (by simpa using hlend)]
              · rw [if_pos (by simpa using hin)]
            · rw [if_pos (by simpa using hid)]
          · rw [if_pos (by simpa using hext)]
        · rw [if_pos (by simpa using hnest)]
      · rw [if_pos (by simpa using hlive)]

/-- Remove the grant an identity names, if this context may.

The holder or the lender, and nobody else. `docs/MEMORY_MODEL.md` §6's ABI call
profile "consumes the same loan identities to reconstruct local authority on a
conforming return", and the party consuming is the caller — so a holder-only check
left §6's return to a party that is not §6's, and for a loan to an external API agent,
which never executes a Grass step, made the return impossible for anyone. -/
def returnGrant? (state : MemoryState) (context : ContextId) (id : GrantId) :
    Option MemoryState :=
  match state.grants.lookup id with
  | some grant =>
      if grant.holder = context ∨ grant.lender = context then
        some { state with grants := state.grants.erase id }
      else Option.none
  | Option.none => Option.none

/-!
## Splitting and joining a grant

`docs/MEMORY_MODEL.md` §3 lists `split` and `join` as operations on the authority
map, and `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 has carried them as owed since
M3 opened. They are here now, in the module that owns the map, for the reason every
other mutator is: a caller that could build the parts itself would be a second door.

**Binary, at an offset, with the parts derived.** A list-of-parts door would have to
check that the parts cover the source's range and lie inside it, and a coverage
predicate over a list is a satisfaction condition with room to be empty — the class
of defect this branch found in §10's proof package. Two parts either side of an
offset need no coverage check, because coverage is arithmetic: the low part runs to
the boundary and the high part runs from it. An *n*-way split is *n* − 1 of these.

**Neither door re-runs `issue?`.** A split is not a new claim of authority, it is a
re-description of one the map already accepted, and re-running the door would refuse
correct splits: `MayLend`'s lender disjunct requires the lender to own the storage
and every grant outstanding to be its own, and a split's source is outstanding and
often lent by a context that owns nothing; its sublet disjunct bounds a holder, and a
split's lender need not hold anything. What justifies skipping the door is a theorem
rather than an argument — `splitGrant?_creates_no_authority` says the result
authorizes nothing the source did not, and `splitGrant?_preserves_authority` says it
authorizes everything the source did.

**What is not stated is an `↔` over the whole map**, because `Granted` ranges over
the raw entry list and a map carrying a shadowed duplicate under the source's
identity would lose that duplicate's authority to the `erase`. No such map can be
built — `mk` and the field are private and every mutator here goes through `insert`
and `erase` — but that is an invariant with no theorem, which
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 already records for `Exclusive`. The two
directions above hold of every map, shadowed or not.
-/

end MemoryState

namespace AuthorityGrant

/-- The part of `grant` below `boundary`. -/
def lowPart (grant : AuthorityGrant) (boundary : Nat) : AuthorityGrant :=
  { grant with range := ⟨grant.range.start, boundary - grant.range.start⟩ }

/-- The part of `grant` from `boundary` up. -/
def highPart (grant : AuthorityGrant) (boundary : Nat) : AuthorityGrant :=
  { grant with range := ⟨boundary, grant.range.stop - boundary⟩ }

/-- The parts carry everything except the range, which is the whole of what a split
changes: a split may not relabel, re-holder or re-rights a grant.
`Grass/Obligation/Delta.lean` learned that from the other side, where an unpinned
`kind` let a split relabel a live duty. Here the fields are not parameters at all,
so there is nothing to pin. -/
theorem parts_differ_only_in_range (grant : AuthorityGrant) (boundary : Nat) :
    (grant.lowPart boundary).kind = grant.kind ∧
    (grant.lowPart boundary).holder = grant.holder ∧
    (grant.lowPart boundary).lender = grant.lender ∧
    (grant.lowPart boundary).provenance = grant.provenance ∧
    (grant.lowPart boundary).rights = grant.rights ∧
    (grant.highPart boundary).kind = grant.kind ∧
    (grant.highPart boundary).holder = grant.holder ∧
    (grant.highPart boundary).lender = grant.lender ∧
    (grant.highPart boundary).provenance = grant.provenance ∧
    (grant.highPart boundary).rights = grant.rights :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Each part lies within the source. This is what makes a split not a claim. -/
theorem lowPart_contained {grant : AuthorityGrant} {boundary : Nat}
    (h : boundary ≤ grant.range.stop) :
    grant.range.Contains (grant.lowPart boundary).range := by
  have h' : boundary ≤ grant.range.start + grant.range.size := h
  refine ⟨Nat.le_refl _, ?_⟩
  simp only [lowPart, ByteRange.stop]
  omega

theorem highPart_contained {grant : AuthorityGrant} {boundary : Nat}
    (hlow : grant.range.start ≤ boundary) (hhigh : boundary ≤ grant.range.stop) :
    grant.range.Contains (grant.highPart boundary).range := by
  have h' : boundary ≤ grant.range.start + grant.range.size := hhigh
  refine ⟨hlow, ?_⟩
  simp only [highPart, ByteRange.stop]
  omega

/-- The grant a join produces: the low one, stretched over both. -/
def joined (low high : AuthorityGrant) : AuthorityGrant :=
  { low with range := ⟨low.range.start, low.range.size + high.range.size⟩ }

/-- And together they cover it: every offset the source covers is covered by one of
them. No predicate checks this; it is arithmetic. -/
theorem covered_by_part {grant : AuthorityGrant} {boundary offset : Nat}
    (h : grant.range.Covers offset) :
    (grant.lowPart boundary).range.Covers offset ∨
      (grant.highPart boundary).range.Covers offset := by
  have h' : grant.range.start ≤ offset ∧ offset < grant.range.start + grant.range.size := h
  rcases Nat.lt_or_ge offset boundary with hcase | hcase
  · refine Or.inl ⟨h'.1, ?_⟩
    simp only [lowPart, ByteRange.stop]
    omega
  · refine Or.inr ⟨hcase, ?_⟩
    simp only [highPart, ByteRange.stop]
    omega

end AuthorityGrant

namespace MemoryState

/-- A covered backing offset of a checked join is covered by one of its two checked
source spans. -/
theorem joined_grantSpan_covers_source {state : MemoryState}
    {low high : AuthorityGrant} {joinedSpan : Coordinates.BackingSpan} {offset : Nat}
    (hmatch : low = { high with range := low.range })
    (hadjacent : low.range.stop = high.range.start)
    (hjoined : state.grantSpan? (low.joined high) = .ok joinedSpan)
    (hcovers : joinedSpan.range.Covers offset) :
    (∃ lowSpan, state.grantSpan? low = .ok lowSpan ∧
      lowSpan.backing = joinedSpan.backing ∧ lowSpan.range.Covers offset) ∨
    (∃ highSpan, state.grantSpan? high = .ok highSpan ∧
      highSpan.backing = joinedSpan.backing ∧ highSpan.range.Covers offset) := by
  unfold grantSpan? at hjoined ⊢
  cases hj : state.resolveAccess? (low.joined high).provenance
      (low.joined high).range with
  | error failure => rw [hj] at hjoined; contradiction
  | ok joinedAccess =>
      rw [hj] at hjoined
      injection hjoined with hjoinedSpan
      have hlowContains : (low.joined high).range.Contains low.range := by
        simp only [AuthorityGrant.joined, ByteRange.Contains, ByteRange.stop]
        omega
      let lowAccess := joinedAccess.restrict hlowContains
      have hlowResolve := resolveAccess?_eq_ok lowAccess
      have hlowResolve' : state.resolveAccess? low.provenance low.range =
          .ok lowAccess := by
        simpa [AuthorityGrant.joined] using hlowResolve
      have hprov : low.provenance = high.provenance := by rw [hmatch]
      have hhighContains : (low.joined high).range.Contains high.range := by
        simp only [AuthorityGrant.joined, ByteRange.Contains, ByteRange.stop]
        simp only [ByteRange.stop] at hadjacent
        omega
      have joinedAccessHigh : state.ResolvedAccess high.provenance
          (low.joined high).range := by
        rw [← hprov]
        exact joinedAccess
      let highAccess := joinedAccessHigh.restrict hhighContains
      have hhighResolve := resolveAccess?_eq_ok highAccess
      rw [hlowResolve', hhighResolve]
      have hjcovers : joinedAccess.span.range.Covers offset := by
        rw [hjoinedSpan]
        exact hcovers
      have hbackingJoined : joinedAccess.span.backing = joinedSpan.backing :=
        congrArg Coordinates.BackingSpan.backing hjoinedSpan
      have hlowAllocation : lowAccess.allocation = joinedAccess.allocation := rfl
      have hadjacent' : low.range.start + low.range.size = high.range.start := by
        simpa [ByteRange.stop] using hadjacent
      have hroot : low.provenance.root = high.provenance.root :=
        congrArg Provenance.root hprov
      have hhighAllocation : highAccess.allocation = joinedAccess.allocation := by
        apply Option.some.inj
        calc
          some highAccess.allocation =
              state.allocations.lookup high.provenance.root := highAccess.allocationLookup.symm
          _ = state.allocations.lookup low.provenance.root := by rw [hroot]
          _ = some joinedAccess.allocation := joinedAccess.allocationLookup
      rcases Nat.lt_or_ge offset (joinedAccess.allocation.origin + low.range.stop) with
        hbefore | hafter
      · left
        refine ⟨lowAccess.span, rfl, hbackingJoined, ?_⟩
        simp only [ResolvedAccess.span, Coordinates.ResolvedRange.span,
          AllocationRecord.mapping, Coordinates.Mapping.span, ByteRange.shift,
          AuthorityGrant.joined, ByteRange.covers_def] at hjcovers ⊢
        rw [hlowAllocation]
        omega
      · right
        refine ⟨highAccess.span, rfl, ?_, ?_⟩
        · unfold ResolvedAccess.span Coordinates.ResolvedRange.span
          rw [hhighAllocation]
          exact hbackingJoined
        · simp only [ResolvedAccess.span, Coordinates.ResolvedRange.span,
            AllocationRecord.mapping, Coordinates.Mapping.span, ByteRange.shift,
            AuthorityGrant.joined, ByteRange.covers_def] at hjcovers ⊢
          rw [hhighAllocation]
          omega

/-- A covered backing offset of a checked source grant is covered by one of the
two checked spans produced by a valid split. -/
theorem split_grantSpan_covers_part {state : MemoryState}
    {grant : AuthorityGrant} {boundary offset : Nat}
    {sourceSpan : Coordinates.BackingSpan}
    (hstart : grant.range.start < boundary) (hstop : boundary < grant.range.stop)
    (hsource : state.grantSpan? grant = .ok sourceSpan)
    (hcovers : sourceSpan.range.Covers offset) :
    (∃ lowSpan, state.grantSpan? (grant.lowPart boundary) = .ok lowSpan ∧
      lowSpan.backing = sourceSpan.backing ∧ lowSpan.range.Covers offset) ∨
    (∃ highSpan, state.grantSpan? (grant.highPart boundary) = .ok highSpan ∧
      highSpan.backing = sourceSpan.backing ∧ highSpan.range.Covers offset) := by
  unfold grantSpan? at hsource ⊢
  cases hs : state.resolveAccess? grant.provenance grant.range with
  | error failure => rw [hs] at hsource; contradiction
  | ok sourceAccess =>
      rw [hs] at hsource
      injection hsource with hsourceSpan
      let lowAccess := sourceAccess.restrict
        (AuthorityGrant.lowPart_contained (Nat.le_of_lt hstop))
      let highAccess := sourceAccess.restrict
        (AuthorityGrant.highPart_contained (Nat.le_of_lt hstart) (Nat.le_of_lt hstop))
      have hlowResolve := resolveAccess?_eq_ok lowAccess
      have hhighResolve := resolveAccess?_eq_ok highAccess
      have hlowResolve' : state.resolveAccess? (grant.lowPart boundary).provenance
          (grant.lowPart boundary).range = .ok lowAccess := by
        simpa [AuthorityGrant.lowPart] using hlowResolve
      have hhighResolve' : state.resolveAccess? (grant.highPart boundary).provenance
          (grant.highPart boundary).range = .ok highAccess := by
        simpa [AuthorityGrant.highPart] using hhighResolve
      rw [hlowResolve', hhighResolve']
      have hsourceCovers : sourceAccess.span.range.Covers offset := by
        rw [hsourceSpan]
        exact hcovers
      have hbacking : sourceAccess.span.backing = sourceSpan.backing :=
        congrArg Coordinates.BackingSpan.backing hsourceSpan
      have hlowAllocation : lowAccess.allocation = sourceAccess.allocation := rfl
      have hhighAllocation : highAccess.allocation = sourceAccess.allocation := rfl
      have hstop' : boundary < grant.range.start + grant.range.size := by
        simpa [ByteRange.stop] using hstop
      rcases Nat.lt_or_ge offset (sourceAccess.allocation.origin + boundary) with
        hlow | hhigh
      · left
        refine ⟨lowAccess.span, rfl, hbacking, ?_⟩
        simp only [ResolvedAccess.span, Coordinates.ResolvedRange.span,
          AllocationRecord.mapping, Coordinates.Mapping.span, ByteRange.shift,
          AuthorityGrant.lowPart, ByteRange.covers_def] at hsourceCovers ⊢
        rw [hlowAllocation]
        omega
      · right
        refine ⟨highAccess.span, rfl, hbacking, ?_⟩
        simp only [ResolvedAccess.span, Coordinates.ResolvedRange.span,
          AllocationRecord.mapping, Coordinates.Mapping.span, ByteRange.shift,
          AuthorityGrant.highPart, ByteRange.covers_def, ByteRange.stop] at hsourceCovers ⊢
        rw [hhighAllocation]
        omega

/-- The map a successful split leaves. Private: it names the private field, and the
public theorems below speak of `splitGrant?`'s result rather than of this. -/
private def splitMap (state : MemoryState) (id low high : GrantId) (boundary : Nat)
    (grant : AuthorityGrant) : FiniteMap GrantId AuthorityGrant :=
  ((state.grants.erase id).insert low (grant.lowPart boundary)).insert
    high (grant.highPart boundary)

/-!
### What a grants-only update leaves alone

`SharesBytes`, `CurrentEpoch` and `Live` read allocation/backing metadata only, so
a state that differs only in `grants` agrees with the original on all three.
-/

private theorem sharesBytes_grants (state : MemoryState)
    (g : FiniteMap GrantId AuthorityGrant) (a b : AllocId) :
    SharesBytes { state with grants := g } a b ↔ state.SharesBytes a b :=
  Iff.rfl

/-- Liveness is a fact about the allocation table, so replacing the grant map leaves
it alone. The twin of `currentEpoch_grants`, needed now that `AuthorizedAt` consults
`Live` rather than only the epoch. -/
private theorem live_grants (state : MemoryState)
    (g : FiniteMap GrantId AuthorityGrant) (provenance : Provenance) :
    Live { state with grants := g } provenance ↔ state.Live provenance := Iff.rfl

private theorem currentEpoch_grants (state : MemoryState)
    (g : FiniteMap GrantId AuthorityGrant) (provenance : Provenance) :
    CurrentEpoch { state with grants := g } provenance ↔ state.CurrentEpoch provenance :=
  Iff.rfl


/--
Split one outstanding grant into two, at `boundary`.

The source identity is consumed and the two parts are recorded under fresh
identities, which is §3's return-consumes-that-exact-identity discipline applied to a
split: a part reusing the source's identity would make "the source is gone" and "the
part is here" the same fact, and `Grass/Obligation/Delta.lean` shows what that costs
when the two are conflated.

Refused when the source is unknown, when either part identity is taken (which
includes the source's own, since it is taken), when the two part identities are the
same, and when `boundary` is not strictly inside the source's range — an `⟨start, 0⟩`
part would be a grant `issue?` refuses to issue, so a split may not manufacture one.
-/
def splitGrant? (state : MemoryState) (id low high : GrantId) (boundary : Nat) :
    Option MemoryState :=
  (state.grants.lookup id).bind fun grant =>
    match state.grantSpan? grant with
    | .error _ => Option.none
    | .ok _ =>
      if low = high then Option.none
      else if (state.grants.lookup low).isSome then Option.none
      else if (state.grants.lookup high).isSome then Option.none
      else if ¬ grant.range.start < boundary then Option.none
      else if ¬ boundary < grant.range.stop then Option.none
      else some { state with grants := state.splitMap id low high boundary grant }

/-- **An unknown identity cannot be split**, which `splitGrant?` refuses before it
looks at anything else. -/
theorem splitGrant?_eq_none_of_unknown {state : MemoryState} {id low high : GrantId}
    {boundary : Nat} (h : state.grantAt? id = Option.none) :
    state.splitGrant? id low high boundary = Option.none := by
  unfold splitGrant?
  rw [show state.grants.lookup id = Option.none from h, Option.bind_none]

/-- **A part may not land on a taken identity**, the source's own included. -/
theorem splitGrant?_eq_none_of_taken {state : MemoryState} {id low high : GrantId}
    {boundary : Nat} (_hne : low ≠ high) (h : (state.grantAt? low).isSome) :
    state.splitGrant? id low high boundary = Option.none := by
  change (state.grants.lookup low).isSome = true at h
  unfold splitGrant?
  cases hlook : state.grants.lookup id with
  | none => rfl
  | some grant =>
    cases hlow : state.grants.lookup low with
    | none => simp [hlow] at h
    | some value => cases hspan : state.grantSpan? grant <;> simp [hspan]

/-- **The two parts may not share an identity**, which would record one part and
lose the other. -/
theorem splitGrant?_eq_none_of_same_identity {state : MemoryState} {id low : GrantId}
    {boundary : Nat} : state.splitGrant? id low low boundary = Option.none := by
  unfold splitGrant?
  cases hlook : state.grants.lookup id with
  | none => rfl
  | some grant => cases hspan : state.grantSpan? grant <;> simp [hspan]

/-- **A boundary outside the source is refused**, in either direction, because a part
of size zero is a grant `issue?` would not issue. -/
theorem splitGrant?_eq_none_of_boundary_low {state : MemoryState} {id low high : GrantId}
    {boundary : Nat} {grant : AuthorityGrant} (hat : state.grantAt? id = some grant)
    (hne : low ≠ high) (hlow : (state.grantAt? low).isSome = false)
    (hhigh : (state.grantAt? high).isSome = false)
    (h : ¬ grant.range.start < boundary) :
    state.splitGrant? id low high boundary = Option.none := by
  have hlow' : (state.grants.lookup low).isSome = false := hlow
  have hhigh' : (state.grants.lookup high).isSome = false := hhigh
  unfold splitGrant?
  rw [show state.grants.lookup id = some grant from hat, Option.bind_some]
  cases hspan : state.grantSpan? grant <;> simp_all

theorem splitGrant?_eq_none_of_boundary_high {state : MemoryState} {id low high : GrantId}
    {boundary : Nat} {grant : AuthorityGrant} (hat : state.grantAt? id = some grant)
    (hne : low ≠ high) (hlow : (state.grantAt? low).isSome = false)
    (hhigh : (state.grantAt? high).isSome = false)
    (h : ¬ boundary < grant.range.stop) :
    state.splitGrant? id low high boundary = Option.none := by
  have hlow' : (state.grants.lookup low).isSome = false := hlow
  have hhigh' : (state.grants.lookup high).isSome = false := hhigh
  unfold splitGrant?
  rw [show state.grants.lookup id = some grant from hat, Option.bind_some]
  cases hspan : state.grantSpan? grant <;> simp_all

/-- What a successful split produced, and the five facts its guards established. -/
private theorem splitGrant?_eq {state next : MemoryState} {id low high : GrantId}
    {boundary : Nat} {grant : AuthorityGrant}
    (h : state.splitGrant? id low high boundary = some next)
    (hat : state.grantAt? id = some grant) :
    next = { state with grants := state.splitMap id low high boundary grant } ∧
      low ≠ high ∧ (state.grants.lookup low).isSome = false ∧
      (state.grants.lookup high).isSome = false ∧
      grant.range.start < boundary ∧ boundary < grant.range.stop := by
  unfold splitGrant? at h
  rw [show state.grants.lookup id = some grant from hat, Option.bind_some] at h
  cases hspan : state.grantSpan? grant <;> simp [hspan] at h
  next span =>
    rcases h with ⟨hne, hlow, hhigh, hstart, hstop, heq⟩
    exact ⟨heq.symm, hne, by simpa using hlow, by simpa using hhigh,
      hstart, hstop⟩

/-- **A split consumes the source and records both parts.** -/
theorem splitGrant?_yields_the_parts {state next : MemoryState} {id low high : GrantId}
    {boundary : Nat} {grant : AuthorityGrant}
    (h : state.splitGrant? id low high boundary = some next)
    (hat : state.grantAt? id = some grant) :
    next.grantAt? low = some (grant.lowPart boundary) ∧
    next.grantAt? high = some (grant.highPart boundary) ∧
    next.grantAt? id = Option.none := by
  obtain ⟨hnext, hne, hlow, hhigh, _, _⟩ := splitGrant?_eq h hat
  have hatl : state.grants.lookup id = some grant := hat
  have hidlow : id ≠ low := by
    intro hid
    subst hid
    rw [hatl] at hlow
    simp at hlow
  have hidhigh : id ≠ high := by
    intro hid
    subst hid
    rw [hatl] at hhigh
    simp at hhigh
  subst hnext
  refine ⟨?_, ?_, ?_⟩
  · show (state.splitMap id low high boundary grant).lookup low = _
    unfold splitMap
    rw [FiniteMap.lookup_insert_ne _ hne, FiniteMap.lookup_insert_self]
  · show (state.splitMap id low high boundary grant).lookup high = _
    unfold splitMap
    rw [FiniteMap.lookup_insert_self]
  · show (state.splitMap id low high boundary grant).lookup id = _
    unfold splitMap
    rw [FiniteMap.lookup_insert_ne _ hidhigh, FiniteMap.lookup_insert_ne _ hidlow,
      FiniteMap.lookup_erase_self]

/-- A split leaves every other identity alone. -/
theorem splitGrant?_other {state next : MemoryState} {id low high other : GrantId}
    {boundary : Nat} {grant : AuthorityGrant}
    (h : state.splitGrant? id low high boundary = some next)
    (hat : state.grantAt? id = some grant) (hid : other ≠ id) (hlow : other ≠ low)
    (hhigh : other ≠ high) : next.grantAt? other = state.grantAt? other := by
  obtain ⟨hnext, _, _, _, _, _⟩ := splitGrant?_eq h hat
  subst hnext
  show (state.splitMap id low high boundary grant).lookup other = _
  unfold splitMap
  rw [FiniteMap.lookup_insert_ne _ hhigh, FiniteMap.lookup_insert_ne _ hlow,
    FiniteMap.lookup_erase_ne _ hid]
  rfl

/-- The map a successful join leaves. Private, for the reason `splitMap` is. -/
private def joinMap (state : MemoryState) (low high into : GrantId)
    (grant : AuthorityGrant) : FiniteMap GrantId AuthorityGrant :=
  ((state.grants.erase low).erase high).insert into grant

/--
Join two adjacent grants into one.

The inverse of `splitGrant?`, and the checks are the ones that make it an inverse
rather than an accumulation. Both sources must be outstanding, the target identity
must be free, the two sources must be distinct identities, and — the clause that
carries the weight — the two grants must be *equal except for their ranges*, with
the low one's range ending exactly where the high one's begins.

**Equality of everything but the range is `decide`d, not spot-checked.**
`AuthorityGrant` derives `DecidableEq`, so `low.grant = { high.grant with range := … }`
compares every field there is, and a field added later is compared without this door
being edited. A door listing the fields it cares about is the shape that let
`Grass/Obligation/Delta.lean` relabel a duty: it pinned protocol and owner because
those were the fields someone thought of.

**Adjacency, not overlap or a gap.** A gap would join authority over bytes neither
source covered, which is the creation `joinGrants?_creates_no_authority` forbids. An
overlap cannot happen between two grants this map holds for the same holder over the
same storage — `LoanConflicts` does not forbid it, since conflict needs distinct
holders — so it is refused here rather than assumed away.
-/
def joinGrants? (state : MemoryState) (low high into : GrantId) :
    Option MemoryState :=
  (state.grants.lookup low).bind fun lowGrant =>
    (state.grants.lookup high).bind fun highGrant =>
      if low = high then Option.none
      else if (state.grants.lookup into).isSome then Option.none
      else if lowGrant ≠ { highGrant with range := lowGrant.range } then Option.none
      else if lowGrant.range.stop ≠ highGrant.range.start then Option.none
      else match state.grantSpan? (lowGrant.joined highGrant) with
        | .error _ => Option.none
        | .ok _ =>
          some { state with grants := state.joinMap low high into (lowGrant.joined highGrant) }

/-- **An unknown source cannot be joined**, from either side, which `joinGrants?`
refuses in the `bind` before any check runs. -/
theorem joinGrants?_eq_none_of_unknown_low {state : MemoryState} {low high into : GrantId}
    (h : state.grantAt? low = Option.none) :
    state.joinGrants? low high into = Option.none := by
  unfold joinGrants?
  rw [show state.grants.lookup low = Option.none from h, Option.bind_none]

theorem joinGrants?_eq_none_of_unknown_high {state : MemoryState} {low high into : GrantId}
    (h : state.grantAt? high = Option.none) :
    state.joinGrants? low high into = Option.none := by
  have h' : state.grants.lookup high = Option.none := h
  unfold joinGrants?
  cases hlook : state.grants.lookup low with
  | none => rfl
  | some lowGrant => rw [Option.bind_some, h', Option.bind_none]

/-- **A join may not land on a taken identity.** -/
theorem joinGrants?_eq_none_of_taken {state : MemoryState} {low high into : GrantId}
    {lowGrant highGrant : AuthorityGrant} (hlow : state.grantAt? low = some lowGrant)
    (hhigh : state.grantAt? high = some highGrant) (hne : low ≠ high)
    (h : (state.grantAt? into).isSome) :
    state.joinGrants? low high into = Option.none := by
  have hlow' : state.grants.lookup low = some lowGrant := hlow
  have hhigh' : state.grants.lookup high = some highGrant := hhigh
  have h' : (state.grants.lookup into).isSome = true := h
  unfold joinGrants?
  rw [hlow', Option.bind_some, hhigh', Option.bind_some, if_neg hne, if_pos h']

/-- **Two grants differing in anything but their range may not be joined**, which is
the whole of the equality this door checks. -/
theorem joinGrants?_eq_none_of_mismatch {state : MemoryState} {low high into : GrantId}
    {lowGrant highGrant : AuthorityGrant} (hlow : state.grantAt? low = some lowGrant)
    (hhigh : state.grantAt? high = some highGrant) (hne : low ≠ high)
    (hinto : (state.grantAt? into).isSome = false)
    (h : lowGrant ≠ { highGrant with range := lowGrant.range }) :
    state.joinGrants? low high into = Option.none := by
  have hlow' : state.grants.lookup low = some lowGrant := hlow
  have hhigh' : state.grants.lookup high = some highGrant := hhigh
  have hinto' : (state.grants.lookup into).isSome = false := hinto
  unfold joinGrants?
  rw [hlow', Option.bind_some, hhigh', Option.bind_some, if_neg hne,
    if_neg (by simpa using hinto'), if_pos h]

/-- **And two grants that do not meet may not be joined**, whether they gap or
overlap. -/
theorem joinGrants?_eq_none_of_not_adjacent {state : MemoryState} {low high into : GrantId}
    {lowGrant highGrant : AuthorityGrant} (hlow : state.grantAt? low = some lowGrant)
    (hhigh : state.grantAt? high = some highGrant) (hne : low ≠ high)
    (hinto : (state.grantAt? into).isSome = false)
    (hmatch : lowGrant = { highGrant with range := lowGrant.range })
    (h : lowGrant.range.stop ≠ highGrant.range.start) :
    state.joinGrants? low high into = Option.none := by
  have hlow' : state.grants.lookup low = some lowGrant := hlow
  have hhigh' : state.grants.lookup high = some highGrant := hhigh
  have hinto' : (state.grants.lookup into).isSome = false := hinto
  unfold joinGrants?
  rw [hlow', Option.bind_some, hhigh', Option.bind_some, if_neg hne,
    if_neg (by simpa using hinto'), if_neg (by simpa using hmatch), if_pos h]

/-- What a successful join produced, and the four facts its guards established. -/
private theorem joinGrants?_eq {state next : MemoryState} {low high into : GrantId}
    {lowGrant highGrant : AuthorityGrant}
    (h : state.joinGrants? low high into = some next)
    (hlow : state.grantAt? low = some lowGrant)
    (hhigh : state.grantAt? high = some highGrant) :
    next = { state with grants := state.joinMap low high into (lowGrant.joined highGrant) } ∧
      low ≠ high ∧ (state.grants.lookup into).isSome = false ∧
      lowGrant = { highGrant with range := lowGrant.range } ∧
      lowGrant.range.stop = highGrant.range.start := by
  have hlow' : state.grants.lookup low = some lowGrant := hlow
  have hhigh' : state.grants.lookup high = some highGrant := hhigh
  unfold joinGrants? at h
  rw [hlow', Option.bind_some, hhigh', Option.bind_some] at h
  split at h
  · exact absurd h (by simp)
  · next hne =>
    split at h
    · exact absurd h (by simp)
    · next hinto =>
      split at h
      · exact absurd h (by simp)
      · next hmatch =>
        split at h
        · exact absurd h (by simp)
        · next hadjacent =>
          cases hspan : state.grantSpan? (lowGrant.joined highGrant) with
          | error failure => rw [hspan] at h; contradiction
          | ok span =>
              rw [hspan] at h
              injection h with h
              exact ⟨h.symm, hne, by simpa using hinto, by simpa using hmatch,
                by simpa using hadjacent⟩

/-- Success at the join door records that the combined envelope resolves before
either source identity is consumed. -/
theorem joinGrants?_resolves_join {state next : MemoryState} {low high into : GrantId}
    {lowGrant highGrant : AuthorityGrant}
    (h : state.joinGrants? low high into = some next)
    (hlow : state.grantAt? low = some lowGrant)
    (hhigh : state.grantAt? high = some highGrant) :
    ∃ span, state.grantSpan? (lowGrant.joined highGrant) = .ok span := by
  have hlow' : state.grants.lookup low = some lowGrant := hlow
  have hhigh' : state.grants.lookup high = some highGrant := hhigh
  unfold joinGrants? at h
  rw [hlow', Option.bind_some, hhigh', Option.bind_some] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · cases hspan : state.grantSpan? (lowGrant.joined highGrant) with
          | error failure => rw [hspan] at h; contradiction
          | ok span => exact ⟨span, rfl⟩

/-- **A join consumes both sources and records the joined grant.** -/
theorem joinGrants?_yields_the_join {state next : MemoryState} {low high into : GrantId}
    {lowGrant highGrant : AuthorityGrant}
    (h : state.joinGrants? low high into = some next)
    (hlow : state.grantAt? low = some lowGrant)
    (hhigh : state.grantAt? high = some highGrant) :
    next.grantAt? into = some (lowGrant.joined highGrant) ∧
    next.grantAt? low = Option.none ∧ next.grantAt? high = Option.none := by
  obtain ⟨hnext, hne, hinto, _, _⟩ := joinGrants?_eq h hlow hhigh
  have hlow' : state.grants.lookup low = some lowGrant := hlow
  have hhigh' : state.grants.lookup high = some highGrant := hhigh
  have hintolow : into ≠ low := by
    intro hid
    subst hid
    rw [hlow'] at hinto
    simp at hinto
  have hintohigh : into ≠ high := by
    intro hid
    subst hid
    rw [hhigh'] at hinto
    simp at hinto
  subst hnext
  refine ⟨?_, ?_, ?_⟩
  · show (state.joinMap low high into (lowGrant.joined highGrant)).lookup into
      = _
    unfold joinMap
    rw [FiniteMap.lookup_insert_self]
  · show (state.joinMap low high into (lowGrant.joined highGrant)).lookup low
      = _
    unfold joinMap
    rw [FiniteMap.lookup_insert_ne _ (Ne.symm hintolow), FiniteMap.lookup_erase_ne _ hne,
      FiniteMap.lookup_erase_self]
  · show (state.joinMap low high into (lowGrant.joined highGrant)).lookup high
      = _
    unfold joinMap
    rw [FiniteMap.lookup_insert_ne _ (Ne.symm hintohigh), FiniteMap.lookup_erase_self]

/--
Hand a grant on to another context.

`docs/MEMORY_MODEL.md` §3's fifth authority state is "transferred or unavailable", and
§7.4 makes transfer real: "acquire operations may transfer protected memory
authority". Until now `unavailable` derived from liveness and epoch and *nothing*
represented a transfer, which `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 recorded as
owed.

**The identity is kept, unlike a split's.** §6 has the lender "consume the same loan
identities to reconstruct local authority on a conforming return", so the identity a
lender lent must still be the identity it returns; a transfer that reissued under a
fresh identity would strand the lender's return. A split consumes its source
precisely because it is *not* the same authority afterwards.

**Only the holder may transfer**, which is what `actor` is for. The lender's power
over an outstanding grant is `returnGrant?`, and nothing in §3 or §6 gives a lender
the power to redirect a loan to a third party while it is out.

**Conflict is re-checked, and this is the check with teeth.** `LoanConflicts` needs
*distinct* holders, so one context may hold two write grants over the same bytes —
`issue?` accepts the second, correctly, because a context does not conflict with
itself. Transfer one of them to a third context and that pair becomes a conflicting
pair, which is the §7.3 violation a door that only checked authorization would
create. `Tests/Memory/Loans.lean`'s `transferring_into_a_conflict_is_refused` is that
state.

**A self-transfer is refused** rather than treated as a no-op: it changes nothing, so
a caller asking for one has made a mistake, and [FOUNDATION.md](../../docs/FOUNDATION.md)
law 8 says reject rather than approximate.

**The recipient is not checked against any context set, and the obligation ledger's
transfer clause does check its own.** `LedgerDelta.Applicable` requires
`newOwner ∈ contexts`; this door requires nothing of the recipient. The asymmetry is
deliberate and was undocumented, which review noted rather than reported. A duty is
discharged by running, so a duty handed to a context that never runs is a duty nobody
can discharge — unrecoverable, and `LedgerDelta.Applicable` is what refuses it. A grant is
not: `returnGrant?` lets the *lender* clear it, so a grant handed to a context that
never steps can still be taken back, and `returnGrant?`'s own docstring makes a
non-stepping holder deliberate ("an external API agent, which never executes a Grass
step"). Requiring a context set here would refuse exactly the case that door exists for.
-/
def transferGrant? (state : MemoryState) (actor : ContextId) (id : GrantId)
    (recipient : ContextId) : Option MemoryState :=
  (state.grants.lookup id).bind fun grant =>
    match state.grantSpan? grant with
    | .error _ => Option.none
    | .ok _ =>
      if grant.holder ≠ actor then Option.none
      else if recipient = actor then Option.none
      else if state.grantEntries.any (fun entry =>
          entry.1 ≠ id && decide (state.LoanConflicts entry.2 { grant with holder := recipient }))
        then Option.none
      else some { state with grants := state.grants.insert id { grant with holder := recipient } }

/-- **A context that does not hold it may not transfer it**, and that includes the
lender, whose power over an outstanding grant is `returnGrant?`. -/
theorem transferGrant?_eq_none_of_not_holder {state : MemoryState} {actor : ContextId}
    {id : GrantId} {recipient : ContextId} {grant : AuthorityGrant}
    (hat : state.grantAt? id = some grant) (h : grant.holder ≠ actor) :
    state.transferGrant? actor id recipient = Option.none := by
  have hat' : state.grants.lookup id = some grant := hat
  unfold transferGrant?
  rw [hat', Option.bind_some]
  cases state.grantSpan? grant <;> simp [h]

/-- **An unknown identity cannot be transferred**, which `transferGrant?` refuses in
the `bind` before any check runs. -/
theorem transferGrant?_eq_none_of_unknown {state : MemoryState} {actor : ContextId}
    {id : GrantId} {recipient : ContextId} (h : state.grantAt? id = Option.none) :
    state.transferGrant? actor id recipient = Option.none := by
  have h' : state.grants.lookup id = Option.none := h
  unfold transferGrant?
  rw [h', Option.bind_none]

/-- **A self-transfer is refused**, because it changes nothing. -/
theorem transferGrant?_eq_none_of_self {state : MemoryState} {actor : ContextId}
    {id : GrantId} {grant : AuthorityGrant} (hat : state.grantAt? id = some grant)
    (hholder : grant.holder = actor) :
    state.transferGrant? actor id actor = Option.none := by
  have hat' : state.grants.lookup id = some grant := hat
  unfold transferGrant?
  rw [hat', Option.bind_some]
  cases state.grantSpan? grant <;> simp [hholder]

/-- What a successful transfer produced, and the three facts its guards
established. -/
private theorem transferGrant?_eq {state next : MemoryState} {actor : ContextId}
    {id : GrantId} {recipient : ContextId} {grant : AuthorityGrant}
    (h : state.transferGrant? actor id recipient = some next)
    (hat : state.grantAt? id = some grant) :
    next = { state with grants := state.grants.insert id { grant with holder := recipient } } ∧
      grant.holder = actor ∧ recipient ≠ actor ∧
      state.grantEntries.any (fun entry =>
        entry.1 ≠ id && decide (state.LoanConflicts entry.2
          { grant with holder := recipient })) = false := by
  have hat' : state.grants.lookup id = some grant := hat
  unfold transferGrant? at h
  rw [hat', Option.bind_some] at h
  cases hspan : state.grantSpan? grant <;> simp [hspan] at h
  next span =>
    rcases h with ⟨hholder, hself, hconflict, heq⟩
    exact ⟨heq.symm, hholder, hself, by simpa using hconflict⟩

/-- **A transfer moves the grant to the recipient, under the identity it had.** -/
theorem transferGrant?_yields_the_transfer {state next : MemoryState} {actor : ContextId}
    {id : GrantId} {recipient : ContextId} {grant : AuthorityGrant}
    (h : state.transferGrant? actor id recipient = some next)
    (hat : state.grantAt? id = some grant) :
    next.grantAt? id = some { grant with holder := recipient } := by
  obtain ⟨hnext, _, _, _⟩ := transferGrant?_eq h hat
  subst hnext
  show (state.grants.insert id { grant with holder := recipient }).lookup id = _
  rw [FiniteMap.lookup_insert_self]

/--
**A transfer that happened was the holder's own, and went somewhere else.**

The guards read back out. Review found `transferGrant?_eq` extracting these two facts
with every one of its five callers discarding them as `_` — a carried fact with no
reader, in a private lemma, which is the same class this layer's `ConsultedAudit.py`
exists for and which no audit can see inside a proof.
-/
theorem transferGrant?_was_by_the_holder {state next : MemoryState} {actor : ContextId}
    {id : GrantId} {recipient : ContextId} {grant : AuthorityGrant}
    (h : state.transferGrant? actor id recipient = some next)
    (hat : state.grantAt? id = some grant) :
    grant.holder = actor ∧ recipient ≠ actor := by
  obtain ⟨_, hholder, hself, _⟩ := transferGrant?_eq h hat
  exact ⟨hholder, hself⟩

/--
**A transfer leaves no conflicting pair.**

§7.3's issuance rule holding across a transfer as well as an issue, and the reason
the guard is more than a formality: `LoanConflicts` needs distinct holders, so a
context may hold two write grants over one range and `issue?` is right to accept the
second. Moving either to a third context turns that pair into the conflict this
refuses.
-/
theorem transferGrant?_leaves_no_conflict {state next : MemoryState} {actor : ContextId}
    {id : GrantId} {recipient : ContextId} {grant : AuthorityGrant}
    {entry : GrantId × AuthorityGrant}
    (h : state.transferGrant? actor id recipient = some next)
    (hat : state.grantAt? id = some grant) (hmem : entry ∈ state.grantEntries)
    (hid : entry.1 ≠ id) :
    ¬ state.LoanConflicts entry.2 { grant with holder := recipient } := by
  obtain ⟨_, _, _, hconflict⟩ := transferGrant?_eq h hat
  have := List.any_eq_false.mp hconflict entry hmem
  simpa [hid] using this

/-- A transfer leaves every other identity alone. -/
theorem transferGrant?_other {state next : MemoryState} {actor : ContextId}
    {id other : GrantId} {recipient : ContextId} {grant : AuthorityGrant}
    (h : state.transferGrant? actor id recipient = some next)
    (hat : state.grantAt? id = some grant) (hne : other ≠ id) :
    next.grantAt? other = state.grantAt? other := by
  obtain ⟨hnext, _, _, _⟩ := transferGrant?_eq h hat
  subst hnext
  show (state.grants.insert id { grant with holder := recipient }).lookup other = _
  rw [FiniteMap.lookup_insert_ne _ hne]
  rfl

/-!
## The authority changes an operation declares

`AuthorityDelta` is the operation-level vocabulary; this is where a declared change
meets the doors above. `Grass/Op/Step.lean` consults it in `refusalOf` and applies it
on the committing branch, which is what gives the five doors a caller that is not a
fixture.

**One function, not a predicate and an applier.** `Grass/Obligation/Delta.lean` and
`Grass/Op/Step.lean` do the obligation ledger the other way: `LedgerDelta.Applicable`
is a `Prop` saying a delta may be applied and `applyDelta` is a separate function
that applies it — two sources of truth, and a clause added to one and forgotten in the
other is a silent divergence. An `Option`-returning applier cannot diverge from
itself. The ledger cannot be brought all the way to this shape without rewriting every
fixture that states `LedgerEffectApplicable`, so it is tied by one theorem and one
construction instead: `Grass/Op/Step.lean`'s `ledgerEffectApplicable_iff_isSome` says
the predicate is exactly the applier succeeding, and the transition installs that
applier's own result rather than recomputing the fold, so the two cannot disagree on
the path the transition takes.

This named a second theorem for the construction half, and no such theorem exists --
one of three dead citations `Tools/CitationAudit.py` could not see because its
citation pattern omitted `?` while its declaration pattern accepted it, so every
citation of an `Option`-returning door was unadjudicated. A construction argument is
worth stating as one; naming it as a theorem is worth less than silence.
-/

/--
Apply one declared authority change, or refuse.

**The actor is the access's context**, and this is where a delta is *authorized* as
opposed to merely accepted by the map. Three of the five doors take no actor —
`issue?` reads the lender from the grant it is given, and `splitGrant?` and
`joinGrants?` are re-descriptions the map alone can check — so their actor rules are
here:

- an `issue` must name the acting context as its **lender**. Without this a context
  could lend bytes another context holds. `MayLend` bounds what the *named* lender
  can lend, so the forgery conjures no authority out of nothing; what it does is let
  one context strip another's exclusivity by lending that other's bytes to itself,
  which is the seizure `MayLend` closed reached by a different route.
- a `split` or a `join` must be performed by the **holder**, because it is that
  context's authority being re-described and a stranger re-describing it changes
  which identities the holder must return. An unknown identity falls through to the
  door, which refuses it and says so.
- `returnGrant?` and `transferGrant?` already take a context and check it, so they
  are passed the actor and nothing is added here.

Splitting the actor rules from the invariant checks has a cost and it is recorded
rather than hidden: a caller reaching `issue?` directly can still name any lender.
Closing it means an `actor` parameter on `issue?` and ninety-odd call sites, worth
doing deliberately rather than as a side effect of this commit;
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 has it.
-/
def applyAuthorityDelta? (state : MemoryState) (actor : ContextId) :
    AuthorityDelta → Option MemoryState
  | .issue id grant =>
      if grant.lender ≠ actor then Option.none else state.issue? id grant
  | .returnGrant id => state.returnGrant? actor id
  | .split id low high boundary =>
      if (state.grantAt? id).all (fun grant => decide (grant.holder = actor)) then
        state.splitGrant? id low high boundary
      else Option.none
  | .join low high into =>
      if (state.grantAt? low).all (fun grant => decide (grant.holder = actor)) then
        state.joinGrants? low high into
      else Option.none
  | .transfer id recipient => state.transferGrant? actor id recipient

/-- Apply every declared change, in order, refusing if any is refused. -/
def applyAuthorityEffect? (state : MemoryState) (actor : ContextId) :
    AuthorityEffect → Option MemoryState
  | [] => some state
  | delta :: rest =>
      (state.applyAuthorityDelta? actor delta).bind fun next =>
        next.applyAuthorityEffect? actor rest

/-- Declaring nothing changes nothing, which is why the field can default to `[]`
without every access having to think about it. -/
@[simp] theorem applyAuthorityEffect?_nil (state : MemoryState) (actor : ContextId) :
    state.applyAuthorityEffect? actor [] = some state := rfl

/-- An accepted effect is the doors' work and nothing else: this is the equation a
caller reasons with, and it is the reason `refusalOf` can decide applicability by
running the same function the commit branch runs. -/
theorem applyAuthorityEffect?_cons (state : MemoryState) (actor : ContextId)
    (delta : AuthorityDelta) (rest : AuthorityEffect) :
    state.applyAuthorityEffect? actor (delta :: rest) =
      (state.applyAuthorityDelta? actor delta).bind fun next =>
        next.applyAuthorityEffect? actor rest := rfl

/-- **A forged lender is refused.** A context may declare a loan of what it holds or
lent; it may not declare a loan on another context's behalf. -/
theorem applyAuthorityDelta?_eq_none_of_forged_lender {state : MemoryState}
    {actor : ContextId} {id : GrantId} {grant : AuthorityGrant}
    (h : grant.lender ≠ actor) :
    state.applyAuthorityDelta? actor (.issue id grant) = Option.none := by
  show (if grant.lender ≠ actor then Option.none else state.issue? id grant) = Option.none
  rw [if_pos h]

/-- **A stranger may not split another context's grant.** -/
theorem applyAuthorityDelta?_eq_none_of_stranger_split {state : MemoryState}
    {actor : ContextId} {id low high : GrantId} {boundary : Nat} {grant : AuthorityGrant}
    (hat : state.grantAt? id = some grant) (h : grant.holder ≠ actor) :
    state.applyAuthorityDelta? actor (.split id low high boundary) = Option.none := by
  show (if (state.grantAt? id).all (fun grant => decide (grant.holder = actor)) then
      state.splitGrant? id low high boundary else Option.none) = Option.none
  rw [if_neg (by simp [hat, h])]

/-- **Nor join it.** -/
theorem applyAuthorityDelta?_eq_none_of_stranger_join {state : MemoryState}
    {actor : ContextId} {low high into : GrantId} {grant : AuthorityGrant}
    (hat : state.grantAt? low = some grant) (h : grant.holder ≠ actor) :
    state.applyAuthorityDelta? actor (.join low high into) = Option.none := by
  show (if (state.grantAt? low).all (fun grant => decide (grant.holder = actor)) then
      state.joinGrants? low high into else Option.none) = Option.none
  rw [if_neg (by simp [hat, h])]

/-!
### Authority is not data

Every door above changes the `grants` field and nothing else, so a declared
authority change moves no bytes. `Grass/Op/Step.lean` needs that: the transition
applies the effect and then writes the access's bytes on top, and its framing law
— every cell the access did not declare is unchanged — would be false if a lend
could touch a cell.

Stated through `allocations`, because that is the field `cellAt?` and `byteAt?` read
and it is public, so the fact is available to a caller who cannot see `grants`.
-/

/-- An issue changes the grant map only. -/
theorem allocations_issue? {state issued : MemoryState} {id : GrantId}
    {grant : AuthorityGrant} (h : state.issue? id grant = some issued) :
    issued.allocations = state.allocations := by
  unfold issue? at h
  repeat' split at h
  all_goals
    first
      | (injection h with h; subst h; rfl)
      | exact absurd h (by simp)

/-- A return changes the grant map only. -/
theorem allocations_returnGrant? {state returned : MemoryState} {context : ContextId}
    {id : GrantId} (h : state.returnGrant? context id = some returned) :
    returned.allocations = state.allocations := by
  unfold returnGrant? at h
  repeat' split at h
  all_goals
    first
      | (injection h with h; subst h; rfl)
      | exact absurd h (by simp)

/-- A split changes the grant map only. -/
theorem allocations_splitGrant? {state next : MemoryState} {id low high : GrantId}
    {boundary : Nat} (h : state.splitGrant? id low high boundary = some next) :
    next.allocations = state.allocations := by
  unfold splitGrant? at h
  cases hlook : state.grants.lookup id with
  | none => rw [hlook, Option.bind_none] at h; exact absurd h (by simp)
  | some grant =>
    rw [hlook, Option.bind_some] at h
    repeat' split at h
    all_goals
      first
        | (injection h with h; subst h; rfl)
        | exact absurd h (by simp)

/-- A join changes the grant map only. -/
theorem allocations_joinGrants? {state next : MemoryState} {low high into : GrantId}
    (h : state.joinGrants? low high into = some next) :
    next.allocations = state.allocations := by
  unfold joinGrants? at h
  cases hlow : state.grants.lookup low with
  | none => rw [hlow, Option.bind_none] at h; exact absurd h (by simp)
  | some lowGrant =>
    rw [hlow, Option.bind_some] at h
    cases hhigh : state.grants.lookup high with
    | none => rw [hhigh, Option.bind_none] at h; exact absurd h (by simp)
    | some highGrant =>
      rw [hhigh, Option.bind_some] at h
      repeat' split at h
      all_goals
        first
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp)

/-- A transfer changes the grant map only. -/
theorem allocations_transferGrant? {state next : MemoryState} {actor : ContextId}
    {id : GrantId} {recipient : ContextId}
    (h : state.transferGrant? actor id recipient = some next) :
    next.allocations = state.allocations := by
  unfold transferGrant? at h
  cases hlook : state.grants.lookup id with
  | none => rw [hlook, Option.bind_none] at h; exact absurd h (by simp)
  | some grant =>
    rw [hlook, Option.bind_some] at h
    repeat' split at h
    all_goals
      first
        | (injection h with h; subst h; rfl)
        | exact absurd h (by simp)

/-- **A declared authority change moves no bytes**, one delta at a time. -/
theorem allocations_applyAuthorityDelta? {state next : MemoryState} {actor : ContextId}
    {delta : AuthorityDelta} (h : state.applyAuthorityDelta? actor delta = some next) :
    next.allocations = state.allocations := by
  cases delta with
  | issue id grant =>
    have h' : (if grant.lender ≠ actor then Option.none else state.issue? id grant)
        = some next := h
    split at h'
    · exact absurd h' (by simp)
    · exact allocations_issue? h'
  | returnGrant id =>
    have h' : state.returnGrant? actor id = some next := h
    exact allocations_returnGrant? h'
  | split id low high boundary =>
    have h' : (if (state.grantAt? id).all (fun grant => decide (grant.holder = actor)) then
        state.splitGrant? id low high boundary else Option.none) = some next := h
    split at h'
    · exact allocations_splitGrant? h'
    · exact absurd h' (by simp)
  | join low high into =>
    have h' : (if (state.grantAt? low).all (fun grant => decide (grant.holder = actor)) then
        state.joinGrants? low high into else Option.none) = some next := h
    split at h'
    · exact allocations_joinGrants? h'
    · exact absurd h' (by simp)
  | transfer id recipient =>
    have h' : state.transferGrant? actor id recipient = some next := h
    exact allocations_transferGrant? h'

/-- **And a whole declared effect moves no bytes.** -/
theorem allocations_applyAuthorityEffect? {state next : MemoryState} {actor : ContextId} :
    ∀ {effect : AuthorityEffect}, state.applyAuthorityEffect? actor effect = some next →
      next.allocations = state.allocations := by
  intro effect
  induction effect generalizing state with
  | nil =>
    intro h
    injection h with h
    subst h
    rfl
  | cons delta rest ih =>
    intro h
    rw [applyAuthorityEffect?_cons] at h
    cases hd : state.applyAuthorityDelta? actor delta with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some mid =>
      rw [hd, Option.bind_some] at h
      exact (ih h).trans (allocations_applyAuthorityDelta? hd)

/-- `backings_issue?` proves that the issue door preserves the complete backing table. -/
theorem backings_issue? {state issued : MemoryState} {id : GrantId}
    {grant : AuthorityGrant} (h : state.issue? id grant = some issued) :
    issued.backings = state.backings := by
  unfold issue? at h
  repeat' split at h
  all_goals
    first
      | (injection h with h; subst h; rfl)
      | exact absurd h (by simp)

theorem backings_returnGrant? {state returned : MemoryState} {context : ContextId}
    {id : GrantId} (h : state.returnGrant? context id = some returned) :
    returned.backings = state.backings := by
  unfold returnGrant? at h
  repeat' split at h
  all_goals
    first
      | (injection h with h; subst h; rfl)
      | exact absurd h (by simp)

theorem backings_splitGrant? {state next : MemoryState} {id low high : GrantId}
    {boundary : Nat} (h : state.splitGrant? id low high boundary = some next) :
    next.backings = state.backings := by
  unfold splitGrant? at h
  cases hlook : state.grants.lookup id with
  | none => rw [hlook, Option.bind_none] at h; exact absurd h (by simp)
  | some grant =>
      rw [hlook, Option.bind_some] at h
      repeat' split at h
      all_goals
        first
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp)

theorem backings_joinGrants? {state next : MemoryState} {low high into : GrantId}
    (h : state.joinGrants? low high into = some next) : next.backings = state.backings := by
  unfold joinGrants? at h
  cases hlow : state.grants.lookup low with
  | none => rw [hlow, Option.bind_none] at h; exact absurd h (by simp)
  | some lowGrant =>
      rw [hlow, Option.bind_some] at h
      cases hhigh : state.grants.lookup high with
      | none => rw [hhigh, Option.bind_none] at h; exact absurd h (by simp)
      | some highGrant =>
          rw [hhigh, Option.bind_some] at h
          repeat' split at h
          all_goals
            first
              | (injection h with h; subst h; rfl)
              | exact absurd h (by simp)

theorem backings_transferGrant? {state next : MemoryState} {actor : ContextId}
    {id : GrantId} {recipient : ContextId}
    (h : state.transferGrant? actor id recipient = some next) :
    next.backings = state.backings := by
  unfold transferGrant? at h
  cases hlook : state.grants.lookup id with
  | none => rw [hlook, Option.bind_none] at h; exact absurd h (by simp)
  | some grant =>
      rw [hlook, Option.bind_some] at h
      repeat' split at h
      all_goals
        first
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp)

/-- `backings_applyAuthorityDelta?` proves that an accepted authority delta preserves
the complete backing table. -/
theorem backings_applyAuthorityDelta? {state next : MemoryState} {actor : ContextId}
    {delta : AuthorityDelta} (h : state.applyAuthorityDelta? actor delta = some next) :
    next.backings = state.backings := by
  cases delta with
  | issue id grant =>
      have h' : (if grant.lender ≠ actor then Option.none else state.issue? id grant) =
          some next := h
      split at h'
      · exact absurd h' (by simp)
      · exact backings_issue? h'
  | returnGrant id => exact backings_returnGrant? h
  | split id low high boundary =>
      have h' : (if (state.grantAt? id).all (fun grant => decide (grant.holder = actor)) then
          state.splitGrant? id low high boundary else Option.none) = some next := h
      split at h'
      · exact backings_splitGrant? h'
      · exact absurd h' (by simp)
  | join low high into =>
      have h' : (if (state.grantAt? low).all (fun grant => decide (grant.holder = actor)) then
          state.joinGrants? low high into else Option.none) = some next := h
      split at h'
      · exact backings_joinGrants? h'
      · exact absurd h' (by simp)
  | transfer id recipient => exact backings_transferGrant? h

/-- `backings_applyAuthorityEffect?` proves that a whole accepted authority effect
preserves the complete backing table. -/
theorem backings_applyAuthorityEffect? {state next : MemoryState} {actor : ContextId} :
    ∀ {effect : AuthorityEffect}, state.applyAuthorityEffect? actor effect = some next →
      next.backings = state.backings := by
  intro effect
  induction effect generalizing state with
  | nil =>
      intro h
      injection h with h
      subst h
      rfl
  | cons delta rest ih =>
      intro h
      rw [applyAuthorityEffect?_cons] at h
      cases hd : state.applyAuthorityDelta? actor delta with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some mid =>
          rw [hd, Option.bind_some] at h
          exact (ih h).trans (backings_applyAuthorityDelta? hd)

/-- The executable backing profile is metadata-only and is invariant under every
accepted authority effect. -/
theorem dedicatedBackings_applyAuthorityEffect? {state next : MemoryState}
    {actor : ContextId} {effect : AuthorityEffect}
    (h : state.applyAuthorityEffect? actor effect = some next) :
    next.DedicatedBackings ↔ state.DedicatedBackings := by
  have hcapacity (id : StorageId) : next.backingCapacity? id = state.backingCapacity? id := by
    unfold backingCapacity?
    rw [backings_applyAuthorityEffect? h]
  unfold DedicatedBackings
  rw [allocations_applyAuthorityEffect? h]
  simp only [hcapacity]

@[simp] theorem grantAt?_eq_lookup (state : MemoryState) (id : GrantId) :
    state.grantAt? id = state.grants.lookup id := rfl

@[simp] theorem grantEntries_eq (state : MemoryState) :
    state.grantEntries = state.grants.entries := rfl

/-- Equal grant-entry views give equal lookup observations. -/
theorem grantAt?_eq_of_grantEntries_eq {before after : MemoryState}
    (same : after.grantEntries = before.grantEntries) (id : GrantId) :
    after.grantAt? id = before.grantAt? id :=
  congrArg (fun entries => Grass.Std.Logical.findValue entries id) same

/-- A successful issue records the grant under the identity it names. -/
theorem grantAt?_issue?_self {state issued : MemoryState} {id : GrantId}
    {grant : AuthorityGrant} (h : state.issue? id grant = some issued) :
    issued.grantAt? id = some grant := by
  unfold issue? at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  injection h with h
  subst h
  exact FiniteMap.lookup_insert_self _ _ _

/-- Issuing one grant leaves every other identity alone. -/
theorem grantAt?_issue?_ne {state issued : MemoryState} {id other : GrantId}
    {grant : AuthorityGrant} (h : state.issue? id grant = some issued)
    (hne : other ≠ id) : issued.grantAt? other = state.grantAt? other := by
  unfold issue? at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  injection h with h
  subst h
  exact FiniteMap.lookup_insert_ne _ hne _

/-- **A reissued identity is refused**, which is §3's "a return consumes that exact
identity" read from the other side: an identity is consumed by a return and by
nothing else. -/
theorem issue?_eq_none_of_reissued (state : MemoryState) {id : GrantId}
    (grant : AuthorityGrant) (h : (state.grantAt? id).isSome) :
    state.issue? id grant = Option.none := by
  unfold issue?
  rw [if_pos (show (state.grants.lookup id).isSome from h)]

/-- An issue happens only into a free identity. -/
theorem grantAt?_eq_none_of_issue? {state issued : MemoryState} {id : GrantId}
    {grant : AuthorityGrant} (h : state.issue? id grant = some issued) :
    state.grantAt? id = Option.none := by
  unfold issue? at h
  split at h
  · exact absurd h (by simp)
  · next hfresh => simpa using hfresh

/-- **A return consumes the identity it names.** -/
theorem grantAt?_returnGrant?_self {state returned : MemoryState} {context : ContextId}
    {id : GrantId} (h : state.returnGrant? context id = some returned) :
    returned.grantAt? id = Option.none := by
  unfold returnGrant? at h
  split at h
  · split at h
    · injection h with h
      subst h
      exact FiniteMap.lookup_erase_self _ _
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Returning one grant leaves every other identity alone. -/
theorem grantAt?_returnGrant?_ne {state returned : MemoryState} {context : ContextId}
    {id other : GrantId} (h : state.returnGrant? context id = some returned)
    (hne : other ≠ id) : returned.grantAt? other = state.grantAt? other := by
  unfold returnGrant? at h
  split at h
  · split at h
    · injection h with h
      subst h
      exact FiniteMap.lookup_erase_ne _ hne
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **A context that neither holds nor lent it may not return it.** -/
theorem returnGrant?_eq_none_of_stranger {state : MemoryState} {context : ContextId}
    {id : GrantId} {grant : AuthorityGrant} (hlook : state.grantAt? id = some grant)
    (hholder : grant.holder ≠ context) (hlender : grant.lender ≠ context) :
    state.returnGrant? context id = Option.none := by
  unfold returnGrant?
  rw [show state.grants.lookup id = some grant from hlook]
  exact if_neg (fun h => h.elim hholder hlender)

/-- **And the lender may return what it lent.** -/
theorem returnGrant?_isSome_of_lender {state : MemoryState} {context : ContextId}
    {id : GrantId} {grant : AuthorityGrant} (hlook : state.grantAt? id = some grant)
    (h : grant.lender = context) : (state.returnGrant? context id).isSome := by
  unfold returnGrant?
  rw [show state.grants.lookup id = some grant from hlook]
  simp only []
  rw [if_pos (Or.inr h)]
  rfl

/-- And a return naming no live grant is refused rather than treated as a no-op. -/
theorem returnGrant?_eq_none_of_absent {state : MemoryState} {context : ContextId}
    {id : GrantId} (h : state.grantAt? id = Option.none) :
    state.returnGrant? context id = Option.none := by
  unfold returnGrant?
  rw [show state.grants.lookup id = Option.none from h]

/-- A grant authorizes one local offset of an already-resolved access exactly when
its own checked backing span covers the corresponding backing offset. Failed grant
resolution authorizes nothing. -/
def AuthorizedAtResolved {state : MemoryState} (grant : AuthorityGrant)
    (context : ContextId) {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (offset : Nat)
    (intent : AccessIntent) : Prop :=
  grant.holder = context ∧
  state.CurrentEpoch grant.provenance ∧
  requested.Covers offset ∧
  (match state.grantSpan? grant with
    | .ok grantSpan => grantSpan.backing = access.span.backing ∧
        grantSpan.range.Covers (access.allocation.origin + offset)
    | .error _ => False) ∧
  grant.rights.Permits intent

instance {state : MemoryState} (grant : AuthorityGrant) (context : ContextId)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (offset : Nat)
    (intent : AccessIntent) :
    Decidable (state.AuthorizedAtResolved grant context access offset intent) :=
  by
    unfold AuthorizedAtResolved
    cases state.grantSpan? grant <;> infer_instance

/-- Prepared authorization transports across transitions that leave allocation and
backing metadata unchanged. -/
theorem AuthorizedAtResolved.transport {before after : MemoryState}
    {grant : AuthorityGrant} {context : ContextId} {provenance : Provenance}
    {requested : ByteRange} (access : before.ResolvedAccess provenance requested)
    {offset : Nat} {intent : AccessIntent}
    (hallocations : after.allocations = before.allocations)
    (hbackings : after.backings = before.backings)
    (h : before.AuthorizedAtResolved grant context access offset intent) :
    after.AuthorizedAtResolved grant context
      (access.transport hallocations hbackings) offset intent := by
  rcases h with ⟨hholder, hcurrent, hrequested, hspatial, hrights⟩
  refine ⟨hholder, ?_, hrequested, ?_, hrights⟩
  · unfold CurrentEpoch at hcurrent ⊢
    rw [hallocations]
    exact hcurrent
  · cases hs : before.grantSpan? grant with
    | error failure => rw [hs] at hspatial; exact hspatial.elim
    | ok span =>
        rw [hs] at hspatial
        have hs' := grantSpan?_eq_ok_transport hs hallocations hbackings
        rw [hs']
        change span.backing = access.span.backing ∧
          span.range.Covers (access.allocation.origin + offset)
        exact hspatial

/-- Prepared authority for a whole access. Different grants may cover different
bytes, matching the existing pointwise grant semantics. -/
def GrantedResolved (state : MemoryState) (context : ContextId)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (intent : AccessIntent) : Prop :=
  ∀ i, i < requested.size →
    ∃ entry ∈ state.grantEntries,
      state.AuthorizedAtResolved entry.2 context access (requested.start + i) intent

instance (state : MemoryState) (context : ContextId)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (intent : AccessIntent) :
    Decidable (state.GrantedResolved context access intent) :=
  inferInstanceAs (Decidable (∀ i, i < requested.size → ∃ entry ∈ state.grantEntries,
    state.AuthorizedAtResolved entry.2 context access (requested.start + i) intent))

/-- Provenance-facing checked wrapper for one byte. It resolves the singleton query
once and delegates to `AuthorizedAtResolved`; every resolver failure denies authority. -/
def AuthorizedAt (state : MemoryState) (grant : AuthorityGrant) (context : ContextId)
    (provenance : Provenance) (offset : Nat) (intent : AccessIntent) : Prop :=
  match state.resolveAccess? provenance (ByteRange.mk offset 1) with
  | .ok access => state.AuthorizedAtResolved grant context access offset intent
  | .error _ => False

instance (state : MemoryState) (grant : AuthorityGrant) (context : ContextId)
    (provenance : Provenance) (offset : Nat) (intent : AccessIntent) :
    Decidable (state.AuthorizedAt grant context provenance offset intent) :=
  by unfold AuthorizedAt; split <;> infer_instance

/-- A grant held by one context authorizes nothing for another. -/
theorem not_authorizedAt_of_other_holder {state : MemoryState} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {offset : Nat}
    {intent : AccessIntent} (h : grant.holder ≠ context) :
    ¬ state.AuthorizedAt grant context provenance offset intent := by
  cases hr : state.resolveAccess? provenance (ByteRange.mk offset 1) <;>
    simp [AuthorizedAt, hr, AuthorizedAtResolved, h]

/-- A read-only grant does not authorize a write. -/
theorem not_authorizedAt_of_insufficient_rights {state : MemoryState}
    {grant : AuthorityGrant} {context : ContextId} {provenance : Provenance}
    {offset : Nat} {intent : AccessIntent} (h : ¬ grant.rights.Permits intent) :
    ¬ state.AuthorizedAt grant context provenance offset intent := by
  cases hr : state.resolveAccess? provenance (ByteRange.mk offset 1) <;>
    simp [AuthorizedAt, hr, AuthorizedAtResolved, h]

/-- A failed singleton access resolution authorizes nothing. -/
theorem not_authorizedAt_of_resolve_error {state : MemoryState} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {offset : Nat}
    {intent : AccessIntent} {failure : ResolveFailure}
    (h : state.resolveAccess? provenance (ByteRange.mk offset 1) = .error failure) :
    ¬ state.AuthorizedAt grant context provenance offset intent := by
  simp [AuthorizedAt, h]

/--
`state.Granted context provenance range intent` holds when some live grant
authorizes that access.

Existentially quantified over the grant, because an access does not name the one
it relies on; see `Grass/Memory/Authority.lean`. Decidable because the grant table
is finite.
-/
def Granted (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) : Prop :=
  match state.resolveAccess? provenance range with
  | .ok access => state.GrantedResolved context access intent
  | .error _ => False

instance (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) :
    Decidable (state.Granted context provenance range intent) :=
  by unfold Granted; split <;> infer_instance

/-- A successful full-query resolution makes the provenance-facing authority
wrapper definitionally equal to the prepared authority predicate. -/
theorem granted_iff_grantedResolved_of_resolveAccess?_eq_ok {state : MemoryState}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent} {access : state.ResolvedAccess provenance range}
    (hresolve : state.resolveAccess? provenance range = .ok access) :
    state.Granted context provenance range intent ↔
      state.GrantedResolved context access intent := by
  simp [Granted, hresolve]

/-- One installed grant whose resolved backing span contains the prepared access
authorizes the whole access. -/
theorem grantedResolved_of_grantAt {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} {intent : AccessIntent}
    (access : state.ResolvedAccess provenance range)
    {id : GrantId} {grant : AuthorityGrant} (hat : state.grantAt? id = some grant)
    {grantSpan : Coordinates.BackingSpan} (hspan : state.grantSpan? grant = .ok grantSpan)
    (hcover : grantSpan.Contains access.span)
    (hholder : grant.holder = context)
    (hgrant : state.CurrentEpoch grant.provenance)
    (hrights : grant.rights.Permits intent) :
    state.GrantedResolved context access intent := by
  intro i hi
  refine ⟨(id, grant), mem_entries_of_lookup hat, hholder, hgrant, ?_, ?_, hrights⟩
  · rw [ByteRange.covers_def]
    omega
  · rw [hspan]
    refine ⟨hcover.1, hcover.2.covers ?_⟩
    exact (Coordinates.Mapping.span_covers access.allocation.mapping range
      (range.start + i)).2 (by rw [ByteRange.covers_def]; omega)

/-- Provenance-facing form of `grantedResolved_of_grantAt`, with the full query
resolution made explicit. -/
theorem granted_of_grantAt {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} {intent : AccessIntent}
    {access : state.ResolvedAccess provenance range}
    (hresolve : state.resolveAccess? provenance range = .ok access)
    {id : GrantId} {grant : AuthorityGrant} (hat : state.grantAt? id = some grant)
    {grantSpan : Coordinates.BackingSpan} (hspan : state.grantSpan? grant = .ok grantSpan)
    (hcover : grantSpan.Contains access.span)
    (hholder : grant.holder = context)
    (hgrant : state.CurrentEpoch grant.provenance)
    (hrights : grant.rights.Permits intent) :
    state.Granted context provenance range intent :=
  (granted_iff_grantedResolved_of_resolveAccess?_eq_ok hresolve).2
    (grantedResolved_of_grantAt access hat hspan hcover hholder hgrant hrights)

/-- `splitGrant?_preserves_authority` proves that a checked split preserves all
authority supplied by its source grant. Query and grant containment are stated in
resolved backing coordinates. -/
theorem splitGrant?_preserves_authority {state next : MemoryState}
    {id low high : GrantId} {boundary : Nat} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent}
    (h : state.splitGrant? id low high boundary = some next)
    (hat : state.grantAt? id = some grant)
    {access : state.ResolvedAccess provenance range}
    (_hresolve : state.resolveAccess? provenance range = .ok access)
    {sourceSpan : Coordinates.BackingSpan}
    (hspan : state.grantSpan? grant = .ok sourceSpan)
    (hcover : sourceSpan.Contains access.span)
    (hholder : grant.holder = context)
    (hcurrent : state.CurrentEpoch grant.provenance)
    (hrights : grant.rights.Permits intent) :
    next.Granted context provenance range intent := by
  obtain ⟨hlowAt, hhighAt, _⟩ := splitGrant?_yields_the_parts h hat
  obtain ⟨hnext, _, _, _, hstart, hstop⟩ := splitGrant?_eq h hat
  subst next
  let splitState : MemoryState := { state with grants := state.splitMap id low high boundary grant }
  let nextAccess : splitState.ResolvedAccess provenance range := access.transport rfl rfl
  have hnextResolve := resolveAccess?_eq_ok nextAccess
  apply (granted_iff_grantedResolved_of_resolveAccess?_eq_ok hnextResolve).2
  intro i hi
  have hrequested : range.Covers (range.start + i) := by
    rw [ByteRange.covers_def]
    omega
  have hqueryPoint : access.span.range.Covers
      (access.allocation.origin + (range.start + i)) :=
    (Coordinates.Mapping.span_covers access.allocation.mapping range _).2 hrequested
  have hsourcePoint := hcover.2.covers hqueryPoint
  rcases split_grantSpan_covers_part hstart hstop hspan hsourcePoint with
      ⟨partSpan, hpartSpan, hbacking, hcovers⟩ |
      ⟨partSpan, hpartSpan, hbacking, hcovers⟩
  · have hpartNext := grantSpan?_eq_ok_transport (after := splitState)
      hpartSpan rfl rfl
    refine ⟨(low, grant.lowPart boundary), mem_entries_of_lookup hlowAt,
      ?_, ?_, hrequested, ?_, ?_⟩
    · simpa [AuthorityGrant.lowPart] using hholder
    · exact (currentEpoch_grants state _ _).mpr
        (by simpa [AuthorityGrant.lowPart] using hcurrent)
    · rw [hpartNext]
      exact ⟨hbacking.trans (hcover.1.trans rfl), hcovers⟩
    · simpa [AuthorityGrant.lowPart] using hrights
  · have hpartNext := grantSpan?_eq_ok_transport (after := splitState)
      hpartSpan rfl rfl
    refine ⟨(high, grant.highPart boundary), mem_entries_of_lookup hhighAt,
      ?_, ?_, hrequested, ?_, ?_⟩
    · simpa [AuthorityGrant.highPart] using hholder
    · exact (currentEpoch_grants state _ _).mpr
        (by simpa [AuthorityGrant.highPart] using hcurrent)
    · rw [hpartNext]
      exact ⟨hbacking.trans (hcover.1.trans rfl), hcovers⟩
    · simpa [AuthorityGrant.highPart] using hrights

/--
**A split creates no authority.**

The other direction, and the one that justifies not re-running `issue?`: every entry
of the split state is one of the two parts or an entry the state already had, and
each part's range lies inside the source's, so an offset a part authorizes is one the
source authorized. `mem_entries_insert` and
`mem_entries_erase` are what bound the new entry list from above; without them a
theorem about a modified map has to unfold the association list here.
-/
theorem splitGrant?_creates_no_authority {state next : MemoryState}
    {id low high : GrantId} {boundary : Nat} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent}
    (h : state.splitGrant? id low high boundary = some next)
    (hat : state.grantAt? id = some grant)
    (hgranted : next.Granted context provenance range intent) :
    state.Granted context provenance range intent := by
  have hsourceResolved : ∃ sourceSpan, state.grantSpan? grant = .ok sourceSpan := by
    unfold splitGrant? at h
    rw [show state.grants.lookup id = some grant from hat, Option.bind_some] at h
    cases hs : state.grantSpan? grant with
    | error failure => rw [hs] at h; contradiction
    | ok sourceSpan => exact ⟨sourceSpan, rfl⟩
  obtain ⟨sourceSpan, hsourceSpan⟩ := hsourceResolved
  obtain ⟨hnext, _, _, _, hstart, hstop⟩ := splitGrant?_eq h hat
  subst next
  let splitState : MemoryState := { state with grants := state.splitMap id low high boundary grant }
  change splitState.Granted context provenance range intent at hgranted
  unfold Granted at hgranted
  cases hresolve : splitState.resolveAccess? provenance range with
  | error failure => rw [hresolve] at hgranted; exact hgranted.elim
  | ok nextAccess =>
      rw [hresolve] at hgranted
      let beforeAccess : state.ResolvedAccess provenance range := nextAccess.transport rfl rfl
      have hbefore := resolveAccess?_eq_ok beforeAccess
      unfold Granted
      rw [hbefore]
      intro i hi
      obtain ⟨entry, hmem, hauth⟩ := hgranted i hi
      have hauthWhole := hauth
      have hmem' : entry = (high, grant.highPart boundary) ∨
          entry = (low, grant.lowPart boundary) ∨ entry ∈ state.grantEntries := by
        have hlist : entry ∈ (state.splitMap id low high boundary grant).entries := by
          simpa [splitState] using hmem
        unfold splitMap at hlist
        rcases mem_entries_insert hlist with hcase | hcase
        · exact Or.inl hcase
        · rcases mem_entries_insert hcase with hcase | hcase
          · exact Or.inr (Or.inl hcase)
          · exact Or.inr (Or.inr (mem_entries_erase hcase))
      rcases hauth with ⟨hholder, hcurrent, hrequested, hspatial, hrights⟩
      rcases hmem' with hcase | hcase | hcase
      · subst hcase
        cases hp : splitState.grantSpan? (grant.highPart boundary) with
        | error failure => rw [hp] at hspatial; exact hspatial.elim
        | ok partSpan =>
            rw [hp] at hspatial
            have hpState := grantSpan?_eq_ok_transport (after := state) hp rfl rfl
            have hc := grantSpan?_contains_of_same_provenance
              (outer := grant) (inner := grant.highPart boundary) rfl
              (AuthorityGrant.highPart_contained (Nat.le_of_lt hstart) (Nat.le_of_lt hstop))
              hsourceSpan hpState
            refine ⟨(id, grant), mem_entries_of_lookup hat, hholder, ?_, hrequested, ?_, hrights⟩
            · exact (currentEpoch_grants state
                (state.splitMap id low high boundary grant) _).mp hcurrent
            · rw [hsourceSpan]
              exact ⟨hc.1.trans hspatial.1,
                hc.2.covers (by simpa [beforeAccess, ResolvedAccess.transport] using hspatial.2)⟩
      · subst hcase
        cases hp : splitState.grantSpan? (grant.lowPart boundary) with
        | error failure => rw [hp] at hspatial; exact hspatial.elim
        | ok partSpan =>
            rw [hp] at hspatial
            have hpState := grantSpan?_eq_ok_transport (after := state) hp rfl rfl
            have hc := grantSpan?_contains_of_same_provenance
              (outer := grant) (inner := grant.lowPart boundary) rfl
              (AuthorityGrant.lowPart_contained (Nat.le_of_lt hstop)) hsourceSpan hpState
            refine ⟨(id, grant), mem_entries_of_lookup hat, hholder, ?_, hrequested, ?_, hrights⟩
            · exact (currentEpoch_grants state
                (state.splitMap id low high boundary grant) _).mp hcurrent
            · rw [hsourceSpan]
              exact ⟨hc.1.trans hspatial.1,
                hc.2.covers (by simpa [beforeAccess, ResolvedAccess.transport] using hspatial.2)⟩
      · refine ⟨entry, hcase, ?_⟩
        have transported := AuthorizedAtResolved.transport (after := state)
          nextAccess rfl rfl hauthWhole
        simpa [beforeAccess] using transported

/-- `joinGrants?_preserves_low_authority` proves that joining checked adjacent grants
preserves authority supplied by the low source. All containment is over resolved
backing spans. -/
theorem joinGrants?_preserves_low_authority {state next : MemoryState}
    {low high into : GrantId} {lowGrant highGrant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent}
    (h : state.joinGrants? low high into = some next)
    (hlow : state.grantAt? low = some lowGrant)
    (hhigh : state.grantAt? high = some highGrant)
    {access : state.ResolvedAccess provenance range}
    (_hresolve : state.resolveAccess? provenance range = .ok access)
    {lowSpan : Coordinates.BackingSpan}
    (hspan : state.grantSpan? lowGrant = .ok lowSpan)
    (hcover : lowSpan.Contains access.span)
    (hholder : lowGrant.holder = context)
    (hcurrent : state.CurrentEpoch lowGrant.provenance)
    (hrights : lowGrant.rights.Permits intent) :
    next.Granted context provenance range intent := by
  obtain ⟨hjoinedAt, _, _⟩ := joinGrants?_yields_the_join h hlow hhigh
  obtain ⟨hnext, _, _, _, _⟩ := joinGrants?_eq h hlow hhigh
  obtain ⟨joinedSpan, hjoinedSpan⟩ := joinGrants?_resolves_join h hlow hhigh
  have hlocal : (lowGrant.joined highGrant).range.Contains lowGrant.range := by
    simp only [AuthorityGrant.joined, ByteRange.Contains, ByteRange.stop]
    omega
  have hcontains := grantSpan?_contains_of_same_provenance
    (outer := lowGrant.joined highGrant) (inner := lowGrant) rfl hlocal
    hjoinedSpan hspan
  subst next
  let joinState : MemoryState :=
    { state with grants := state.joinMap low high into (lowGrant.joined highGrant) }
  let nextAccess : joinState.ResolvedAccess provenance range := access.transport rfl rfl
  have hnextResolve := resolveAccess?_eq_ok nextAccess
  have hjoinedNext := grantSpan?_eq_ok_transport (after := joinState)
    hjoinedSpan rfl rfl
  apply (granted_iff_grantedResolved_of_resolveAccess?_eq_ok hnextResolve).2
  apply grantedResolved_of_grantAt (state := joinState) nextAccess hjoinedAt hjoinedNext
    ⟨hcontains.1.trans hcover.1, hcontains.2.trans hcover.2⟩
  · exact hholder
  · exact (currentEpoch_grants state _ _).mpr hcurrent
  · exact hrights

/-- `joinGrants?_preserves_high_authority` proves that joining checked adjacent grants
preserves authority supplied by the high source. The metadata-equality door supplies
the provenance, holder, and rights equalities. -/
theorem joinGrants?_preserves_high_authority {state next : MemoryState}
    {low high into : GrantId} {lowGrant highGrant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent}
    (h : state.joinGrants? low high into = some next)
    (hlow : state.grantAt? low = some lowGrant)
    (hhigh : state.grantAt? high = some highGrant)
    {access : state.ResolvedAccess provenance range}
    (_hresolve : state.resolveAccess? provenance range = .ok access)
    {highSpan : Coordinates.BackingSpan}
    (hspan : state.grantSpan? highGrant = .ok highSpan)
    (hcover : highSpan.Contains access.span)
    (hholder : highGrant.holder = context)
    (hcurrent : state.CurrentEpoch highGrant.provenance)
    (hrights : highGrant.rights.Permits intent) :
    next.Granted context provenance range intent := by
  obtain ⟨hjoinedAt, _, _⟩ := joinGrants?_yields_the_join h hlow hhigh
  obtain ⟨hnext, _, _, hmatch, hadjacent⟩ := joinGrants?_eq h hlow hhigh
  obtain ⟨joinedSpan, hjoinedSpan⟩ := joinGrants?_resolves_join h hlow hhigh
  have hprovenance : (lowGrant.joined highGrant).provenance = highGrant.provenance := by
    show lowGrant.provenance = highGrant.provenance
    rw [hmatch]
  have hlocal : (lowGrant.joined highGrant).range.Contains highGrant.range := by
    simp only [AuthorityGrant.joined, ByteRange.Contains, ByteRange.stop]
    simp only [ByteRange.stop] at hadjacent
    omega
  have hcontains := grantSpan?_contains_of_same_provenance
    (outer := lowGrant.joined highGrant) (inner := highGrant) hprovenance hlocal
    hjoinedSpan hspan
  subst next
  let joinState : MemoryState :=
    { state with grants := state.joinMap low high into (lowGrant.joined highGrant) }
  let nextAccess : joinState.ResolvedAccess provenance range := access.transport rfl rfl
  have hnextResolve := resolveAccess?_eq_ok nextAccess
  have hjoinedNext := grantSpan?_eq_ok_transport (after := joinState)
    hjoinedSpan rfl rfl
  apply (granted_iff_grantedResolved_of_resolveAccess?_eq_ok hnextResolve).2
  apply grantedResolved_of_grantAt (state := joinState) nextAccess hjoinedAt hjoinedNext
    ⟨hcontains.1.trans hcover.1, hcontains.2.trans hcover.2⟩
  · show lowGrant.holder = context
    rw [hmatch]
    exact hholder
  · apply (currentEpoch_grants state _ _).mpr
    show state.CurrentEpoch lowGrant.provenance
    rw [hmatch]
    exact hcurrent
  · show lowGrant.rights.Permits intent
    rw [hmatch]
    exact hrights

/--
**A join creates no authority.**

The direction that justifies not re-running `issue?`, and the one adjacency is for: a
gap between the sources would put bytes inside the joined range that neither source
covered, and this theorem would be false. Every entry of the joined state is the
joined grant or an entry the state already had, and the joined grant's every offset
is one source's or the other's.
-/
theorem joinGrants?_creates_no_authority {state next : MemoryState}
    {low high into : GrantId} {lowGrant highGrant : AuthorityGrant} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} {intent : AccessIntent}
    (h : state.joinGrants? low high into = some next)
    (hlow : state.grantAt? low = some lowGrant)
    (hhigh : state.grantAt? high = some highGrant)
    (hgranted : next.Granted context provenance range intent) :
    state.Granted context provenance range intent := by
  obtain ⟨hnext, _, _, hmatch, hadjacent⟩ := joinGrants?_eq h hlow hhigh
  subst next
  let joinState : MemoryState :=
    { state with grants := state.joinMap low high into (lowGrant.joined highGrant) }
  change joinState.Granted context provenance range intent at hgranted
  unfold Granted at hgranted
  cases hresolve : joinState.resolveAccess? provenance range with
  | error failure => rw [hresolve] at hgranted; exact hgranted.elim
  | ok nextAccess =>
      rw [hresolve] at hgranted
      let beforeAccess : state.ResolvedAccess provenance range :=
        nextAccess.transport rfl rfl
      have hbefore := resolveAccess?_eq_ok beforeAccess
      unfold Granted
      rw [hbefore]
      intro i hi
      obtain ⟨entry, hmem, hauth⟩ := hgranted i hi
      have hmem' : entry = (into, lowGrant.joined highGrant) ∨
          entry ∈ state.grantEntries := by
        have hlist : entry ∈ (state.joinMap low high into
            (lowGrant.joined highGrant)).entries := by
          simpa [joinState] using hmem
        unfold joinMap at hlist
        rcases mem_entries_insert hlist with hcase | hcase
        · exact Or.inl hcase
        · exact Or.inr (mem_entries_erase (mem_entries_erase hcase))
      rcases hmem' with hcase | hcase
      · subst hcase
        rcases hauth with ⟨hholder, hcurrent, hrequested, hspatial, hrights⟩
        cases hs : joinState.grantSpan? (lowGrant.joined highGrant) with
        | error failure => rw [hs] at hspatial; exact hspatial.elim
        | ok joinedSpan =>
            rw [hs] at hspatial
            have hsState := grantSpan?_eq_ok_transport (after := state) hs rfl rfl
            have hsource := joined_grantSpan_covers_source hmatch hadjacent hsState
              hspatial.2
            rcases hsource with ⟨lowSpan, hlowSpan, hbacking, hcovers⟩ |
                ⟨highSpan, hhighSpan, hbacking, hcovers⟩
            · refine ⟨(low, lowGrant), mem_entries_of_lookup hlow, hholder, ?_,
                hrequested, ?_, hrights⟩
              · exact (currentEpoch_grants state _ _).mp hcurrent
              · rw [hlowSpan]
                exact ⟨hbacking.trans (hspatial.1.trans rfl), hcovers⟩
            · refine ⟨(high, highGrant), mem_entries_of_lookup hhigh, ?_, ?_,
                hrequested, ?_, ?_⟩
              · rw [← show lowGrant.holder = highGrant.holder from by rw [hmatch]]
                exact hholder
              · rw [← show lowGrant.provenance = highGrant.provenance from by rw [hmatch]]
                exact (currentEpoch_grants state _ _).mp hcurrent
              · rw [hhighSpan]
                exact ⟨hbacking.trans (hspatial.1.trans rfl), hcovers⟩
              · rw [← show lowGrant.rights = highGrant.rights from by rw [hmatch]]
                exact hrights
      · refine ⟨entry, hcase, ?_⟩
        have transported := AuthorizedAtResolved.transport (after := state)
          nextAccess rfl rfl hauth
        simpa [beforeAccess] using transported

/--
**A transfer gives the recipient exactly what the holder had.**

The hypotheses are `granted_of_grantAt`'s over the *transferred* grant, which differs
from the source only in its holder, so this is the source's authority now standing in
the recipient's name.
-/
theorem transferGrant?_grants_the_recipient {state next : MemoryState} {actor : ContextId}
    {id : GrantId} {recipient : ContextId} {grant : AuthorityGrant}
    {provenance : Provenance} {range : ByteRange} {intent : AccessIntent}
    (h : state.transferGrant? actor id recipient = some next)
    (hat : state.grantAt? id = some grant)
    {access : state.ResolvedAccess provenance range}
    (_hresolve : state.resolveAccess? provenance range = .ok access)
    {grantSpan : Coordinates.BackingSpan} (hspan : state.grantSpan? grant = .ok grantSpan)
    (hcover : grantSpan.Contains access.span)
    (hgrant : state.CurrentEpoch grant.provenance)
    (hrights : grant.rights.Permits intent) :
    next.Granted recipient provenance range intent := by
  have hmoved := transferGrant?_yields_the_transfer h hat
  obtain ⟨hnext, _, _, _⟩ := transferGrant?_eq h hat
  subst next
  let movedGrant : AuthorityGrant := { grant with holder := recipient }
  let movedState : MemoryState := { state with grants := state.grants.insert id movedGrant }
  let nextAccess : movedState.ResolvedAccess provenance range := access.transport rfl rfl
  have hnextResolve := resolveAccess?_eq_ok nextAccess
  have hspanMoved := grantSpan?_eq_ok_transport (after := movedState) hspan rfl rfl
  apply (granted_iff_grantedResolved_of_resolveAccess?_eq_ok hnextResolve).2
  apply grantedResolved_of_grantAt (state := movedState) nextAccess
    (id := id) (grant := movedGrant)
  · change movedState.grantAt? id = some movedGrant at hmoved
    exact hmoved
  · exact hspanMoved
  · change grantSpan.Contains access.span
    exact hcover
  · rfl
  · change state.CurrentEpoch grant.provenance
    exact hgrant
  · simpa using hrights

/--
**A transfer creates no authority for anyone but the recipient.**

The safety half. Every entry of the transferred state is the moved grant or an entry
the state already had, and the moved grant is held by the recipient, so a context
that is not the recipient is authorized by exactly what authorized it before. What
this deliberately does *not* say is that the old holder lost the bytes: it may hold
other grants over them, and `Tests/Memory/Loans.lean` shows the concrete case where
it holds none and the authority really is gone.
-/
theorem transferGrant?_creates_no_authority {state next : MemoryState} {actor : ContextId}
    {id : GrantId} {recipient : ContextId} {grant : AuthorityGrant} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} {intent : AccessIntent}
    (h : state.transferGrant? actor id recipient = some next)
    (hat : state.grantAt? id = some grant) (hne : context ≠ recipient)
    (hgranted : next.Granted context provenance range intent) :
    state.Granted context provenance range intent := by
  obtain ⟨hnext, _, _, _⟩ := transferGrant?_eq h hat
  subst next
  let movedGrant : AuthorityGrant := { grant with holder := recipient }
  let movedState : MemoryState := { state with grants := state.grants.insert id movedGrant }
  change movedState.Granted context provenance range intent at hgranted
  unfold Granted at hgranted
  cases hresolve : movedState.resolveAccess? provenance range with
  | error failure => simp [hresolve] at hgranted
  | ok nextAccess =>
      rw [hresolve] at hgranted
      let beforeAccess : state.ResolvedAccess provenance range :=
        nextAccess.transport rfl rfl
      have hbefore := resolveAccess?_eq_ok beforeAccess
      unfold Granted
      rw [hbefore]
      intro i hi
      obtain ⟨entry, hmem, hauth⟩ := hgranted i hi
      have hmem' : entry = (id, movedGrant) ∨ entry ∈ state.grantEntries := by
        apply mem_entries_insert
        simpa [movedState] using hmem
      rcases hmem' with hcase | hcase
      · subst hcase
        exact absurd (show recipient = context from hauth.1) (Ne.symm hne)
      · refine ⟨entry, hcase, ?_⟩
        have transported := AuthorizedAtResolved.transport (after := state)
          nextAccess rfl rfl hauth
        simpa [beforeAccess] using transported

/-- `state.GrantedOfKind` additionally requires the authorizing grant to be of a
particular kind, which is how one provider distinguishes itself from another over
the same table. -/
def GrantedOfKind (state : MemoryState) (kind : GrantKind) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) : Prop :=
  match state.resolveAccess? provenance range with
  | .error _ => False
  | .ok access => ∀ i, i < range.size →
      ∃ entry ∈ state.grantEntries,
        entry.2.kind = kind ∧
          state.AuthorizedAtResolved entry.2 context access (range.start + i) intent

instance (state : MemoryState) (kind : GrantKind) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) :
    Decidable (state.GrantedOfKind kind context provenance range intent) :=
  by unfold GrantedOfKind; split <;> infer_instance

/-- A state with no grants authorizes nothing. Authority is held, not assumed. -/
theorem not_granted_empty (context : ContextId) (provenance : Provenance)
    {range : ByteRange} (_hne : ¬ range.IsEmpty) (intent : AccessIntent) :
    ¬ empty.Granted context provenance range intent := by
  intro h
  unfold Granted at h
  have hr : empty.resolveAccess? provenance range = .error .provenanceNotAllocated := rfl
  rw [hr] at h
  exact h

/-- Refusal predicate for allocation installation and replacement. It keeps a live
allocation's backing/origin binding immutable, blocks record changes while authority
is outstanding over the same backing, prevents a fresh allocation from adopting an
identity still named as any grant's provenance root, and admits only states satisfying
the temporary `DedicatedBackings` runtime profile. -/
private def allocationRefused (state : MemoryState) (id : AllocId)
    (record : AllocationRecord) : Prop :=
  (state.allocations.lookup id = Option.none ∧
    state.grantEntries.any
      (fun entry => decide (entry.2.provenance.root = id)) = true) ∨
  (state.allocations.lookup id).any (fun existing =>
      decide (existing.live = true ∧
        (existing.backing ≠ record.backing ∨ existing.origin ≠ record.origin))) = true ∨
  ((state.allocations.lookup id).any (fun existing => decide (existing ≠ record)) = true ∧
    state.grantEntries.any
      (fun entry => decide (state.SharesBytes entry.2.provenance.root id)) = true) ∨
  ¬ ({ state with allocations := state.allocations.insert id record } :
      MemoryState).DedicatedBackings

instance (state : MemoryState) (id : AllocId) (record : AllocationRecord) :
    Decidable (allocationRefused state id record) := by
  unfold allocationRefused
  infer_instance

def allocate? (state : MemoryState) (id : AllocId) (record : AllocationRecord) :
    Option MemoryState :=
  if allocationRefused state id record then none
  else some { state with allocations := state.allocations.insert id record }

/-- Every admitted allocation transition satisfies the temporary executable backing
layout; this is an enforced door condition, not a caller invariant. -/
theorem dedicatedBackings_allocate? {state next : MemoryState} {id : AllocId}
    {record : AllocationRecord} (h : state.allocate? id record = some next) :
    next.DedicatedBackings := by
  unfold allocate? at h
  split at h
  · contradiction
  · rename_i hadmitted
    injection h with hnext
    subst next
    by_cases hd : ({ state with allocations := state.allocations.insert id record } :
        MemoryState).DedicatedBackings
    · exact hd
    · exact False.elim (hadmitted (Or.inr (Or.inr (Or.inr hd))))

/-- Allocate several records in order, refusing if any is refused.

A fixture building a machine state allocates half a dozen things, and threading
`Option` through that by hand buries the state it is trying to show. One
`isSome` theorem beside the definition is the whole obligation. -/
def allocateAll? (state : MemoryState) :
    List (AllocId × AllocationRecord) → Option MemoryState
  | [] => some state
  | (id, record) :: rest => (state.allocate? id record).bind (·.allocateAll? rest)

/-- What an allocation ends up as: `allocate?` writes the record it was given. -/
theorem allocate?_lookup_self {state next : MemoryState} {id : AllocId}
    {record : AllocationRecord} (h : state.allocate? id record = some next) :
    next.allocations.lookup id = some record := by
  unfold allocate? at h
  split at h
  · contradiction
  · injection h with h
    subst h
    exact FiniteMap.lookup_insert_self _ _ _

/-- And it leaves every other allocation alone. -/
theorem allocate?_lookup_ne {state next : MemoryState} {id other : AllocId}
    {record : AllocationRecord} (h : state.allocate? id record = some next)
    (hne : other ≠ id) : next.allocations.lookup other = state.allocations.lookup other := by
  unfold allocate? at h
  split at h
  · contradiction
  · injection h with h
    subst h
    exact FiniteMap.lookup_insert_ne _ hne _

/-- A fresh identity with no grant still rooted in it is allocatable when the
resulting checked backing layout is supported by the temporary runtime profile. -/
theorem allocate?_isSome_of_fresh (state : MemoryState) (id : AllocId)
    (record : AllocationRecord) (h : state.allocations.lookup id = Option.none)
    (hrootless : state.grantEntries.any
      (fun entry => decide (entry.2.provenance.root = id)) = false)
    (hdedicated : ({ state with allocations := state.allocations.insert id record } :
      MemoryState).DedicatedBackings) :
    (state.allocate? id record).isSome := by
  have hrefuse : ¬ allocationRefused state id record := by
    intro hrefuse
    rcases hrefuse with horphan | hmapping | hgranted | hlayout
    · rw [hrootless] at horphan
      simp at horphan
    · simp [h] at hmapping
    · simp [h] at hgranted
    · exact hlayout hdedicated
  simp [allocate?, hrefuse]

/-- `allocate?_eq_none_of_orphan_grant` proves an absent allocation identity cannot be installed
while any grant still names it as its provenance root. -/
theorem allocate?_eq_none_of_orphan_grant {state : MemoryState} {id : AllocId}
    {record : AllocationRecord} {entry : GrantId × AuthorityGrant}
    (habsent : state.allocations.lookup id = Option.none)
    (hmember : entry ∈ state.grantEntries)
    (hroot : entry.2.provenance.root = id) :
    state.allocate? id record = Option.none := by
  have hrooted : state.grantEntries.any
      (fun candidate => decide (candidate.2.provenance.root = id)) = true := by
    apply List.any_eq_true.2
    exact ⟨entry, hmember, by simp [hroot]⟩
  have hrefuse : allocationRefused state id record :=
    Or.inl ⟨habsent, hrooted⟩
  simp [allocate?, hrefuse]

/-- **Reallocating under an outstanding grant is refused.** §5.1's precondition, as a
refusal rather than as a sentence. -/
theorem allocate?_eq_none_of_outstanding {state : MemoryState} {id : AllocId}
    {record existing : AllocationRecord}
    (hlook : state.allocations.lookup id = some existing)
    (hchange : existing ≠ record)
    (hgrants : state.grantEntries.any
      (fun entry => decide (state.SharesBytes entry.2.provenance.root id)) = true) :
    state.allocate? id record = Option.none := by
  have hrefuse : allocationRefused state id record := by
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact ⟨by simp [hlook, hchange], hgrants⟩
  simp [allocate?, hrefuse]

/-- **A record replaced by an equal one is accepted, grants or not**, which is all the
identity case says.

This theorem took `existing.metadata = record.metadata` and its docstring said "a
permission, liveness or placement change is not a reallocation" -- which was false in
both directions. Permission, liveness and placement are *in* the metadata, so those
changes were refused under an outstanding grant, not accepted; and what the metadata
left out was `owners` and `bytes`, so those changes were accepted, which is the hole
`allocate?`'s guard now closes. Review found the sentence and the hole together. -/
theorem allocate?_isSome_of_same_record {state : MemoryState} {id : AllocId}
    {record existing : AllocationRecord}
    (hlook : state.allocations.lookup id = some existing)
    (hsame : existing = record)
    (hdedicated : ({ state with allocations := state.allocations.insert id record } :
      MemoryState).DedicatedBackings) :
    (state.allocate? id record).isSome := by
  subst existing
  have hrefuse : ¬ allocationRefused state id record := by
    simp [allocationRefused, hlook, hdedicated]
  simp [allocate?, hrefuse]

/-- A record with nothing outstanding may be replaced when a live mapping stays
stable and the resulting layout satisfies `DedicatedBackings`. -/
theorem allocate?_isSome_of_nothing_outstanding {state : MemoryState} {id : AllocId}
    {record : AllocationRecord}
    (hgrants : state.grantEntries.any
      (fun entry => decide (state.SharesBytes entry.2.provenance.root id)) = false) :
    (∀ existing, state.allocations.lookup id = some existing →
      ¬ (existing.live = true ∧
        (existing.backing ≠ record.backing ∨ existing.origin ≠ record.origin))) →
    ({ state with allocations := state.allocations.insert id record } :
      MemoryState).DedicatedBackings →
    (state.allocate? id record).isSome := by
  intro hstable hdedicated
  have hrefuse : ¬ allocationRefused state id record := by
    intro hrefuse
    rcases hrefuse with horphan | hmapping | hgranted | hlayout
    · obtain ⟨entry, hmember, hroot⟩ := List.any_eq_true.1 horphan.2
      have rootEq : entry.2.provenance.root = id := of_decide_eq_true hroot
      have shares : state.SharesBytes entry.2.provenance.root id := Or.inl rootEq
      have outstanding : state.grantEntries.any
          (fun candidate => decide
            (state.SharesBytes candidate.2.provenance.root id)) = true := by
        apply List.any_eq_true.2
        exact ⟨entry, hmember, decide_eq_true shares⟩
      rw [hgrants] at outstanding
      contradiction
    · cases hlook : state.allocations.lookup id with
      | none => simp [hlook] at hmapping
      | some existing =>
          exact hstable existing hlook (by simpa [hlook] using hmapping)
    · rw [hgrants] at hgranted
      simp at hgranted
    · exact hlayout hdedicated
  simp [allocate?, hrefuse]

/-- `orphanGrantAllocationDoorRegression` uses the sealed representation internally
for a malformed orphan-grant pre-state; it does not assert a public construction
sequence or expose an unchecked state-building door. The local pre-fix allocator
admits and revives write authority. The repaired door refuses, while the same
backing/record without the grant and an identical existing record still succeed. -/
private theorem orphanGrantAllocationDoorRegression :
    let allocs : FreshSupply AllocTag := .initial
    let epochs : FreshSupply EpochTag := .initial
    let contexts : FreshSupply ContextTag := .initial
    let grants : FreshSupply GrantTag := .initial
    let storages : FreshSupply StorageTag := .initial
    let id : AllocId := allocs.fresh.1
    let epoch : EpochId := epochs.fresh.1
    let holder : ContextId := contexts.fresh.1
    let lender : ContextId := contexts.fresh.2.fresh.1
    let grantId : GrantId := grants.fresh.1
    let backing : StorageId := storages.fresh.1
    let record : AllocationRecord :=
      { extent := ⟨0, 8⟩, epoch := epoch, space := .cpuVirtual
        source := .virtualAlloc, owners := [lender]
        permission := .readWrite, live := true, backing := backing
        origin := 0, base := some 0x1000 }
    let provenance : Provenance :=
      { space := .cpuVirtual, root := id, epoch := epoch, source := .virtualAlloc
        rootExtent := ⟨0, 8⟩, path := [] }
    let grant : AuthorityGrant :=
      { kind := .loan, holder := holder, lender := lender, provenance := provenance
        range := ⟨0, 8⟩, rights := .readWrite }
    let state : MemoryState :=
      { allocations := .empty
        backings := (FiniteMap.empty).insert backing ⟨8, .empty⟩
        grants := (FiniteMap.empty).insert grantId grant }
    let after : MemoryState :=
      { state with allocations := state.allocations.insert id record }
    let oldRefused : MemoryState → AllocId → AllocationRecord → Prop :=
      fun before target candidate =>
        (before.allocations.lookup target).any (fun existing =>
            decide (existing.live = true ∧
              (existing.backing ≠ candidate.backing ∨ existing.origin ≠ candidate.origin))) = true ∨
        ((before.allocations.lookup target).any (fun existing => decide (existing ≠ candidate)) = true ∧
          before.grantEntries.any
            (fun entry => decide (before.SharesBytes entry.2.provenance.root target)) = true) ∨
        ¬ ({ before with allocations := before.allocations.insert target candidate } :
            MemoryState).DedicatedBackings
    let oldAllocate? : MemoryState → AllocId → AllocationRecord → Option MemoryState :=
      fun before target candidate =>
        if oldRefused before target candidate then none
        else some { before with allocations := before.allocations.insert target candidate }
    oldAllocate? state id record = some after ∧
      after.DedicatedBackings ∧
      after.CurrentEpoch provenance ∧
      after.Granted holder provenance ⟨0, 8⟩ .write ∧
      state.allocate? id record = none ∧
      (({ state with grants := .empty } : MemoryState).allocate? id record).isSome ∧
      (after.allocate? id record).isSome ∧
      (({ state with grants := (FiniteMap.empty).insert grantId (
        { grant with provenance := { provenance with root := allocs.fresh.2.fresh.1 } }) } :
          MemoryState).allocate? id record).isSome := by
  constructor
  · rfl
  · decide

/--
Tear down several allocations at once, or refuse.

§5's arena reset "requires returning all live use loans", and `allocate?` refuses one
reallocation at a time, so a profile resetting an arena walked its allocations itself
and nothing made the walk all-or-nothing: a walk that stopped halfway left some
storage dead and some live, with no record that it had stopped. This is the bulk
operation. Every named allocation ends dead, or `Option.none` and the state is
untouched.

**An identity the table does not hold is refused** rather than treated as already
gone. A caller naming an allocation that was never allocated has lost track of its
arena, and [FOUNDATION.md](../../docs/FOUNDATION.md) law 8 says say so rather than
carry on.

**The grant check is `allocate?`'s**, which is the point of routing through it: a
teardown is a metadata change, so every outstanding grant over the same backing
refuses it, and §5's precondition is the refusal it already was for one allocation.

**What is still owed is the arena itself.** The list comes from the caller, so
nothing here knows it names *every* allocation of the arena being reset — a caller
that forgets one tears down the rest and leaves it live, and this operation cannot
tell. Closing that needs an arena identity on `AllocationRecord`, which §5's model
owes; `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records it.
-/
def tearDown? (state : MemoryState) : List AllocId → Option MemoryState
  | [] => some state
  | id :: rest =>
      (state.allocations.lookup id).bind fun record =>
      (state.allocate? id { record with live := false }).bind (·.tearDown? rest)

/-- `DedicatedBackings.tearDown?` proves that bulk teardown preserves the enforced
layout because each recursive allocation transition passes through `allocate?`. -/
theorem DedicatedBackings.tearDown? {state next : MemoryState} {ids : List AllocId}
    (hdedicated : state.DedicatedBackings) (h : state.tearDown? ids = some next) :
    next.DedicatedBackings := by
  induction ids generalizing state with
  | nil =>
      change some state = some next at h
      injection h with hnext
      subst next
      exact hdedicated
  | cons id rest ih =>
      unfold MemoryState.tearDown? at h
      cases hlookup : state.allocations.lookup id with
      | none => simp [hlookup] at h
      | some record =>
          simp only [hlookup, Option.bind_some] at h
          cases hnext : state.allocate? id { record with live := false } with
          | none => simp [hnext] at h
          | some updated =>
              simp only [hnext, Option.bind_some] at h
              exact ih (dedicatedBackings_allocate? hnext) h

/-- Tearing down nothing changes nothing. -/
@[simp] theorem tearDown?_nil (state : MemoryState) : state.tearDown? [] = some state := rfl

/-- **An identity the table does not hold refuses the whole teardown.** -/
theorem tearDown?_eq_none_of_absent {state : MemoryState} {id : AllocId}
    {rest : List AllocId} (h : state.allocations.lookup id = Option.none) :
    state.tearDown? (id :: rest) = Option.none := by
  unfold tearDown?
  rw [h, Option.bind_none]

/-- **An outstanding grant refuses it**, through `allocate?`. -/
theorem tearDown?_eq_none_of_outstanding {state : MemoryState} {id : AllocId}
    {record : AllocationRecord} {rest : List AllocId}
    (hlook : state.allocations.lookup id = some record) (hlive : record.live = true)
    (hgrants : state.grantEntries.any
      (fun entry => decide (state.SharesBytes entry.2.provenance.root id)) = true) :
    state.tearDown? (id :: rest) = Option.none := by
  unfold tearDown?
  rw [hlook, Option.bind_some]
  have hmeta : record ≠ ({ record with live := false } : AllocationRecord) := by
    intro hcontra
    have : record.live = false := congrArg AllocationRecord.live hcontra
    rw [hlive] at this
    exact absurd this (by simp)
  rw [allocate?_eq_none_of_outstanding hlook hmeta hgrants, Option.bind_none]

/-- A teardown leaves every identity it does not name alone, which is what makes the
law below about the names rather than about the whole table. -/
theorem tearDown?_lookup_of_not_mem {state : MemoryState} :
    ∀ {ids : List AllocId} {next : MemoryState}, state.tearDown? ids = some next →
      ∀ {id : AllocId}, id ∉ ids →
        next.allocations.lookup id = state.allocations.lookup id := by
  intro ids
  induction ids generalizing state with
  | nil =>
    intro next h id _
    injection h with h
    subst h
    rfl
  | cons head rest ih =>
    intro next h id hmem
    unfold tearDown? at h
    cases hlook : state.allocations.lookup head with
    | none => rw [hlook, Option.bind_none] at h; exact absurd h (by simp)
    | some record =>
      rw [hlook, Option.bind_some] at h
      cases hstep : state.allocate? head { record with live := false } with
      | none => rw [hstep, Option.bind_none] at h; exact absurd h (by simp)
      | some stepped =>
        rw [hstep, Option.bind_some] at h
        have hne : id ≠ head := fun hid => hmem (hid ▸ List.mem_cons_self)
        have hrest : id ∉ rest := fun hin => hmem (List.mem_cons_of_mem _ hin)
        rw [ih h hrest, allocate?_lookup_ne hstep hne]

/--
**Everything named is dead afterwards.**

The law the bulk operation exists for, and the one a hand-written walk could not
state: not "each call succeeded" but "every allocation in the list is dead in the
state that came out". Duplicates in the list are harmless — the second teardown of an
identity finds it already dead and `allocate?` accepts a record it already holds.
-/
theorem tearDown?_kills_every_name {state : MemoryState} :
    ∀ {ids : List AllocId} {next : MemoryState}, state.tearDown? ids = some next →
      ∀ id ∈ ids, (next.allocations.lookup id).any (fun record => !record.live) = true := by
  intro ids
  induction ids generalizing state with
  | nil => intro next _ id hmem; exact absurd hmem (by simp)
  | cons head rest ih =>
    intro next h id hmem
    unfold tearDown? at h
    cases hlook : state.allocations.lookup head with
    | none => rw [hlook, Option.bind_none] at h; exact absurd h (by simp)
    | some record =>
      rw [hlook, Option.bind_some] at h
      cases hstep : state.allocate? head { record with live := false } with
      | none => rw [hstep, Option.bind_none] at h; exact absurd h (by simp)
      | some stepped =>
        rw [hstep, Option.bind_some] at h
        rcases List.mem_cons.mp hmem with hcase | hcase
        · subst hcase
          by_cases hlater : id ∈ rest
          · exact ih h id hlater
          · have hkept : next.allocations.lookup id = stepped.allocations.lookup id :=
              tearDown?_lookup_of_not_mem h hlater
            rw [hkept, allocate?_lookup_self hstep]
            rfl
        · exact ih h id hcase

/-- A torn-down allocation is not live, whatever epoch its provenance names.

`tearDown?_kills_every_name` gives not-live; `Live` wants live *and* a matching epoch,
so the first conjunct settles it and the epoch never enters. That asymmetry is why
`AuthorizedAt` had to move off `CurrentEpoch`: teardown does not advance the epoch, so
an epoch check alone sees nothing. -/
theorem not_live_of_tearDown? {state next : MemoryState} {ids : List AllocId}
    {provenance : Provenance} (h : state.tearDown? ids = some next)
    (hmem : provenance.root ∈ ids) : ¬ next.Live provenance := by
  have hkill := tearDown?_kills_every_name h provenance.root hmem
  unfold Live
  cases hlook : next.allocations.lookup provenance.root with
  | none => simp
  | some record =>
      rw [hlook] at hkill
      simp only [Option.any_some, Bool.not_eq_true'] at hkill
      simp [hkill]

/--
**After a teardown, nothing authorizes the torn-down storage.**

The law `g-construct:76` asked for: `withStack` closes every declared exit by tearing
the scope down, and needs the returned outer contract to be unable to authorize what
the scope held. Stated over `Granted` rather than a particular grant, because that is
what an outer contract asks -- is anything in the table authority over these bytes.

It does not lean on the teardown having removed the grants. `tearDown?` refuses while
any is outstanding, so in practice there are none; this says the stronger thing, that
a grant which somehow survived would authorize nothing. Before `AuthorizedAt` consulted
liveness that was false, and two door guards stood in for it -- an emergent property
rather than a law, which is what g-construct could not build on.

The non-empty hypothesis is `Granted`'s: it is vacuously true on an empty range in
every state.
-/
theorem not_granted_of_tearDown? {state next : MemoryState} {ids : List AllocId}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent}
    (h : state.tearDown? ids = some next) (hmem : provenance.root ∈ ids)
    (_hne : ¬ range.IsEmpty) : ¬ next.Granted context provenance range intent := by
  intro hgranted
  unfold Granted at hgranted
  cases hr : next.resolveAccess? provenance range with
  | error failure => simp [hr] at hgranted
  | ok access =>
      have hlive : next.Live provenance := by
        unfold Live
        rw [access.allocationLookup]
        simp [access.allocationLive, access.epochAgrees]
      exact (not_live_of_tearDown? h hmem) hlive

/-! ## Backing-owned byte access and framing -/

/-- Metadata that completely determines spatial and non-initialization denial
decisions for an allocation. Outer `none` means the allocation is missing; a present
record with `capacity := none` means its backing is missing. -/
structure AccessMetadata where
  allocation : AllocationRecord.Metadata
  /-- `none` means this allocated view names no installed backing. -/
  capacity : Option Nat
deriving DecidableEq, Repr

/-- Look up all stable inputs to access resolution. The backing's bytes are omitted;
initialization is compared separately through cells. -/
def MetadataAt (state : MemoryState) (id : AllocId) : Option AccessMetadata :=
  (state.allocations.lookup id).map fun allocation =>
    ⟨allocation.metadata, state.backingCapacity? allocation.backing⟩

/-- Checked observational wrapper for legacy callers. Missing or malformed backing
state fails closed as `none`; executable access paths use `ResolvedAccess.cellAt?`. -/
def cellAtBacking? (state : MemoryState) (span : Coordinates.BackingSpan)
    (offset : Nat) : Option (Byte × Bool) := do
  let backing ← state.backings.lookup span.backing
  if span.range.WithinBound backing.capacity ∧ span.range.Covers offset then
    backing.cellAt? offset
  else none

/-- Checked observational wrapper for legacy callers. Missing or malformed backing
state fails closed as `none`; executable access paths use `ResolvedAccess.cellAt?`. -/
def cellAt? (state : MemoryState) (id : AllocId) (offset : Nat) : Option (Byte × Bool) := do
  let allocation ← state.allocations.lookup id
  if !allocation.live then none else pure ()
  let backing ← state.backings.lookup allocation.backing
  let requested := ByteRange.mk offset 1
  let _ ← Coordinates.resolveRange? allocation.mapping allocation.extent
    backing.capacity requested
  backing.cellAt? (allocation.origin + offset)

/-- Checked byte observation. -/
def byteAt? (state : MemoryState) (id : AllocId) (offset : Nat) : Option Byte :=
  (state.cellAt? id offset).map Prod.fst

/-- Pointwise initialization through the checked observational wrapper. -/
def InitializedAt (state : MemoryState) (id : AllocId) (offset : Nat) : Prop :=
  (state.cellAt? id offset).map Prod.snd = some true

instance (state : MemoryState) (id : AllocId) (offset : Nat) :
    Decidable (state.InitializedAt id offset) :=
  inferInstanceAs (Decidable (_ = _))

/-- Range initialization through one checked allocation/backing resolution. Invalid
bindings are false rather than vacuously initialized. -/
def RangeInitialized (state : MemoryState) (id : AllocId) (range : ByteRange) : Prop :=
  (match state.allocations.lookup id with
  | none => false
  | some allocation =>
      if !allocation.live then false
      else
        match state.backings.lookup allocation.backing with
        | none => false
        | some backing =>
            match Coordinates.resolveRange? allocation.mapping allocation.extent
                backing.capacity range with
            | none => false
            | some resolved => decide (backing.bytes.Initialized resolved.span.range)) = true

instance (state : MemoryState) (id : AllocId) (range : ByteRange) :
    Decidable (state.RangeInitialized id range) := inferInstanceAs (Decidable (_ = true))

/-- Two states agree on every checked allocation-local cell. -/
def AgreesOn (a b : MemoryState) : Prop :=
  ∀ id offset, a.cellAt? id offset = b.cellAt? id offset

theorem AgreesOn.refl (state : MemoryState) : state.AgreesOn state := fun _ _ => rfl
theorem AgreesOn.symm {a b : MemoryState} (h : a.AgreesOn b) : b.AgreesOn a :=
  fun id offset => (h id offset).symm
theorem AgreesOn.trans {a b c : MemoryState} (hab : a.AgreesOn b) (hbc : b.AgreesOn c) :
    a.AgreesOn c := fun id offset => (hab id offset).trans (hbc id offset)

/-- Checked allocation-local observation depends on both the allocation bindings and
the backing table. -/
theorem cellAt?_of_maps_eq {a b : MemoryState}
    (hallocations : a.allocations = b.allocations)
    (hbackings : a.backings = b.backings) (id : AllocId) (offset : Nat) :
    a.cellAt? id offset = b.cellAt? id offset := by
  unfold cellAt?
  rw [hallocations, hbackings]

/-- Authority effects preserve bytes because they preserve both maps consulted by
the checked observation wrapper. -/
theorem cellAt?_applyAuthorityEffect? {state next : MemoryState} {actor : ContextId}
    {effect : AuthorityEffect} (h : state.applyAuthorityEffect? actor effect = some next)
    (id : AllocId) (offset : Nat) : next.cellAt? id offset = state.cellAt? id offset :=
  cellAt?_of_maps_eq (allocations_applyAuthorityEffect? h)
    (backings_applyAuthorityEffect? h) id offset

/-- `writeResolved` commits a bounded byte sequence through the exact prepared access;
its `fits` argument prevents a caller from extending the write past the request. -/
def writeResolved (state : MemoryState) {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (_fits : bytes.length ≤ requested.size) : MemoryState :=
  { state with
    backings := state.backings.insert access.span.backing
      (access.backing.write access.span.range.start bytes initializes) }

/-- Reuse any prepared access after a resolved byte write. The allocation metadata
and backing capacity stay fixed; when both accesses name the written backing, the
certificate retains its updated backing record. -/
def ResolvedAccess.afterWrite {state : MemoryState}
    {queryProvenance writerProvenance : Provenance}
    {queryRange writerRange : ByteRange}
    (query : state.ResolvedAccess queryProvenance queryRange)
    (writer : state.ResolvedAccess writerProvenance writerRange)
    (bytes : ByteSeq) (initializes : Bool) (fits : bytes.length ≤ writerRange.size) :
    (state.writeResolved writer bytes initializes fits).ResolvedAccess
      queryProvenance queryRange := by
  by_cases hsame : query.span.backing = writer.span.backing
  · have hrecord : query.backing = writer.backing := by
      apply Option.some.inj
      calc
        some query.backing = state.backings.lookup query.allocation.backing :=
          query.backingLookup.symm
        _ = state.backings.lookup writer.allocation.backing := by
          simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
            Coordinates.Mapping.span, AllocationRecord.mapping] using
              congrArg (state.backings.lookup ·) hsame
        _ = some writer.backing := writer.backingLookup
    exact
      { query with
        backing := query.backing.write writer.span.range.start bytes initializes
        allocationLookup := query.allocationLookup
        backingLookup := by
          unfold writeResolved
          change (state.backings.insert writer.allocation.backing
              (writer.backing.write writer.span.range.start bytes initializes)).lookup
                query.allocation.backing = _
          have hids : query.allocation.backing = writer.allocation.backing := by
            simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
              Coordinates.Mapping.span, AllocationRecord.mapping] using hsame
          rw [hids, FiniteMap.lookup_insert_self, hrecord]
        coordinates := query.coordinates }
  · exact
      { query with
        allocationLookup := query.allocationLookup
        backingLookup := by
          unfold writeResolved
          have hids : query.allocation.backing ≠ writer.span.backing := by
            simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
              Coordinates.Mapping.span, AllocationRecord.mapping] using hsame
          change (state.backings.insert writer.span.backing
            (writer.backing.write writer.span.range.start bytes initializes)).lookup
              query.allocation.backing = some query.backing
          rw [FiniteMap.lookup_insert_ne _ hids]
          exact query.backingLookup }

@[simp] theorem ResolvedAccess.afterWrite_span {state : MemoryState}
    {queryProvenance writerProvenance : Provenance}
    {queryRange writerRange : ByteRange}
    (query : state.ResolvedAccess queryProvenance queryRange)
    (writer : state.ResolvedAccess writerProvenance writerRange)
    (bytes : ByteSeq) (initializes : Bool) (fits : bytes.length ≤ writerRange.size) :
    (query.afterWrite writer bytes initializes fits).span = query.span := by
  unfold ResolvedAccess.afterWrite
  split <;> rfl

@[simp] theorem ResolvedAccess.afterWrite_allocation {state : MemoryState}
    {queryProvenance writerProvenance : Provenance}
    {queryRange writerRange : ByteRange}
    (query : state.ResolvedAccess queryProvenance queryRange)
    (writer : state.ResolvedAccess writerProvenance writerRange)
    (bytes : ByteSeq) (initializes : Bool) (fits : bytes.length ≤ writerRange.size) :
    (query.afterWrite writer bytes initializes fits).allocation = query.allocation := by
  unfold ResolvedAccess.afterWrite
  split <;> rfl

@[simp] theorem ResolvedAccess.afterWrite_self_backing {state : MemoryState}
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested)
    (bytes : ByteSeq) (initializes : Bool) (fits : bytes.length ≤ requested.size) :
    (access.afterWrite access bytes initializes fits).backing =
      access.backing.write access.span.range.start bytes initializes := by
  unfold ResolvedAccess.afterWrite
  simp

@[simp] theorem allocations_writeResolved (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size) :
    (state.writeResolved access bytes initializes fits).allocations = state.allocations := rfl

@[simp] theorem backings_writeResolved (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size) :
    (state.writeResolved access bytes initializes fits).backings =
      state.backings.insert access.span.backing
        (access.backing.write access.span.range.start bytes initializes) := rfl

@[simp] theorem grantEntries_writeResolved (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size) :
    (state.writeResolved access bytes initializes fits).grantEntries = state.grantEntries := rfl

/-- A resolved covered offset agrees with the checked state wrapper. -/
theorem ResolvedAccess.cellAt?_eq_state {state : MemoryState}
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) {offset : Nat}
    (covered : requested.Covers offset) :
    access.cellAt? offset = state.cellAt? provenance.root offset := by
  have hsingle : access.allocation.extent.Contains (ByteRange.mk offset 1) := by
    apply access.coordinates.withinView.trans
    change requested.start ≤ offset ∧ offset < requested.start + requested.size at covered
    change requested.start ≤ offset ∧ offset + 1 ≤ requested.start + requested.size
    omega
  simp [ResolvedAccess.cellAt?, covered, MemoryState.cellAt?, access.allocationLookup,
    access.backingLookup, access.allocationLive, Coordinates.resolveRange?, hsingle,
    access.coordinates.viewWithinBacking]

/-- Byte projection of `ResolvedAccess.cellAt?_eq_state`. -/
theorem ResolvedAccess.byteAt?_eq_state {state : MemoryState}
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) {offset : Nat}
    (covered : requested.Covers offset) :
    access.byteAt? offset = state.byteAt? provenance.root offset := by
  unfold ResolvedAccess.byteAt? MemoryState.byteAt?
  rw [access.cellAt?_eq_state covered]

/-- The initialization predicate retained by a resolution is the checked state
predicate for that same full query. -/
theorem ResolvedAccess.rangeInitialized_iff_state {state : MemoryState}
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) :
    access.RangeInitialized ↔ state.RangeInitialized provenance.root requested := by
  unfold ResolvedAccess.RangeInitialized
  change access.backing.bytes.Initialized
      (access.allocation.mapping.span requested).range ↔ _
  unfold MemoryState.RangeInitialized
  rw [access.allocationLookup]
  simp only [access.allocationLive, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, access.backingLookup]
  unfold Coordinates.resolveRange?
  have hcoordinates : access.allocation.extent.Contains requested ∧
      (access.allocation.extent.shift access.allocation.mapping.origin).WithinBound
        access.backing.capacity :=
    ⟨access.coordinates.withinView, access.coordinates.viewWithinBacking⟩
  rw [dif_pos hcoordinates]
  simp only [decide_eq_true_eq]
  unfold Coordinates.ResolvedRange.span
  exact Iff.rfl

/-- A resolved write changes backing bytes, never the installed backing capacity. -/
@[simp] theorem backingCapacity?_writeResolved (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size) (id : StorageId) :
    (state.writeResolved access bytes initializes fits).backingCapacity? id =
      state.backingCapacity? id := by
  unfold backingCapacity? writeResolved
  have halook : state.backings.lookup access.span.backing = some access.backing := by
    simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
      Coordinates.Mapping.span, AllocationRecord.mapping] using access.backingLookup
  by_cases h : id = access.span.backing
  · subst id
    simp [halook, BackingRecord.write]
  · simp [h]

/-- `metadataAt_writeResolved` proves that a resolved write preserves the full stable
access metadata view. -/
@[simp] theorem metadataAt_writeResolved (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size) (id : AllocId) :
    (state.writeResolved access bytes initializes fits).MetadataAt id = state.MetadataAt id := by
  unfold MetadataAt
  rw [allocations_writeResolved]
  simp only [backingCapacity?_writeResolved]

/-- `DedicatedBackings.writeResolved` proves that writing through a resolution
preserves the temporary executable backing layout. -/
theorem DedicatedBackings.writeResolved {state : MemoryState}
    (hdedicated : state.DedicatedBackings)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size) :
    (state.writeResolved access bytes initializes fits).DedicatedBackings := by
  unfold DedicatedBackings at hdedicated ⊢
  simpa only [allocations_writeResolved, backingCapacity?_writeResolved] using hdedicated

/-- `rangeInitialized_afterWrite_iff_of_span_disjoint` proves that a disjoint resolved
write preserves initialization of the whole prepared query. The disjointness is
measured against the bytes actually committed. -/
theorem rangeInitialized_afterWrite_iff_of_span_disjoint {state : MemoryState}
    {queryProvenance writerProvenance : Provenance}
    {queryRange writerRange : ByteRange}
    (query : state.ResolvedAccess queryProvenance queryRange)
    (writer : state.ResolvedAccess writerProvenance writerRange)
    (bytes : ByteSeq) (initializes : Bool) (fits : bytes.length ≤ writerRange.size)
    (hd : (writer.prefix bytes.length).span.Disjoint query.span) :
    (query.afterWrite writer bytes initializes fits).RangeInitialized ↔
      query.RangeInitialized := by
  have hsize : bytes.length ≤ writer.span.range.size := by
    simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
      Coordinates.Mapping.span, AllocationRecord.mapping, ByteRange.shift] using fits
  unfold ResolvedAccess.afterWrite
  split
  · rename_i hsame
    have hdrange : (ByteRange.mk writer.span.range.start bytes.length).Disjoint
        query.span.range := by
      unfold Coordinates.BackingSpan.Disjoint at hd
      rcases hd with hbacking | hrange
      · exact absurd hsame.symm hbacking
      · rw [ResolvedAccess.prefix_span] at hrange
        simpa [ByteRange.take, Nat.min_eq_left hsize] using hrange
    exact ByteStore.initialized_write_iff_of_disjoint query.backing.bytes hdrange
  · rfl

/-- A resolved write leaves every disjoint backing span observationally unchanged. -/
theorem cellAtBacking?_writeResolved_of_span_disjoint (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size)
    {span : Coordinates.BackingSpan}
    (hd : (access.prefix bytes.length).span.Disjoint span) (offset : Nat) :
    (state.writeResolved access bytes initializes fits).cellAtBacking? span offset =
      state.cellAtBacking? span offset := by
  have halook : state.backings.lookup access.span.backing = some access.backing := by
    simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
      Coordinates.Mapping.span, AllocationRecord.mapping] using access.backingLookup
  by_cases hbacking : span.backing = access.span.backing
  · have hsize : bytes.length ≤ access.span.range.size := by
      simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
        Coordinates.Mapping.span, AllocationRecord.mapping, ByteRange.shift] using fits
    have hdrange : (ByteRange.mk access.span.range.start bytes.length).Disjoint span.range := by
      unfold Coordinates.BackingSpan.Disjoint at hd
      rcases hd with hne | hrange
      · exact absurd hbacking.symm hne
      · rw [ResolvedAccess.prefix_span] at hrange
        simpa [ByteRange.take, Nat.min_eq_left hsize] using hrange
    by_cases hvalid : span.range.WithinBound access.backing.capacity ∧
        span.range.Covers offset
    · simp [cellAtBacking?, writeResolved, hbacking, halook, hvalid, BackingRecord.write,
        BackingRecord.cellAt?,
        ByteStore.cellAt?_write_of_disjoint access.backing.bytes hdrange hvalid.2]
    · simp [cellAtBacking?, writeResolved, hbacking, halook, hvalid, BackingRecord.write]
  · simp [cellAtBacking?, writeResolved, hbacking]

/-- Under the temporary dedicated-backing profile, a resolved write changes no
checked allocation-local cell outside the source request. Dead or malformed views
remain failed closed on both sides. -/
theorem cellAt?_writeResolved_of_untouched (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size)
    (hdedicated : state.DedicatedBackings) {id : AllocId} {offset : Nat}
    (h : ¬ (provenance.root = id ∧ requested.Covers offset)) :
    (state.writeResolved access bytes initializes fits).cellAt? id offset =
      state.cellAt? id offset := by
  cases hrecord : state.allocations.lookup id with
  | none =>
      simp [MemoryState.cellAt?, writeResolved, hrecord]
  | some record =>
      by_cases hlive : record.live = true
      · by_cases hid : provenance.root = id
        · have hrecords : record = access.allocation := by
            apply Option.some.inj
            exact hrecord.symm.trans (hid ▸ access.allocationLookup)
          subst record
          have hnotCovered : ¬ requested.Covers offset := fun hcovered =>
            h ⟨hid, hcovered⟩
          have hwriteNotCovered :
              ¬ (ByteRange.mk access.span.range.start bytes.length).Covers
                (access.allocation.origin + offset) := by
            intro hcovered
            apply hnotCovered
            rw [ByteRange.covers_def] at hcovered ⊢
            change access.allocation.origin + requested.start ≤
                access.allocation.origin + offset ∧
              access.allocation.origin + offset <
                access.allocation.origin + requested.start + bytes.length at hcovered
            omega
          have hspanBacking : access.allocation.backing = access.span.backing := rfl
          have hspanLookup : state.backings.lookup access.span.backing =
              some access.backing := by
            rw [← hspanBacking]
            exact access.backingLookup
          simp [MemoryState.cellAt?, writeResolved, hrecord, access.allocationLive,
            hspanLookup, hspanBacking, BackingRecord.write, BackingRecord.cellAt?,
            ByteStore.cellAt?_write_of_not_covers access.backing.bytes hwriteNotCovered]
        · have hbackingNe : record.backing ≠ access.span.backing := by
            have hne := hdedicated.backing_ne_of_live_lookup
              access.allocationLookup hrecord access.allocationLive hlive hid
            exact Ne.symm (by
              simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
                Coordinates.Mapping.span, AllocationRecord.mapping] using hne)
          simp [MemoryState.cellAt?, writeResolved, hrecord, hlive, hbackingNe]
      · have hliveFalse : record.live = false := by
          cases hvalue : record.live <;> simp_all
        simp [MemoryState.cellAt?, writeResolved, hrecord, hliveFalse]

/-- Inside the committed prefix, a resolved write determines the checked local
cell. The offset is allocation-local; translation to the backing happens once
through `access.span`. -/
theorem cellAt?_writeResolved_of_covers (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size) {offset : Nat}
    (hcovered : (ByteRange.mk requested.start bytes.length).Covers offset) :
    (state.writeResolved access bytes initializes fits).cellAt?
        provenance.root offset =
      (bytes[offset - requested.start]?).map (·, initializes) := by
  have hrequested : requested.Covers offset := by
    change requested.start ≤ offset ∧
      offset < requested.start + bytes.length at hcovered
    rw [ByteRange.covers_def]
    omega
  let nextAccess := access.afterWrite access bytes initializes fits
  rw [← nextAccess.cellAt?_eq_state hrequested]
  unfold ResolvedAccess.cellAt?
  rw [if_pos hrequested]
  rw [show nextAccess.backing =
      access.backing.write access.span.range.start bytes initializes by
    simp [nextAccess]]
  rw [show nextAccess.allocation = access.allocation by simp [nextAccess]]
  unfold BackingRecord.cellAt?
  change (access.backing.bytes.write access.span.range.start bytes initializes).cellAt?
      (access.allocation.origin + offset) = _
  rw [ByteStore.cellAt?_write_of_covers]
  · congr 2
    unfold ResolvedAccess.span Coordinates.ResolvedRange.span
    simp only [Coordinates.Mapping.span, AllocationRecord.mapping, ByteRange.shift]
    omega
  · change requested.start ≤ offset ∧
      offset < requested.start + bytes.length at hcovered
    unfold ResolvedAccess.span Coordinates.ResolvedRange.span
    simp only [Coordinates.Mapping.span, AllocationRecord.mapping, ByteRange.shift,
      ByteRange.covers_def]
    omega

/-- Byte projection of `cellAt?_writeResolved_of_covers`. -/
theorem byteAt?_writeResolved_of_covers (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (initializes : Bool) (fits : bytes.length ≤ requested.size) {offset : Nat}
    (hcovered : (ByteRange.mk requested.start bytes.length).Covers offset) :
    (state.writeResolved access bytes initializes fits).byteAt?
        provenance.root offset = bytes[offset - requested.start]? := by
  unfold byteAt?
  rw [cellAt?_writeResolved_of_covers state access bytes initializes fits hcovered]
  cases bytes[offset - requested.start]? <;> rfl

/-- Every byte covered by an initializing resolved write is initialized through the
checked allocation-local observation. -/
theorem initializedAt_writeResolved_of_covers (state : MemoryState)
    {provenance : Provenance} {requested : ByteRange}
    (access : state.ResolvedAccess provenance requested) (bytes : ByteSeq)
    (fits : bytes.length ≤ requested.size) {offset : Nat}
    (hcovered : (ByteRange.mk requested.start bytes.length).Covers offset) :
    (state.writeResolved access bytes true fits).InitializedAt provenance.root offset := by
  unfold InitializedAt
  rw [cellAt?_writeResolved_of_covers state access bytes true fits hcovered]
  have hindex : offset - requested.start < bytes.length := by
    change requested.start ≤ offset ∧
      offset < requested.start + bytes.length at hcovered
    omega
  rw [List.getElem?_eq_getElem hindex]
  rfl

private theorem ResolvedAccess.backing_eq_of_span_backing_eq {state : MemoryState}
    {aProvenance bProvenance : Provenance} {aRange bRange : ByteRange}
    (a : state.ResolvedAccess aProvenance aRange)
    (b : state.ResolvedAccess bProvenance bRange)
    (h : a.span.backing = b.span.backing) : a.backing = b.backing := by
  apply Option.some.inj
  calc
    some a.backing = state.backings.lookup a.allocation.backing := a.backingLookup.symm
    _ = state.backings.lookup b.allocation.backing := by
      simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
        Coordinates.Mapping.span, AllocationRecord.mapping] using
          congrArg (state.backings.lookup ·) h
    _ = some b.backing := b.backingLookup

private theorem ResolvedAccess.afterWrite_backing_of_span_eq {state : MemoryState}
    {queryProvenance writerProvenance : Provenance}
    {queryRange writerRange : ByteRange}
    (query : state.ResolvedAccess queryProvenance queryRange)
    (writer : state.ResolvedAccess writerProvenance writerRange)
    (bytes : ByteSeq) (initializes : Bool) (fits : bytes.length ≤ writerRange.size)
    (h : query.span.backing = writer.span.backing) :
    (query.afterWrite writer bytes initializes fits).backing =
      query.backing.write writer.span.range.start bytes initializes := by
  unfold ResolvedAccess.afterWrite
  simp [h]

private theorem ResolvedAccess.afterWrite_backing_of_span_ne {state : MemoryState}
    {queryProvenance writerProvenance : Provenance}
    {queryRange writerRange : ByteRange}
    (query : state.ResolvedAccess queryProvenance queryRange)
    (writer : state.ResolvedAccess writerProvenance writerRange)
    (bytes : ByteSeq) (initializes : Bool) (fits : bytes.length ≤ writerRange.size)
    (h : query.span.backing ≠ writer.span.backing) :
    (query.afterWrite writer bytes initializes fits).backing = query.backing := by
  unfold ResolvedAccess.afterWrite
  simp [h]

/-- Two resolved writes to disjoint physical spans commute observationally. The
prepared accesses for the second write are transported through the first write,
so neither branch repeats backing resolution. -/
theorem writeResolved_comm (state : MemoryState)
    {aProvenance bProvenance : Provenance} {aRange bRange : ByteRange}
    (a : state.ResolvedAccess aProvenance aRange)
    (b : state.ResolvedAccess bProvenance bRange)
    (bytesA bytesB : ByteSeq) (initA initB : Bool)
    (fitsA : bytesA.length ≤ aRange.size) (fitsB : bytesB.length ≤ bRange.size)
    (hd : (a.prefix bytesA.length).span.Disjoint
      (b.prefix bytesB.length).span) :
    let bAfterA := b.afterWrite a bytesA initA fitsA
    let aAfterB := a.afterWrite b bytesB initB fitsB
    ((state.writeResolved a bytesA initA fitsA).writeResolved
        bAfterA bytesB initB fitsB).AgreesOn
      ((state.writeResolved b bytesB initB fitsB).writeResolved
        aAfterB bytesA initA fitsA) := by
  dsimp only
  intro id offset
  by_cases hsame : a.span.backing = b.span.backing
  · have hbacking : a.backing = b.backing := a.backing_eq_of_span_backing_eq b hsame
    have hbAfter := b.afterWrite_backing_of_span_eq a bytesA initA fitsA hsame.symm
    have haAfter := a.afterWrite_backing_of_span_eq b bytesB initB fitsB hsame
    have hsizeA : bytesA.length ≤ a.span.range.size := by
      simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
        Coordinates.Mapping.span, AllocationRecord.mapping, ByteRange.shift] using fitsA
    have hsizeB : bytesB.length ≤ b.span.range.size := by
      simpa [ResolvedAccess.span, Coordinates.ResolvedRange.span,
        Coordinates.Mapping.span, AllocationRecord.mapping, ByteRange.shift] using fitsB
    have hdRange : (ByteRange.mk a.span.range.start bytesA.length).Disjoint
        (ByteRange.mk b.span.range.start bytesB.length) := by
      unfold Coordinates.BackingSpan.Disjoint at hd
      rcases hd with hne | hrange
      · exact absurd hsame hne
      · rw [ResolvedAccess.prefix_span, ResolvedAccess.prefix_span] at hrange
        simpa [ByteRange.take, Nat.min_eq_left hsizeA, Nat.min_eq_left hsizeB] using hrange
    unfold cellAt?
    simp only [allocations_writeResolved, backings_writeResolved,
      ResolvedAccess.afterWrite_span, hbAfter, haAfter]
    cases hallocation : state.allocations.lookup id with
    | none => simp
    | some allocation =>
        cases hlive : allocation.live with
        | false => simp [hlive]
        | true =>
            by_cases hnames : allocation.backing = a.span.backing
            · simp [hlive, hnames, hsame, BackingRecord.capacity_write]
              unfold BackingRecord.cellAt? BackingRecord.write
              rw [← hbacking]
              cases Coordinates.resolveRange? allocation.mapping allocation.extent
                  a.backing.capacity (ByteRange.mk offset 1) with
              | none => rfl
              | some resolved =>
                  exact ByteStore.cellAt?_write_comm a.backing.bytes hdRange
                    (allocation.origin + offset)
            · have hnamesB : allocation.backing ≠ b.span.backing := by
                intro h
                exact hnames (h.trans hsame.symm)
              simp [hnames, hnamesB]
  · have hreverse : b.span.backing ≠ a.span.backing := Ne.symm hsame
    have hbAfter := b.afterWrite_backing_of_span_ne a bytesA initA fitsA hreverse
    have haAfter := a.afterWrite_backing_of_span_ne b bytesB initB fitsB hsame
    have hlookup : ∀ backingId,
        ((state.backings.insert a.span.backing
              (a.backing.write a.span.range.start bytesA initA)).insert
            b.span.backing (b.backing.write b.span.range.start bytesB initB)).lookup backingId =
          ((state.backings.insert b.span.backing
              (b.backing.write b.span.range.start bytesB initB)).insert
            a.span.backing (a.backing.write a.span.range.start bytesA initA)).lookup backingId := by
      intro backingId
      by_cases ha : backingId = a.span.backing
      · subst backingId
        rw [FiniteMap.lookup_insert_ne _ hsame, FiniteMap.lookup_insert_self,
          FiniteMap.lookup_insert_self]
      · by_cases hb : backingId = b.span.backing
        · subst backingId
          rw [FiniteMap.lookup_insert_self, FiniteMap.lookup_insert_ne _ hreverse,
            FiniteMap.lookup_insert_self]
        · rw [FiniteMap.lookup_insert_ne _ hb, FiniteMap.lookup_insert_ne _ ha,
            FiniteMap.lookup_insert_ne _ ha, FiniteMap.lookup_insert_ne _ hb]
    unfold cellAt?
    simp only [allocations_writeResolved, backings_writeResolved,
      ResolvedAccess.afterWrite_span, hbAfter, haAfter]
    cases hallocation : state.allocations.lookup id with
    | none => simp
    | some allocation =>
        cases hlive : allocation.live <;> simp [hlive, hlookup]

/-! ### Placement

`Grass/Memory/Addressing.lean` proves that inside a non-wrapping allocation
distinct offsets have distinct machine addresses. Until an allocation carried a
base there was nothing to instantiate it with, and
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 recorded the offset-to-address debt as
undischarged for exactly that reason. These connect the two.

Placement is not authority in `docs/MEMORY_MODEL.md` §2's sense: provenance decides
what an access may touch, while backing/origin bindings identify stored bytes. It is
not *unread* by `denialOf`, which is a
different claim and was made here — `placementWraps` and
`addressDisagreesWithPlacement` both read the base. What placement answers is the
further question of whether two offsets name the same machine byte. -/

/-- The machine address of an offset in `id`, if `id` is placed at all. -/
def addressAt? (state : MemoryState) (id : AllocId) (offset : Nat) :
    Option MachineAddress :=
  (state.allocations.lookup id).bind (fun record => record.base.map (addressOf · offset))

/--
`state.AddressAgrees d` holds when the access's declared address is the one its
allocation's placement gives the offset it names.

`docs/MEMORY_MODEL.md` §2 makes provenance and not address the authority, which is
why `denialOf` decides on provenance — but an access still *declares* an address,
`MemoryEvent` carries it, and a declaration nothing checks is a declaration that can
say anything. It said anything: every Spike 1 fixture's address contradicted the
placement the same fixture built.

Vacuous where there is nothing to compare — an unplaced allocation, or one that does
not exist. A logical address space has allocations with no machine address at all,
which is why `AllocationRecord.base` is an `Option`, and demanding agreement with an
address that does not exist would force every such profile to invent one.
-/
def AddressAgrees (state : MemoryState) (d : AccessDescriptor) : Prop :=
  match state.addressAt? d.provenance.root d.range.start with
  | some addr => d.address = .numeric addr
  | Option.none => True

instance (state : MemoryState) (d : AccessDescriptor) : Decidable (state.AddressAgrees d) := by
  unfold AddressAgrees
  split <;> infer_instance

/-- `state.PlacedWithoutWrap id` holds when `id`'s bytes do not wrap the address
space **if it is placed at all**.

Both binders are `Option` membership, so this is vacuously true of an unplaced
allocation and of one that does not exist. That is the right shape for a
hypothesis — `addressAt?_ne_of_disjoint` takes `record.base = some base` separately
and only then uses this — but an earlier docstring read it as asserting placement,
which it does not, and `Tests/Memory/Placement.lean`'s deliberately unplaced
allocation satisfies it. -/
def PlacedWithoutWrap (state : MemoryState) (id : AllocId) : Prop :=
  ∀ record ∈ state.allocations.lookup id, ∀ base ∈ record.base,
    FitsAllocation base record.extent.stop

instance (state : MemoryState) (id : AllocId) : Decidable (state.PlacedWithoutWrap id) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _))

/--
**Disjoint ranges in one placed allocation do not alias.**

The bridge `Grass/Memory/Range.lean` records as owed, instantiated at last. Offsets
are `Nat` and disjointness is `Nat` arithmetic; this is what connects that to
machine addresses, for an allocation a profile actually placed.
-/
theorem addressAt?_ne_of_disjoint {state : MemoryState} {id : AllocId}
    (hplaced : state.PlacedWithoutWrap id) {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) {r t : ByteRange}
    (hr : r.WithinBound record.extent.stop) (ht : t.WithinBound record.extent.stop)
    (hd : r.Disjoint t) {i j : Nat} (hi : r.Covers i) (hj : t.Covers j)
    {base : MachineAddress} (hbase : record.base = some base) :
    state.addressAt? id i ≠ state.addressAt? id j := by
  have hfits : FitsAllocation base record.extent.stop :=
    hplaced record (by rw [hfound]; simp) base (by rw [hbase]; simp)
  have hne := disjoint_ranges_do_not_alias hfits hr ht hd hi hj
  unfold addressAt?
  rw [hfound]
  simp only [Option.bind_some]
  rw [hbase]
  simp only [Option.map_some, ne_eq, Option.some.injEq]
  exact hne

/-- **A provenance in a superseded epoch is not live.** `docs/MEMORY_MODEL.md` §2:
address reuse never revives old pointers, and §5 makes an arena advance the epoch
before reusing storage. This is that sentence read as a refusal. -/
theorem not_live_of_stale_epoch {state : MemoryState} {provenance : Provenance}
    {record : AllocationRecord}
    (hlook : state.allocations.lookup provenance.root = some record)
    (hepoch : record.epoch ≠ provenance.epoch) : ¬ state.Live provenance := by
  unfold Live
  rw [hlook]
  simp [hepoch]

/-- **A torn-down allocation is not live**, whatever provenance is presented. -/
theorem not_live_of_dead {state : MemoryState} {provenance : Provenance}
    {record : AllocationRecord}
    (hlook : state.allocations.lookup provenance.root = some record)
    (hdead : record.live = false) : ¬ state.Live provenance := by
  unfold Live
  rw [hlook]
  simp [hdead]

/--
**§10's allocator item, as a proposition this layer states rather than one a profile
names.**

`docs/MEMORY_MODEL.md` §10 asks for "allocator/arena freshness, teardown, and epoch
invalidation". The second of `RequiredProofPackage`'s eleven fields to stop being a
bare `Prop`; see `LoanMapLaws` for why that matters and
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 for which milestone owes each of the nine
that remain.

The allocator requirements couple two points: an identity absent from both the
allocation table and every grant root can be allocated when its checked backing
layout is supported, and `MemoryState.allocate?` refuses an identity
whose *record would change at all* while authority is outstanding over its bytes --
§5.1's precondition.

The second conjunct read "whose metadata would change" and that was the width of the
guard, which review found too narrow: `AllocationRecord.Metadata` omits `owners` and
`bytes`, so a stranger could write itself into an allocation's owner list under
somebody else's outstanding loan and buy §3's authority with it. Teardown says
every name given is dead afterwards and no other name moved. Epoch invalidation is
the two liveness refusals above, which is what makes a stale pointer unusable rather
than merely stale.

What this does not say: that a profile's own allocator is faithful to any of it. It
says the state's allocation table obeys these laws for every profile, so no profile
can close §10's allocator item by naming a weaker sentence.
-/
def AllocatorLaws : Prop :=
  (∀ (state : MemoryState) (id : AllocId) (record : AllocationRecord),
      state.allocations.lookup id = Option.none →
      state.grantEntries.any
        (fun entry => decide (entry.2.provenance.root = id)) = false →
      ({ state with allocations := state.allocations.insert id record } :
        MemoryState).DedicatedBackings →
      (state.allocate? id record).isSome) ∧
  (∀ (state : MemoryState) (id : AllocId) (record existing : AllocationRecord),
      state.allocations.lookup id = some existing →
      existing ≠ record →
      state.grantEntries.any
        (fun entry => decide (state.SharesBytes entry.2.provenance.root id)) = true →
      state.allocate? id record = Option.none) ∧
  (∀ (state next : MemoryState) (id : AllocId) (record : AllocationRecord),
      state.allocate? id record = some next →
      next.allocations.lookup id = some record) ∧
  (∀ (state next : MemoryState) (id other : AllocId) (record : AllocationRecord),
      state.allocate? id record = some next → other ≠ id →
      next.allocations.lookup other = state.allocations.lookup other) ∧
  (∀ (state next : MemoryState) (ids : List AllocId),
      state.tearDown? ids = some next →
      ∀ id ∈ ids, (next.allocations.lookup id).any (fun record => !record.live) = true) ∧
  (∀ (state next : MemoryState) (ids : List AllocId),
      state.tearDown? ids = some next →
      ∀ (id : AllocId), id ∉ ids →
        next.allocations.lookup id = state.allocations.lookup id) ∧
  (∀ (state : MemoryState) (provenance : Provenance) (record : AllocationRecord),
      state.allocations.lookup provenance.root = some record →
      record.epoch ≠ provenance.epoch → ¬ state.Live provenance) ∧
  (∀ (state : MemoryState) (provenance : Provenance) (record : AllocationRecord),
      state.allocations.lookup provenance.root = some record →
      record.live = false → ¬ state.Live provenance)

/-- **The allocator laws hold**, which is the proof every `MemoryProfile` supplies for
§10's allocator item. Its conjuncts are, in order, `allocate?_isSome_of_fresh`,
`allocate?_eq_none_of_outstanding`, `allocate?_lookup_self`, `allocate?_lookup_ne`,
`tearDown?_kills_every_name`, `tearDown?_lookup_of_not_mem`, `not_live_of_stale_epoch`
and `not_live_of_dead`. -/
theorem allocatorLaws : AllocatorLaws :=
  ⟨fun state id record h hr hd => allocate?_isSome_of_fresh state id record h hr hd,
   fun _ _ _ _ hl hc hg => allocate?_eq_none_of_outstanding hl hc hg,
   fun _ _ _ _ h => allocate?_lookup_self h,
   fun _ _ _ _ _ h hne => allocate?_lookup_ne h hne,
   fun _ _ _ h => tearDown?_kills_every_name h,
   fun _ _ _ h _ hmem => tearDown?_lookup_of_not_mem h hmem,
   fun _ _ _ hl he => not_live_of_stale_epoch hl he,
   fun _ _ _ hl hd => not_live_of_dead hl hd⟩

/--
**§10's loan-map item, as a proposition this layer states rather than one a profile
names.**

`docs/MEMORY_MODEL.md` §10 asks for "loan map laws: unique loan identity; split, join,
transfer, reclamation". `RequiredProofPackage` carried that as a bare `Prop` field, so
a profile chose the sentence as well as the proof and `True` closed it. The field's
type is this now, and `MemoryState.loanMapLaws` below is the proof every profile
supplies, so the item is closed by construction and cannot be weakened by the profile
that closes it.

Each conjunct is the statement of a theorem already proved here, in order:
`issue?_eq_none_of_reissued`, `splitGrant?_creates_no_authority`,
`splitGrant?_yields_the_parts`, `joinGrants?_creates_no_authority`,
`joinGrants?_yields_the_join`, `transferGrant?_creates_no_authority`,
`transferGrant?_grants_the_recipient`, `grantAt?_returnGrant?_self` and
`grantAt?_returnGrant?_ne`.

**What this is not.** It is not a claim that the profile proved anything specific to
its target -- the proof is generic and identical for every profile, which is the
correct answer for laws about a map this layer owns. It is a claim that §10's
loan-map sentence now has one meaning across all profiles. The other ten fields of
`RequiredProofPackage` are still `Prop`s a profile names, and
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records which milestone owes each of
them the same treatment.
-/
def LoanMapLaws : Prop :=
  (∀ (state : MemoryState) (id : GrantId) (grant : AuthorityGrant),
      (state.grantAt? id).isSome → state.issue? id grant = Option.none) ∧
  (∀ (state next : MemoryState) (id low high : GrantId) (boundary : Nat)
      (grant : AuthorityGrant) (context : ContextId) (provenance : Provenance)
      (range : ByteRange) (intent : AccessIntent),
      state.splitGrant? id low high boundary = some next →
      state.grantAt? id = some grant →
      next.Granted context provenance range intent →
      state.Granted context provenance range intent) ∧
  (∀ (state next : MemoryState) (id low high : GrantId) (boundary : Nat)
      (grant : AuthorityGrant),
      state.splitGrant? id low high boundary = some next →
      state.grantAt? id = some grant →
      next.grantAt? low = some (grant.lowPart boundary) ∧
      next.grantAt? high = some (grant.highPart boundary) ∧
      next.grantAt? id = Option.none) ∧
  (∀ (state next : MemoryState) (low high into : GrantId)
      (lowGrant highGrant : AuthorityGrant) (context : ContextId)
      (provenance : Provenance) (range : ByteRange) (intent : AccessIntent),
      state.joinGrants? low high into = some next →
      state.grantAt? low = some lowGrant →
      state.grantAt? high = some highGrant →
      next.Granted context provenance range intent →
      state.Granted context provenance range intent) ∧
  (∀ (state next : MemoryState) (low high into : GrantId)
      (lowGrant highGrant : AuthorityGrant),
      state.joinGrants? low high into = some next →
      state.grantAt? low = some lowGrant →
      state.grantAt? high = some highGrant →
      next.grantAt? into = some (lowGrant.joined highGrant) ∧
      next.grantAt? low = Option.none ∧ next.grantAt? high = Option.none) ∧
  (∀ (state next : MemoryState) (actor : ContextId) (id : GrantId)
      (recipient : ContextId) (grant : AuthorityGrant) (context : ContextId)
      (provenance : Provenance) (range : ByteRange) (intent : AccessIntent),
      state.transferGrant? actor id recipient = some next →
      state.grantAt? id = some grant → context ≠ recipient →
      next.Granted context provenance range intent →
      state.Granted context provenance range intent) ∧
  (∀ (state next : MemoryState) (actor : ContextId) (id : GrantId)
      (recipient : ContextId) (grant : AuthorityGrant) (provenance : Provenance)
      (range : ByteRange) (intent : AccessIntent)
      (access : state.ResolvedAccess provenance range)
      (grantSpan : Coordinates.BackingSpan),
      state.transferGrant? actor id recipient = some next →
      state.grantAt? id = some grant →
      state.resolveAccess? provenance range = .ok access →
      state.grantSpan? grant = .ok grantSpan →
      grantSpan.Contains access.span →
      state.CurrentEpoch grant.provenance →
      grant.rights.Permits intent →
      next.Granted recipient provenance range intent) ∧
  (∀ (state returned : MemoryState) (context : ContextId) (id : GrantId),
      state.returnGrant? context id = some returned →
      returned.grantAt? id = Option.none) ∧
  (∀ (state returned : MemoryState) (context : ContextId) (id other : GrantId),
      state.returnGrant? context id = some returned → other ≠ id →
      returned.grantAt? other = state.grantAt? other)

/-- **The loan-map laws hold**, which is the proof every `MemoryProfile` supplies for
§10's loan-map item. Nothing about it is profile-specific, and that is the point: the
item is discharged by this layer for every target, so no profile can close §10 by
naming a weaker sentence. -/
theorem loanMapLaws : LoanMapLaws :=
  ⟨fun state _ grant h => issue?_eq_none_of_reissued state grant h,
   fun _ _ _ _ _ _ _ _ _ _ _ h hat hg => splitGrant?_creates_no_authority h hat hg,
   fun _ _ _ _ _ _ _ h hat => splitGrant?_yields_the_parts h hat,
   fun _ _ _ _ _ _ _ _ _ _ _ h hl hh hg => joinGrants?_creates_no_authority h hl hh hg,
   fun _ _ _ _ _ _ _ h hl hh => joinGrants?_yields_the_join h hl hh,
   fun _ _ _ _ _ _ _ _ _ _ h hat hne hg =>
     transferGrant?_creates_no_authority h hat hne hg,
   fun _ _ _ _ _ _ _ _ _ _ _ h hat hresolve hspan hcover hcurrent hrights =>
     transferGrant?_grants_the_recipient h hat hresolve hspan hcover hcurrent hrights,
   fun _ _ _ _ h => grantAt?_returnGrant?_self h,
   fun _ _ _ _ _ h hne => grantAt?_returnGrant?_ne h hne⟩

end MemoryState

/--
One architectural fault that was raised.

`docs/MEMORY_MODEL.md` §8: "Architectural faults are modeled events/transitions."
A faulting substep that performs no memory access — a divide error between two
operand reads, say — produces no `MemoryEvent`, so without this record the fault
leaves no trace and a faulting execution is indistinguishable from a clean one.
That was true of an earlier transition, which took the fault as an argument and
dropped it on the branch where the faulting substep was not an access.

This is not the fault *model*. It records that a fault of a named class was
raised by a named context at a named substep; the ISA profile owns what each
class means, and `docs/SEMANTICS.md` owns how a fault reaches the program result.
-/
structure RaisedFault where
  /-- Which fault was raised. -/
  fault : FaultClassId
  /-- The context it was raised in. -/
  context : ContextId
  /-- The instruction or API that raised it. -/
  cause : EventCause
  /-- The index of the substep that did not complete. -/
  substep : Nat
deriving DecidableEq, Repr

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

  `ValidMemoryEvent`, not `MemoryEvent`: every event in the trace carries its own
  well-formedness proof, so the property holds by construction rather than by a
  check something could forget. An earlier trace held bare events beside a
  predicate nothing consulted, and every event the transition minted violated it.

  A malformed trace is unrepresentable outside the event module:
  `ValidMemoryEvent.mk` is private and `MemoryEvent.ofOutcome` is the only
  producer. That claim was withdrawn when the constructor was public and review
  assembled a contradictory event; sealing is what makes it true rather than
  aspirational.

  It is still only as strong as the fields. Two of them went uncompared until that
  review, so sealing stops a bypass and does not stop a weak clause. -/
  events : List ValidMemoryEvent
  /-- The supply that mints event identities. -/
  eventSupply : FreshSupply EventTag
  /-- The architectural faults raised so far, most recent last.

  Separate from `events` because a fault is not a memory event: it may touch no
  bytes, and `MemoryEvent` requires a location. Separate from `violations`
  because `docs/MEMORY_MODEL.md` §8 draws exactly that line — a fault is
  behaviour a specification may permit, a violation is behaviour
  `VerifiedProgram` proves never happens. -/
  faults : List RaisedFault
  /-- What kind of execution context each identity is.

  `docs/MEMORY_MODEL.md` §7.1 requires an event to carry execution context
  identity *and* kind. The identity came from the access descriptor and the kind
  from an argument to `step`, with nothing relating them, so the same
  `ContextId` could be stepped as a thread once and a device engine the next time
  and each event carried whatever pair the caller supplied. Two sources of truth
  for one fact, which is the defect this layer keeps finding; review found this
  instance after the identity half was closed and the kind half was not.

  A context's kind is a fact about the machine, so it lives in the state. `step`
  refuses an identity whose kind disagrees with what is recorded here, and records
  the pairing the first time it sees one. -/
  contexts : FiniteMap ContextId ContextKind

namespace MachineState

/-- The state a program starts in. -/
def initial (memory : MemoryState) : MachineState :=
  { memory := memory, obligations := .empty, violations := .empty
    events := [], eventSupply := .initial, faults := [], contexts := .empty }

/--
`state.FaultsRecognized recognized` holds when every fault the state has recorded is
of a class the list names.

`docs/MEMORY_MODEL.md` §8: "`VerifiedProgram` proves the ledger remains empty **and
that only spec-allowed fault outcomes occur**." The first conjunct has
`AuditViolationLedger.IsEmpty`, `Extends`, and `Grass.Op.step_extends_violations`. The
second had nothing: `faults` was appended to by `runStep` and read by no predicate
anywhere under `Grass/`, only by fixture assertions, so there was no analogue of
`IsEmpty` for a `VerifiedProgram` to prove. Review found it, and found that no
milestone owned it either.

This is the half of §8's second conjunct this layer can state. "Spec-allowed" is a
profile's word, and a profile's fault vocabulary is the list it declares — so a fault
outside it is a fault the profile never modelled, which
`Grass/Op/Step.lean` refuses at declaration time through `faultClassNotDeclared` and
`operationFaultNotRecognized`. What this adds is the *state-level* statement those
refusals make true, so a consumer has something to carry rather than an argument about
which gates ran.

What it is **not** is the whole conjunct. §8's "spec-allowed" is a claim about which
outcomes a specification permits at a given point, and that needs the specification —
`docs/SEMANTICS.md`'s, not this layer's. Recorded in
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2.
-/
def FaultsRecognized (state : MachineState) (recognized : List FaultClassId) : Prop :=
  ∀ raised ∈ state.faults, raised.fault ∈ recognized

instance (state : MachineState) (recognized : List FaultClassId) :
    Decidable (state.FaultsRecognized recognized) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The initial state has recorded no fault, so every list recognises them. -/
@[simp] theorem faultsRecognized_initial (memory : MemoryState)
    (recognized : List FaultClassId) :
    (MachineState.initial memory).FaultsRecognized recognized := by
  intro raised hmem
  simp [MachineState.initial] at hmem

/-- Recognition is monotone in the list, so a profile that declares more still
recognises what a narrower one did. -/
theorem FaultsRecognized.mono {state : MachineState} {a b : List FaultClassId}
    (h : state.FaultsRecognized a) (hsub : ∀ f ∈ a, f ∈ b) :
    state.FaultsRecognized b := fun raised hmem => hsub _ (h raised hmem)

/-- **A state that has recorded a fault outside the list does not satisfy it.** The
discriminating direction: without it the predicate would hold of every state whose
`faults` list the checker happened not to look at. -/
theorem not_faultsRecognized_of_mem {state : MachineState} {recognized : List FaultClassId}
    {raised : RaisedFault} (hmem : raised ∈ state.faults)
    (h : raised.fault ∉ recognized) : ¬ state.FaultsRecognized recognized :=
  fun hr => h (hr raised hmem)

/-- `state.KindAgrees context kind` holds when the state has not already recorded
a different kind for that identity. A context the state has never seen agrees with
any kind, and is recorded by `noteContext`. -/
def KindAgrees (state : MachineState) (context : ContextId) (kind : ContextKind) : Prop :=
  state.contexts.lookup context = Option.none ∨
    state.contexts.lookup context = some kind

instance (state : MachineState) (context : ContextId) (kind : ContextKind) :
    Decidable (state.KindAgrees context kind) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Record the pairing, so a later step with a different kind disagrees. -/
def noteContext (state : MachineState) (context : ContextId) (kind : ContextKind) :
    MachineState :=
  { state with contexts := state.contexts.insert context kind }

/-- Recording a context's kind touches nothing else, so a framing argument passes
straight through it. -/
@[simp] theorem noteContext_memory (state : MachineState) (context : ContextId)
    (kind : ContextKind) : (state.noteContext context kind).memory = state.memory := rfl

/-- Recording a pairing makes it agree, and makes every other kind disagree. -/
@[simp] theorem kindAgrees_noteContext (state : MachineState) (context : ContextId)
    (kind : ContextKind) : (state.noteContext context kind).KindAgrees context kind :=
  .inr (by simp [noteContext])

theorem not_kindAgrees_noteContext_of_ne (state : MachineState) (context : ContextId)
    {kind other : ContextKind} (h : other ≠ kind) :
    ¬ (state.noteContext context kind).KindAgrees context other := by
  rintro (hn | hs)
  · simp [noteContext] at hn
  · simp [noteContext] at hs
    exact h hs.symm

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
