import Grass.Memory.Addressing
import Grass.Memory.ByteStore
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
  /-- The allocation's bytes.

  Initialization is read off this rather than tracked beside it: a separate list
  of initialized offsets was a second source of truth that could disagree with
  the values, and `RangeInitialized` now cannot drift from what was written. -/
  bytes : ByteStore
  /-- Where the allocation sits in its address space, if it sits anywhere.

  `Option`, and not because placement is optional bookkeeping. `docs/MEMORY_MODEL.md`
  §7.5 makes address spaces non-interchangeable and a logical space — a SPIR-V
  `Private` storage class, say — has allocations with no machine address at all, so
  a mandatory base would force every profile to invent one. Placement is also not
  authority: §2 makes provenance decide what an access may touch, and nothing in
  `denialOf` reads this. It is here so `Grass/Memory/Addressing.lean`'s bridge can
  be instantiated, which §4.2 recorded as owed for as long as no allocation carried
  an address.

  No default. A profile placing an allocation says where; a profile that does not
  place it says `none` deliberately. -/
  base : Option MachineAddress
deriving DecidableEq, Repr

/--
Everything about an allocation except its bytes.

`denialOf` reads exactly these six fields plus initialization, so this is the
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
  /-- The permission its storage carries. -/
  permission : Permission
  /-- Whether it is live. -/
  live : Bool
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
  ⟨record.extent, record.epoch, record.space, record.permission, record.live, record.base⟩

/--
The memory state.

`aliases` is symmetric by convention and `SharesBytes` closes it, so a profile
declares each aliased pair once.
-/
structure MemoryState where
  private mk ::
  /-- The live and dead allocations. -/
  allocations : FiniteMap AllocId AllocationRecord
  /-- Pairs of allocations whose bytes are the same storage. -/
  aliases : List (AllocId × AllocId)
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
def empty : MemoryState := { allocations := .empty, aliases := [], grants := .empty }

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

So the field is private and the two operations that change it are here:
`issueGrant?` and `returnGrant?`. `Grass/Memory/Loan.lean` states §3's laws over
them and adds the loan-specific refusals; `grantEntries` and `grantAt?` are the
read-only views everything else uses.

**And `mk` is private too**, which is the third time this hole has been closed.
Marking the *field* private privatises the projection and leaves the constructor
alone, so `MemoryState.mk allocations aliases ⟨…⟩` still built any map at all —
review rebuilt `Tests/Op/StandardLoan.lean`'s own lent state with the loan filtered
out of `grantEntries`, and the thread's store committed. That is the same failure
`Grass/Memory/ByteStore.lean`'s comment records for `ByteStore.rec`, and this module
had it while claiming there was no second door. `MemoryState.rec` cannot construct,
so with `mk` private the map is reachable only through the two mutators.
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

/-- The grants outstanding, as a read-only view. -/
def grantEntries (state : MemoryState) : List (GrantId × AuthorityGrant) :=
  state.grants.entries

/-- The grant an identity names, if it names one. -/
def grantAt? (state : MemoryState) (id : GrantId) : Option AuthorityGrant :=
  state.grants.lookup id

/-- Record a grant under a fresh identity, or refuse.

The identity rule only. `Grass/Memory/Loan.lean`'s `issue?` is the door a caller
uses: it adds §7.3's conflict refusal and the checks that a grant is over live,
current, in-extent bytes. This exists separately because those checks need
definitions that live above this module, and the *field* has to be sealed here. -/
def issueGrant? (state : MemoryState) (id : GrantId) (grant : AuthorityGrant) :
    Option MemoryState :=
  if (state.grants.lookup id).isSome then Option.none
  else some { state with grants := state.grants.insert id grant }

/-- Remove the grant an identity names, if this context may. -/
def returnGrant? (state : MemoryState) (context : ContextId) (id : GrantId) :
    Option MemoryState :=
  match state.grants.lookup id with
  | some grant =>
      if grant.holder = context ∨ grant.lender = context then
        some { state with grants := state.grants.erase id }
      else Option.none
  | Option.none => Option.none

@[simp] theorem grantAt?_eq_lookup (state : MemoryState) (id : GrantId) :
    state.grantAt? id = state.grants.lookup id := rfl

@[simp] theorem grantEntries_eq (state : MemoryState) :
    state.grantEntries = state.grants.entries := rfl

/-- A successful issue records the grant under the identity it names. -/
theorem grantAt?_issueGrant?_self {state issued : MemoryState} {id : GrantId}
    {grant : AuthorityGrant} (h : state.issueGrant? id grant = some issued) :
    issued.grantAt? id = some grant := by
  unfold issueGrant? at h
  split at h
  · exact absurd h (by simp)
  · injection h with h
    subst h
    exact FiniteMap.lookup_insert_self _ _ _

/-- **A reissued identity is refused**, which is §3's "a return consumes that exact
identity" read from the other side: an identity is consumed by a return and by
nothing else. -/
theorem issueGrant?_eq_none_of_reissued (state : MemoryState) {id : GrantId}
    (grant : AuthorityGrant) (h : (state.grantAt? id).isSome) :
    state.issueGrant? id grant = Option.none := by
  unfold issueGrant?
  rw [if_pos (show (state.grants.lookup id).isSome from h)]

/-- An issue happens only into a free identity. -/
theorem grantAt?_eq_none_of_issueGrant? {state issued : MemoryState} {id : GrantId}
    {grant : AuthorityGrant} (h : state.issueGrant? id grant = some issued) :
    state.grantAt? id = Option.none := by
  unfold issueGrant? at h
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

/-- One declared aliasing hop, in either direction. Aliasing is symmetric by
convention and this is where the convention is discharged. -/
def AliasHop (state : MemoryState) (a b : AllocId) : Prop :=
  (a, b) ∈ state.aliases ∨ (b, a) ∈ state.aliases

instance (state : MemoryState) (a b : AllocId) : Decidable (state.AliasHop a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- `state.SharesAfter n a b` holds when `b` is reachable from `a` in at most `n`
declared hops. The bounded form, so the closure below is decidable. -/
def SharesAfter (state : MemoryState) : Nat → AllocId → AllocId → Prop
  | 0, a, b => a = b
  | n + 1, a, b =>
      a = b ∨ ∃ mid ∈ state.allocations.domain, state.AliasHop a mid ∧
        state.SharesAfter n mid b

instance decSharesAfter (state : MemoryState) : (n : Nat) → (a b : AllocId) →
    Decidable (state.SharesAfter n a b)
  | 0, _, _ => inferInstanceAs (Decidable (_ = _))
  | n + 1, _, b =>
      have : ∀ mid, Decidable (state.SharesAfter n mid b) := fun mid =>
        decSharesAfter state n mid b
      inferInstanceAs (Decidable (_ ∨ ∃ _ ∈ _, _))

/--
`state.SharesBytes a b` holds when two allocations name the same storage.

**Transitively.** `docs/MEMORY_MODEL.md` §7.5 makes mapping, pinning and sharing
typed transitions, and those compose: a profile that declares a file aliased to a
view, and that view aliased to a second view, has said all three name the same
bytes. This was a single hop, so the two ends of such a chain were declared
non-conflicting and a cross-context write to the far end committed with no
violation — the same defect `SharesBytes` was introduced to fix, one hop further
out. Local adversarial review built the chain.

The bound is the number of declared aliases, which is the longest simple path any
chain can have, so `SharesAfter` at that bound is the full closure and stays
decidable.
-/
def SharesBytes (state : MemoryState) (a b : AllocId) : Prop :=
  state.SharesAfter state.aliases.length a b

instance (state : MemoryState) (a b : AllocId) : Decidable (state.SharesBytes a b) :=
  inferInstanceAs (Decidable (state.SharesAfter _ a b))

theorem sharesAfter_zero_of_eq {state : MemoryState} {n : Nat} {a b : AllocId}
    (h : a = b) : state.SharesAfter n a b := by
  cases n with
  | zero => exact h
  | succ m => exact .inl h

theorem sharesBytes_refl (state : MemoryState) (a : AllocId) : state.SharesBytes a a :=
  sharesAfter_zero_of_eq rfl

/-- One declared hop shares bytes, provided the intermediate allocation exists.
The direction a profile's `alias` declaration is used in. -/
theorem sharesBytes_of_hop {state : MemoryState} {a b : AllocId}
    (hhop : state.AliasHop a b) (hb : b ∈ state.allocations.domain)
    (hpos : 0 < state.aliases.length) : state.SharesBytes a b := by
  unfold SharesBytes
  cases hn : state.aliases.length with
  | zero => omega
  | succ m => exact .inr ⟨b, hb, hhop, sharesAfter_zero_of_eq rfl⟩

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

/--
`state.AuthorizedBy grant context provenance range intent` holds when this grant
lets `context` perform that access, in this state.

Six clauses: the holder is the context performing the access, the grant is over the
same *bytes*, both provenances are current, the grant's range covers the access's,
and the rights permit the intent.

**On the state, and using `SharesBytes`.** This was the deleted `Authorizes` function, a
pure function on provenances using `Provenance.SameStorage` — equal `space`, `root`
and `epoch`. That is the relation this layer has now moved off twice for being
wrong in the unsafe direction, and leaving it here made it wrong in the *other*
direction: `MemoryState.grantsOver` sees aliases and this did not, so a holder
reaching its own lent bytes through a declared alias was frozen by its own loan and
authorized by nothing. §7.5's mapped file and host-visible device buffer are exactly
that shape. Whether two allocations name the same bytes is a fact about the state,
so this takes the state.

The `space` conjunct is gone with `SameStorage` and is not replaced. An access is
checked against its own allocation's space by `AccessDescriptor.WellFormedIn` and by
`denialOf`; requiring the *grant* to name the same space as well would refuse a
device engine's grant over a host-visible buffer, which is the case §7.5 exists to
describe.

`Contains` compares offsets relative to a root, and aliased allocations are assumed
to agree offset for offset — `MemoryState.aliases` records no offset mapping.
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 records that.
-/
def AuthorizedBy (state : MemoryState) (grant : AuthorityGrant) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) : Prop :=
  grant.holder = context ∧
  state.SharesBytes grant.provenance.root provenance.root ∧
  state.CurrentEpoch grant.provenance ∧
  state.CurrentEpoch provenance ∧
  grant.range.Contains range ∧
  grant.rights.Permits intent

instance (state : MemoryState) (grant : AuthorityGrant) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) :
    Decidable (state.AuthorizedBy grant context provenance range intent) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A grant held by one context authorizes nothing for another. Authority is not
ambient: `docs/FOUNDATION.md` law 6 forbids ambient provider choice, and the same
reading applies to authority a context did not receive. -/
theorem not_authorizedBy_of_other_holder {state : MemoryState} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent} (h : grant.holder ≠ context) :
    ¬ state.AuthorizedBy grant context provenance range intent := fun ha => h ha.1

/-- A grant over storage that does not share bytes with the access authorizes
nothing, however their offsets compare (`docs/MEMORY_MODEL.md` §7.5). -/
theorem not_authorizedBy_of_other_storage {state : MemoryState} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent}
    (h : ¬ state.SharesBytes grant.provenance.root provenance.root) :
    ¬ state.AuthorizedBy grant context provenance range intent := fun ha => h ha.2.1

/-- A read-only grant does not authorize a write. -/
theorem not_authorizedBy_of_insufficient_rights {state : MemoryState}
    {grant : AuthorityGrant} {context : ContextId} {provenance : Provenance}
    {range : ByteRange} {intent : AccessIntent} (h : ¬ grant.rights.Permits intent) :
    ¬ state.AuthorizedBy grant context provenance range intent := fun ha => h ha.2.2.2.2.2

/-- A grant over a defunct epoch authorizes nothing, and neither does any grant to a
stale pointer. §2's reuse rule, at the authority gate. -/
theorem not_authorizedBy_of_stale_epoch {state : MemoryState} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent} (h : ¬ state.CurrentEpoch provenance) :
    ¬ state.AuthorizedBy grant context provenance range intent := fun ha => h ha.2.2.2.1

/--
`state.Granted context provenance range intent` holds when some live grant
authorizes that access.

Existentially quantified over the grant, because an access does not name the one
it relies on; see `Grass/Memory/Authority.lean`. Decidable because the grant table
is finite.
-/
def Granted (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) : Prop :=
  ∃ entry ∈ state.grantEntries,
    state.AuthorizedBy entry.2 context provenance range intent

instance (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) :
    Decidable (state.Granted context provenance range intent) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- `state.GrantedOfKind` additionally requires the authorizing grant to be of a
particular kind, which is how one provider distinguishes itself from another over
the same table. -/
def GrantedOfKind (state : MemoryState) (kind : GrantKind) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) : Prop :=
  ∃ entry ∈ state.grantEntries,
    entry.2.kind = kind ∧ state.AuthorizedBy entry.2 context provenance range intent

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

/-- Record a new allocation. -/
def allocate (state : MemoryState) (id : AllocId) (record : AllocationRecord) :
    MemoryState :=
  { state with allocations := state.allocations.insert id record }

/-- Declare that two allocations name the same storage. -/
def alias (state : MemoryState) (a b : AllocId) : MemoryState :=
  { state with aliases := (a, b) :: state.aliases }

/--
Write `bytes` at `start` in allocation `id`.

`initializes` is `AccessDescriptor.producesInitialized`: a completed write does
not always credit initialization, and `ByteStore` carries that per run so the two
facts cannot disagree. A write to an allocation that is not there changes
nothing; `performAccess` reaches this only after `denialOf` has found the record,
so the missing case is unreachable there rather than silently permissive.
-/
def write (state : MemoryState) (id : AllocId) (start : Nat) (bytes : ByteSeq)
    (initializes : Bool) : MemoryState :=
  match state.allocations.lookup id with
  | Option.none => state
  | some record =>
      { state with
        allocations := state.allocations.insert id
          { record with bytes := record.bytes.write start bytes initializes } }

/-- The byte allocation `id` holds at `offset`, if it holds one. -/
def byteAt? (state : MemoryState) (id : AllocId) (offset : Nat) : Option Byte :=
  (state.allocations.lookup id).bind (·.bytes.byteAt? offset)

/-- What allocation `id` holds at `offset`: the byte and whether it counts as
initialized. Both from one lookup, for the reason `ByteStore.cellAt?` gives. -/
def cellAt? (state : MemoryState) (id : AllocId) (offset : Nat) : Option (Byte × Bool) :=
  (state.allocations.lookup id).bind (·.bytes.cellAt? offset)

/-- The byte is the cell's first component. Both go through one lookup, so a
framing fact proved for cells is immediately a framing fact for bytes. -/
@[simp] theorem byteAt?_eq_map_cellAt? (state : MemoryState) (id : AllocId) (offset : Nat) :
    state.byteAt? id offset = (state.cellAt? id offset).map Prod.fst := by
  unfold byteAt? cellAt? ByteStore.byteAt?
  cases state.allocations.lookup id <;> simp

/-- `state.InitializedAt id offset` holds when that byte is initialized. The
pointwise form of `RangeInitialized`, which a padding argument needs because
padding is a set of offsets rather than a range. -/
def InitializedAt (state : MemoryState) (id : AllocId) (offset : Nat) : Prop :=
  (state.cellAt? id offset).map Prod.snd = some true

instance (state : MemoryState) (id : AllocId) (offset : Nat) :
    Decidable (state.InitializedAt id offset) :=
  inferInstanceAs (Decidable (_ = _))

/-- `state.RangeInitialized id range` holds when every offset of `range` is
initialized in `id`. Read off the byte store, so it says what the writes said. -/
def RangeInitialized (state : MemoryState) (id : AllocId) (range : ByteRange) : Prop :=
  match state.allocations.lookup id with
  | Option.none => False
  | some record => record.bytes.Initialized range

instance (state : MemoryState) (id : AllocId) (range : ByteRange) :
    Decidable (state.RangeInitialized id range) := by
  unfold RangeInitialized; split <;> infer_instance

/-! ### Framing

What a write does *not* change. `applyAccess` reasons by disjointness, and
disjointness is only useful with lemmas saying that everything outside the
written range survives. `docs/MEMORY_MODEL.md` §2 makes provenance the authority,
so the two axes are "a different allocation" and "a disjoint range within the
same one"; both are below. -/

/-- A write changes no allocation's metadata: extent, epoch, space, permission,
and liveness come back unchanged. `denialOf` reads exactly those five fields, so
`write_preserves_metadata` is what says a write cannot quietly widen what a later
access may reach. -/
theorem write_preserves_metadata (state : MemoryState) (id : AllocId) (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) (other : AllocId) (record : AllocationRecord)
    (h : (state.write id start bytes initializes).allocations.lookup other = some record) :
    ∃ before, state.allocations.lookup other = some before ∧
      before.extent = record.extent ∧ before.epoch = record.epoch ∧
      before.space = record.space ∧ before.permission = record.permission ∧
      before.live = record.live := by
  unfold write at h
  split at h
  · exact ⟨record, h, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i found hfound
    by_cases hid : other = id
    · subst hid
      rw [FiniteMap.lookup_insert_self] at h
      cases h
      exact ⟨found, hfound, rfl, rfl, rfl, rfl, rfl⟩
    · rw [FiniteMap.lookup_insert_ne _ hid _] at h
      exact ⟨record, h, rfl, rfl, rfl, rfl, rfl⟩

/-- **A write to one allocation leaves every other allocation alone.**

Distinct `AllocId`s are distinct storage by construction, which is what
`docs/MEMORY_MODEL.md` §2 means by making provenance rather than address the
authority. -/
theorem write_preserves_other_allocation (state : MemoryState) {id other : AllocId}
    (hne : other ≠ id) (start : Nat) (bytes : ByteSeq) (initializes : Bool) :
    (state.write id start bytes initializes).allocations.lookup other =
      state.allocations.lookup other := by
  unfold write
  split
  · rfl
  · exact FiniteMap.lookup_insert_ne _ hne _

/-- Initialization of another allocation survives a write. -/
theorem rangeInitialized_write_of_other_allocation (state : MemoryState)
    {id other : AllocId} (hne : other ≠ id) (start : Nat) (bytes : ByteSeq)
    (initializes : Bool) {range : ByteRange} (h : state.RangeInitialized other range) :
    (state.write id start bytes initializes).RangeInitialized other range := by
  unfold RangeInitialized at h ⊢
  rw [write_preserves_other_allocation state hne start bytes initializes]
  exact h

/-- **Initialization of a disjoint range in the same allocation survives a
write.** The state-level form of `ByteStore.initialized_write_of_disjoint`, and
the one a framing argument about two fields of one object needs. -/
theorem rangeInitialized_write_of_disjoint (state : MemoryState) (id : AllocId)
    {start : Nat} {bytes : ByteSeq} {initializes : Bool} {range : ByteRange}
    (hd : (ByteRange.mk start bytes.length).Disjoint range)
    (h : state.RangeInitialized id range) :
    (state.write id start bytes initializes).RangeInitialized id range := by
  unfold RangeInitialized at h ⊢
  unfold write
  cases hfound : state.allocations.lookup id with
  | none => rw [hfound] at h; exact absurd h (by simp)
  | some record =>
    rw [hfound] at h
    rw [FiniteMap.lookup_insert_self]
    exact ByteStore.initialized_write_of_disjoint record.bytes hd h

/--
Two memory states agree when every allocation holds the same *cell* — byte and
initialization — at every offset. This, and not structural equality, is what a
framing law can say about a journal-backed store.

Over `cellAt?` rather than `byteAt?`, and that is the whole point. An earlier
version compared bytes only, which made the commutation laws unable to carry the
refusal decision across: `denialOf` reads `RangeInitialized`, so two states
agreeing on every byte can still disagree about whether a later access is refused.
Review built exactly that pair. It is the same mistake `ByteStore`'s module
comment warns about, made one layer up.
-/
def AgreesOn (a b : MemoryState) : Prop :=
  ∀ id offset, a.cellAt? id offset = b.cellAt? id offset

/-- Agreeing states hold the same bytes. The `byteAt?` consequence, for callers
that only need values. -/
theorem AgreesOn.byteAt? {a b : MemoryState} (h : a.AgreesOn b) (id : AllocId)
    (offset : Nat) : a.byteAt? id offset = b.byteAt? id offset := by
  rw [byteAt?_eq_map_cellAt?, byteAt?_eq_map_cellAt?, h id offset]

/-- Agreeing states agree on what is initialized, which is what lets a
commutation argument carry the refusal decision. -/
theorem AgreesOn.initializedAt {a b : MemoryState} (h : a.AgreesOn b) (id : AllocId)
    (offset : Nat) : a.InitializedAt id offset ↔ b.InitializedAt id offset := by
  unfold InitializedAt
  rw [h id offset]

theorem AgreesOn.refl (state : MemoryState) : state.AgreesOn state := fun _ _ => rfl

theorem AgreesOn.symm {a b : MemoryState} (h : a.AgreesOn b) : b.AgreesOn a :=
  fun id offset => (h id offset).symm

theorem AgreesOn.trans {a b c : MemoryState} (hab : a.AgreesOn b) (hbc : b.AgreesOn c) :
    a.AgreesOn c := fun id offset => (hab id offset).trans (hbc id offset)

/-- A write to a missing allocation changes nothing. `performAccess` reaches
`write` only after `denialOf` has found the record, so this case does not arise
there; it is stated because `write` is total and a caller may not have checked. -/
theorem write_of_missing (state : MemoryState) {id : AllocId} (start : Nat)
    (bytes : ByteSeq) (initializes : Bool)
    (h : state.allocations.lookup id = Option.none) :
    state.write id start bytes initializes = state := by
  unfold write; rw [h]

/-- A write leaves its own allocation present, with the written store. -/
theorem lookup_write_self (state : MemoryState) {id : AllocId} (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) {record : AllocationRecord}
    (h : state.allocations.lookup id = some record) :
    (state.write id start bytes initializes).allocations.lookup id =
      some { record with bytes := record.bytes.write start bytes initializes } := by
  unfold write
  rw [h]
  exact FiniteMap.lookup_insert_self _ _ _

/-- The cell a write leaves at an offset, in terms of the store's own law. -/
theorem cellAt?_write_self (state : MemoryState) {id : AllocId} (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) {record : AllocationRecord}
    (h : state.allocations.lookup id = some record) (offset : Nat) :
    (state.write id start bytes initializes).cellAt? id offset =
      (record.bytes.write start bytes initializes).cellAt? offset := by
  unfold cellAt?
  rw [lookup_write_self state start bytes initializes h]
  rfl

/-- The byte a write leaves at an offset, in terms of the store's own law. -/
theorem byteAt?_write_self (state : MemoryState) {id : AllocId} (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) {record : AllocationRecord}
    (h : state.allocations.lookup id = some record) (offset : Nat) :
    (state.write id start bytes initializes).byteAt? id offset =
      (record.bytes.write start bytes initializes).byteAt? offset := by
  unfold byteAt?
  rw [lookup_write_self state start bytes initializes h]
  rfl

/-- Two states whose allocation records agree at `id` agree on what is
initialized there. -/
theorem rangeInitialized_congr_of_lookup {a b : MemoryState} {id : AllocId}
    {range : ByteRange} (h : a.allocations.lookup id = b.allocations.lookup id) :
    a.RangeInitialized id range ↔ b.RangeInitialized id range := by
  unfold RangeInitialized
  rw [h]

/-- **A write neither creates nor destroys initialization outside its own range.**
The `iff` rather than the forward direction alone: framing has to carry a *lack*
of initialization across a write too, or an `uninitializedRead` could be laundered
by writing somewhere else. -/
theorem rangeInitialized_write_iff_of_disjoint (state : MemoryState) {id : AllocId}
    {start : Nat} {bytes : ByteSeq} {initializes : Bool} {range : ByteRange}
    (hd : (ByteRange.mk start bytes.length).Disjoint range) :
    (state.write id start bytes initializes).RangeInitialized id range ↔
      state.RangeInitialized id range := by
  unfold RangeInitialized
  cases hfound : state.allocations.lookup id with
  | none => rw [write_of_missing state _ _ _ hfound, hfound]
  | some record =>
    rw [lookup_write_self state start bytes initializes hfound]
    exact ByteStore.initialized_write_iff_of_disjoint record.bytes hd

/-- Inside the range it wrote, a write determines the cell: byte and
initialization both come from the run just prepended. -/
theorem cellAt?_write_of_covers (state : MemoryState) {id : AllocId} {start : Nat}
    {bytes : ByteSeq} {initializes : Bool} {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) {offset : Nat}
    (h : (ByteRange.mk start bytes.length).Covers offset) :
    (state.write id start bytes initializes).cellAt? id offset =
      (bytes[offset - start]?).map (·, initializes) := by
  unfold cellAt?
  rw [lookup_write_self state start bytes initializes hfound]
  simp only [Option.bind_some]
  exact ByteStore.cellAt?_write_of_covers record.bytes h

/-- The byte a write leaves inside its own range. -/
theorem byteAt?_write_of_covers (state : MemoryState) {id : AllocId} {start : Nat}
    {bytes : ByteSeq} {initializes : Bool} {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) {offset : Nat}
    (h : (ByteRange.mk start bytes.length).Covers offset) :
    (state.write id start bytes initializes).byteAt? id offset = bytes[offset - start]? := by
  unfold byteAt?
  rw [lookup_write_self state start bytes initializes hfound]
  simp only [Option.bind_some]
  unfold ByteStore.byteAt?
  rw [ByteStore.cellAt?_write_of_covers record.bytes h]
  cases bytes[offset - start]? <;> simp

/-- An initializing write initializes each byte it covered. -/
theorem initializedAt_write_of_covers (state : MemoryState) {id : AllocId} {start : Nat}
    {bytes : ByteSeq} {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) {offset : Nat}
    (h : (ByteRange.mk start bytes.length).Covers offset) :
    (state.write id start bytes true).InitializedAt id offset := by
  unfold InitializedAt
  rw [cellAt?_write_of_covers state hfound h]
  cases hb : bytes[offset - start]? with
  | none =>
    rw [ByteRange.covers_def] at h
    exact absurd (List.getElem?_eq_none_iff.mp hb) (by simp at h ⊢; omega)
  | some b => simp

/-- **A write frames every cell it did not write**, in the same allocation or in
another: byte and initialization together, so a framing argument can carry a lack
of initialization across a write as well as its presence. -/
theorem cellAt?_write_of_not_covers (state : MemoryState) (id : AllocId) {start : Nat}
    {bytes : ByteSeq} {initializes : Bool} {other : AllocId} {offset : Nat}
    (h : other ≠ id ∨ ¬ (ByteRange.mk start bytes.length).Covers offset) :
    (state.write id start bytes initializes).cellAt? other offset =
      state.cellAt? other offset := by
  unfold cellAt?
  cases h with
  | inl hne => rw [write_preserves_other_allocation state hne]
  | inr hout =>
    by_cases hid : other = id
    · subst hid
      cases hfound : state.allocations.lookup other with
      | none =>
        rw [write_of_missing state start bytes initializes hfound, hfound]
      | some record =>
        rw [lookup_write_self state start bytes initializes hfound]
        simp only [Option.bind_some]
        exact ByteStore.cellAt?_write_of_not_covers record.bytes hout
    · rw [write_preserves_other_allocation state hid]

/-- The initialization half of `cellAt?_write_of_not_covers`, in the shape a
padding argument uses. -/
theorem initializedAt_write_iff_of_not_covers (state : MemoryState) (id : AllocId)
    {start : Nat} {bytes : ByteSeq} {initializes : Bool} {other : AllocId} {offset : Nat}
    (h : other ≠ id ∨ ¬ (ByteRange.mk start bytes.length).Covers offset) :
    (state.write id start bytes initializes).InitializedAt other offset ↔
      state.InitializedAt other offset := by
  unfold InitializedAt
  rw [cellAt?_write_of_not_covers state id h]

/-- `state.MetadataAt id` is what a decision about `id` reads besides its bytes. -/
def MetadataAt (state : MemoryState) (id : AllocId) : Option AllocationRecord.Metadata :=
  (state.allocations.lookup id).map AllocationRecord.metadata

/-- A write moves no metadata, which is the half of a framing argument that says a
later access is decided the same way. The bytes are exactly what it does move. -/
@[simp] theorem metadataAt_write (state : MemoryState) (id : AllocId) (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) (other : AllocId) :
    (state.write id start bytes initializes).MetadataAt other = state.MetadataAt other := by
  unfold MetadataAt write
  cases hfound : state.allocations.lookup id with
  | none => rfl
  | some record =>
    by_cases hid : other = id
    · subst hid
      rw [FiniteMap.lookup_insert_self, hfound]
      rfl
    · rw [FiniteMap.lookup_insert_ne _ hid]

/-- An allocation is present exactly when its metadata is. -/
theorem isSome_metadataAt (state : MemoryState) (id : AllocId) :
    (state.MetadataAt id).isSome = (state.allocations.lookup id).isSome := by
  unfold MetadataAt
  cases state.allocations.lookup id <;> rfl

/--
Cell agreement plus metadata agreement gives initialization agreement.

`AgreesOn` alone does not: `RangeInitialized` is `False` for a missing allocation,
so a state where `id` is absent and one where it is present with an empty store
agree at every cell and disagree here. That was the gap
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 recorded, and the presence half is what
closes it.
-/
theorem rangeInitialized_congr_of_agrees {a b : MemoryState} {id : AllocId}
    {range : ByteRange} (hpresent : a.MetadataAt id = b.MetadataAt id)
    (hcells : a.AgreesOn b) : a.RangeInitialized id range ↔ b.RangeInitialized id range := by
  have hsome : (a.allocations.lookup id).isSome = (b.allocations.lookup id).isSome := by
    rw [← isSome_metadataAt, ← isSome_metadataAt, hpresent]
  unfold RangeInitialized
  cases ha : a.allocations.lookup id with
  | none =>
    have : (b.allocations.lookup id).isSome = false := by rw [← hsome, ha]; rfl
    cases hb : b.allocations.lookup id with
    | none => exact Iff.rfl
    | some _ => rw [hb] at this; simp at this
  | some ra =>
    cases hb : b.allocations.lookup id with
    | none =>
      have : (a.allocations.lookup id).isSome = false := by rw [hsome, hb]; rfl
      rw [ha] at this; simp at this
    | some rb =>
      constructor <;> intro h offset hcov
      · have := h offset hcov
        have hc := hcells id offset
        unfold cellAt? at hc
        rw [ha, hb] at hc
        simp only [Option.bind_some] at hc
        unfold ByteStore.InitializedAt at this ⊢
        rw [← hc]; exact this
      · have := h offset hcov
        have hc := hcells id offset
        unfold cellAt? at hc
        rw [ha, hb] at hc
        simp only [Option.bind_some] at hc
        unfold ByteStore.InitializedAt at this ⊢
        rw [hc]; exact this

/-- A write depends on its allocation and nothing else, so two states agreeing
about that allocation write it identically. -/
theorem cellAt?_write_congr {a b : MemoryState} {id : AllocId}
    (h : a.allocations.lookup id = b.allocations.lookup id) (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) (offset : Nat) :
    (a.write id start bytes initializes).cellAt? id offset =
      (b.write id start bytes initializes).cellAt? id offset := by
  unfold write cellAt?
  cases hl : b.allocations.lookup id with
  | none =>
    have ha : a.allocations.lookup id = Option.none := by rw [h, hl]
    simp only [ha, hl]
  | some r =>
    have ha : a.allocations.lookup id = some r := by rw [h, hl]
    simp only [ha, FiniteMap.lookup_insert_self]

/--
**Writes to different allocations commute**, whatever ranges they name.

The companion to `write_comm`, which needs disjoint ranges because it is about one
allocation. Here disjointness is free: `docs/MEMORY_MODEL.md` §2 makes distinct
`AllocId`s distinct storage by construction, so two writes to different
allocations cannot interfere however their offsets compare.
-/
theorem write_comm_of_ne (state : MemoryState) {a b : AllocId} (hne : a ≠ b)
    (sa : Nat) (ba : ByteSeq) (ia : Bool) (sb : Nat) (bb : ByteSeq) (ib : Bool) :
    ((state.write a sa ba ia).write b sb bb ib).AgreesOn
      ((state.write b sb bb ib).write a sa ba ia) := by
  intro other offset
  by_cases hoa : other = a
  · subst hoa
    rw [cellAt?_write_of_not_covers _ b (Or.inl hne),
      cellAt?_write_congr (write_preserves_other_allocation state hne sb bb ib) sa ba ia]
  · by_cases hob : other = b
    · subst hob
      rw [cellAt?_write_of_not_covers _ a (Or.inl (Ne.symm hne)),
        cellAt?_write_congr (write_preserves_other_allocation state (Ne.symm hne) sa ba ia)
          sb bb ib]
    · rw [cellAt?_write_of_not_covers _ b (Or.inl hob),
        cellAt?_write_of_not_covers _ a (Or.inl hoa),
        cellAt?_write_of_not_covers _ a (Or.inl hoa),
        cellAt?_write_of_not_covers _ b (Or.inl hob)]

/-! ### Placement

`Grass/Memory/Addressing.lean` proves that inside a non-wrapping allocation
distinct offsets have distinct machine addresses. Until an allocation carried a
base there was nothing to instantiate it with, and
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 recorded the offset-to-address debt as
undischarged for exactly that reason. These connect the two.

Placement is not authority. `denialOf` reads none of this: `docs/MEMORY_MODEL.md`
§2 makes provenance decide what an access may touch, and two allocations at one
base are still distinct storage unless `aliases` says otherwise. What placement
answers is the different question of whether two offsets name the same machine
byte. -/

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
    FitsAllocation base record.extent.size

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
    (hr : r.WithinBound record.extent.size) (ht : t.WithinBound record.extent.size)
    (hd : r.Disjoint t) {i j : Nat} (hi : r.Covers i) (hj : t.Covers j)
    {base : MachineAddress} (hbase : record.base = some base) :
    state.addressAt? id i ≠ state.addressAt? id j := by
  have hfits : FitsAllocation base record.extent.size :=
    hplaced record (by rw [hfound]; simp) base (by rw [hbase]; simp)
  have hne := disjoint_ranges_do_not_alias hfits hr ht hd hi hj
  unfold addressAt?
  rw [hfound]
  simp only [Option.bind_some]
  rw [hbase]
  simp only [Option.map_some, ne_eq, Option.some.injEq]
  exact hne

/--
**Writes to disjoint ranges commute.**

Stated as `AgreesOn` rather than as state equality: the byte store is a journal,
so the two orders leave different write histories, and no proof will make those
equal. `AgreesOn` compares cells, so a caller can conclude both `AgreesOn.byteAt?`
and `AgreesOn.initializedAt`. `ByteStore.cellAt?_write_comm` is where the content
is. It does not carry the refusal decision, which needs allocation metadata as
well; see `AgreesOn`.
-/
theorem write_comm (state : MemoryState) (id : AllocId) {a b : Nat}
    {bytesA bytesB : ByteSeq} {initA initB : Bool}
    (hd : (ByteRange.mk a bytesA.length).Disjoint (ByteRange.mk b bytesB.length)) :
    ((state.write id a bytesA initA).write id b bytesB initB).AgreesOn
      ((state.write id b bytesB initB).write id a bytesA initA) := by
  intro other offset
  by_cases hid : other = id
  · subst hid
    cases hfound : state.allocations.lookup other with
    | none =>
      rw [write_of_missing state a bytesA initA hfound,
        write_of_missing state b bytesB initB hfound,
        write_of_missing state a bytesA initA hfound]
    | some record =>
      rw [cellAt?_write_self _ b bytesB initB
            (lookup_write_self state a bytesA initA hfound),
        cellAt?_write_self _ a bytesA initA
            (lookup_write_self state b bytesB initB hfound)]
      exact ByteStore.cellAt?_write_comm record.bytes hd offset
  · unfold cellAt?
    rw [write_preserves_other_allocation _ hid, write_preserves_other_allocation _ hid,
      write_preserves_other_allocation _ hid, write_preserves_other_allocation _ hid]

/-- An initializing write initializes what it wrote, provided the allocation is
there. The state-level form of `ByteStore.initialized_write`. -/
theorem rangeInitialized_write (state : MemoryState) {id : AllocId} {start : Nat}
    {bytes : ByteSeq} {record : AllocationRecord}
    (hfound : state.allocations.lookup id = some record) :
    (state.write id start bytes true).RangeInitialized id ⟨start, bytes.length⟩ := by
  unfold RangeInitialized write
  simp only [hfound, FiniteMap.lookup_insert_self]
  exact ByteStore.initialized_write record.bytes start bytes


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
