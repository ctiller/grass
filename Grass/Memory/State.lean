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
`issue?` and `returnGrant?`. `Grass/Memory/Loan.lean` states §3's laws over
them and adds the loan-specific refusals; `grantEntries` and `grantAt?` are the
read-only views everything else uses.

**And `mk` is private too**, which is the third time this hole was closed — and the
checks live here rather than a module up, which is the fourth. Marking the *field*
private privatised the projection and left the constructor alone, so
`MemoryState.mk allocations aliases ⟨…⟩` still built any map at all; review rebuilt
`Tests/Op/StandardLoan.lean`'s own lent state with the loan filtered out of
`grantEntries`, and the thread's store committed. Sealing `mk` closed that, and left
a low-level `issueGrant?` public in this module that ran the identity check and none
of the others, so review installed a four-kilobyte grant over a sixty-four-byte
allocation through it and froze an honest store. There is one door now and it is the
checked one.
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
The grants outstanding over the same *bytes* as `provenance`, meeting `range`, in
the epoch that provenance names.

Three departures from the obvious filter, each of which review demonstrated:

**`MemoryState.SharesBytes`, not `Provenance.SameStorage`.** `Grass/Memory/State.lean`
records that `Conflicts` used to require `SameStorage` and "declared every aliased
pair non-conflicting: a write through a mapped view and a write through the file it
maps would not conflict", which is why `SharesBytes` exists at all — and this
function was written with `SameStorage` anyway. Review drove a thread's store to
lent bytes through an aliasing view and it committed with no violation.

**`ByteRange.Meets`, not `¬ Disjoint`.** An empty range covers no offset, so every
range is `Disjoint` from a position, and asking what was outstanding over offset 4
while `[0, 8)` was lent returned nothing.

**Every kind of grant, not only loans.** `docs/MEMORY_MODEL.md` §7.3's conflict is
about authority, not about one kind of it. Filtering to `GrantKind.loan` meant a
`.frame` grant — or one of a kind a profile invented, which `GrantKind` is open
nominal to allow — carried write authority that froze nobody and conflicted with
nothing. `loansOver` below is this list narrowed to loans, for §3's laws, which
really are about loans.

**And no epoch clause.** There was one, on the grant's own provenance, and it was
wrong in the unsafe direction: review re-epoched one member of an alias set and the
grant over it vanished from this list while the other member stayed live, so the
freeze lifted and an unauthorized store committed. A grant that names a defunct
epoch is also unable to *authorize* anything — `MemoryState.AuthorizedAt` checks
both provenances — so dropping it here means a stale grant freezes without
authorizing, which is the refuse-both-ways answer `docs/FOUNDATION.md` law 8 asks
for. §5.1 requires live use loans to be returned before reallocation, so a stale
grant that still freezes is a profile that skipped a step, not a case to be
accommodated.

It also restores agreement with `LoanConflicts`, which has no epoch clause either.
The epoch filter had made the two disagree about which grants exist, and review used
exactly that gap: a context could not *obtain* a loan (the conflict test saw the
stale grant) and did not need one (this list did not), so the write proceeded
unauthorized.
-/
def grantsOver (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    List (GrantId × AuthorityGrant) :=
  state.grantEntries.filter fun entry =>
    decide (state.SharesBytes entry.2.provenance.root provenance.root) &&
      decide (entry.2.range.Meets range)

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
The cost is that the lender's read of its own shared-immutably-lent bytes is refused
along with a stranger's — `AllocationRecord` records no owner, so the two are
indistinguishable here, and permitting one permits both.
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records that. -/
def AnyGrantOver (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    Prop := state.grantsOver provenance range ≠ []

instance (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    Decidable (state.AnyGrantOver provenance range) :=
  inferInstanceAs (Decidable (_ ≠ _))

/--
Two grants issue conflicting authority.

`docs/MEMORY_MODEL.md` §7.3 defines a conflict as overlapping live bytes with at
least one writer *from distinct concurrent contexts*, and says "unique loans
prevent ordinary conflicting authority from being issued". This is that test
applied at issue time.

**Distinct holders.** §7.3's rule is about distinct contexts, and without the
clause a context could not hold two grants over its own bytes — which is the
idiom `Grass/Op/LoanAuthority.lean` endorses for "the owner may still read", and
which was therefore mutually exclusive with any other grant on those bytes.

**`Meets` in both directions**, because `Meets` is asymmetric and neither grant is
the query here. `loansOver` moved off `Disjoint` and this did not, which left one
module with two answers to what "overlapping" means.

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

The other is not closable at issue time, and `Grass/Op/LoanAuthority.lean`'s
access-time rule is what covers it. Declaring an alias *after* two
non-conflicting grants are issued makes them conflict, with nothing re-examined, and
§7.5 makes declaring one a real transition. The pair that must never *act* is stopped
at access time by `Grass/Op/LoanAuthority.lean`, which is where the guarantee lives;
this is the cheaper check that stops the honest caller earlier.
-/
def LoanConflicts (state : MemoryState) (a b : AuthorityGrant) : Prop :=
  a.holder ≠ b.holder ∧
    state.SharesBytes a.provenance.root b.provenance.root ∧
    (a.range.Meets b.range ∨ b.range.Meets a.range) ∧
    (a.rights.write ∨ b.rights.write) ∧
    ¬ (a.rights.atomicOnly ∧ b.rights.atomicOnly)

instance (state : MemoryState) (a b : AuthorityGrant) :
    Decidable (state.LoanConflicts a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/--
`state.MayLend grant` holds when the grant's lender has the authority it is lending.

**You cannot lend what you do not have**, which `issue?_eq_none_of_nothing_to_lend`
now says and nothing said before. `issue?` checked
reissue, emptiness, liveness, nestedness, extent agreement, containment and conflict,
and never related the lender to the storage — while `LoanConflicts` requires distinct
holders, so the *first* grant over any bytes conflicts with nothing. Review had one
context issue itself a whole-buffer write loan over an allocation another context
exclusively owned: the owner became `frozen`, its counter-grant was refused as
conflicting, it could not return a grant it neither held nor lent, and it could not
free or re-epoch the allocation because a grant was outstanding. Permanent seizure, in
one accepted call. `AuthorityGrant.kind`'s own docstring calls a loan "a borrow of
authority over bytes the lender retains".

Three ways to have it, and the third is the one that took thinking about.

Nothing is held over the bytes at all — the unlent case, which is how a first grant is
ever issued, and which matches `Grass/Op/LoanAuthority.lean`'s reading that unheld
bytes are not this rule's business. Or the lender holds a grant covering the range
with rights that supply what is being lent, which is `Permission.Grants` at the
authority layer. Or every grant outstanding over the bytes was lent *by this lender* —
whoever put them out may put more out.

Without the third, an owner who lends once can never lend again, because it holds
nothing itself: `AllocationRecord` records no owner, so a lender's claim on unheld
bytes leaves no trace except in the grants it issued. Two read loans from one owner is
`sharedImmutable`'s whole point, and the first two disjuncts alone refuse the second
of them.

**What this does not stop**, and cannot: seizing bytes nothing is held over. That is
the first disjunct, and it is the same rule a legitimate owner's first loan needs — so
with no owner in `AllocationRecord`, the model cannot tell the two apart. What it does
stop is stealing from a lender: once a context has lent bytes out, no other context can
issue a grant over them, which is what closed review's permanent-seizure state. The
residue is the missing-owner gap `Grass/Op/LoanAuthority.lean` records from the other
side and `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records as owed.
-/
def MayLend (state : MemoryState) (grant : AuthorityGrant) : Prop :=
  ¬ state.AnyGrantOver grant.provenance grant.range ∨
    state.grantEntries.any (fun entry =>
      entry.2.holder = grant.lender &&
        decide (state.SharesBytes entry.2.provenance.root grant.provenance.root) &&
        decide (state.CurrentEpoch entry.2.provenance) &&
        decide (entry.2.range.Contains grant.range) &&
        decide (entry.2.rights.Grants grant.rights)) = true ∨
    (state.grantsOver grant.provenance grant.range).all
      (fun entry => entry.2.lender = grant.lender) = true

instance (state : MemoryState) (grant : AuthorityGrant) : Decidable (state.MayLend grant) :=
  inferInstanceAs (Decidable (¬ _ ∨ _ = _ ∨ _ = _))

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
re-examined, and §7.5 makes that a real transition. `Grass/Op/LoanAuthority.lean`
reads the map it finds; this is the cheaper check that stops the honest caller
earlier.

Refusing rather than overwriting or ignoring is `docs/FOUNDATION.md` law 8's
direction. Four of the five refusals are stated —  `issue?_eq_none_of_reissued`,
`issue?_eq_none_of_empty`, `issue?_eq_none_of_not_live` and
`issue?_eq_none_of_conflict` — so a caller that cannot issue finds out which rule
stopped it. The extent clause has no theorem of its own; it is checked and not
stated.
-/
def issue? (state : MemoryState) (id : GrantId) (grant : AuthorityGrant) :
    Option MemoryState :=
  if (state.grants.lookup id).isSome then Option.none
  else if grant.range.IsEmpty then Option.none
  else if ¬ state.Live grant.provenance then Option.none
  else if ¬ grant.provenance.Nested then Option.none
  else if ¬ state.RootExtentAgrees grant.provenance then Option.none
  else if ¬ grant.provenance.extent.Contains grant.range then Option.none
  else if ¬ state.MayLend grant then Option.none
  else if state.grantEntries.any
      (fun entry => decide (state.LoanConflicts entry.2 grant))
    then Option.none
  else some { state with grants := state.grants.insert id grant }

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
            by_cases hin : grant.provenance.extent.Contains grant.range
            · rw [if_neg (by simpa using hin), if_pos (by simpa using h)]
            · rw [if_pos (by simpa using hin)]
          · rw [if_pos (by simpa using hext)]
        · rw [if_pos (by simpa using hnest)]
      · rw [if_pos (by simpa using hlive)]

/-- Over bytes nothing is held on, anyone may lend. That is how a first grant is ever
issued, and it is the claim `MayLend`'s docstring says is not a transfer. -/
theorem mayLend_of_unheld {state : MemoryState} {grant : AuthorityGrant}
    (h : ¬ state.AnyGrantOver grant.provenance grant.range) : state.MayLend grant :=
  Or.inl h

/-- **A grant over no bytes is refused.** It would conflict at issue with a live one
— `LoanConflicts` tries `Meets` in both directions — and freeze nobody once
installed, because an empty extent meets no position. Decoration with a refusal
attached. -/
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
            by_cases hin : grant.provenance.extent.Contains grant.range
            · rw [if_neg (by simpa using hin)]
              by_cases hlend : state.MayLend grant
              · rw [if_neg (by simpa using hlend), if_pos h]
              · rw [if_pos (by simpa using hlend)]
            · rw [if_pos (by simpa using hin)]
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

@[simp] theorem grantAt?_eq_lookup (state : MemoryState) (id : GrantId) :
    state.grantAt? id = state.grants.lookup id := rfl

@[simp] theorem grantEntries_eq (state : MemoryState) :
    state.grantEntries = state.grants.entries := rfl

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
  injection h with h
  subst h
  exact FiniteMap.lookup_insert_self _ _ _

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

/--
`state.AuthorizedAt grant context provenance offset intent` holds when this grant
lets `context` touch that byte, in this state.

Six clauses: the holder is the context performing the access, the grant is over the
same *bytes*, both provenances are current, the grant's range covers the byte, and
the rights permit the intent.

**On the state, and using `SharesBytes`.** This was a pure function on provenances in
`Grass/Memory/Authority.lean`, using `Provenance.SameStorage` — equal `space`, `root`
and `epoch`. That is the relation this layer has now moved off twice for being wrong
in the unsafe direction, and leaving it there made it wrong in the *other* direction:
`MemoryState.grantsOver` sees aliases and it did not, so a holder reaching its own
lent bytes through a declared alias was frozen by its own loan and authorized by
nothing. §7.5's mapped file and host-visible device buffer are exactly that shape.
Whether two allocations name the same bytes is a fact about the state, so this takes
the state.

The `space` conjunct is gone with `SameStorage` and is not replaced. An access is
checked against its own allocation's space by `AccessDescriptor.WellFormedIn` and by
`denialOf`; requiring the *grant* to name the same space as well would refuse a
device engine's grant over a host-visible buffer, which is the case §7.5 exists to
describe.

**At one byte, not over a range**, and that is deliberate. A range-shaped version
existed beside this one, `Granted` moved off it, and it kept its four safety theorems
— so the theorems a reader cites to believe the gate is safe stopped bearing on the
gate. Review found it. There is one predicate now and the negatives below are stated
over it.

`Contains` compares offsets relative to a root, and aliased allocations are assumed
to agree offset for offset — `MemoryState.aliases` records no offset mapping.
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 records that.
-/
def AuthorizedAt (state : MemoryState) (grant : AuthorityGrant) (context : ContextId)
    (provenance : Provenance) (offset : Nat) (intent : AccessIntent) : Prop :=
  grant.holder = context ∧
  state.SharesBytes grant.provenance.root provenance.root ∧
  state.CurrentEpoch grant.provenance ∧
  state.CurrentEpoch provenance ∧
  grant.range.Covers offset ∧
  grant.rights.Permits intent

instance (state : MemoryState) (grant : AuthorityGrant) (context : ContextId)
    (provenance : Provenance) (offset : Nat) (intent : AccessIntent) :
    Decidable (state.AuthorizedAt grant context provenance offset intent) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A grant held by one context authorizes nothing for another. Authority is not
ambient: `docs/FOUNDATION.md` law 6 forbids ambient provider choice, and the same
reading applies to authority a context did not receive. -/
theorem not_authorizedAt_of_other_holder {state : MemoryState} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {offset : Nat}
    {intent : AccessIntent} (h : grant.holder ≠ context) :
    ¬ state.AuthorizedAt grant context provenance offset intent := fun ha => h ha.1

/-- A grant over storage that does not share bytes with the access authorizes
nothing, however their offsets compare (`docs/MEMORY_MODEL.md` §7.5). -/
theorem not_authorizedAt_of_other_storage {state : MemoryState} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {offset : Nat}
    {intent : AccessIntent}
    (h : ¬ state.SharesBytes grant.provenance.root provenance.root) :
    ¬ state.AuthorizedAt grant context provenance offset intent := fun ha => h ha.2.1

/-- A read-only grant does not authorize a write. -/
theorem not_authorizedAt_of_insufficient_rights {state : MemoryState}
    {grant : AuthorityGrant} {context : ContextId} {provenance : Provenance}
    {offset : Nat} {intent : AccessIntent} (h : ¬ grant.rights.Permits intent) :
    ¬ state.AuthorizedAt grant context provenance offset intent :=
  fun ha => h ha.2.2.2.2.2

/-- A grant over a defunct epoch authorizes nothing, and neither does any grant to a
stale pointer. §2's reuse rule, at the authority gate. -/
theorem not_authorizedAt_of_stale_epoch {state : MemoryState} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {offset : Nat}
    {intent : AccessIntent} (h : ¬ state.CurrentEpoch provenance) :
    ¬ state.AuthorizedAt grant context provenance offset intent := fun ha => h ha.2.2.2.1

/-- A grant whose range covers a whole access covers each of its bytes. The bridge a
caller with one covering grant uses to reach `Granted`. -/
theorem authorizedAt_of_covering {state : MemoryState} {grant : AuthorityGrant}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    {intent : AccessIntent} {i : Nat} (hi : i < range.size)
    (hcover : grant.range.Contains range)
    (hholder : grant.holder = context)
    (hshares : state.SharesBytes grant.provenance.root provenance.root)
    (hgrant : state.CurrentEpoch grant.provenance)
    (haccess : state.CurrentEpoch provenance)
    (hrights : grant.rights.Permits intent) :
    state.AuthorizedAt grant context provenance (range.start + i) intent := by
  refine ⟨hholder, hshares, hgrant, haccess, ?_, hrights⟩
  rw [ByteRange.contains_def] at hcover
  rw [ByteRange.covers_def]
  omega

/--
`state.Granted context provenance range intent` holds when some live grant
authorizes that access.

Existentially quantified over the grant, because an access does not name the one
it relies on; see `Grass/Memory/Authority.lean`. Decidable because the grant table
is finite.
-/
def Granted (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) : Prop :=
  ∀ i, i < range.size →
    ∃ entry ∈ state.grantEntries,
      state.AuthorizedAt entry.2 context provenance (range.start + i) intent

instance (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) (intent : AccessIntent) :
    Decidable (state.Granted context provenance range intent) :=
  inferInstanceAs (Decidable (∀ _, _ → ∃ _ ∈ _, _))

/-- One grant covering the whole range is enough, which is the ordinary case. -/
theorem granted_of_covering {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} {intent : AccessIntent}
    {entry : GrantId × AuthorityGrant} (hmem : entry ∈ state.grantEntries)
    (hcover : entry.2.range.Contains range)
    (hholder : entry.2.holder = context)
    (hshares : state.SharesBytes entry.2.provenance.root provenance.root)
    (hgrant : state.CurrentEpoch entry.2.provenance)
    (haccess : state.CurrentEpoch provenance)
    (hrights : entry.2.rights.Permits intent) :
    state.Granted context provenance range intent :=
  fun _ hi => ⟨entry, hmem,
    authorizedAt_of_covering hi hcover hholder hshares hgrant haccess hrights⟩

/--
The same bridge from an identity rather than from a membership.

`granted_of_covering`'s `entry ∈ grantEntries` hypothesis is what a concrete fixture
has and a symbolic caller does not — review found that every fixture in `Tests/`
discharges it by `decide`, so the bridge had never been used the way a general
theorem would use it. `Grass/Std/Logical/FiniteMap.lean`'s `mem_entries_of_lookup`
supplies the step, and this is the form to reach for: it takes the `grantAt?` a caller
holding a grant identity actually has.
-/
theorem granted_of_grantAt {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} {intent : AccessIntent}
    {id : GrantId} {grant : AuthorityGrant} (hat : state.grantAt? id = some grant)
    (hcover : grant.range.Contains range)
    (hholder : grant.holder = context)
    (hshares : state.SharesBytes grant.provenance.root provenance.root)
    (hgrant : state.CurrentEpoch grant.provenance)
    (haccess : state.CurrentEpoch provenance)
    (hrights : grant.rights.Permits intent) :
    state.Granted context provenance range intent :=
  granted_of_covering (entry := (id, grant))
    (Grass.Std.Logical.FiniteMap.mem_entries_of_lookup hat)
    hcover hholder hshares hgrant haccess hrights

/--
`Granted` refuted, from a refutation of every outstanding grant.

The `not_authorizedAt_of_*` family says a *particular* grant does not authorize a
particular byte, and `Granted` is existential over `grantEntries`, so those negatives
composed into nothing: review pointed out that no theorem in the tree turns them into
a `¬ Granted`. This is the composition. The `¬ range.IsEmpty` hypothesis is not
incidental — `Granted` is vacuously true on an empty range, in every state, which is
why `AccessDescriptor.WellFormedIn.rangeNonEmpty` exists two layers up.
-/
theorem not_granted_of_no_authorizing_entry {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} {intent : AccessIntent}
    (hne : ¬ range.IsEmpty)
    (h : ∀ entry ∈ state.grantEntries, ∀ offset,
      ¬ state.AuthorizedAt entry.2 context provenance offset intent) :
    ¬ state.Granted context provenance range intent := by
  intro hgranted
  have hsize : 0 < range.size := by
    rcases Nat.eq_zero_or_pos range.size with hzero | hpos
    · exact absurd (by simpa [ByteRange.IsEmpty] using hzero) hne
    · exact hpos
  obtain ⟨entry, hmem, hauth⟩ := hgranted 0 hsize
  exact h entry hmem (range.start + 0) hauth

/-- `state.GrantedOfKind` additionally requires the authorizing grant to be of a
particular kind, which is how one provider distinguishes itself from another over
the same table. -/
def GrantedOfKind (state : MemoryState) (kind : GrantKind) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) : Prop :=
  ∀ i, i < range.size →
    ∃ entry ∈ state.grantEntries,
      entry.2.kind = kind ∧
        state.AuthorizedAt entry.2 context provenance (range.start + i) intent

instance (state : MemoryState) (kind : GrantKind) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent) :
    Decidable (state.GrantedOfKind kind context provenance range intent) :=
  inferInstanceAs (Decidable (∀ _, _ → ∃ _ ∈ _, _))

/-- A state with no grants authorizes nothing. Authority is held, not assumed. -/
theorem not_granted_empty (context : ContextId) (provenance : Provenance)
    {range : ByteRange} (hne : ¬ range.IsEmpty) (intent : AccessIntent) :
    ¬ empty.Granted context provenance range intent := by
  intro h
  have hpos : 0 < range.size := by
    rw [ByteRange.isEmpty_def] at hne
    omega
  obtain ⟨entry, hmem, -⟩ := h 0 hpos
  simp [empty, grantEntries, FiniteMap.empty] at hmem

/--
Record an allocation, or refuse.

`Option`, and for the same reason `issue?` is. `FiniteMap.insert` replaces, so this
is also the *re*-allocation operation, and `docs/MEMORY_MODEL.md` §5.1 makes
reallocation conditional: "reallocation requires the return of all live use loans".
Nothing checked that. A profile could bump an allocation's epoch under an outstanding
grant, and the result is a grant that freezes the new storage — `grantsOver` has no
epoch clause, deliberately — while authorizing nothing, since
`MemoryState.AuthorizedAt` requires both provenances current. Review reached that
state and found only the stale grant's holder or lender could clear it.

Refused rather than reconciled: which of the two the profile meant is not this
module's to guess (`docs/FOUNDATION.md` law 8), and §5.1 already says which comes
first.

**Teardown counts as well as reuse**, and an earlier version accepted it: it refused
only an epoch change, and its own docstring listed "a liveness change" among the
things always allowed. So `live := true → false` under an outstanding grant was
admitted, and the consequence was silent rather than loud — `authorityOf` reports
`unavailable` for a dead allocation, so every outstanding loan over it evaporated
with no return and no violation, and a later record with the same epoch and
`live := true` resurrected them. §5 requires arena teardown to take "the return of all
live use loans" in the same breath as §5.1 requires it of reallocation.

**And the scan is alias-aware.** It matched `entry.2.provenance.root = id`, so a
grant held over a mapped view did not block a reallocation of the file it maps, even
though `SharesBytes` says they are the same bytes — the asymmetry this layer has now
fixed three times in three places.

A *fresh* identity is always accepted, and so is replacing a record without changing
its epoch or killing it: a permission change, a placement, a byte write.
-/
def allocate? (state : MemoryState) (id : AllocId) (record : AllocationRecord) :
    Option MemoryState :=
  match state.allocations.lookup id with
  | some existing =>
      if existing.metadata ≠ record.metadata ∧
          state.grantEntries.any
            (fun entry => decide (state.SharesBytes entry.2.provenance.root id)) then
        Option.none
      else some { state with allocations := state.allocations.insert id record }
  | Option.none => some { state with allocations := state.allocations.insert id record }

/-- Allocate several records in order, refusing if any is refused.

A fixture building a machine state allocates half a dozen things, and threading
`Option` through that by hand buries the state it is trying to show. One
`isSome` theorem beside the definition is the whole obligation. -/
def allocateAll? (state : MemoryState) :
    List (AllocId × AllocationRecord) → Option MemoryState
  | [] => some state
  | (id, record) :: rest => (state.allocate? id record).bind (·.allocateAll? rest)

/-- **A fresh identity is always allocatable.** -/
theorem allocate?_isSome_of_fresh (state : MemoryState) (id : AllocId)
    (record : AllocationRecord) (h : state.allocations.lookup id = Option.none) :
    (state.allocate? id record).isSome := by
  unfold allocate?
  rw [h]
  rfl

/-- **Reallocating under an outstanding grant is refused.** §5.1's precondition, as a
refusal rather than as a sentence. -/
theorem allocate?_eq_none_of_outstanding {state : MemoryState} {id : AllocId}
    {record existing : AllocationRecord}
    (hlook : state.allocations.lookup id = some existing)
    (hchange : existing.metadata ≠ record.metadata)
    (hgrants : state.grantEntries.any
      (fun entry => decide (state.SharesBytes entry.2.provenance.root id)) = true) :
    state.allocate? id record = Option.none := by
  unfold allocate?
  rw [hlook]
  simp only []
  rw [if_pos (show existing.metadata ≠ record.metadata ∧ _ from ⟨hchange, hgrants⟩)]

/-- A record replaced without changing its epoch is accepted, grants or not: a
permission, liveness or placement change is not a reallocation. -/
theorem allocate?_isSome_of_same_metadata {state : MemoryState} {id : AllocId}
    {record existing : AllocationRecord}
    (hlook : state.allocations.lookup id = some existing)
    (hsame : existing.metadata = record.metadata) :
    (state.allocate? id record).isSome := by
  unfold allocate?
  rw [hlook]
  simp only []
  rw [if_neg (fun h => h.1 hsame)]
  rfl

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
