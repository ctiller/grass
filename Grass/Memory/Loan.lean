import Grass.Memory.State

/-!
# Loans and exclusive authority

`docs/MEMORY_MODEL.md` §3 is the whole of what this module implements. M1 carried
`AuthorityGrant` a milestone early, deliberately general and deliberately not a
loan model: it existed so `Grass/Op/Step.lean`'s `AuthorityProvider` had a real
table to check against, and its own comment says split, join, freeze, and
exclusivity-iff-empty are M3's. This is M3's.

## What §3 actually demands

A loan map keyed by identity, carrying holder, range, rights, lifetime, and
conditions; and a list of canonical authority states, named here as
`AuthorityState`.

**That list is open.** §3's words are "The canonical authority states *include*:",
and an earlier version of this file justified `AuthorityState` being a closed sum
by claiming §3 named a closed list. It does not, and review caught the misreading.
Closing the sum is this module's decision, not §3's requirement, and the
consequence is written where the type is declared.

Four of the five entries §3 lists are derived here from state that already exists:
exclusive and frozen from the loan map, shared-immutable from the rights on the
outstanding loans, and unavailable from allocation liveness. The fifth — atomic
shared access with an ordering profile — is **not** named here. Nothing carries an
ordering: `AuthorityGrant` has `kind`, `holder`, `provenance`, `range`, `rights`
and no ordering field, so a constructor for it would be built by nothing and the
§3 law about it ("Atomics do not grant ordinary non-atomic access") would be a
theorem about an unreachable case. There was such a constructor and such a theorem,
and deleting them is the point: a vacuous theorem reads as coverage. The law is
owed, and `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 records it against M8, where
`ConsistencyProfile` gives ordering something to mean.

**`AuthorityGrant` carries the first four and not the last two**, and this file
does not add them. Its own docstring already said so; the sentence here originally
described what §3 demands and read as a description of the code, which is the
drift this branch keeps being corrected for. A lifetime nothing consults would be
one more field carried and never read — the shape that produced
`AllocationRecord.initialized` and `AccessIntent.isDevice`. The lifetime discipline
belongs with M4's frames, where a bounded lifetime has something to mean, and
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 records it as owed.

And three laws:

- a return consumes that exact identity — `MemoryState.lookup_returnLoan_self`
  with `MemoryState.lookup_returnLoan_ne`;
- exclusive authority is restored only when the relevant map is empty —
  `MemoryState.Exclusive` is defined as that emptiness, and
  `MemoryState.exclusive_iff_no_outstanding` relates it to the count;
- counts are derived caches only — `MemoryState.outstandingLoans` computes from
  the map and no field records one.

The third is a constraint on the *representation*, and the way to satisfy it is
not to write a counting field down. `outstandingLoans` computes from the map, so
there is nothing that can disagree with it — the same discipline that removed
`AllocationRecord.initialized` and `AccessIntent.isDevice`, which were the two
places this layer has been bitten by a second source of truth.

## What is not here

Split and join of loans. `MemoryState.authorityOf` puts an owner into
`AuthorityState.frozen` while another context's write loan is outstanding and
`not_permitsOrdinaryWrite_of_lentForWriting` is the borrow discipline that follows,
so the freeze half of §3 is here; splitting one loan into two and joining two back
is not. Nor is the lifetime field, nor atomic authority, both above.

## What consumes `AuthorityState`

Theorems, and nothing else. The operational decision — may this access proceed —
is `Grass/Op/LoanAuthority.lean`'s provider, which tests the loan map directly, and
`loan_refuses_only_the_frozen` there is the bridge saying the two agree. That is
worth stating plainly, because a summary type with no runtime consumer is one step
away from the defect this layer keeps finding, and the difference is that this one
is a *specification* summary whose purpose is to give §3's laws a statement. What
would make it the defect is a constructor nothing builds, so `authorityOf` builds
every constructor there is and `Tests/Memory/Loans.lean` exhibits each.
-/

namespace Grass.Memory

open Grass.Core Grass.Std.Logical

/--
The authority a context holds over some bytes, from `docs/MEMORY_MODEL.md` §3's
list.

**A closed sum over an open list.** §3 says the canonical states "include" these,
which is an enumeration a profile may extend; this is a sum, which it may not. The
closure is deliberate and its consequence is the safe one: a profile needing a
sixth state cannot express it, so it cannot silently be treated as one of these
four — `docs/FOUNDATION.md` law 8 forbids the permissive fallback, not the
extension. Extending means editing this module, in the open, with the laws below
re-proved. A genuinely new *kind* of authority remains a `GrantKind`, which is open
nominal precisely so that is the usual road.

Every constructor here is built by `authorityOf` below. That is a standing
requirement rather than an accident: two of them were built by nothing, which made
the theorems about them vacuous, and a fifth constructor for atomic shared access
was deleted for the same reason (see the module comment).
-/
inductive AuthorityState where
  /-- Exclusive read/write ownership: no other context holds a loan over the
  storage. -/
  | exclusive
  /-- Shared immutable access: loans are outstanding, and none of them may write.
  Nothing here proves the bytes cannot change — no rule stops the *lender* writing
  them, and §7.3's race rules are M8's. What is stated is that this state permits
  no ordinary write (`not_permitsOrdinaryWrite_sharedImmutable`) and that it arises
  exactly when the outstanding loans are all read-only
  (`authorityOf_eq_sharedImmutable_iff`). -/
  | sharedImmutable
  /-- An owner fragment frozen because another context may write it. -/
  | frozen
  /-- No authority at all: the storage is dead or was never allocated. -/
  | unavailable
deriving DecidableEq, Repr

namespace AuthorityState

/-- Whether this state permits an ordinary write.

Only `exclusive` does. `sharedImmutable` is immutable by name; `frozen` is the
state an owner is in *because* another context may write the bytes; and
`unavailable` holds nothing. -/
def PermitsOrdinaryWrite : AuthorityState → Prop
  | .exclusive => True
  | _ => False

instance : (s : AuthorityState) → Decidable s.PermitsOrdinaryWrite
  | .exclusive => .isTrue trivial
  | .sharedImmutable | .frozen | .unavailable => .isFalse (fun h => h)

/-- **Exclusive is the only state that permits an ordinary write.** Stated as an
equivalence so a proof about `authorityOf` need only pin the state down, and so
that adding a constructor cannot quietly widen what is permitted: a new case breaks
this theorem rather than falling through the wildcard above unnoticed. -/
theorem permitsOrdinaryWrite_iff_exclusive {s : AuthorityState} :
    s.PermitsOrdinaryWrite ↔ s = .exclusive := by
  cases s <;> simp [PermitsOrdinaryWrite]

/-- A frozen fragment does not permit an ordinary write: that is what being frozen
while another context may write means. -/
@[simp] theorem not_permitsOrdinaryWrite_frozen :
    ¬ AuthorityState.frozen.PermitsOrdinaryWrite := fun h => h

/-- Shared immutable access does not permit a write either. Its whole content is
that the bytes do not change while the loans are held. -/
@[simp] theorem not_permitsOrdinaryWrite_sharedImmutable :
    ¬ AuthorityState.sharedImmutable.PermitsOrdinaryWrite := fun h => h

/-- Dead or unallocated storage permits nothing. `AllocationRecord.live`'s own
docstring says a dead allocation authorizes nothing whatever provenance is
presented, and this is that fact at the authority layer. -/
@[simp] theorem not_permitsOrdinaryWrite_unavailable :
    ¬ AuthorityState.unavailable.PermitsOrdinaryWrite := fun h => h

end AuthorityState

namespace MemoryState

/--
The loans outstanding over the same *bytes* as `provenance`, overlapping `range`.

`MemoryState.SharesBytes`, not `Provenance.SameStorage`. That is not a detail: this
layer already learned the difference once. `Grass/Memory/State.lean` records that
`Conflicts` used to require `SameStorage` and "declared every aliased pair
non-conflicting: a write through a mapped view and a write through the file it maps
would not conflict", which is why `SharesBytes` exists at all — and this function
was written with `SameStorage` anyway. Review drove a thread's store to lent bytes
through an aliasing view and it committed with no violation, defeating the loan
rule with one allocation identity.

Aliasing is a fact about storage, so a loan over a mapped file is a loan over the
view of it. `SharesBytes` is reflexive, so this still catches the ordinary
same-allocation case.

`ByteRange.Meets`, not `¬ Disjoint`, and for the same reason one layer down. An
empty range covers no offset, so every range is `Disjoint` from it — and a query
about a *position* got the answer "no loans outstanding". Review asked what
authority the owner held over offset 4 while `[0, 8)` was lent out and was told
exclusive, with an ordinary write permitted. `docs/MEMORY_MODEL.md` §5.1 makes
positions meaningful, so a query about one has to be answered about one.

The argument order matters: the loan's range is the extent, the queried range is
the position. A loan over *no* bytes therefore constrains nothing, which is what
stops a zero-byte grant freezing live storage.
-/
def loansOver (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    List (GrantId × AuthorityGrant) :=
  state.grants.entries.filter fun entry =>
    entry.2.kind = GrantKind.loan &&
      decide (state.SharesBytes entry.2.provenance.root provenance.root) &&
      decide (entry.2.range.Meets range)

/-- How many loans are outstanding. A derived cache in the strict sense: it is a
function of the map and there is nowhere else for it to live. -/
def outstandingLoans (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    Nat := (state.loansOver provenance range).length

/--
`state.Exclusive provenance range` holds when no loan is outstanding over those
bytes.

§3 requires exclusive authority to be restored only when the relevant map is
empty, and this is defined as that emptiness rather than checked against a stored
number — so `exclusive_iff_no_outstanding` reads a count off the map instead of
trusting one, and there is no counter that could go stale.
-/
def Exclusive (state : MemoryState) (provenance : Provenance) (range : ByteRange) : Prop :=
  state.loansOver provenance range = []

instance (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    Decidable (state.Exclusive provenance range) :=
  inferInstanceAs (Decidable (_ = _))

/-- **Exclusive exactly when the relevant map is empty.** The count form of the
same fact, which is what makes `outstandingLoans` a cache rather than a second
authority. -/
theorem exclusive_iff_no_outstanding (state : MemoryState) (provenance : Provenance)
    (range : ByteRange) :
    state.Exclusive provenance range ↔ state.outstandingLoans provenance range = 0 := by
  unfold Exclusive outstandingLoans
  exact ⟨fun h => by rw [h]; rfl, fun h => List.eq_nil_of_length_eq_zero h⟩

/--
`state.Live provenance` holds when the provenance's root allocation exists and is
live.

Authority over storage that is gone is not weak authority, it is none — which is
`AllocationRecord.live`'s own rule ("a dead allocation authorizes nothing, whatever
provenance is presented") read at this layer. Without it `authorityOf` reported the
empty state as exclusively owned by anybody who asked, and `AuthorityState.unavailable`
was a constructor nothing built.
-/
def Live (state : MemoryState) (provenance : Provenance) : Prop :=
  (state.MetadataAt provenance.root).any (fun record => record.live) = true

instance (state : MemoryState) (provenance : Provenance) : Decidable (state.Live provenance) :=
  inferInstanceAs (Decidable (_ = _))

/-- `state.LentToAnother context provenance range` holds when some other context's
loan covers those bytes. -/
def LentToAnother (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : Prop :=
  (state.loansOver provenance range).any (fun entry => entry.2.holder ≠ context) = true

instance (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : Decidable (state.LentToAnother context provenance range) :=
  inferInstanceAs (Decidable (_ = _))

/-- `state.LentForWriting context provenance range` holds when some other context's
loan covers those bytes **and may write them**.

The distinction `LentToAnother` alone cannot make: `docs/MEMORY_MODEL.md` §3 lists
shared immutable access as a state of its own, and §7.3 makes a conflict require at
least one writer. Loans that may only read leave the bytes immutable for as long as
they are held, which is a different situation from a frozen fragment and is why
`sharedImmutable` is a state rather than a name. -/
def LentForWriting (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : Prop :=
  (state.loansOver provenance range).any
    (fun entry => entry.2.holder ≠ context && decide (entry.2.rights.Permits .write)) = true

instance (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : Decidable (state.LentForWriting context provenance range) :=
  inferInstanceAs (Decidable (_ = _))

/-- A loan that may write is a loan. The two predicates are not independent, and
`frozen` and `sharedImmutable` partition `LentToAnother` because of this. -/
theorem lentToAnother_of_lentForWriting {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange}
    (h : state.LentForWriting context provenance range) :
    state.LentToAnother context provenance range := by
  unfold LentForWriting at h
  unfold LentToAnother
  simp only [List.any_eq_true] at *
  obtain ⟨entry, hmem, hcond⟩ := h
  exact ⟨entry, hmem, ((Bool.and_eq_true _ _).mp hcond).1⟩

/--
The authority `context` holds over bytes that may be lent.

Four cases, and every `AuthorityState` constructor is one of them — the type says
that is a standing requirement, and this is where it is met. Dead or absent
storage is `unavailable`; nothing lent to anyone else is `exclusive`; another
context able to write is `frozen`, which is §3's "frozen owner fragments while
loans exist"; and otherwise the outstanding loans are all read-only, which is §3's
shared immutable access.

**It takes the context, and an earlier version did not.** Without it a context that
lent to itself was reported frozen while `Grass/Op/LoanAuthority.lean` let its
write through — the two halves of the model contradicting each other, which review
demonstrated. A loan you hold yourself does not freeze you out of your own bytes;
that is what holding it means.

Like `outstandingLoans` it is a function of the state, so lending freezes,
returning thaws, and freeing revokes, with no field to keep in step.
-/
def authorityOf (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : AuthorityState :=
  if ¬ state.Live provenance then .unavailable
  else if ¬ state.LentToAnother context provenance range then .exclusive
  else if state.LentForWriting context provenance range then .frozen
  else .sharedImmutable

/-- **Unavailable exactly when the storage is dead or absent.** -/
@[simp] theorem authorityOf_eq_unavailable_iff (state : MemoryState) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) :
    state.authorityOf context provenance range = .unavailable ↔ ¬ state.Live provenance := by
  unfold authorityOf
  by_cases hlive : state.Live provenance
  · rw [if_neg (by simpa using hlive)]
    by_cases hlent : state.LentToAnother context provenance range
    · rw [if_neg (by simpa using hlent)]
      by_cases hwrite : state.LentForWriting context provenance range <;>
        simp [hwrite, hlive]
    · rw [if_pos (by simpa using hlent)]
      simp [hlive]
  · rw [if_pos hlive]
    simp [hlive]

/-- **Exclusive exactly when the storage is live and nobody else holds a covering
loan.** The `Live` conjunct is not decoration: without it the empty state reported
exclusive ownership of an allocation that does not exist. -/
@[simp] theorem authorityOf_eq_exclusive_iff (state : MemoryState) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) :
    state.authorityOf context provenance range = .exclusive ↔
      state.Live provenance ∧ ¬ state.LentToAnother context provenance range := by
  unfold authorityOf
  by_cases hlive : state.Live provenance
  · rw [if_neg (by simpa using hlive)]
    by_cases hlent : state.LentToAnother context provenance range
    · rw [if_neg (by simpa using hlent)]
      by_cases hwrite : state.LentForWriting context provenance range <;>
        simp [hwrite, hlent]
    · rw [if_pos (by simpa using hlent)]
      simp [hlive, hlent]
  · rw [if_pos hlive]
    simp [hlive]

/-- **Frozen exactly when another context may write the bytes.** -/
@[simp] theorem authorityOf_eq_frozen_iff (state : MemoryState) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) :
    state.authorityOf context provenance range = .frozen ↔
      state.Live provenance ∧ state.LentForWriting context provenance range := by
  unfold authorityOf
  by_cases hlive : state.Live provenance
  · rw [if_neg (by simpa using hlive)]
    by_cases hlent : state.LentToAnother context provenance range
    · rw [if_neg (by simpa using hlent)]
      by_cases hwrite : state.LentForWriting context provenance range <;>
        simp [hwrite, hlive]
    · rw [if_pos (by simpa using hlent)]
      have hnw : ¬ state.LentForWriting context provenance range :=
        fun hw => hlent (lentToAnother_of_lentForWriting hw)
      simp [hlive, hnw]
  · rw [if_pos hlive]
    simp [hlive]

/-- **Shared immutable exactly when live bytes are lent, and only for reading.** -/
@[simp] theorem authorityOf_eq_sharedImmutable_iff (state : MemoryState)
    (context : ContextId) (provenance : Provenance) (range : ByteRange) :
    state.authorityOf context provenance range = .sharedImmutable ↔
      state.Live provenance ∧ state.LentToAnother context provenance range ∧
        ¬ state.LentForWriting context provenance range := by
  unfold authorityOf
  by_cases hlive : state.Live provenance
  · rw [if_neg (by simpa using hlive)]
    by_cases hlent : state.LentToAnother context provenance range
    · rw [if_neg (by simpa using hlent)]
      by_cases hwrite : state.LentForWriting context provenance range <;>
        simp [hwrite, hlive, hlent]
    · rw [if_pos (by simpa using hlent)]
      simp [hlent]
  · rw [if_pos hlive]
    simp [hlive]

/--
**A context may not write bytes another context may write.**

The borrow discipline, as a theorem rather than a convention. While another
context's write loan covers the range this context's fragment is frozen, and
`AuthorityState.PermitsOrdinaryWrite` is false of `frozen`.
-/
theorem not_permitsOrdinaryWrite_of_lentForWriting {state : MemoryState}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    (hlive : state.Live provenance) (h : state.LentForWriting context provenance range) :
    ¬ (state.authorityOf context provenance range).PermitsOrdinaryWrite := by
  rw [(authorityOf_eq_frozen_iff state context provenance range).mpr ⟨hlive, h⟩]
  exact AuthorityState.not_permitsOrdinaryWrite_frozen

/-- **A context may not write bytes another context is reading under a loan.**
Shared immutable access is immutable for the lender too: §7.3 makes a write against
an outstanding read a conflict, and the read loan is what says the reader is there. -/
theorem not_permitsOrdinaryWrite_of_lentToAnother {state : MemoryState}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    (h : state.LentToAnother context provenance range) :
    ¬ (state.authorityOf context provenance range).PermitsOrdinaryWrite := by
  rw [AuthorityState.permitsOrdinaryWrite_iff_exclusive,
    authorityOf_eq_exclusive_iff state context provenance range]
  exact fun hc => hc.2 h

/-- **Dead storage may not be written**, however few loans are outstanding over it.
Exclusivity is not authority: `Exclusive` says the loan map is empty, and an empty
loan map over a freed allocation is not permission to write it. -/
theorem not_permitsOrdinaryWrite_of_not_live {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} (h : ¬ state.Live provenance) :
    ¬ (state.authorityOf context provenance range).PermitsOrdinaryWrite := by
  rw [(authorityOf_eq_unavailable_iff state context provenance range).mpr h]
  exact AuthorityState.not_permitsOrdinaryWrite_unavailable

/-- Live storage with nothing outstanding against this context may be written.
Exclusivity in the strong sense — no loans at all — implies this, so an unlent
owner of a live allocation writes. -/
theorem permitsOrdinaryWrite_of_exclusive {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} (hlive : state.Live provenance)
    (h : state.Exclusive provenance range) :
    (state.authorityOf context provenance range).PermitsOrdinaryWrite := by
  rw [AuthorityState.permitsOrdinaryWrite_iff_exclusive,
    authorityOf_eq_exclusive_iff state context provenance range]
  refine ⟨hlive, ?_⟩
  unfold LentToAnother Exclusive at *
  rw [h]
  simp

/--
Two grants issue conflicting authority.

`docs/MEMORY_MODEL.md` §7.3 defines a conflict as overlapping live bytes with at
least one writer, and says "unique loans prevent ordinary conflicting authority
from being issued". This is that test applied at issue time rather than at access
time: the point of uniqueness is that the conflicting pair never exists, not that
one of them is later refused.

Two read-only loans over one range do not conflict, which is `sharedImmutable`
being a real state rather than a name.
-/
def LoanConflicts (state : MemoryState) (a b : AuthorityGrant) : Prop :=
  state.SharesBytes a.provenance.root b.provenance.root ∧
    ¬ a.range.Disjoint b.range ∧
    (a.rights.Permits AccessIntent.write ∨ b.rights.Permits AccessIntent.write)

instance (state : MemoryState) (a b : AuthorityGrant) :
    Decidable (state.LoanConflicts a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/--
Issue a loan, or refuse.

`Option`, because both ways of getting this wrong are silent otherwise, and review
found both.

**Reissue.** An earlier version was `grants.insert`, and `FiniteMap.insert` erases
any existing binding — so lending twice under one identity returned the first loan
with no `returnLoan`, and exclusivity came back for bytes still borrowed. §3 says a
return consumes that exact identity; a reissue is a return nobody asked for.

**Conflict.** §7.3 says unique loans prevent conflicting authority from being
issued. Nothing prevented issuing two overlapping write loans to different holders,
and each satisfied the access rule, so both could write the same bytes. Refusing at
issue is what "prevent from being issued" means.

Refusing rather than overwriting or ignoring is `docs/FOUNDATION.md` law 8's
direction, and `lend?_eq_none_of_reissued` and `lend?_eq_none_of_conflict` are the
two refusals stated, so a caller that cannot lend finds out.
-/
def lend? (state : MemoryState) (id : GrantId) (grant : AuthorityGrant) :
    Option MemoryState :=
  if (state.grants.lookup id).isSome then Option.none
  else if state.grants.entries.any
      (fun entry => entry.2.kind = GrantKind.loan && decide (state.LoanConflicts entry.2 grant))
    then Option.none
  else some { state with grants := state.grants.insert id grant }

/-- **A reissued identity is refused.** -/
theorem lend?_eq_none_of_reissued (state : MemoryState) {id : GrantId}
    (grant : AuthorityGrant) (h : (state.grants.lookup id).isSome) :
    state.lend? id grant = Option.none := by
  unfold lend?
  rw [if_pos h]

/-- **Conflicting authority is refused at issue.** -/
theorem lend?_eq_none_of_conflict (state : MemoryState) (id : GrantId)
    (grant : AuthorityGrant)
    (h : state.grants.entries.any
      (fun entry => entry.2.kind = GrantKind.loan &&
        decide (state.LoanConflicts entry.2 grant)) = true) :
    state.lend? id grant = Option.none := by
  unfold lend?
  by_cases hfresh : (state.grants.lookup id).isSome = true
  · rw [if_pos hfresh]
  · rw [if_neg hfresh, if_pos h]

/-- Return the loan with **that exact identity**.

`docs/MEMORY_MODEL.md` §3: "Returning one loan consumes that exact identity."
`GrantId` is a `Uid`, which a supply never reissues, so the identity a return names
is the one that was lent — a return cannot consume a different loan that happens to
describe the same bytes, rights, and holder. That is why the map is keyed by
identity and not by shape. -/
def returnLoan (state : MemoryState) (id : GrantId) : MemoryState :=
  { state with grants := state.grants.erase id }

/-- **A return consumes the identity it names, and only that one.** -/
@[simp] theorem lookup_returnLoan_self (state : MemoryState) (id : GrantId) :
    (state.returnLoan id).grants.lookup id = Option.none :=
  FiniteMap.lookup_erase_self _ _

/-- Returning one loan leaves every other identity alone. Two loans over the same
bytes are two loans, and returning one does not return the other. -/
@[simp] theorem lookup_returnLoan_ne (state : MemoryState) {id other : GrantId}
    (h : other ≠ id) :
    (state.returnLoan id).grants.lookup other = state.grants.lookup other :=
  FiniteMap.lookup_erase_ne _ h

/-- A successful lend records the loan under the identity it names. -/
theorem lookup_lend?_self {state lent : MemoryState} {id : GrantId}
    {grant : AuthorityGrant} (h : state.lend? id grant = some lent) :
    lent.grants.lookup id = some grant := by
  unfold lend? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · injection h with h
      subst h
      exact FiniteMap.lookup_insert_self _ _ _

/-- A state with no grants is exclusive everywhere: nothing is lent, so nothing is
outstanding.

**Exclusive is not authority**, and this theorem is the clearest place to say so.
The empty state has no allocations either, so `authorityOf` reports `unavailable`
over the same bytes and permits no write — `not_permitsOrdinaryWrite_of_not_live`.
Reading `Exclusive` as permission is the mistake `authorityOf` used to make. -/
@[simp] theorem exclusive_empty (provenance : Provenance) (range : ByteRange) :
    empty.Exclusive provenance range := rfl

/-- The empty state is not live anywhere, so its exclusivity grants nothing. -/
@[simp] theorem not_live_empty (provenance : Provenance) : ¬ empty.Live provenance := by
  simp [Live, MetadataAt, empty, FiniteMap.empty, FiniteMap.lookup]

end MemoryState

end Grass.Memory
