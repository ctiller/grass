import Grass.Memory.State

/-!
# Loans and exclusive authority

`docs/MEMORY_MODEL.md` §3 is the whole of what this module implements. M1 carried
`AuthorityGrant` a milestone early, deliberately general and deliberately not a
loan model: it existed so `Grass/Op/Step.lean`'s `AuthorityProvider` had a real
table to check against, and its own comment says split, join, freeze, and
exclusivity-iff-empty are M3's. This is M3's.

## What §3 actually demands

Five canonical authority states, named here as `AuthorityState`. A loan map keyed
by identity, carrying holder, range, rights, lifetime, and conditions.

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

Split and join of loans. `MemoryState.ownerAuthority` puts an owner into
`AuthorityState.frozen` while a loan is outstanding and
`not_permitsOrdinaryWrite_of_not_exclusive` is the borrow discipline that follows,
so the freeze half of §3 is here; splitting one loan into two and joining two back
is not. Nor is the lifetime field above.
-/

namespace Grass.Memory

open Grass.Core Grass.Std.Logical

/--
The canonical authority states of `docs/MEMORY_MODEL.md` §3.

Named as a closed sum because §3 names them as the canonical list. A profile
needing another does not add a constructor here: `atomicShared` carries the
profile's own ordering, and a genuinely new *kind* of authority is a
`GrantKind`, which is open nominal precisely so this does not have to be.
-/
inductive AuthorityState where
  /-- Exclusive read/write ownership: no loan is outstanding over the storage. -/
  | exclusive
  /-- Shared immutable access. -/
  | sharedImmutable
  /-- Atomic shared access under a declared ordering profile. -/
  | atomicShared (ordering : OrderingDemand)
  /-- An owner fragment frozen because loans exist over it. -/
  | frozen
  /-- Authority transferred elsewhere, or otherwise unavailable. -/
  | unavailable
deriving DecidableEq, Repr

namespace AuthorityState

/-- Whether this state permits an ordinary non-atomic write.

Only `exclusive` does. `sharedImmutable` is immutable by name; `atomicShared`
grants atomic access and §3 says atomics do not grant ordinary non-atomic access;
`frozen` is the state an owner is in *because* it lent the bytes out; and
`unavailable` holds nothing. -/
def PermitsOrdinaryWrite : AuthorityState → Prop
  | .exclusive => True
  | _ => False

instance : (s : AuthorityState) → Decidable s.PermitsOrdinaryWrite
  | .exclusive => .isTrue trivial
  | .sharedImmutable | .atomicShared _ | .frozen | .unavailable => .isFalse (fun h => h)

/-- **Atomic authority is not ordinary authority.** `docs/MEMORY_MODEL.md` §3:
"Atomics do not grant ordinary non-atomic access and must follow the ISA/platform
ordering model." -/
@[simp] theorem not_permitsOrdinaryWrite_atomicShared (ordering : OrderingDemand) :
    ¬ (AuthorityState.atomicShared ordering).PermitsOrdinaryWrite := fun h => h

/-- A frozen fragment does not permit an ordinary write either: that is what being
frozen while a loan exists means. -/
@[simp] theorem not_permitsOrdinaryWrite_frozen :
    ¬ AuthorityState.frozen.PermitsOrdinaryWrite := fun h => h

end AuthorityState

namespace MemoryState

/--
The loans outstanding over `provenance`'s storage that overlap `range`.

Derived, and that is the point. §3 says "counts are derived caches only", so there
is no field to disagree with the map — the discipline that removed
`AllocationRecord.initialized` and `AccessIntent.isDevice` from this layer.

`Provenance.SameStorage` rather than provenance equality, because a loan over an
object covers a loan over a field of it: the path descends, the storage does not
change.
-/
def loansOver (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    List (GrantId × AuthorityGrant) :=
  state.grants.entries.filter fun entry =>
    entry.2.kind = GrantKind.loan &&
      decide (entry.2.provenance.SameStorage provenance) &&
      decide (¬ entry.2.range.Disjoint range)

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
The authority an *owner* holds over bytes it may have lent.

`docs/MEMORY_MODEL.md` §3 lists "frozen owner fragments while loans exist" among
the canonical states, and this is what puts an owner into one. An owner with no
outstanding loan over the bytes holds them exclusively; an owner with one holds a
frozen fragment, and `AuthorityState.PermitsOrdinaryWrite` is false of that.

It is a *function of the map*, like `outstandingLoans` and for the same reason: an
owner's authority is not a fact stored beside the loans that could disagree with
them. Lending is what freezes, returning is what thaws, and neither needs to
remember to update a field.

This is the owner's view. A borrower's authority is its loan's `rights`, which
`AuthorityGrant.Authorizes` already decides; the two are different questions and
this answers only the first.
-/
def ownerAuthority (state : MemoryState) (provenance : Provenance) (range : ByteRange) :
    AuthorityState :=
  if state.Exclusive provenance range then .exclusive else .frozen

/-- An owner is exclusive exactly when nothing is lent. -/
@[simp] theorem ownerAuthority_eq_exclusive_iff (state : MemoryState)
    (provenance : Provenance) (range : ByteRange) :
    state.ownerAuthority provenance range = .exclusive ↔
      state.Exclusive provenance range := by
  unfold ownerAuthority
  by_cases h : state.Exclusive provenance range <;> simp [h]

/-- And frozen exactly when something is. -/
@[simp] theorem ownerAuthority_eq_frozen_iff (state : MemoryState)
    (provenance : Provenance) (range : ByteRange) :
    state.ownerAuthority provenance range = .frozen ↔
      ¬ state.Exclusive provenance range := by
  unfold ownerAuthority
  by_cases h : state.Exclusive provenance range <;> simp [h]

/--
**An owner may not write bytes it has lent.**

The borrow discipline, as a theorem rather than as a convention. While any loan is
outstanding over the range the owner's fragment is frozen, and
`AuthorityState.PermitsOrdinaryWrite` is false of `frozen` — so the owner regains
the ability to write only by the relevant map becoming empty, which §3 requires and
which `Exclusive` is defined as.
-/
theorem not_permitsOrdinaryWrite_of_not_exclusive {state : MemoryState}
    {provenance : Provenance} {range : ByteRange}
    (h : ¬ state.Exclusive provenance range) :
    ¬ (state.ownerAuthority provenance range).PermitsOrdinaryWrite := by
  rw [(ownerAuthority_eq_frozen_iff state provenance range).mpr h]
  exact AuthorityState.not_permitsOrdinaryWrite_frozen

/-- And regains it when the map empties, so the freeze is not a one-way door. -/
theorem permitsOrdinaryWrite_of_exclusive {state : MemoryState}
    {provenance : Provenance} {range : ByteRange}
    (h : state.Exclusive provenance range) :
    (state.ownerAuthority provenance range).PermitsOrdinaryWrite := by
  rw [(ownerAuthority_eq_exclusive_iff state provenance range).mpr h]
  trivial

/-- Record a loan under a fresh identity. -/
def lend (state : MemoryState) (id : GrantId) (grant : AuthorityGrant) : MemoryState :=
  { state with grants := state.grants.insert id grant }

/--
Return the loan with **that exact identity**.

`docs/MEMORY_MODEL.md` §3: "Returning one loan consumes that exact identity."
`GrantId` is a `Uid`, which a supply never reissues, so the identity a return
names is the one that was lent — a return cannot consume a different loan that
happens to describe the same bytes, rights, and holder. That is why the map is
keyed by identity and not by shape.
-/
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

/-- Lending records the loan under the identity it names. -/
@[simp] theorem lookup_lend_self (state : MemoryState) (id : GrantId)
    (grant : AuthorityGrant) : (state.lend id grant).grants.lookup id = some grant :=
  FiniteMap.lookup_insert_self _ _ _

/--
**Lending ends exclusivity.**

The owner's fragment is frozen while the loan exists, which is `AuthorityState.frozen`
and which §3 lists among the canonical states. Stated as the loss of `Exclusive`,
because that is the property a later access check consults.
-/
theorem not_exclusive_lend {state : MemoryState} {id : GrantId} {grant : AuthorityGrant}
    {provenance : Provenance} {range : ByteRange}
    (hkind : grant.kind = GrantKind.loan)
    (hstorage : grant.provenance.SameStorage provenance)
    (hoverlap : ¬ grant.range.Disjoint range) :
    ¬ (state.lend id grant).Exclusive provenance range := by
  unfold Exclusive loansOver lend
  intro hnil
  have hmem : (id, grant) ∈ (state.grants.insert id grant).entries := by
    show (id, grant) ∈ (id, grant) :: eraseKey state.grants.entries id
    exact List.mem_cons_self
  have hin : (id, grant) ∈
      (state.grants.insert id grant).entries.filter (fun entry =>
        entry.2.kind = GrantKind.loan &&
          decide (entry.2.provenance.SameStorage provenance) &&
          decide (¬ entry.2.range.Disjoint range)) := by
    refine List.mem_filter.mpr ⟨hmem, ?_⟩
    simp [hkind, hstorage, hoverlap]
  rw [hnil] at hin
  exact absurd hin (by simp)

/-- A state with no grants is exclusive everywhere. Authority is held, not
assumed, so the empty state is the exclusive one. -/
@[simp] theorem exclusive_empty (provenance : Provenance) (range : ByteRange) :
    empty.Exclusive provenance range := rfl

end MemoryState

end Grass.Memory
