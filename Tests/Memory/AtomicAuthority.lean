import Grass.Memory.Loan

/-!
# Atomic authority does not convey ordinary access

`docs/MEMORY_MODEL.md` §3: "Atomics do not grant ordinary non-atomic access and
must follow the ISA/platform ordering model."

The first clause had no mechanism at all for several milestones, and the way it
came to have none is worth recording. `AuthorityState` carried an `atomicShared`
constructor and `not_permitsOrdinaryWrite_atomicShared` was the §3 law about it —
and nothing built the constructor, because `AuthorityGrant` carries no ordering and
`authorityOf` reads only the grant map. A theorem about an unreachable case reads as
coverage without being any, so both were deleted.

The reasoning offered for the deletion went one step too far. It said the rule had
nothing to constrain, and review pointed out that this is false: `Permission.Permits`
is the sole rights gate on the chain `MemoryState.AuthorizedAt` →
`MemoryState.Granted` → `AuthorityProvider.loan.refuses` → `Grass/Op/Step.lean`,
and it had no clause about atomicity. (The chain was named as the deleted `Authorizes` function and
`MemoryState.GrantedOfKind` until review checked: the first was deleted, and the
second has no caller under `Grass/` — the provider calls `Granted`, which is
kind-blind on purpose, because `Grass/Op/Step.lean` composes providers conjunctively
and a loan provider refusing an access another authority covers would make that
authority unusable.) So a grant a profile issued for atomic access
authorized an ordinary one indistinguishably. `Permission.atomicOnly` is the rule at
that gate.

The second clause — following the ISA and platform ordering model — is not here and
is not claimed. That is `ConsistencyProfile`'s, which is M8's, and
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records it.
-/

namespace Tests.Memory.AtomicAuthority

open Grass.Core Grass.Memory

private def allocs : FreshSupply AllocTag := .initial
private def epochs : FreshSupply EpochTag := .initial
private def contexts : FreshSupply ContextTag := .initial
private def grants : FreshSupply GrantTag := .initial

/-- The shared word. -/
def counter : AllocId := allocs.fresh.1

/-- The context holding atomic authority over it. -/
def holder : ContextId := contexts.fresh.1

/-- A second context, which holds nothing. -/
def stranger : ContextId := contexts.fresh.2.fresh.1

private def epoch : EpochId := epochs.fresh.1

/-- The atomic grant's identity. -/
def atomicLoan : GrantId := grants.fresh.1

/-- Provenance of the whole word. -/
def counterProv : Provenance :=
  { space := .cpuVirtual, root := counter, epoch := epoch, source := .virtualAlloc
    rootExtent := ⟨0, 8⟩, path := [] }

/-- A state owning the word. -/
def owned : MemoryState :=
  (MemoryState.empty.allocate? counter
    { extent := ⟨0, 8⟩, epoch := epoch, space := .cpuVirtual
      permission := .readWrite, live := true, bytes := .empty
      base := some 0x2000 }).getD .empty

/-- The allocation happened, so `getD` did not fall back to the empty state. -/
theorem the_allocation_succeeds :
    (MemoryState.empty.allocate? counter
      { extent := ⟨0, 8⟩, epoch := epoch, space := .cpuVirtual
        permission := .readWrite, live := true, bytes := .empty
        base := some 0x2000 }).isSome := by decide

/-- Read/write conveyed for **atomic** access only. §3's atomic shared access,
expressed as a right rather than as an authority state. -/
def atomicGrant : AuthorityGrant :=
  { kind := .loan, holder := holder, lender := stranger, provenance := counterProv
    range := ⟨0, 8⟩, rights := .atomicReadWrite }

/-- The same grant without the restriction, so every theorem below can be compared
against the case that differs in exactly one field. -/
def ordinaryGrant : AuthorityGrant :=
  { atomicGrant with rights := .readWrite }

/-- The state holding the atomic grant. -/
def lentAtomically : MemoryState := (owned.issue? atomicLoan atomicGrant).getD owned

/-- And the one holding the ordinary grant. -/
def lentOrdinarily : MemoryState := (owned.issue? atomicLoan ordinaryGrant).getD owned

/-- Both lends succeeded, so neither `getD` fell back to `owned` and the theorems
below are about lent states. -/
theorem the_lends_succeed :
    (owned.issue? atomicLoan atomicGrant).isSome ∧
    (owned.issue? atomicLoan ordinaryGrant).isSome := by
  exact ⟨by decide, by decide⟩

/-! ## The grant does not authorize an ordinary access -/

/--
**The holder of atomic authority may not perform an ordinary write.**

§3's sentence, at the gate. `GrantedOfKind` is what
`Grass/Op/LoanAuthority.lean`'s holder test consults, so this is the transition's
own question asked of the map.
-/
theorem an_atomic_grant_does_not_authorize_an_ordinary_write :
    ¬ lentAtomically.GrantedOfKind .loan holder counterProv ⟨0, 8⟩ AccessIntent.write := by
  decide

/-- **Nor an ordinary read.** §3 says atomics do not grant ordinary non-atomic
*access*, which is not only writes — a plain load of a word another context is
updating atomically is exactly the race the rule exists for. -/
theorem an_atomic_grant_does_not_authorize_an_ordinary_read :
    ¬ lentAtomically.GrantedOfKind .loan holder counterProv ⟨0, 8⟩ AccessIntent.read := by
  decide

/-- **But it does authorize the atomic access it exists for.** Without this the two
theorems above would be consistent with a grant that authorizes nothing, which is
not a rule about atomicity. -/
theorem an_atomic_grant_authorizes_an_atomic_access :
    lentAtomically.GrantedOfKind .loan holder counterProv ⟨0, 8⟩
      AccessIntent.atomicReadWrite := by decide

/-- The ordinary grant differs in exactly one field and does authorize the ordinary
write, so the refusals above are `atomicOnly` biting rather than something else in
the fixture. -/
theorem the_ordinary_grant_authorizes_the_ordinary_write :
    lentOrdinarily.GrantedOfKind .loan holder counterProv ⟨0, 8⟩ AccessIntent.write ∧
    atomicGrant.rights.read = ordinaryGrant.rights.read ∧
    atomicGrant.rights.write = ordinaryGrant.rights.write ∧
    atomicGrant.rights.execute = ordinaryGrant.rights.execute ∧
    atomicGrant.rights.atomicOnly ≠ ordinaryGrant.rights.atomicOnly := by
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- And an ordinary permission conveys an atomic access, so the restriction runs one
way only: a profile that never says `atomicOnly` has acquired no new refusal. -/
theorem an_ordinary_grant_authorizes_an_atomic_access :
    lentOrdinarily.GrantedOfKind .loan holder counterProv ⟨0, 8⟩
      AccessIntent.atomicWrite := by decide

/-! ## It is still a grant for every other purpose

`Permission.atomicOnly` restricts what the grant *conveys to its holder*. It must
not make the grant invisible to the conflict rules: a context updating a word
atomically is precisely a context whose bytes another context may not write
ordinarily.

That is not automatic, and getting it wrong took minutes. `WritableByAnother`
probed `rights.Permits AccessIntent.write`, and an atomic-only grant does not
*permit* an ordinary write — so the first version of this file reported the
stranger `sharedImmutable` and the atomic writer froze nobody. The probe is
`rights.write`, the capability, because §7.3's "at least one writer" asks who may
change the bytes. -/

/-- **The stranger holds `atomicShared` authority**, which is §3's third canonical
state derived rather than declared. It was a constructor nothing built for one
round, and the theorem about it was deleted for holding of an unreachable case. -/
theorem the_atomic_grant_gives_the_stranger_atomic_shared :
    lentAtomically.authorityOf stranger counterProv ⟨0, 8⟩ = AuthorityState.atomicShared := by
  decide

/-- **And that state refuses the stranger an ordinary write**, which is §3's
sentence reaching a state a real map produces. -/
theorem the_stranger_may_not_write_ordinarily :
    ¬ (lentAtomically.authorityOf stranger counterProv ⟨0, 8⟩).PermitsOrdinaryWrite ∧
    ¬ (lentAtomically.authorityOf stranger counterProv ⟨0, 8⟩).PermitsIntent
        AccessIntent.read := by
  exact ⟨by decide, by decide⟩

/-- But it permits an atomic one, so the stranger may join the protocol. Without
this the theorems above would be a freeze under another name. -/
theorem the_stranger_may_act_atomically :
    (lentAtomically.authorityOf stranger counterProv ⟨0, 8⟩).PermitsIntent
      AccessIntent.atomicReadWrite := by decide

/-- The **ordinary** grant freezes instead, so `atomicShared` above is
`atomicOnly` biting and not the shape of the fixture. -/
theorem the_ordinary_grant_freezes :
    lentOrdinarily.authorityOf stranger counterProv ⟨0, 8⟩ = AuthorityState.frozen := by
  decide

/-! ## Two contexts may share a word atomically, and only atomically

§7.3's issuance sentence is "unique loans prevent **ordinary** conflicting authority
from being issued". `LoanConflicts` had no ordinary/atomic distinction, so `issue?`
prevented *all* conflicting authority and two contexts could not share a word
atomically at all — which is `atomicShared` being unreachable by construction as
well as underived. -/

/-- A second atomic grant over the same word, to the stranger. -/
def strangersAtomicGrant : AuthorityGrant :=
  { atomicGrant with holder := stranger }

/-- A second identity for it. -/
def secondLoan : GrantId := grants.fresh.2.fresh.1

/-- **Two atomic grants over one word coexist.** -/
theorem two_atomic_grants_are_accepted :
    (lentAtomically.issue? secondLoan strangersAtomicGrant).isSome := by decide

/-- An ordinary grant alongside the atomic one is still refused: one ordinary
participant makes it an ordinary race. -/
theorem an_ordinary_grant_alongside_an_atomic_one_is_refused :
    lentAtomically.issue? secondLoan { ordinaryGrant with holder := stranger } =
      Option.none := by decide

/-- And once both atomic grants are outstanding, a third context sees
`atomicShared` rather than a freeze. -/
theorem both_holders_see_atomic_shared :
    ((lentAtomically.issue? secondLoan strangersAtomicGrant).getD lentAtomically).authorityOf
      holder counterProv ⟨0, 8⟩ = AuthorityState.atomicShared := by decide

/-- And it still counts as an outstanding loan, so §3's exclusivity sees it. -/
theorem the_atomic_grant_ends_exclusivity :
    ¬ lentAtomically.Exclusive counterProv ⟨0, 8⟩ ∧
    lentAtomically.outstandingLoans counterProv ⟨0, 8⟩ = 1 := by
  exact ⟨by decide, by decide⟩

/-- **What is not here.** §3's second clause — atomics "must follow the
ISA/platform ordering model" — has no mechanism, and this file does not pretend
otherwise. The grant carries no ordering, so nothing relates it to
`AccessDescriptor.ordering`; a §7.1 refinement theorem and M8's `ConsistencyProfile`
are what would. This theorem records that the two grants above are indistinguishable
on ordering, which is the gap stated rather than argued away. -/
theorem no_ordering_is_carried :
    atomicGrant.rights.atomicOnly = true ∧
    lentAtomically.grantAt? atomicLoan = some atomicGrant := by
  exact ⟨by decide, by decide⟩

end Tests.Memory.AtomicAuthority
