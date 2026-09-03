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

**Four and a half of the five entries** are derived here from state that already
exists: exclusive and frozen from the grant map, shared-immutable and atomic-shared
from the rights on the outstanding grants, and unavailable from allocation liveness
and epoch.

§3's fifth entry is "transferred **or** unavailable authority", and `unavailable`
covers the second half only. Nothing here represents a transfer — authority moved
rather than lent — and §4.4.1 of `docs/MEMORY_IMPLEMENTATION_PLAN.md` records it as
owed. The count was "four of five" for one round, which read as coverage of a bullet
half-delivered; that is the mistake this file keeps making, in miniature.

§3's third entry, atomic shared access, took the longest road and the record is
worth keeping. There was an `atomicShared (ordering : OrderingDemand)` constructor
and a theorem stating §3's "atomics do not grant ordinary non-atomic access" about
it, and nothing built the constructor — `AuthorityGrant` carried nothing an atomic
state could be read off. So the theorem held of an unreachable case, and both were
deleted, because a vacuous theorem reads as coverage.

The reasoning offered for that deletion went one step too far, and review caught it:
it said the rule had nothing to constrain. `Permission.Permits` is the sole rights
gate on the chain `MemoryState.AuthorizedAt` → `MemoryState.Granted` →
`Grass/Op/LoanAuthority.lean` → `step`, and it had no clause about atomicity, (The chain was named as the deleted `Authorizes` function and
`MemoryState.GrantedOfKind` until review checked: the first was deleted, and the
second has no caller under `Grass/` — the provider calls `Granted`, which is
kind-blind on purpose, because `Grass/Op/Step.lean` composes providers conjunctively
and a loan provider refusing an access another authority covers would make that
authority unusable.) so a
grant issued for atomic access authorized an ordinary one indistinguishably.
`Permission.atomicOnly` is that rule at that gate, and it is what the state is now
derived from. The constructor is back without its ordering payload, which was a
second place to say what `AccessDescriptor.ordering` already says.

§3's second clause — atomics "must follow the ISA/platform ordering model" — is
still not here, and nothing here can supply it: it needs the §7.1 refinement theorem
an ISA owner owes and the strength relation M8's `ConsistencyProfile` induces.
§4.4.1 records it.

**`AuthorityGrant` carries the first four and not the last two**, and this file
does not add them. Its own docstring already said so; the sentence here originally
described what §3 demands and read as a description of the code, which is the
drift this branch keeps being corrected for. A lifetime nothing consults would be
one more field carried and never read — the shape that produced
`AllocationRecord.initialized` and `AccessIntent.isDevice`. The lifetime discipline
belongs with M4's frames, where a bounded lifetime has something to mean, and
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records it as owed — §4.4.1 and not
§4.2, which an earlier version of this line cited and which holds M2's debts. A
recorded debt whose citation misses is not recorded.

And three laws:

- a return consumes that exact identity — `MemoryState.lookup_returnLoan?_self`
  with `MemoryState.lookup_returnLoan?_ne`;
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
`AuthorityState.frozen` while another context's write grant is outstanding and
`not_permitsOrdinaryWrite_of_writableByAnother` is the borrow discipline that
follows, so the freeze half of §3 is here; splitting one loan into two and joining
two back is not. Nor is the lifetime field, nor atomic authority, nor transferred
authority — all above.

## What consumes `AuthorityState`

`Grass/Op/LoanAuthority.lean`'s provider, on every access. It was theorems and
nothing else for a round, defended on the grounds that
`loan_refuses_only_the_frozen` bridged the summary to the transition — and that
theorem mentioned neither `authorityOf` nor `frozen`, and the "the two agree" it was
said to establish was false in both directions. Three reviewers found it
independently.

The provider now refuses any access the state does not permit
(`AuthorityState.PermitsIntent`), which is what closed two demonstrated holes: two
write grants installed through a door that checked nothing, and two
non-conflicting grants made to conflict by an alias declared afterwards. Both are
facts about what *another* context holds, which is what `HeldByAnother` and
`WritableByAnother` ask and a holder test does not;
`Tests/Op/StandardLoan.lean`'s `the_identity_cannot_be_stolen` and
`an_alias_declared_after_issue_is_refused` are those two states, stepped.

Refusal is still strictly wider than `frozen` — the provider also refuses an access
to lent bytes by a context holding no covering loan, which `authorityOf` may call
`exclusive` or `sharedImmutable` — and `a_self_loan_bounds_its_holder` in
`Tests/Op/StandardLoan.lean` exhibits that rather than leaving it to be assumed.
-/

namespace Grass.Memory

open Grass.Core Grass.Std.Logical

/--
The authority a context holds over some bytes, from `docs/MEMORY_MODEL.md` §3's
list.

**A closed sum over an open list.** §3 says the canonical states "include" these,
which is an enumeration a profile may extend; this is a sum, which it may not.

The closure is this module's decision and it is **not** the safe direction, which an
earlier version of this docstring claimed while citing law 8 for it. `authorityOf`
is a total function into these four: a situation they do not describe is not
rejected, it is classified as the nearest one. `docs/FOUNDATION.md` law 8 demands
rejection of what the model has no account of, and nothing here rejects. The
closure is kept because the alternative — an open sum with a permissive default —
is worse, and because extending means editing this module in the open with the laws
below re-proved; it is not kept because it is safe. A genuinely new *kind* of
authority remains a `GrantKind`, which is open nominal precisely so that is the
usual road, and `grantsOver` now sees every kind so that road does not lead past
the freeze.

Every constructor here is built by `authorityOf` below. That is a standing
requirement rather than an accident: two of them were built by nothing, which made
the theorems about them vacuous, and a fifth constructor for atomic shared access
was deleted for the same reason (see the module comment).
-/
inductive AuthorityState where
  /-- Exclusive read/write ownership: the storage is live and in this provenance's
  epoch, and no other context holds a grant over it
  (`authorityOf_eq_exclusive_iff` — both conjuncts).

  Weaker than §3's sentence about exclusive authority, which is about the loan map
  being empty and is `MemoryState.Exclusive`. A context holding the only grant gets
  this state while that map is non-empty. The two are different questions and
  `Grass/Op/LoanAuthority.lean` asks both. -/
  | exclusive
  /-- Atomic shared access: every outstanding grant held by another context conveys
  atomic access only, and at least one of them may write.

  §3's third canonical state, and for one round it was **deleted** rather than
  derived — `AuthorityGrant` carried nothing an atomic state could be read off, so
  the constructor was built by nothing and the theorem about it held of an
  unreachable case. `Permission.atomicOnly` is what it is read off now.

  No ordering payload. The deleted constructor carried an `OrderingDemand`, which
  is a second place to say what `AccessDescriptor.ordering` already says; §3's
  clause that atomics "must follow the ISA/platform ordering model" is M8's and is
  recorded as owed. What this state carries is §3's first clause: it permits an
  atomic access and refuses an ordinary one. -/
  | atomicShared
  /-- Shared immutable access: grants are outstanding, and none of them may write.

  The lender is stopped from writing — `not_permitsOrdinaryWrite_of_heldByAnother`,
  and `Tests/Memory/Loans.lean`'s `a_shared_immutable_lender_may_not_write` — so
  this is not a state with no guarantee, which an earlier version of this docstring
  said. What is *not* proved here is that the bytes stay unchanged in fact: that is
  §7.3's race question and M8's, and this layer states permission rather than
  outcome.

  It arises exactly when the storage is live, another context holds a grant, and no
  such grant may write (`authorityOf_eq_sharedImmutable_iff` — all three
  conjuncts). -/
  | sharedImmutable
  /-- An owner fragment frozen because another context may write it. -/
  | frozen
  /-- No authority at all: the storage is dead, was never allocated, or has moved
  to a later epoch. Half of §3's "transferred or unavailable"; transfer is owed. -/

  | unavailable
deriving DecidableEq, Repr

namespace AuthorityState

/--
Whether this state permits an access of this intent.

Written out per constructor with no wildcard. A wildcard would send a new
constructor to `False`, which is conservative and silent, and this file has twice
been corrected for prose claiming an exhaustive match it did not have: adding a
constructor must fail to compile here, and it does.

`sharedImmutable` permits a read and refuses a write. That is what §3's separate
listing of shared immutable access is for — §7.3 makes a conflict require a
writer, so reads under read-only loans are the case that is *not* a conflict.
-/
def PermitsIntent : AuthorityState → AccessIntent → Prop
  | .exclusive, _ => True
  | .atomicShared, intent => intent.isAtomic = true
  | .sharedImmutable, intent => intent.writes = false
  | .frozen, _ => False
  | .unavailable, _ => False

instance : (s : AuthorityState) → (intent : AccessIntent) → Decidable (s.PermitsIntent intent)
  | .exclusive, _ => .isTrue trivial
  | .atomicShared, _ => inferInstanceAs (Decidable (_ = _))
  | .sharedImmutable, _ => inferInstanceAs (Decidable (_ = _))
  | .frozen, _ => .isFalse (fun h => h)
  | .unavailable, _ => .isFalse (fun h => h)

/-- Whether this state permits an ordinary write. Defined as `PermitsIntent` at a
write rather than as a second match, so the two cannot disagree. -/
def PermitsOrdinaryWrite (s : AuthorityState) : Prop := s.PermitsIntent AccessIntent.write

instance (s : AuthorityState) : Decidable s.PermitsOrdinaryWrite :=
  inferInstanceAs (Decidable (s.PermitsIntent _))

/-- **Exclusive is the only state that permits an ordinary write.** A record of the
current sum rather than a guard: a fifth constructor would leave this true if
`PermitsIntent` sent it to `False`. What refuses to compile is `PermitsIntent`
itself, which enumerates the constructors. -/
theorem permitsOrdinaryWrite_iff_exclusive {s : AuthorityState} :
    s.PermitsOrdinaryWrite ↔ s = .exclusive := by
  cases s <;> simp [PermitsOrdinaryWrite, PermitsIntent, AccessIntent.write]

/-- **Atomic authority is not ordinary authority.** `docs/MEMORY_MODEL.md` §3:
"Atomics do not grant ordinary non-atomic access." The theorem that was deleted for
holding of an unreachable case, restored now that `authorityOf` reaches the state —
`Tests/Memory/AtomicAuthority.lean` builds it. -/
@[simp] theorem not_permitsOrdinaryWrite_atomicShared :
    ¬ AuthorityState.atomicShared.PermitsOrdinaryWrite := by
  simp [PermitsOrdinaryWrite, PermitsIntent, AccessIntent.write]

/-- Nor an ordinary read: §3 says atomics do not grant ordinary non-atomic
*access*, which is not only writes. -/
@[simp] theorem not_permitsIntent_read_atomicShared :
    ¬ AuthorityState.atomicShared.PermitsIntent AccessIntent.read := by
  simp [PermitsIntent, AccessIntent.read]

/-- But it permits the atomic access it exists for, so the two above are a
restriction and not a state that permits nothing. -/
@[simp] theorem permitsIntent_atomicReadWrite_atomicShared :
    AuthorityState.atomicShared.PermitsIntent AccessIntent.atomicReadWrite := by
  simp [PermitsIntent, AccessIntent.atomicReadWrite]

/-- A frozen fragment does not permit an ordinary write: that is what being frozen
while another context may write means. -/
@[simp] theorem not_permitsOrdinaryWrite_frozen :
    ¬ AuthorityState.frozen.PermitsOrdinaryWrite := fun h => h

/-- Shared immutable access does not permit a write. Its content is exactly that;
as the constructor's docstring says, nothing here proves the bytes do not change. -/
@[simp] theorem not_permitsOrdinaryWrite_sharedImmutable :
    ¬ AuthorityState.sharedImmutable.PermitsOrdinaryWrite := by
  simp [PermitsOrdinaryWrite, PermitsIntent, AccessIntent.write]

/-- But it does permit a read: that is the whole difference from `frozen`, and
without it the two states would be one. -/
@[simp] theorem permitsIntent_read_sharedImmutable :
    AuthorityState.sharedImmutable.PermitsIntent AccessIntent.read := by
  simp [PermitsIntent, AccessIntent.read]

/-- Dead or unallocated storage permits nothing at all — not even a read.
`AllocationRecord.live`'s own docstring says a dead allocation authorizes nothing
whatever provenance is presented, and this is that fact at the authority layer. -/
@[simp] theorem not_permitsIntent_unavailable (intent : AccessIntent) :
    ¬ AuthorityState.unavailable.PermitsIntent intent := fun h => h

/-- A frozen fragment permits nothing either, reads included: §7.3 makes a read
against another context's outstanding write a conflict. -/
@[simp] theorem not_permitsIntent_frozen (intent : AccessIntent) :
    ¬ AuthorityState.frozen.PermitsIntent intent := fun h => h

end AuthorityState

namespace MemoryState

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

**It is not authority.** It says the loan map is empty; it says nothing about
whether the storage is live, whether the provenance is current, or whether a grant
of another kind is outstanding. `exclusive_empty` and `not_live_empty` are that
gap exhibited, and `authorityOf` is what a caller asking about permission wants.
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
`state.HeldByAnother context provenance range` holds when some other context holds
authority over those bytes.

Any kind of grant, for the reason `grantsOver` gives. The name says "held" rather
than "lent" because it is not only loans.
-/
def HeldByAnother (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : Prop :=
  (state.grantsOver provenance range).any (fun entry => entry.2.holder ≠ context) = true

instance (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : Decidable (state.HeldByAnother context provenance range) :=
  inferInstanceAs (Decidable (_ = _))

/-- Nothing held means nothing outstanding for anybody. -/
theorem not_heldByAnother_of_not_anyGrantOver {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange}
    (h : ¬ state.AnyGrantOver provenance range) :
    ¬ state.HeldByAnother context provenance range := by
  unfold AnyGrantOver at h
  unfold HeldByAnother
  have he : state.grantsOver provenance range = [] := by
    by_cases hc : state.grantsOver provenance range = []
    · exact hc
    · exact absurd hc h
  rw [he]
  simp

/-- `state.WritableByAnother context provenance range` holds when some other
context's grant covers those bytes **and may modify them**.

The distinction `HeldByAnother` alone cannot make. `docs/MEMORY_MODEL.md` §3 lists
shared immutable access as a state of its own, and §7.3 makes a conflict require at
least one writer, so grants that may only read are the case that is not a conflict.
Whether the bytes stay unchanged in fact is §7.3's race question and M8's.

**The probe is `rights.write`, the capability, and not `rights.Permits .write`.**
Those differ once `Permission.atomicOnly` exists: an atomic-only grant does not
*permit* an ordinary write, and it certainly may modify the bytes. Writing this
with `Permits` made a context updating a word atomically stop freezing another
context's ordinary write — a fixture in `Tests/Memory/AtomicAuthority.lean` caught
it within minutes of `atomicOnly` landing. §7.3's "at least one writer" is about who
may change the bytes, not about what intent a permission admits. -/
def WritableByAnother (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : Prop :=
  (state.grantsOver provenance range).any
    (fun entry => entry.2.holder ≠ context && entry.2.rights.write) = true

instance (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : Decidable (state.WritableByAnother context provenance range) :=
  inferInstanceAs (Decidable (_ = _))

/-- `state.NonAtomicHeldByAnother context provenance range` holds when some other
context's grant over those bytes is **not** atomic-only.

What separates §3's atomic shared access from a freeze. If every other grant
conveys atomic access only, then an atomic accessor is participating in exactly the
protocol they are — which is what atomics are for. One ordinary participant among
them and the situation is an ordinary race, so the state is `frozen` and nothing
proceeds. This is deliberately decided on the grants that are actually there rather
than on `issue?` having refused the mixture.

Not because another door exists — `issue?` is the only one, and `MemoryState.mk` is
private so there is no fourth way in. Because a rule that holds *only* by an argument
about how the map was built is one alias declaration away from not holding: two grants
that do not conflict when issued become conflicting when a profile declares them the
same storage afterwards, and `docs/MEMORY_MODEL.md` §7.5 makes that a real transition.
This predicate reads the grants that are there. -/
def NonAtomicHeldByAnother (state : MemoryState) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) : Prop :=
  (state.grantsOver provenance range).any
    (fun entry => entry.2.holder ≠ context && !entry.2.rights.atomicOnly) = true

instance (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : Decidable (state.NonAtomicHeldByAnother context provenance range) :=
  inferInstanceAs (Decidable (_ = _))

/-- A grant that may write is a grant. The two predicates are not independent, and
over live storage `frozen` and `sharedImmutable` partition `HeldByAnother` because
of this — over dead or stale storage they do not, because `unavailable` takes
precedence over both. -/
theorem heldByAnother_of_writableByAnother {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange}
    (h : state.WritableByAnother context provenance range) :
    state.HeldByAnother context provenance range := by
  unfold WritableByAnother at h
  unfold HeldByAnother
  simp only [List.any_eq_true] at *
  obtain ⟨entry, hmem, hcond⟩ := h
  exact ⟨entry, hmem, ((Bool.and_eq_true _ _).mp hcond).1⟩

/-- And a non-atomic grant is a grant. -/
theorem heldByAnother_of_nonAtomicHeldByAnother {state : MemoryState}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    (h : state.NonAtomicHeldByAnother context provenance range) :
    state.HeldByAnother context provenance range := by
  unfold NonAtomicHeldByAnother at h
  unfold HeldByAnother
  simp only [List.any_eq_true] at *
  obtain ⟨entry, hmem, hcond⟩ := h
  exact ⟨entry, hmem, ((Bool.and_eq_true _ _).mp hcond).1⟩

/--
The authority `context` holds over bytes that may be lent.

Four cases, and every `AuthorityState` constructor is one of them — the type says
that is a standing requirement, and this is where it is met. Dead, absent or
stale-epoch storage is `unavailable`; nothing held by anyone else is `exclusive`;
another context able to write is `frozen`, which is §3's "frozen owner fragments
while loans exist"; and otherwise every outstanding grant is read-only, which is
§3's shared immutable access.

**It takes the context, and an earlier version did not.** Without it a context that
lent to itself was reported frozen while `Grass/Op/LoanAuthority.lean` let its
write through — the two halves of the model contradicting each other, which review
demonstrated. A loan you hold yourself does not freeze you out of your own bytes;
that is what holding it means.

**`exclusive` here is not §3's sentence.** §3 says exclusive authority is restored
only when the relevant map is empty, and `Exclusive` is that sentence. This is
weaker: a context holding the only grant over the bytes gets `exclusive` while the
map is non-empty. The two are deliberately different questions — one is about the
map, one is about what this context may do — and `Grass/Op/LoanAuthority.lean`
consults both, so neither substitutes for the other.

Like `outstandingLoans` it is a function of the state, so lending freezes,
returning thaws, freeing revokes, and an epoch bump revokes, with no field to keep
in step.
-/
def authorityOf (state : MemoryState) (context : ContextId) (provenance : Provenance)
    (range : ByteRange) : AuthorityState :=
  if ¬ state.Live provenance then .unavailable
  else if ¬ state.HeldByAnother context provenance range then .exclusive
  else if ¬ state.WritableByAnother context provenance range then .sharedImmutable
  else if state.NonAtomicHeldByAnother context provenance range then .frozen
  else .atomicShared

/-- **Unavailable exactly when the storage is dead, absent, or in another epoch.** -/
@[simp] theorem authorityOf_eq_unavailable_iff (state : MemoryState) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) :
    state.authorityOf context provenance range = .unavailable ↔ ¬ state.Live provenance := by
  unfold authorityOf
  by_cases hlive : state.Live provenance
  · rw [if_neg (by simpa using hlive)]
    by_cases hheld : state.HeldByAnother context provenance range
    · rw [if_neg (by simpa using hheld)]
      by_cases hwrite : state.WritableByAnother context provenance range
      · rw [if_neg (by simpa using hwrite)]
        by_cases hna : state.NonAtomicHeldByAnother context provenance range <;>
          simp [hna, hlive]
      · rw [if_pos (by simpa using hwrite)]
        simp [hlive]
    · rw [if_pos (by simpa using hheld)]
      simp [hlive]
  · rw [if_pos hlive]
    simp [hlive]

/-- **Exclusive exactly when the storage is live and nobody else holds a covering
grant.** The `Live` conjunct is not decoration: without it the empty state reported
exclusive ownership of an allocation that does not exist. -/
@[simp] theorem authorityOf_eq_exclusive_iff (state : MemoryState) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) :
    state.authorityOf context provenance range = .exclusive ↔
      state.Live provenance ∧ ¬ state.HeldByAnother context provenance range := by
  unfold authorityOf
  by_cases hlive : state.Live provenance
  · rw [if_neg (by simpa using hlive)]
    by_cases hheld : state.HeldByAnother context provenance range
    · rw [if_neg (by simpa using hheld)]
      by_cases hwrite : state.WritableByAnother context provenance range
      · rw [if_neg (by simpa using hwrite)]
        by_cases hna : state.NonAtomicHeldByAnother context provenance range <;>
          simp [hna, hheld]
      · rw [if_pos (by simpa using hwrite)]
        simp [hheld]
    · rw [if_pos (by simpa using hheld)]
      simp [hlive, hheld]
  · rw [if_pos hlive]
    simp [hlive]

/-- **Shared immutable exactly when live bytes are held by another context, and by
none that may modify them.** -/
@[simp] theorem authorityOf_eq_sharedImmutable_iff (state : MemoryState)
    (context : ContextId) (provenance : Provenance) (range : ByteRange) :
    state.authorityOf context provenance range = .sharedImmutable ↔
      state.Live provenance ∧ state.HeldByAnother context provenance range ∧
        ¬ state.WritableByAnother context provenance range := by
  unfold authorityOf
  by_cases hlive : state.Live provenance
  · rw [if_neg (by simpa using hlive)]
    by_cases hheld : state.HeldByAnother context provenance range
    · rw [if_neg (by simpa using hheld)]
      by_cases hwrite : state.WritableByAnother context provenance range
      · rw [if_neg (by simpa using hwrite)]
        by_cases hna : state.NonAtomicHeldByAnother context provenance range <;>
          simp [hna, hlive, hheld, hwrite]
      · rw [if_pos (by simpa using hwrite)]
        simp [hlive, hheld, hwrite]
    · rw [if_pos (by simpa using hheld)]
      simp [hheld]
  · rw [if_pos hlive]
    simp [hlive]

/-- **Frozen exactly when another context may modify the bytes and some other
holder is not atomic-only.** One ordinary participant among the grants makes it an
ordinary race, whatever the others declare. -/
@[simp] theorem authorityOf_eq_frozen_iff (state : MemoryState) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) :
    state.authorityOf context provenance range = .frozen ↔
      state.Live provenance ∧ state.WritableByAnother context provenance range ∧
        state.NonAtomicHeldByAnother context provenance range := by
  unfold authorityOf
  by_cases hlive : state.Live provenance
  · rw [if_neg (by simpa using hlive)]
    by_cases hheld : state.HeldByAnother context provenance range
    · rw [if_neg (by simpa using hheld)]
      by_cases hwrite : state.WritableByAnother context provenance range
      · rw [if_neg (by simpa using hwrite)]
        by_cases hna : state.NonAtomicHeldByAnother context provenance range <;>
          simp [hna, hlive, hwrite]
      · rw [if_pos (by simpa using hwrite)]
        simp [hlive, hwrite]
    · rw [if_pos (by simpa using hheld)]
      have hnw : ¬ state.WritableByAnother context provenance range :=
        fun hw => hheld (heldByAnother_of_writableByAnother hw)
      simp [hlive, hnw]
  · rw [if_pos hlive]
    simp [hlive]

/-- **Atomic shared exactly when another context may modify the bytes and every
other holder conveys atomic access only.**

§3's third canonical state, derived. It was a constructor nothing built for one
round, and the theorem about it was deleted for holding of an unreachable case;
`Permission.atomicOnly` is what makes it reachable. -/
@[simp] theorem authorityOf_eq_atomicShared_iff (state : MemoryState)
    (context : ContextId) (provenance : Provenance) (range : ByteRange) :
    state.authorityOf context provenance range = .atomicShared ↔
      state.Live provenance ∧ state.WritableByAnother context provenance range ∧
        ¬ state.NonAtomicHeldByAnother context provenance range := by
  unfold authorityOf
  by_cases hlive : state.Live provenance
  · rw [if_neg (by simpa using hlive)]
    by_cases hheld : state.HeldByAnother context provenance range
    · rw [if_neg (by simpa using hheld)]
      by_cases hwrite : state.WritableByAnother context provenance range
      · rw [if_neg (by simpa using hwrite)]
        by_cases hna : state.NonAtomicHeldByAnother context provenance range <;>
          simp [hna, hlive, hwrite]
      · rw [if_pos (by simpa using hwrite)]
        simp [hwrite]
    · rw [if_pos (by simpa using hheld)]
      have hnw : ¬ state.WritableByAnother context provenance range :=
        fun hw => hheld (heldByAnother_of_writableByAnother hw)
      simp [hnw]
  · rw [if_pos hlive]
    simp [hlive]

/-- **A context may not write bytes another context holds at all**, read grant
included. §7.3 makes a write against an outstanding read a conflict, and the read
grant is what says the reader is there. -/
theorem not_permitsOrdinaryWrite_of_heldByAnother {state : MemoryState}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    (h : state.HeldByAnother context provenance range) :
    ¬ (state.authorityOf context provenance range).PermitsOrdinaryWrite := by
  rw [AuthorityState.permitsOrdinaryWrite_iff_exclusive,
    authorityOf_eq_exclusive_iff state context provenance range]
  exact fun hc => hc.2 h

/--
**A context may not write bytes another context may write.**

The borrow discipline, as a theorem rather than a convention. While another
context's write grant covers the range this context's fragment is frozen, and
`AuthorityState.PermitsOrdinaryWrite` is false of `frozen`.
-/
theorem not_permitsOrdinaryWrite_of_writableByAnother {state : MemoryState}
    {context : ContextId} {provenance : Provenance} {range : ByteRange}
    (h : state.WritableByAnother context provenance range) :
    ¬ (state.authorityOf context provenance range).PermitsOrdinaryWrite :=
  not_permitsOrdinaryWrite_of_heldByAnother (heldByAnother_of_writableByAnother h)

/-- **Dead, absent or stale-epoch storage may not be written**, however few loans
are outstanding over it. `Exclusive` says the loan map is empty, and an empty loan
map over a freed allocation is not permission to write it. -/
theorem not_permitsOrdinaryWrite_of_not_live {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} (h : ¬ state.Live provenance) :
    ¬ (state.authorityOf context provenance range).PermitsOrdinaryWrite := by
  rw [(authorityOf_eq_unavailable_iff state context provenance range).mpr h]
  exact fun hc => hc

/-- Live storage nobody else holds may be written by this context.

The hypothesis is `¬ HeldByAnother` and **not** `Exclusive`: an empty loan map is
not an empty grant map, and it was `Exclusive` here that let a `.frame` grant's
bytes be reported writable. -/
theorem permitsOrdinaryWrite_of_unheld {state : MemoryState} {context : ContextId}
    {provenance : Provenance} {range : ByteRange} (hlive : state.Live provenance)
    (h : ¬ state.HeldByAnother context provenance range) :
    (state.authorityOf context provenance range).PermitsOrdinaryWrite := by
  rw [AuthorityState.permitsOrdinaryWrite_iff_exclusive,
    authorityOf_eq_exclusive_iff state context provenance range]
  exact ⟨hlive, h⟩

/--
Return the loan with **that exact identity**, if this context may.

`docs/MEMORY_MODEL.md` §3: "Returning one loan consumes that exact identity."
`GrantId` is a `Uid`, which a supply never reissues, so the identity a return names
is the one that was lent — a return cannot consume a different loan that happens to
describe the same bytes, rights, and holder. That is why the map is keyed by identity
and not by shape.

`MemoryState.returnGrant?` is the mechanism and carries the who-may-return rule,
because the field it erases is sealed in that module. This is the name §3's laws are
stated under.
-/
def returnLoan? (state : MemoryState) (context : ContextId) (id : GrantId) :
    Option MemoryState := state.returnGrant? context id

/-- **A return consumes the identity it names.** -/
theorem lookup_returnLoan?_self {state returned : MemoryState} {context : ContextId}
    {id : GrantId} (h : state.returnLoan? context id = some returned) :
    returned.grantAt? id = Option.none :=
  MemoryState.grantAt?_returnGrant?_self h

/-- Returning one loan leaves every other identity alone. Two loans over the same
bytes are two loans, and returning one does not return the other. -/
theorem lookup_returnLoan?_ne {state returned : MemoryState} {context : ContextId}
    {id other : GrantId} (h : state.returnLoan? context id = some returned)
    (hne : other ≠ id) : returned.grantAt? other = state.grantAt? other :=
  MemoryState.grantAt?_returnGrant?_ne h hne

/-- **A context that neither holds nor lent it may not return it.** -/
theorem returnLoan?_eq_none_of_stranger {state : MemoryState} {context : ContextId}
    {id : GrantId} {grant : AuthorityGrant} (hlook : state.grantAt? id = some grant)
    (hholder : grant.holder ≠ context) (hlender : grant.lender ≠ context) :
    state.returnLoan? context id = Option.none :=
  MemoryState.returnGrant?_eq_none_of_stranger hlook hholder hlender

/-- **And the lender may return what it lent.** §6's conforming return, performed by
the party §6 says performs it. -/
theorem returnLoan?_isSome_of_lender {state : MemoryState} {context : ContextId}
    {id : GrantId} {grant : AuthorityGrant} (hlook : state.grantAt? id = some grant)
    (h : grant.lender = context) : (state.returnLoan? context id).isSome :=
  MemoryState.returnGrant?_isSome_of_lender hlook h

/-- And a return naming no live loan is refused rather than treated as a no-op. -/
theorem returnLoan?_eq_none_of_absent {state : MemoryState} {context : ContextId}
    {id : GrantId} (h : state.grantAt? id = Option.none) :
    state.returnLoan? context id = Option.none :=
  MemoryState.returnGrant?_eq_none_of_absent h

/-- A successful issue records the grant under the identity it names. -/
theorem lookup_issue?_self {state issued : MemoryState} {id : GrantId}
    {grant : AuthorityGrant} (h : state.issue? id grant = some issued) :
    issued.grantAt? id = some grant :=
  MemoryState.grantAt?_issue?_self h

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
  simp [Live, empty, FiniteMap.empty, FiniteMap.lookup]

/-- **There is no second door**, and it took four closures to be able to say so.

`MemoryState.grant` was one — `grants.insert`, no checks — kept on the argument that
the access-time rule reads whatever map it finds. `FiniteMap.insert` erases, so
installing a grant under an identity another context held deleted that grant, and the
map the access-time rule then found no longer contained it.

Deleting it was not enough: `MemoryState.grants` was a public field, so
`{ state with grants := state.grants.insert id g }` *is* the deleted function, and
two of this project's own fixtures used it. Sealing the field was not enough either,
because that privatises the projection and leaves `MemoryState.mk`. And sealing `mk`
was not enough, because a low-level `issueGrant?` sat public beside it running the
identity check and none of the others — review installed a four-kilobyte grant over a
sixty-four-byte allocation through it.

`MemoryState.issue?` runs every check and is the only thing that writes the map; this
is the statement that its identity rule is the map's. -/
theorem issued_identity_is_fresh {state issued : MemoryState} {id : GrantId}
    {grant : AuthorityGrant} (h : state.issue? id grant = some issued) :
    state.grantAt? id = Option.none :=
  MemoryState.grantAt?_eq_none_of_issue? h

end MemoryState

end Grass.Memory
