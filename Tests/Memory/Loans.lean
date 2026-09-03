import Grass.Memory.Loan

/-!
# Loans, exclusivity, and identity

`docs/MEMORY_MODEL.md` §3 states three things this checks: returning one loan
consumes *that exact identity*, exclusive authority is restored only when the
relevant map is empty, and counts are derived caches only.

The third is the one a fixture can most easily fake, so it is checked the way that
would catch a fake: `outstandingLoans` is computed from the map, and the theorems
below compare it against `Exclusive` at every step rather than trusting it.
-/

namespace Tests.Memory.Loans

open Grass.Core Grass.Memory

private def allocs : FreshSupply AllocTag := .initial
private def epochs : FreshSupply EpochTag := .initial
private def contexts : FreshSupply ContextTag := .initial
private def grants : FreshSupply GrantTag := .initial

/-- The lent storage. -/
def buffer : AllocId := allocs.fresh.1

/-- Its owner. -/
def owner : ContextId := contexts.fresh.1

/-- A second context, which borrows. -/
def borrower : ContextId := contexts.fresh.2.fresh.1

/-- A third context, which neither holds nor lent anything. -/
def stranger : ContextId := contexts.fresh.2.fresh.2.fresh.1

/-- Two loan identities. Distinct because a supply never reissues. -/
def firstLoan : GrantId := grants.fresh.1

/-- The second. -/
def secondLoan : GrantId := grants.fresh.2.fresh.1

/-- A third, so a fixture can add a loan to a state that already holds two. -/
def thirdLoan : GrantId := grants.fresh.2.fresh.2.fresh.1

private def epoch : EpochId := epochs.fresh.1

/-- A second epoch, for the storage that replaces the buffer. -/
def laterEpoch : EpochId := epochs.fresh.2.fresh.1

/-- Provenance of the whole buffer. -/
def bufferProv : Provenance :=
  { space := .cpuVirtual, root := buffer, epoch := epoch, source := .virtualAlloc
    rootExtent := ⟨0, 64⟩, path := [] }

/-- Provenance of the same buffer in the epoch that replaced it. -/
def currentProv : Provenance := { bufferProv with epoch := laterEpoch }

/-- A live call frame's authority over the same bytes, held by the borrower. Not a
loan, and §7.3 does not care. -/
def frameGrant : AuthorityGrant :=
  { kind := .frame, holder := borrower, lender := owner, provenance := bufferProv
    range := ⟨0, 8⟩, rights := .readWrite }

/-- A state owning the buffer and lending nothing. -/
def unlent : MemoryState :=
  (MemoryState.empty.allocate? buffer
    { extent := ⟨0, 64⟩, epoch := epoch, space := .cpuVirtual
      permission := .readWrite, live := true, bytes := .empty
      base := some 0x1000 }).getD .empty

/-- The allocation happened, so `getD` did not fall back to the empty state. -/
theorem the_allocation_succeeds :
    (MemoryState.empty.allocate? buffer
      { extent := ⟨0, 64⟩, epoch := epoch, space := .cpuVirtual
        permission := .readWrite, live := true, bytes := .empty
        base := some 0x1000 }).isSome := by decide

/-- A write loan of the first eight bytes to the borrower. -/
def loanOfHead : AuthorityGrant :=
  { kind := .loan, holder := borrower, lender := owner, provenance := bufferProv
    range := ⟨0, 8⟩, rights := .readWrite }

/-- A *read* loan of the same bytes. Two of these may coexist, which is
`AuthorityState.sharedImmutable` being a real state rather than a name, and is what
lets the identity theorems below hold two loans at once now that overlapping write
loans are refused at issue. -/
def readLoanOfHead : AuthorityGrant :=
  { loanOfHead with rights := .readOnly }

/-- A loan of a disjoint eight bytes. -/
def loanOfTail : AuthorityGrant :=
  { loanOfHead with range := ⟨8, 8⟩ }

/-- The same head, lent to a *different* holder. §7.3's conflict is between distinct
contexts, so this is the grant that conflicts with `loanOfHead` and
`loanOfHead` itself is not. -/
def loanOfHeadToOwner : AuthorityGrant :=
  { loanOfHead with holder := owner }

/-- A loan over no bytes at all, which is a grant of nothing and must freeze
nothing. -/
def emptyLoan : AuthorityGrant :=
  { loanOfHead with range := ByteRange.empty 4 }

/-- Lending the head. `issue?` refuses a reissued identity or a conflicting loan, so
a fixture has to say which state it means; `the_lends_succeed` checks these are the
lends that happened rather than silent fallbacks. -/
def lentHead : MemoryState := (unlent.issue? firstLoan loanOfHead).getD unlent

/-- Lending the disjoint tail. -/
def lentTail : MemoryState := (unlent.issue? secondLoan loanOfTail).getD unlent

/-- Two *read* loans over the same bytes, under distinct identities. -/
def lentTwice : MemoryState :=
  ((unlent.issue? firstLoan readLoanOfHead).getD unlent).issue? secondLoan readLoanOfHead
    |>.getD unlent

/-- Each lend above actually succeeded, so `getD` never fell back and the theorems
below are about lent states rather than about `unlent`. -/
theorem the_lends_succeed :
    (unlent.issue? firstLoan loanOfHead).isSome ∧
    (unlent.issue? secondLoan loanOfTail).isSome ∧
    (((unlent.issue? firstLoan readLoanOfHead).getD unlent).issue?
      secondLoan readLoanOfHead).isSome := by
  exact ⟨by decide, by decide, by decide⟩

/-! ## Exclusivity is the empty map, not a count -/

/-- Owning and lending nothing is exclusive. -/
theorem unlent_is_exclusive : unlent.Exclusive bufferProv ⟨0, 8⟩ := by decide

/-- Lending ends it, and the derived count agrees. -/
theorem lending_ends_exclusivity :
    ¬ (lentHead).Exclusive bufferProv ⟨0, 8⟩ ∧
    (lentHead).outstandingLoans bufferProv ⟨0, 8⟩ = 1 := by
  exact ⟨by decide, by decide⟩

/-- A loan of disjoint bytes does not end exclusivity over the head. §3's "relevant
map" is the loans over *those* bytes, not every loan in the state. -/
theorem a_disjoint_loan_leaves_the_head_exclusive :
    (lentTail).Exclusive bufferProv ⟨0, 8⟩ ∧
    ¬ (lentTail).Exclusive bufferProv ⟨8, 8⟩ := by
  exact ⟨by decide, by decide⟩

/-! ## A return consumes the identity it names -/

/-- The state after the borrower returns its loan. -/
def returned : MemoryState := (lentHead.returnLoan? borrower firstLoan).getD lentHead

/-- Returning the loan restores exclusivity, and the return actually happened
rather than `getD` falling back. -/
theorem returning_restores_exclusivity :
    (lentHead.returnLoan? borrower firstLoan).isSome ∧
    returned.Exclusive bufferProv ⟨0, 8⟩ := by
  exact ⟨by decide, by decide⟩

/-- **A context that neither holds nor lent it may not return it.** §3 says which
loan a return consumes and not who may return it, and the unchecked version let any
context return any loan and then write the thawed bytes — an authority check
defeated by calling the function that removes it. -/
theorem a_stranger_may_not_return_the_loan :
    lentHead.returnLoan? stranger firstLoan = Option.none := by decide

/-- **But the lender may.** `docs/MEMORY_MODEL.md` §6's ABI call profile "consumes
the same loan identities to reconstruct local authority on a conforming return", and
the party consuming is the caller — the lender — not the callee. A holder-only check
made §6's return impossible, and for a loan to an external API agent, which never
executes a Grass step, made it impossible for anyone. -/
theorem the_lender_may_return_the_loan :
    (lentHead.returnLoan? owner firstLoan).isSome ∧
    loanOfHead.lender = owner ∧ loanOfHead.holder = borrower := by
  exact ⟨by decide, by decide, by decide⟩

/-- And a return naming no live loan is refused rather than treated as a no-op. -/
theorem returning_an_unheld_identity_is_refused :
    unlent.returnLoan? borrower firstLoan = Option.none := by decide

/--
**Returning one loan does not return another over the same bytes.**

Two loans of the identical range, rights and holder, differing only in identity.
Returning the first leaves the second outstanding, so exclusivity is *not*
restored. A map keyed by shape rather than by identity would get this wrong, which
is why §3 says a return consumes that exact identity.
-/
theorem returning_one_of_two_leaves_the_other :
    ¬ ((lentTwice.returnLoan? borrower firstLoan).getD lentTwice).Exclusive
        bufferProv ⟨0, 8⟩ ∧
    ((lentTwice.returnLoan? borrower firstLoan).getD lentTwice).outstandingLoans
        bufferProv ⟨0, 8⟩ = 1 ∧
    (lentTwice.returnLoan? borrower firstLoan).isSome := by
  exact ⟨by decide, by decide, by decide⟩

/-- Returning both does restore it, so the theorem above is about identity rather
than about returns never working. -/
theorem returning_both_restores_exclusivity :
    (((lentTwice.returnLoan? borrower firstLoan).getD lentTwice).returnLoan?
      borrower secondLoan).getD lentTwice |>.Exclusive bufferProv ⟨0, 8⟩ := by decide

/-- The two loans really are identical apart from identity.

An earlier version asserted `loanOfHead = loanOfHead`, one term compared to itself,
which could never have failed. Its replacement compared the two entries against
*each other*, which is better but still weak: both lends are handed the same grant,
so any uniform mangling `issue?` applied would give `f g = f g` and pass — storing
nothing at all included, in which case both sides are `none`. Review pointed that
out too. This names the grant, so it fails if `issue?` stores anything but what it
was handed. -/
theorem the_two_loans_differ_only_in_identity :
    lentTwice.grantAt? firstLoan = some readLoanOfHead ∧
    lentTwice.grantAt? secondLoan = some readLoanOfHead ∧
    firstLoan ≠ secondLoan := by
  exact ⟨by decide, by decide, by decide⟩

/-! ## A loan cannot be issued twice, nor conflict with a live one

Both refusals were absent and both were silent. `lend` was `grants.insert`, and
`FiniteMap.insert` erases any existing binding, so a reissued identity returned a
loan nobody returned. And nothing stopped two overlapping write loans coexisting,
though §7.3 says unique loans prevent conflicting authority from being *issued*. -/

/-- **A reissued identity is refused**, rather than silently returning the loan
that identity already names. -/
theorem a_reissued_identity_is_refused :
    lentHead.issue? firstLoan loanOfTail = Option.none := by decide

/-- A *different* identity for the same tail is accepted, so the refusal is about
reissue and not about the tail. -/
theorem a_fresh_identity_for_the_tail_is_accepted :
    (lentHead.issue? secondLoan loanOfTail).isSome := by decide

/-- **A conflicting loan is refused at issue.** Two write loans over the same bytes
held by *different* contexts are conflicting authority, and §7.3 says unique loans
prevent it being issued. -/
theorem a_conflicting_write_loan_is_refused :
    lentHead.issue? secondLoan loanOfHeadToOwner = Option.none := by decide

/-- **A second loan to the same holder is not a conflict.** §7.3's rule is about
distinct concurrent contexts, and without the holder clause a context could not
hold two grants over its own bytes — which is the idiom
`Grass/Op/LoanAuthority.lean` endorses for "the owner may still read", and which
was therefore mutually exclusive with any other grant on those bytes. -/
theorem a_second_loan_to_the_same_holder_is_accepted :
    (lentHead.issue? secondLoan loanOfHead).isSome := by decide

/-- A provenance claiming a root extent the allocation does not have. -/
def fatProv : Provenance := { bufferProv with rootExtent := ⟨0, 4096⟩ }

/-- **A grant whose provenance misdescribes its allocation is refused.**

`issue?` bounds a grant by `grant.provenance.extent`, which the provenance itself
supplies — so the clause was self-certifying, and review issued a write grant over
four kilobytes of a sixty-four-byte allocation and watched it authorize accesses and
freeze a context that legitimately owned the storage. `RootExtentAgrees` compares
the claim to the allocation table. -/
theorem a_grant_over_a_lying_provenance_is_refused :
    unlent.issue? firstLoan { loanOfHead with provenance := fatProv, range := ⟨0, 4096⟩ } =
      Option.none ∧
    ¬ unlent.RootExtentAgrees fatProv ∧
    unlent.RootExtentAgrees bufferProv := by
  exact ⟨by decide, by decide, by decide⟩

/-- **A grant whose provenance path is not nested is refused.** Every access already
had to satisfy `AccessDescriptor.WellFormedIn.provenanceNested`, and no grant did, so
a single unnested step was a second way to claim any extent at all. -/
theorem a_grant_over_an_unnested_path_is_refused :
    unlent.issue? firstLoan
        { loanOfHead with
          provenance := { bufferProv with
            path := [{ kind := .field, label := ⟨"lie"⟩, extent := ⟨0, 4096⟩ }] }
          range := ⟨0, 4096⟩ } = Option.none := by decide

/-- Two *read* loans over the same bytes are not conflicting, so they are accepted.
Without this the theorem above would be consistent with refusing every overlapping
loan, and `sharedImmutable` would be a name for nothing. -/
theorem two_read_loans_over_one_range_are_accepted :
    (((unlent.issue? firstLoan readLoanOfHead).getD unlent).issue?
      secondLoan readLoanOfHead).isSome := by decide

/-! ## Lending freezes the lender's fragment, not the holder's

§3 lists "frozen owner fragments while loans exist" among the canonical states.
`authorityOf` is what puts a context into one, and it takes the context: a loan you
hold yourself does not freeze you out of your own bytes. An earlier version did not
take it, and reported a context that had lent to itself as frozen while the
transition let its write through — the two halves of the model contradicting each
other. -/

/-- With nothing lent, the owner may write. -/
theorem an_unlent_owner_may_write :
    unlent.authorityOf owner bufferProv ⟨0, 8⟩ = AuthorityState.exclusive ∧
    (unlent.authorityOf owner bufferProv ⟨0, 8⟩).PermitsOrdinaryWrite := by
  exact ⟨by decide, by decide⟩

/-- **Lending to another context freezes the lender, and a frozen context may not
write.** -/
theorem a_lending_owner_may_not_write :
    lentHead.authorityOf owner bufferProv ⟨0, 8⟩ = AuthorityState.frozen ∧
    ¬ (lentHead.authorityOf owner bufferProv ⟨0, 8⟩).PermitsOrdinaryWrite := by
  exact ⟨by decide, by decide⟩

/-- **The borrower is not frozen by its own loan.** This is the case that made the
model contradict itself: `Exclusive` is false here, because a loan exists, and the
holder may still write — which is what holding a write loan means. -/
theorem the_borrower_is_not_frozen_by_its_own_loan :
    ¬ lentHead.Exclusive bufferProv ⟨0, 8⟩ ∧
    lentHead.authorityOf borrower bufferProv ⟨0, 8⟩ = AuthorityState.exclusive := by
  exact ⟨by decide, by decide⟩

/-- Returning thaws the lender, so the freeze is not a one-way door. -/
theorem returning_thaws_the_owner :
    returned.authorityOf owner bufferProv ⟨0, 8⟩ = AuthorityState.exclusive := by decide

/-- The lender keeps bytes it did not lend. A loan of the head does not freeze the
tail, which is what makes "frozen *fragments*" fragments. -/
theorem lending_the_head_leaves_the_tail_writable :
    lentHead.authorityOf owner bufferProv ⟨8, 8⟩ = AuthorityState.exclusive := by decide

/-! ## Read loans are shared immutable access, not a freeze

§3 lists shared immutable access as a state of its own and §7.3 makes a conflict
require a writer. A read loan leaves the bytes immutable for as long as it is held,
which is not the same situation as a frozen fragment — and until `authorityOf`
distinguished them, `AuthorityState.sharedImmutable` was a constructor nothing
built and every theorem about it was vacuous. -/

/-- **Read loans put the lender into shared immutable access, not frozen.** -/
theorem read_loans_are_shared_immutable :
    lentTwice.authorityOf owner bufferProv ⟨0, 8⟩ = AuthorityState.sharedImmutable := by
  decide

/-- And shared immutable access does not permit the lender to write, so the
distinction from `frozen` is about which state it is, not about permission. §7.3
makes a write against an outstanding read a conflict. -/
theorem a_shared_immutable_lender_may_not_write :
    ¬ (lentTwice.authorityOf owner bufferProv ⟨0, 8⟩).PermitsOrdinaryWrite := by decide

/-- A write loan freezes, so the state above is about the rights on the loan rather
than about a loan existing.

The two ranges are disjoint and deliberately so. An earlier caption said this was
"one write loan among the read loans", which it is not — the read loans are over
`[0, 8)` and this query is over `[8, 16)`, so they play no part. The
distinguishing case, a write loan overlapping the read loans, cannot be built:
`issue?` refuses it, which is `a_conflicting_write_loan_is_refused`. -/
theorem a_write_loan_freezes :
    ((lentTwice.issue? thirdLoan loanOfTail).getD lentTwice).authorityOf
      owner bufferProv ⟨8, 8⟩ = AuthorityState.frozen ∧
    (lentTwice.issue? thirdLoan loanOfTail).isSome := by
  exact ⟨by decide, by decide⟩

/-! ## Dead storage is not exclusively owned, it is unavailable

`Exclusive` says the loan map is empty over those bytes. Reading that as permission
is the mistake `authorityOf` made: it reported the *empty state* as exclusively
owned by whoever asked, and `AuthorityState.unavailable` was built by nothing.
`AllocationRecord.live`'s own docstring says a dead allocation authorizes nothing
whatever provenance is presented. -/

/-- The same buffer, freed. -/
def freed : MemoryState :=
  (MemoryState.empty.allocate? buffer
    { extent := ⟨0, 64⟩, epoch := epoch, space := .cpuVirtual
      permission := .readWrite, live := false, bytes := .empty
      base := some 0x1000 }).getD .empty

/-- **A freed allocation is exclusive and unwritable.** Both halves matter: the
loan map really is empty, and that really is not authority. -/
theorem a_freed_allocation_is_exclusive_and_unavailable :
    freed.Exclusive bufferProv ⟨0, 8⟩ ∧
    freed.authorityOf owner bufferProv ⟨0, 8⟩ = AuthorityState.unavailable ∧
    ¬ (freed.authorityOf owner bufferProv ⟨0, 8⟩).PermitsOrdinaryWrite := by
  exact ⟨by decide, by decide, by decide⟩

/-- **An allocation that never existed is unavailable too**, which is the case that
made this visible: the empty state has an empty loan map. -/
theorem an_unallocated_root_is_unavailable :
    MemoryState.empty.Exclusive bufferProv ⟨0, 8⟩ ∧
    MemoryState.empty.authorityOf owner bufferProv ⟨0, 8⟩ = AuthorityState.unavailable := by
  exact ⟨by decide, by decide⟩

/-! ## A position inside a loan is inside it

`ByteRange.Disjoint` is blind to where an empty range sits, because an empty range
covers no offset — so `⟨0,8⟩.Disjoint (empty 4)` is true. `loansOver` filtered on
that, and answering "what authority do I hold over offset 4" while `[0, 8)` was
lent for writing returned exclusive, with an ordinary write permitted.
`docs/MEMORY_MODEL.md` §5.1 makes positions meaningful, so a query about one has to
be answered about one. `ByteRange.Meets` is the predicate that does. -/

/-- **A position inside a lent range is frozen.** Offset 4, inside `[0, 8)`. -/
theorem a_position_inside_a_loan_is_frozen :
    lentHead.authorityOf owner bufferProv (ByteRange.empty 4) = AuthorityState.frozen := by
  decide

/-- And the pair really is `Disjoint`, which is why the fixture above fails under
the old filter: `loansOver` would have excluded the loan and reported the owner
`exclusive`. This pins the fact that made the defect. An earlier caption said the
fixture "would have passed under it", which is backwards. -/
theorem the_position_is_disjoint_from_the_loan :
    loanOfHead.range.Disjoint (ByteRange.empty 4) := by decide

/-- **One past the end is not frozen.** §5.1 keeps that position meaningful and
non-dereferenceable; it is not a byte of the loan, and freezing it would freeze the
byte after every loan in the state. -/
theorem one_past_the_end_of_a_loan_is_not_frozen :
    lentHead.authorityOf owner bufferProv (ByteRange.empty 8) = AuthorityState.exclusive := by
  decide

/-- **A grant over no bytes is refused at issue.**

It was issuable, and it was decoration with a refusal attached: `LoanConflicts`
tries `Meets` in both directions so an empty grant *conflicted* with a live one and
could not be issued alongside it, while installed on its own it froze nobody,
because an empty extent meets no position. `AccessDescriptor.WellFormedIn` refuses
an empty access for the same reason and `issue?` now refuses an empty grant. -/
theorem a_grant_of_no_bytes_is_refused :
    unlent.issue? firstLoan emptyLoan = Option.none ∧
    emptyLoan.range.IsEmpty := by
  exact ⟨by decide, by decide⟩

/-- And the same grant with a non-empty range is accepted, so the refusal is about
the empty range rather than about the grant. -/
theorem the_same_grant_with_bytes_is_accepted :
    (unlent.issue? firstLoan { emptyLoan with range := ⟨4, 4⟩ }).isSome := by decide

/-! ## Only exclusive authority permits an ordinary write

There is no atomic case here and no `AuthorityState.atomicShared`. §3 lists atomic
shared access among the canonical states, and `AuthorityGrant` carries no ordering
— `kind`, `holder`, `provenance`, `range`, `rights` — so `authorityOf`, which reads
only the grant map, had nothing to derive that state from and the theorem about it
held of an unreachable case. A vacuous theorem reads as coverage, so both were
deleted and `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records the law as owed.

Ordering itself does exist at this layer — `Grass/Memory/Ordering.lean`,
`AccessDescriptor.ordering`, `AccessIntent.isAtomic` — so it is not true that §3's
atomic rule has nothing to constrain, and §4.4.1 says where it could bite. What is
missing is any link from ordering to what a grant permits. -/

/-- Every state, and what each permits. A record of the current sum, not a guard: a
fifth constructor would leave this true. What refuses to compile is
`AuthorityState.PermitsIntent`, which enumerates the constructors with no
wildcard. -/
theorem only_exclusive_permits_an_ordinary_write :
    AuthorityState.exclusive.PermitsOrdinaryWrite ∧
    ¬ AuthorityState.sharedImmutable.PermitsOrdinaryWrite ∧
    ¬ AuthorityState.frozen.PermitsOrdinaryWrite ∧
    ¬ AuthorityState.unavailable.PermitsOrdinaryWrite := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- And what each permits a *read*: `sharedImmutable` is the only state that
distinguishes the two, which is the whole reason it is a state and not a name. -/
theorem only_shared_immutable_distinguishes_reads :
    AuthorityState.exclusive.PermitsIntent AccessIntent.read ∧
    AuthorityState.sharedImmutable.PermitsIntent AccessIntent.read ∧
    ¬ AuthorityState.frozen.PermitsIntent AccessIntent.read ∧
    ¬ AuthorityState.unavailable.PermitsIntent AccessIntent.read := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-! ## Authority ends with the epoch, and is not only about loans -/

/-- The buffer, freed: same epoch, no longer live. -/
def freedRecord : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch, space := .cpuVirtual
    permission := .readWrite, live := false, bytes := .empty, base := some 0x1000 }

/-- A second allocation over the same storage, declared an alias of the buffer. -/
def view : AllocId := allocs.fresh.2.fresh.1

/-- Provenance of the view. -/
def viewProv : Provenance := { bufferProv with root := view }

/-- A state holding both, aliased. -/
def aliasedPair : MemoryState :=
  ((unlent.allocate? view
      { extent := ⟨0, 64⟩, epoch := epoch, space := .cpuVirtual
        permission := .readWrite, live := true, bytes := .empty
        base := some 0x1000 }).getD unlent).alias buffer view

/-- A loan over the *view*, not over the buffer. -/
def viewLoan : AuthorityGrant := { loanOfHead with provenance := viewProv }

/-- The buffer, freed and re-allocated at the same identity in a new epoch. -/
def reusedRecord : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := laterEpoch, space := .cpuVirtual
    permission := .readWrite, live := true, bytes := .empty, base := some 0x1000 }

/-- A state holding it. `bufferProv` names the *old* epoch. -/
def reused : MemoryState := (MemoryState.empty.allocate? buffer reusedRecord).getD .empty

/-- The buffer lent while live, then reallocated under it. -/
def lentThenReused : MemoryState :=
  (lentHead.allocate? buffer reusedRecord).getD lentHead

/-- **A stale pointer into re-used storage holds no authority.**
`docs/MEMORY_MODEL.md` §2: address reuse never revives old pointers. Before `Live`
compared epochs this reported `exclusive`, with an ordinary write permitted. -/
theorem a_stale_provenance_is_unavailable :
    ¬ reused.Live bufferProv ∧
    reused.authorityOf owner bufferProv ⟨0, 8⟩ = AuthorityState.unavailable := by
  exact ⟨by decide, by decide⟩

/--
**Reallocating under an outstanding loan is refused.**

`docs/MEMORY_MODEL.md` §5.1: "reallocation requires the return of all live use
loans". Nothing checked it, and the state that skipping it produced was a mess three
rounds of review kept circling: a grant naming a defunct epoch still freezes the
storage that replaced it — `grantsOver` has no epoch clause, deliberately, because
the clause it had was worse — while `MemoryState.AuthorizedAt` refuses to let it
authorize anything and `LoanConflicts` refuses a replacement grant. Only the stale
grant's holder or lender could clear it.

Refusing the reallocation removes the state rather than accommodating it, which is
`docs/FOUNDATION.md` law 8's direction and §5.1's own ordering.
-/
theorem reallocating_under_a_loan_is_refused :
    lentHead.allocate? buffer reusedRecord = Option.none ∧
    ¬ lentHead.Exclusive bufferProv ⟨0, 8⟩ := by
  exact ⟨by decide, by decide⟩

/-- And the same reallocation is accepted once the loan is returned, so the refusal
tracks the loan rather than being a ban on reallocation. -/
theorem reallocating_after_the_return_is_accepted :
    (returned.allocate? buffer reusedRecord).isSome := by decide

/-- **Freeing under a live loan is refused too.** An earlier version refused only an
epoch change, and its own docstring listed "a liveness change" among the things
always allowed — so `live := true → false` with a loan outstanding was admitted, and
the consequence was silent: `authorityOf` reports `unavailable` for a dead
allocation, so the loan evaporated with no return and no violation, and a record with
the same epoch and `live := true` resurrected it. §5 asks for the return of all live
use loans at teardown in the same breath as §5.1 asks it of reuse. -/
theorem freeing_under_a_loan_is_refused :
    lentHead.allocate? buffer freedRecord = Option.none ∧
    (returned.allocate? buffer freedRecord).isSome := by
  exact ⟨by decide, by decide⟩

/-- **And a grant held over an aliased view blocks it.** The scan matched
`provenance.root = id`, so a loan over a mapped view did not block a reallocation of
the file it maps, though `SharesBytes` says they are the same bytes — the asymmetry
this layer has now fixed in three places. -/
theorem an_aliased_grant_blocks_the_reallocation :
    ((aliasedPair.issue? firstLoan viewLoan).getD aliasedPair).allocate? buffer
      reusedRecord = Option.none ∧
    (aliasedPair.issue? firstLoan viewLoan).isSome := by
  exact ⟨by decide, by decide⟩

/-- **A grant of another kind freezes too.** §7.3's conflict is about authority,
not about one kind of it, and `grantsOver` filtered to `GrantKind.loan` — so a
`.frame` grant, or one of a kind a profile invented, carried write authority that
froze nobody. -/
theorem a_frame_grant_freezes :
    ((unlent.issue? firstLoan frameGrant).getD unlent).authorityOf owner bufferProv ⟨0, 8⟩ =
      AuthorityState.frozen := by decide

/-- But it is still not a *loan*, so §3's exclusivity — which is about the loan map
— is untouched. The two questions are deliberately different, and reading
`Exclusive` as permission is what let the frame grant through. -/
theorem a_frame_grant_is_not_a_loan :
    ((unlent.issue? firstLoan frameGrant).getD unlent).Exclusive bufferProv ⟨0, 8⟩ ∧
    (unlent.issue? firstLoan frameGrant).isSome := by
  exact ⟨by decide, by decide⟩

/-! ## Splitting and joining a loan

`docs/MEMORY_MODEL.md` §3's split and join, exercised on a concrete map. The two
theorems that carry the design — authority is preserved and none is created — are
proved in `Grass/Memory/State.lean` over an arbitrary state; what a fixture adds is
that the doors accept the cases they should and refuse the ones they should, and that
the state after a split is the state a reader would expect rather than a fallback.
-/

/-- A fourth identity, for the low part of a split. -/
def lowLoan : GrantId := grants.fresh.2.fresh.2.fresh.2.fresh.1

/-- A fifth, for the high part. -/
def highLoan : GrantId := grants.fresh.2.fresh.2.fresh.2.fresh.2.fresh.1

/-- A sixth, for the grant a join produces. -/
def joinedLoan : GrantId := grants.fresh.2.fresh.2.fresh.2.fresh.2.fresh.2.fresh.1

/-- The head loan, split at offset four. -/
def splitHead : MemoryState :=
  (lentHead.splitGrant? firstLoan lowLoan highLoan 4).getD lentHead

/-- **The split happened**, so the theorems below are not about `lentHead`. The
identities are the ones asked for, the source is gone, and the parts are the halves.
-/
theorem the_split_succeeds :
    (lentHead.splitGrant? firstLoan lowLoan highLoan 4).isSome ∧
    splitHead.grantAt? firstLoan = Option.none ∧
    splitHead.grantAt? lowLoan = some (loanOfHead.lowPart 4) ∧
    splitHead.grantAt? highLoan = some (loanOfHead.highPart 4) ∧
    (loanOfHead.lowPart 4).range = ⟨0, 4⟩ ∧
    (loanOfHead.highPart 4).range = ⟨4, 4⟩ := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **And it changed no authority.** The borrower is still granted the whole eight
bytes it was lent, and the owner is still frozen out of them — which is the pair a
split that leaked or lost authority would break. -/
theorem the_split_preserves_the_authority :
    splitHead.Granted borrower bufferProv ⟨0, 8⟩ AccessIntent.readWrite ∧
    ¬ splitHead.Granted owner bufferProv ⟨0, 8⟩ AccessIntent.write ∧
    splitHead.authorityOf owner bufferProv ⟨0, 8⟩ = AuthorityState.frozen ∧
    ¬ splitHead.Exclusive bufferProv ⟨0, 8⟩ := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- **A stranger gains nothing from a split either**, which is the leak a
re-description of authority could most easily produce. -/
theorem the_split_grants_the_stranger_nothing :
    ¬ splitHead.Granted stranger bufferProv ⟨0, 4⟩ AccessIntent.read ∧
    ¬ splitHead.Granted stranger bufferProv ⟨4, 4⟩ AccessIntent.read := by
  exact ⟨by decide, by decide⟩

/-- **A boundary on either end is refused**, because a part of size zero is a grant
`issue?` would not issue. -/
theorem the_degenerate_boundaries_are_refused :
    lentHead.splitGrant? firstLoan lowLoan highLoan 0 = Option.none ∧
    lentHead.splitGrant? firstLoan lowLoan highLoan 8 = Option.none ∧
    lentHead.splitGrant? firstLoan lowLoan highLoan 9 = Option.none := by
  exact ⟨by decide, by decide, by decide⟩

/-- **A part may not land on a taken identity**, the source's own included, and the
two parts may not share one. -/
theorem the_taken_identities_are_refused :
    lentHead.splitGrant? firstLoan firstLoan highLoan 4 = Option.none ∧
    lentHead.splitGrant? firstLoan lowLoan firstLoan 4 = Option.none ∧
    lentHead.splitGrant? firstLoan lowLoan lowLoan 4 = Option.none := by
  exact ⟨by decide, by decide, by decide⟩

/-- **An unknown source is refused.** -/
theorem splitting_an_unknown_loan_is_refused :
    unlent.splitGrant? firstLoan lowLoan highLoan 4 = Option.none := by decide

/-- The parts, rejoined. -/
def rejoinedHead : MemoryState :=
  (splitHead.joinGrants? lowLoan highLoan joinedLoan).getD splitHead

/-- **A join puts the halves back**, under a fresh identity and with the original
range, and both parts are consumed. -/
theorem the_join_restores_the_loan :
    (splitHead.joinGrants? lowLoan highLoan joinedLoan).isSome ∧
    rejoinedHead.grantAt? joinedLoan = some loanOfHead ∧
    rejoinedHead.grantAt? lowLoan = Option.none ∧
    rejoinedHead.grantAt? highLoan = Option.none := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- **And the authority is the authority the source had.** `loanOfHead` is what the
join produced, so this is the round trip closing: split, join, and the map is back to
one grant of the head with a new identity. -/
theorem the_round_trip_preserves_the_authority :
    rejoinedHead.Granted borrower bufferProv ⟨0, 8⟩ AccessIntent.readWrite ∧
    rejoinedHead.authorityOf owner bufferProv ⟨0, 8⟩ = AuthorityState.frozen ∧
    rejoinedHead.outstandingLoans bufferProv ⟨0, 8⟩ = 1 := by
  exact ⟨by decide, by decide, by decide⟩

/-- **A join in the wrong order is refused**, because the low grant's range must end
where the high one's begins and these do not. -/
theorem the_reversed_join_is_refused :
    splitHead.joinGrants? highLoan lowLoan joinedLoan = Option.none := by decide

/-- A lone low half, with nothing adjacent to it. -/
def loneLowHalf : MemoryState :=
  (unlent.issue? firstLoan { loanOfHead with range := ⟨0, 4⟩ }).getD unlent

/-- The two adjacent halves, differing only in rights. -/
def mismatchedPair : MemoryState :=
  (loneLowHalf.issue? secondLoan { readLoanOfHead with range := ⟨4, 4⟩ }).getD loneLowHalf

/-- Both states are the states they are named for, so the refusals below are about
the join rather than about a missing source. -/
theorem the_join_fixtures_are_real :
    loneLowHalf.grantAt? firstLoan = some { loanOfHead with range := ⟨0, 4⟩ } ∧
    loneLowHalf.grantAt? secondLoan = Option.none ∧
    mismatchedPair.grantAt? firstLoan = some { loanOfHead with range := ⟨0, 4⟩ } ∧
    mismatchedPair.grantAt? secondLoan = some { readLoanOfHead with range := ⟨4, 4⟩ } := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- **A missing partner is refused**, which is the unknown-source clause: nothing is
outstanding under `secondLoan` in `loneLowHalf`. -/
theorem joining_with_an_unknown_partner_is_refused :
    loneLowHalf.joinGrants? firstLoan secondLoan joinedLoan = Option.none := by decide

/-- **And grants differing in anything but their range are refused.** The rights
differ here; nothing about the door mentions rights, because it compares the whole
grant — a door listing the fields it cares about is the shape that let a duty be
relabelled in `Grass/Obligation/Delta.lean`. -/
theorem a_mismatched_join_is_refused :
    mismatchedPair.joinGrants? firstLoan secondLoan joinedLoan = Option.none := by decide

/-- Two grants of the same rights with four bytes of gap between them. -/
def gappedPair : MemoryState :=
  (loneLowHalf.issue? secondLoan { loanOfHead with range := ⟨8, 4⟩ }).getD loneLowHalf

/-- **A gap is refused**, and this is the refusal the design rests on: joining
⟨0,4⟩ to ⟨8,4⟩ would produce a grant over ⟨0,12⟩, authorizing four bytes neither
source covered. `joinGrants?_creates_no_authority` would be false without the
adjacency check, so here it is as a refusal. -/
theorem a_gapped_join_is_refused :
    gappedPair.joinGrants? firstLoan secondLoan joinedLoan = Option.none ∧
    gappedPair.grantAt? firstLoan = some { loanOfHead with range := ⟨0, 4⟩ } ∧
    gappedPair.grantAt? secondLoan = some { loanOfHead with range := ⟨8, 4⟩ } := by
  exact ⟨by decide, by decide, by decide⟩

/-- And the bytes in the gap are granted to nobody, before or after the refused
join, which is what "neither source covered them" means here. -/
theorem the_gap_is_granted_to_nobody :
    ¬ gappedPair.Granted borrower bufferProv ⟨4, 4⟩ AccessIntent.read ∧
    gappedPair.Granted borrower bufferProv ⟨0, 4⟩ AccessIntent.readWrite ∧
    gappedPair.Granted borrower bufferProv ⟨8, 4⟩ AccessIntent.readWrite := by
  exact ⟨by decide, by decide, by decide⟩

/-- The same pair with matching rights joins, so the refusal above is the mismatch
and nothing else about the state. -/
theorem the_matching_pair_joins :
    ((loneLowHalf.issue? secondLoan { loanOfHead with range := ⟨4, 4⟩ }).getD
      loneLowHalf).joinGrants? firstLoan secondLoan joinedLoan |>.isSome := by decide

/-! ## The negatives, composed, over a state nobody built

Every fixture above is concrete, and `decide` settles a concrete state. Review's point
was that the `not_authorizedAt_of_*` family and `granted_of_covering` had *only* that
use: the negatives refute one grant at one byte and `Granted` is existential over the
entry list, so nothing turned them into a `¬ Granted`; and `granted_of_covering`'s
`entry ∈ grantEntries` hypothesis was dischargeable by `decide` and by nothing else.
The two theorems below take an arbitrary `state` — no fixture, no `decide` — which is
the use those lemmas were written for and had never had. -/

/-- **A context that holds no grant is granted nothing**, in any state, over any
storage, for any intent. -/
theorem a_non_holder_is_granted_nothing (state : MemoryState) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent)
    (hne : ¬ range.IsEmpty)
    (h : ∀ entry ∈ state.grantEntries, entry.2.holder ≠ context) :
    ¬ state.Granted context provenance range intent :=
  MemoryState.not_granted_of_no_authorizing_entry hne fun entry hmem _ =>
    MemoryState.not_authorizedAt_of_other_holder (h entry hmem)

/-- **And a grant identity is enough to establish authority**, without knowing what
else the state holds. -/
theorem an_identity_suffices (state : MemoryState) (context : ContextId)
    (provenance : Provenance) (range : ByteRange) (intent : AccessIntent)
    (id : GrantId) (grant : AuthorityGrant) (hat : state.grantAt? id = some grant)
    (hcover : grant.range.Contains range) (hholder : grant.holder = context)
    (hshares : state.SharesBytes grant.provenance.root provenance.root)
    (hgrant : state.CurrentEpoch grant.provenance)
    (haccess : state.CurrentEpoch provenance)
    (hrights : grant.rights.Permits intent) :
    state.Granted context provenance range intent :=
  MemoryState.granted_of_grantAt hat hcover hholder hshares hgrant haccess hrights

end Tests.Memory.Loans
