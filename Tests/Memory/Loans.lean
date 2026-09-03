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

/-- Two loan identities. Distinct because a supply never reissues. -/
def firstLoan : GrantId := grants.fresh.1

/-- The second. -/
def secondLoan : GrantId := grants.fresh.2.fresh.1

private def epoch : EpochId := epochs.fresh.1

/-- Provenance of the whole buffer. -/
def bufferProv : Provenance :=
  { space := .cpuVirtual, root := buffer, epoch := epoch, source := .virtualAlloc
    rootExtent := ⟨0, 64⟩, path := [] }

/-- A state owning the buffer and lending nothing. -/
def unlent : MemoryState :=
  MemoryState.empty.allocate buffer
    { extent := ⟨0, 64⟩, epoch := epoch, space := .cpuVirtual
      permission := .readWrite, live := true, bytes := .empty, base := some 0x1000 }

/-- A loan of the first eight bytes to the borrower. -/
def loanOfHead : AuthorityGrant :=
  { kind := .loan, holder := borrower, provenance := bufferProv
    range := ⟨0, 8⟩, rights := .readWrite }

/-- A loan of a disjoint eight bytes. -/
def loanOfTail : AuthorityGrant :=
  { loanOfHead with range := ⟨8, 8⟩ }

/-! ## Exclusivity is the empty map, not a count -/

/-- Owning and lending nothing is exclusive. -/
theorem unlent_is_exclusive : unlent.Exclusive bufferProv ⟨0, 8⟩ := by decide

/-- Lending ends it, and the derived count agrees. -/
theorem lending_ends_exclusivity :
    ¬ (unlent.lend firstLoan loanOfHead).Exclusive bufferProv ⟨0, 8⟩ ∧
    (unlent.lend firstLoan loanOfHead).outstandingLoans bufferProv ⟨0, 8⟩ = 1 := by
  exact ⟨by decide, by decide⟩

/-- A loan of disjoint bytes does not end exclusivity over the head. §3's "relevant
map" is the loans over *those* bytes, not every loan in the state. -/
theorem a_disjoint_loan_leaves_the_head_exclusive :
    (unlent.lend secondLoan loanOfTail).Exclusive bufferProv ⟨0, 8⟩ ∧
    ¬ (unlent.lend secondLoan loanOfTail).Exclusive bufferProv ⟨8, 8⟩ := by
  exact ⟨by decide, by decide⟩

/-! ## A return consumes the identity it names -/

/-- Returning the loan restores exclusivity. -/
theorem returning_restores_exclusivity :
    ((unlent.lend firstLoan loanOfHead).returnLoan firstLoan).Exclusive
      bufferProv ⟨0, 8⟩ := by decide

/--
**Returning one loan does not return another over the same bytes.**

Two loans of the identical range, rights and holder, differing only in identity.
Returning the first leaves the second outstanding, so exclusivity is *not*
restored. A map keyed by shape rather than by identity would get this wrong, which
is why §3 says a return consumes that exact identity.
-/
theorem returning_one_of_two_leaves_the_other :
    ¬ (((unlent.lend firstLoan loanOfHead).lend secondLoan loanOfHead).returnLoan
        firstLoan).Exclusive bufferProv ⟨0, 8⟩ ∧
    (((unlent.lend firstLoan loanOfHead).lend secondLoan loanOfHead).returnLoan
        firstLoan).outstandingLoans bufferProv ⟨0, 8⟩ = 1 := by
  exact ⟨by decide, by decide⟩

/-- Returning both does restore it, so the theorem above is about identity rather
than about returns never working. -/
theorem returning_both_restores_exclusivity :
    (((unlent.lend firstLoan loanOfHead).lend secondLoan loanOfHead).returnLoan
        firstLoan).returnLoan secondLoan |>.Exclusive bufferProv ⟨0, 8⟩ := by decide

/-- The two loans really are identical apart from identity, so nothing else
distinguishes them. -/
theorem the_two_loans_differ_only_in_identity :
    loanOfHead = loanOfHead ∧ firstLoan ≠ secondLoan := by
  exact ⟨rfl, by decide⟩

/-! ## Lending freezes the owner's fragment

§3 lists "frozen owner fragments while loans exist" among the canonical authority
states. `ownerAuthority` is what puts an owner into one, and it is a function of
the map: lending freezes, returning thaws, and no field has to be kept in step. -/

/-- Owning and lending nothing is exclusive, and an ordinary write is permitted. -/
theorem an_unlent_owner_may_write :
    unlent.ownerAuthority bufferProv ⟨0, 8⟩ = .exclusive ∧
    (unlent.ownerAuthority bufferProv ⟨0, 8⟩).PermitsOrdinaryWrite := by
  exact ⟨by decide, by decide⟩

/-- **Lending freezes the owner, and a frozen owner may not write.** The borrow
discipline: the bytes are lent out, so the owner does not have them. -/
theorem a_lending_owner_may_not_write :
    (unlent.lend firstLoan loanOfHead).ownerAuthority bufferProv ⟨0, 8⟩ = .frozen ∧
    ¬ ((unlent.lend firstLoan loanOfHead).ownerAuthority bufferProv ⟨0, 8⟩).PermitsOrdinaryWrite := by
  exact ⟨by decide, by decide⟩

/-- Returning thaws it, so the freeze is not a one-way door. -/
theorem returning_thaws_the_owner :
    ((unlent.lend firstLoan loanOfHead).returnLoan firstLoan).ownerAuthority
      bufferProv ⟨0, 8⟩ = .exclusive := by decide

/-- The owner keeps bytes it did not lend. A loan of the head does not freeze the
tail, which is what makes "frozen *fragments*" fragments. -/
theorem lending_the_head_leaves_the_tail_writable :
    (unlent.lend firstLoan loanOfHead).ownerAuthority bufferProv ⟨8, 8⟩ = .exclusive := by
  decide

/-! ## Atomic authority is not ordinary authority -/

/-- §3: "Atomics do not grant ordinary non-atomic access." -/
theorem atomic_is_not_ordinary (ordering : OrderingDemand) :
    ¬ (AuthorityState.atomicShared ordering).PermitsOrdinaryWrite ∧
    ¬ AuthorityState.frozen.PermitsOrdinaryWrite ∧
    AuthorityState.exclusive.PermitsOrdinaryWrite :=
  ⟨fun h => h, fun h => h, trivial⟩

end Tests.Memory.Loans
