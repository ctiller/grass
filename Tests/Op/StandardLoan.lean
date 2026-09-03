import Grass.Op.LoanAuthority
import Tests.Op.FakeIsa

/-!
# A profile adopting the standard loan provider

`Tests/Op/FakeIsa.lean` writes its own loan provider, which was the right thing to
do when the point was to demonstrate that the seam accepts one. It is not the right
thing for every profile to do, and `Grass/Op/LoanAuthority.lean` exists so it need
not be.

This drives the standard provider end to end: a policy that differs from the seam
fixture's only in which authority providers it carries, stepping the same
operations. What it checks is that the loan rule holds *through `step`* — the
`Loan.lean` theorems are about the map, and a rule proved about a map that the
transition does not consult would be the defect this branch has found repeatedly.
-/

namespace Tests.Op.StandardLoan

open Grass.Core Grass.Memory Grass.Op Grass.Tests.FakeIsa

/-- The seam fixture's profile, with the standard loan rule in place of its
hand-written providers. -/
def policy : StepPolicy :=
  { Grass.Tests.FakeIsa.policy with
    authorities := [AuthorityProvider.loan]
    violationClassesDeclared := by decide }

/-- Step an `Alpha` operation under it. -/
def step (state : MachineState) (op : Alpha) : StepOutcome :=
  Grass.Op.step policy state (SomeOperation.of op) thread₀ .thread ⟨⟨"alpha"⟩⟩

/-- Nothing is lent in the starting state, so the buffer is reachable and an
ordinary store commits. Without this the refusals below would prove only that the
provider refuses everything. -/
theorem an_unlent_store_commits :
    ∀ s, (step state₀ .store).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- A loan of the buffer's head to the device engine. -/
def lentToEngine : MachineState :=
  { state₀ with
    memory := (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite }).getD state₀.memory }

/-- The lend succeeded, so `getD` did not fall back to the unlent state. -/
theorem the_engine_lend_succeeds :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite }).isSome := by decide

/-- The lend really did freeze those bytes, so the refusal below is about lending
rather than about the state being odd. -/
theorem the_lend_freezes_the_head :
    ¬ lentToEngine.memory.Exclusive bufferProv ⟨0, 8⟩ ∧
    lentToEngine.memory.authorityOf thread₀ bufferProv ⟨0, 8⟩ = AuthorityState.frozen := by
  exact ⟨by decide, by decide⟩

/--
**The thread's store to lent bytes is refused, through `step`.**

`Loan.lean` proves an owner holding a frozen fragment may not write it. This is
the transition declining to let it: nothing commits, and the violation is
recorded.
-/
theorem a_store_to_lent_bytes_is_refused :
    ∀ s, (step lentToEngine .store).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.memory.byteAt? bufferAlloc 0 = some 0x00 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/--
**A loan cannot be bypassed through an aliasing allocation.**

The regression for the worst defect local review found in this module. `loansOver`
decided "the relevant map" with `Provenance.SameStorage`, which is not the
same-bytes relation — this layer had already learned that once, which is why
`MemoryState.SharesBytes` exists and why `ConflictsWithHistory` consults it. So a
loan over `bufferAlloc` left `viewAlloc` looking exclusive, and a thread's store
through the mapped view committed with no violation while the engine held the
bytes. That is the §7.5 mapped-file and host-visible-device-buffer shape exactly.
-/
theorem a_loan_cannot_be_bypassed_through_an_alias :
    ¬ lentToEngine.memory.Exclusive viewProv ⟨0, 8⟩ ∧
    ∀ s, (step lentToEngine .storeThroughView).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  refine ⟨by decide, ?_⟩
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- The alias really is one: the two provenances name different storage by
`SameStorage` and the same bytes by `SharesBytes`, which is what made the bypass
possible and what closes it. -/
theorem the_view_aliases_the_buffer :
    ¬ bufferProv.SameStorage viewProv ∧
    state₀.memory.SharesBytes bufferAlloc viewAlloc := by
  exact ⟨by decide, by decide⟩

/-- Returning the loan restores the thread's access, so the refusal tracks the
loan rather than being permanent. -/
theorem returning_restores_access :
    (lentToEngine.memory.returnLoan? engine₀ bufferLoan).isSome ∧
    ∀ s, (step { lentToEngine with
                 memory := (lentToEngine.memory.returnLoan? engine₀ bufferLoan).getD
                   lentToEngine.memory } .store).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  refine ⟨by decide, ?_⟩
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- **The thread cannot return the engine's loan and then write.** The return is an
authority operation and an unchecked one let any context perform it, so the freeze
was defeated by calling the function that removes it. -/
theorem the_thread_cannot_return_the_engines_loan :
    lentToEngine.memory.returnLoan? thread₀ bufferLoan = Option.none := by decide

/--
**A read of lent bytes is refused too**, not only a write.

§3's rule is that lent bytes are reachable only through a loan, and `Alpha.load`
names the same eight bytes the loan covers. Worth pinning, because "lending stops
the owner writing" is the intuitive half and it would be easy to build a provider
that enforced only that.
-/
theorem a_read_of_lent_bytes_is_also_refused :
    ∀ s, (step lentToEngine .load).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- A loan of the buffer's *tail*, which no `Alpha` operation touches. -/
def tailLentToEngine : MachineState :=
  { state₀ with
    memory := (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨8, 8⟩, rights := .readWrite }).getD state₀.memory }

/--
**The freeze is per-fragment, and `step` sees that.**

Lending `[8, 16)` leaves `[0, 8)` reachable, so a store there still commits. Without
this the refusals above would be consistent with a provider that refuses any access
to an allocation with any loan outstanding anywhere — which is not what §3 says and
would make lending one field of a struct lock the whole struct.
-/
theorem lending_the_tail_leaves_the_head_reachable :
    ∀ s, (step tailLentToEngine .store).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-! ## The rule does not depend on how the map was built

`MemoryState.issue?` refuses to *issue* conflicting authority, and for a while the
provider was a pure holder test that relied on it: if the accessor holds a covering
loan, proceed. Review found two ways to reach a state `issue?` would have refused,
and in both the write committed with no violation recorded.

A rule that holds only because of how a state was constructed is not a rule about
the state. The provider now reads `MemoryState.authorityOf` on the map it is
handed. -/

/-- The thread holds a write loan over the buffer's head. -/
def lentToThread : MemoryState :=
  (state₀.memory.issue? bufferLoan
    { kind := .loan, holder := thread₀, provenance := bufferProv
      range := ⟨0, 8⟩, rights := .readWrite }).getD state₀.memory

/-- **The conflicting pair cannot be issued.** §7.3's rule at the door, which is
where a caller doing the right thing finds out. -/
theorem the_conflicting_pair_cannot_be_issued :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := thread₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite }).isSome ∧
    lentToThread.issue? secondBufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite } = Option.none := by
  exact ⟨by decide, by decide⟩

/--
**And the identity cannot be stolen.**

This was the second door. `MemoryState.grant` inserted with no checks at all, and
`FiniteMap.insert` *erases* — so installing a grant under an identity another
context held deleted that grant, and the access-time rule then read a map the
victim's loan was no longer in. Review did exactly that and the write committed with
no violation. `grant` is gone; `issue?` refuses a reissued identity, which is §3's
"a return consumes that exact identity" read from the other side.
-/
theorem the_identity_cannot_be_stolen :
    lentToThread.issue? bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite } = Option.none ∧
    (lentToThread.grants.lookup bufferLoan).isSome := by
  exact ⟨by decide, by decide⟩

/-- Two loans that do **not** conflict when issued: `[0, 8)` of the buffer to the
thread, `[0, 8)` of `borrowedAlloc` to the engine. Different allocations, so
`issue?` is right to accept them. -/
def separatelyLent : MemoryState :=
  (lentToThread.issue? secondBufferLoan
      { kind := .loan, holder := engine₀, provenance := borrowedProv
        range := ⟨0, 8⟩, rights := .readWrite }).getD lentToThread

/-- Then the profile declares the mapping. `docs/MEMORY_MODEL.md` §7.5 makes that a
real transition, and nothing re-examines the grants already issued. -/
def aliasedAfterIssue : MachineState :=
  { state₀ with memory := separatelyLent.alias bufferAlloc borrowedAlloc }

/-- Both lends succeeded, and they became conflicting only once the alias was
declared: issued in the other order, `issue?` refuses the second. -/
theorem the_conflict_appears_after_issue :
    (separatelyLent.grants.lookup bufferLoan).isSome ∧
    (separatelyLent.grants.lookup secondBufferLoan).isSome ∧
    ((state₀.memory.alias bufferAlloc borrowedAlloc).issue? bufferLoan
        { kind := .loan, holder := thread₀, provenance := bufferProv
          range := ⟨0, 8⟩, rights := .readWrite }).isSome := by
  exact ⟨by decide, by decide, by decide⟩

/-- **And the thread's store is refused**, though it holds a covering write loan
and `issue?` was never given the chance to refuse anything. This is the case no
issue-time check can catch. -/
theorem an_alias_declared_after_issue_is_refused :
    aliasedAfterIssue.memory.authorityOf thread₀ bufferProv ⟨0, 8⟩ = AuthorityState.frozen ∧
    ∀ s, (step aliasedAfterIssue .store).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  refine ⟨by decide, ?_⟩
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- The engine holds a *read* loan over the head. -/
def readLentToEngine : MachineState :=
  { state₀ with
    memory := (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readOnly }).getD state₀.memory }

/--
**A read against shared immutable access commits.**

This fixture asserted the opposite for one round, and pinned it as a feature: the
holder test was `MemoryState.Exclusive`, the loan map being empty of *everyone's*
loans, so a context holding no loan at all was refused a read of bytes another
context held only a read loan over. §3's sentence about the map being empty is about
*exclusive authority*; §7.3's conflict needs a writer; and `authorityOf` calls this
state `sharedImmutable` and permits reads. The transition contradicted its own
summary, and `AuthorityState.sharedImmutable` was reachable at the transition for
co-borrowers and never for anyone else.
-/
theorem a_read_against_shared_immutable_access_commits :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readOnly }).isSome ∧
    readLentToEngine.memory.authorityOf thread₀ bufferProv ⟨0, 8⟩ =
      AuthorityState.sharedImmutable ∧
    ∀ s, (step readLentToEngine .load).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  refine ⟨by decide, by decide, ?_⟩
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- **But a write against it is still refused**, so the change above is about reads
and not about the state having become permissive. -/
theorem a_write_against_shared_immutable_access_is_refused :
    ∀ s, (step readLentToEngine .store).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- The thread holds a *read-only* loan over the head — this layer's own "declare a
loan to yourself" idiom for "the owner may still read". -/
def selfReadLoan : MachineState :=
  { state₀ with
    memory := (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := thread₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readOnly }).getD state₀.memory }

/--
**A self-loan bounds its holder**, and that is the holder half's whole job.

The thread holds the only loan over these bytes, so `authorityOf` calls its state
`exclusive` and `MemoryState.permitsOrdinaryWrite_of_unheld` says it may write. The
transition refuses the write anyway, because the loan the thread holds is read-only.
Refusal is therefore wider than `frozen` — but for this reason and not the one this
file used to give.
-/
theorem a_self_loan_bounds_its_holder :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := thread₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readOnly }).isSome ∧
    selfReadLoan.memory.authorityOf thread₀ bufferProv ⟨0, 8⟩ = AuthorityState.exclusive ∧
    ∀ s, (step selfReadLoan .store).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  refine ⟨by decide, by decide, ?_⟩
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- And its *read* commits, so the self-loan is a bound and not a lockout. Under the
old holder test this was refused too, which made the endorsed idiom unusable. -/
theorem a_self_loan_permits_the_read_it_grants :
    ∀ s, (step selfReadLoan .load).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

end Tests.Op.StandardLoan
