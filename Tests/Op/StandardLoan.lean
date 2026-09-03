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
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite }).getD state₀.memory }

/-- The lend succeeded, so `getD` did not fall back to the unlent state. -/
theorem the_engine_lend_succeeds :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := bufferProv
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

/-- **And what "the same bytes" does not yet mean.**

`MemoryState.SharesBytes` is what the whole authority layer keys on — `grantsOver`,
`AuthorizedBy`, `MemoryEvent.Conflicts` — and `MemoryState.write` writes the bytes of
the *named* allocation only. So a store through the view leaves the buffer's bytes
unchanged, and a read of the buffer afterwards sees the old value. "Same storage" is
an authority-level fiction with no byte-level counterpart, which means the theorem
above guards a relation the memory semantics does not implement.

Stated here rather than only in `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2, because a
reader meeting the theorem above should meet this in the same file. Closing it is
either write-propagation across the alias set, which needs the offset mapping
`MemoryState.aliases` does not record, or allocations sharing one byte store by
identity — the second removes `SharesAfter` and `AliasHop` entirely and is the
better shape, and both change `MemoryState`. -/
theorem the_alias_is_not_yet_a_byte_level_fact :
    ∀ s, (step state₀ .storeThroughView).state? = some s →
      s.memory.byteAt? viewAlloc 0 = some 0xab ∧
      s.memory.byteAt? bufferAlloc 0 = some 0x00 ∧
      state₀.memory.SharesBytes viewAlloc bufferAlloc := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

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

/-- **The thread lent it, so the thread may return it** — and that is §6's
conforming return, where the caller consumes the identity it lent. The fixture above
returns as the holder; this one as the lender. -/
theorem the_lender_may_return_it :
    (lentToEngine.memory.returnLoan? thread₀ bufferLoan).isSome := by decide

/-- **And a context that neither holds nor lent it may not.** The return is an
authority operation and an unchecked one let any context perform it, so the freeze
was defeated by calling the function that removes it. -/
theorem a_stranger_cannot_return_the_loan :
    lentToEngine.memory.returnLoan? engine₁ bufferLoan = Option.none := by decide

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
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := bufferProv
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
    { kind := .loan, holder := thread₀, lender := engine₀, provenance := bufferProv
      range := ⟨0, 8⟩, rights := .readWrite }).getD state₀.memory

/-- **The conflicting pair cannot be issued.** §7.3's rule at the door, which is
where a caller doing the right thing finds out. -/
theorem the_conflicting_pair_cannot_be_issued :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := thread₀, lender := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite }).isSome ∧
    lentToThread.issue? secondBufferLoan
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := bufferProv
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
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite } = Option.none ∧
    (lentToThread.grantAt? bufferLoan).isSome := by
  exact ⟨by decide, by decide⟩

/-- Two loans that do **not** conflict when issued: `[0, 8)` of the buffer to the
thread, `[0, 8)` of `borrowedAlloc` to the engine. Different allocations, so
`issue?` is right to accept them. -/
def separatelyLent : MemoryState :=
  (lentToThread.issue? secondBufferLoan
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := borrowedProv
        range := ⟨0, 8⟩, rights := .readWrite }).getD lentToThread

/-- Then the profile declares the mapping. `docs/MEMORY_MODEL.md` §7.5 makes that a
real transition, and nothing re-examines the grants already issued. -/
def aliasedAfterIssue : MachineState :=
  { state₀ with memory := separatelyLent.alias bufferAlloc borrowedAlloc }

/-- Both lends succeeded, and they became conflicting only once the alias was
declared: issued in the other order, `issue?` refuses the second. -/
theorem the_conflict_appears_after_issue :
    (separatelyLent.grantAt? bufferLoan).isSome ∧
    (separatelyLent.grantAt? secondBufferLoan).isSome ∧
    ((state₀.memory.alias bufferAlloc borrowedAlloc).issue? bufferLoan
        { kind := .loan, holder := thread₀, lender := engine₀, provenance := bufferProv
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
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readOnly }).getD state₀.memory }

/--
**A read against shared immutable access is refused to a context holding nothing**,
and this fixture has now asserted both answers.

The holder test was `Exclusive` — the loan map empty of everyone's loans — and this
was refused. It became `LoanHeldBySelf`, asking only what *this* context held, and
this was permitted, on the argument that §7.3's conflict needs a writer and
`authorityOf` calls the state `sharedImmutable`. Review then showed what asking only
about oneself costs: with atomic-only grants outstanding, `authorityOf` reports
`atomicShared`, and a context holding *nothing* could join the protocol atomically —
two contexts atomically writing the same live bytes, one of them never let in.

So the test asks whether anything is held at all, and this read is refused again. It
is an over-refusal and it is stated as one: the lender of the read loan is refused
alongside a stranger, because `AllocationRecord` records no owner and the two are the
same context to this rule. Permitting one permits both, and permitting both is the
hole. §4.4.1 records it.
-/
theorem a_read_against_shared_immutable_access_is_refused :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readOnly }).isSome ∧
    readLentToEngine.memory.authorityOf thread₀ bufferProv ⟨0, 8⟩ =
      AuthorityState.sharedImmutable ∧
    ∀ s, (step readLentToEngine .load).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
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
      { kind := .loan, holder := thread₀, lender := engine₀, provenance := bufferProv
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
      { kind := .loan, holder := thread₀, lender := engine₀, provenance := bufferProv
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

/-- The engine holds authority over the head for **atomic access only**. -/
def atomicLentToEngine : MachineState :=
  { state₀ with
    memory := (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .atomicReadWrite }).getD state₀.memory }

/--
**A context holding nothing may not join an atomic protocol.**

The hole `Permission.atomicOnly` opened and review demonstrated. Marking a grant
atomic-only drops the state every *other* context sees from `frozen` to
`atomicShared`, and `atomicShared` permits any atomic intent — so with a holder test
that asked only what *this* context held, a context holding no grant at all was
un-refused, and two contexts could atomically write the same live bytes with one of
them never let in. §7.3's conflict is overlapping live bytes, distinct contexts, a
writer, and this was all three.
-/
theorem a_stranger_may_not_join_the_atomic_protocol :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .atomicReadWrite }).isSome ∧
    atomicLentToEngine.memory.authorityOf thread₀ bufferProv ⟨0, 8⟩ =
      AuthorityState.atomicShared ∧
    ∀ s, (step atomicLentToEngine .atomicAdd).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  refine ⟨by decide, by decide, ?_⟩
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- And the state really is the permissive one: `atomicShared` permits the intent,
so the refusal above comes from the holder half and not from the summary. Without
this the theorem above would be consistent with `atomicShared` permitting nothing. -/
theorem the_atomic_state_permits_the_intent :
    (atomicLentToEngine.memory.authorityOf thread₀ bufferProv ⟨0, 8⟩).PermitsIntent
      AccessIntent.atomicReadWrite ∧
    ¬ atomicLentToEngine.memory.Granted thread₀ bufferProv ⟨0, 8⟩
        AccessIntent.atomicReadWrite := by
  exact ⟨by decide, by decide⟩

/-- Two adjacent write loans, both held by the thread. `issue?` accepts them: §7.3's
conflict is between distinct holders. -/
def splitBetweenTwoLoans : MachineState :=
  { state₀ with
    memory := ((state₀.memory.issue? bufferLoan
        { kind := .loan, holder := thread₀, lender := engine₀, provenance := bufferProv
          range := ⟨0, 4⟩, rights := .readWrite }).getD state₀.memory).issue?
        secondBufferLoan
        { kind := .loan, holder := thread₀, lender := engine₀, provenance := bufferProv
          range := ⟨4, 4⟩, rights := .readWrite } |>.getD state₀.memory }

/--
**A context's grants compose.**

`Granted` required a *single* grant to cover the whole access, and review issued one
context adjacent write loans over `[0, 4)` and `[4, 8)` and found its store to
`[0, 8)` refused — while `denialOf` cleared it, `authorityOf` called the state
`exclusive`, and the context was authorized on each half separately. Nothing in
`docs/MEMORY_MODEL.md` §3 says authority must arrive in one piece. `Granted` is now
stated per byte, so it does not, and the fragments a future split produces are usable
before split itself lands.
-/
theorem adjacent_loans_compose :
    (splitBetweenTwoLoans.memory.grantAt? bufferLoan).isSome ∧
    (splitBetweenTwoLoans.memory.grantAt? secondBufferLoan).isSome ∧
    splitBetweenTwoLoans.memory.Granted thread₀ bufferProv ⟨0, 8⟩ AccessIntent.write ∧
    ∀ s, (step splitBetweenTwoLoans .store).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- And a gap in the cover is still a refusal, so composition is per byte and not a
weakening. The thread holds `[0, 4)` only; its store to `[0, 8)` is refused. -/
theorem a_gap_in_the_cover_is_refused :
    ¬ (((state₀.memory.issue? bufferLoan
        { kind := .loan, holder := thread₀, lender := engine₀, provenance := bufferProv
          range := ⟨0, 4⟩, rights := .readWrite }).getD state₀.memory).Granted
      thread₀ bufferProv ⟨0, 8⟩ AccessIntent.write) ∧
    ∀ s, (step { state₀ with
                 memory := (state₀.memory.issue? bufferLoan
                   { kind := .loan, holder := thread₀, lender := engine₀
                     provenance := bufferProv, range := ⟨0, 4⟩
                     rights := .readWrite }).getD state₀.memory } .store).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  refine ⟨by decide, ?_⟩
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

end Tests.Op.StandardLoan
