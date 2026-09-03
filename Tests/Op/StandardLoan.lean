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
    memory := (state₀.memory.lend? bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite }).getD state₀.memory }

/-- The lend succeeded, so `getD` did not fall back to the unlent state. -/
theorem the_engine_lend_succeeds :
    (state₀.memory.lend? bufferLoan
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
    memory := (state₀.memory.lend? bufferLoan
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

`MemoryState.lend?` refuses to *issue* conflicting authority, and for a while the
provider was a pure holder test that relied on it: if the accessor holds a covering
loan, proceed. Review found two ways to reach a state `lend?` would have refused,
and in both the write committed with no violation recorded.

A rule that holds only because of how a state was constructed is not a rule about
the state. The provider now reads `MemoryState.authorityOf` on the map it is
handed. -/

/-- Two write loans over the same bytes, to two contexts, installed through
`MemoryState.grant` — which inserts with no checks at all. -/
def doublyGranted : MachineState :=
  { state₀ with
    memory := (state₀.memory.grant bufferLoan
        { kind := .loan, holder := thread₀, provenance := bufferProv
          range := ⟨0, 8⟩, rights := .readWrite }).grant secondBufferLoan
        { kind := .loan, holder := engine₀, provenance := bufferProv
          range := ⟨0, 8⟩, rights := .readWrite } }

/-- `lend?` really would have refused this pair, so the state below is the one
§7.3 says cannot be issued rather than an ordinary one. -/
theorem lend_would_have_refused_the_pair :
    ((state₀.memory.grant bufferLoan
        { kind := .loan, holder := thread₀, provenance := bufferProv
          range := ⟨0, 8⟩, rights := .readWrite }).lend? secondBufferLoan
        { kind := .loan, holder := engine₀, provenance := bufferProv
          range := ⟨0, 8⟩, rights := .readWrite }) = Option.none := by decide

/-- **And the thread's store is refused even though the thread holds a covering
write loan.** Under the holder test it committed: `GrantedOfKind` succeeded, and
nothing asked what anyone else held. -/
theorem a_grant_installed_conflict_is_refused :
    ∀ s, (step doublyGranted .store).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- The state really is the frozen one, so the refusal above is the rule biting
rather than something else in the fixture. -/
theorem the_granted_pair_freezes_both :
    doublyGranted.memory.authorityOf thread₀ bufferProv ⟨0, 8⟩ = AuthorityState.frozen ∧
    doublyGranted.memory.authorityOf engine₀ bufferProv ⟨0, 8⟩ = AuthorityState.frozen := by
  exact ⟨by decide, by decide⟩

/-- Two loans that do **not** conflict when issued: `[0, 8)` of the buffer to the
thread, `[0, 8)` of `borrowedAlloc` to the engine. Different allocations, so
`lend?` is right to accept them. -/
def separatelyLent : MemoryState :=
  ((state₀.memory.lend? bufferLoan
      { kind := .loan, holder := thread₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite }).getD state₀.memory).lend? secondBufferLoan
      { kind := .loan, holder := engine₀, provenance := borrowedProv
        range := ⟨0, 8⟩, rights := .readWrite } |>.getD state₀.memory

/-- Then the profile declares the mapping. `docs/MEMORY_MODEL.md` §7.5 makes that a
real transition, and nothing re-examines the grants already issued. -/
def aliasedAfterIssue : MachineState :=
  { state₀ with memory := separatelyLent.alias bufferAlloc borrowedAlloc }

/-- Both lends succeeded, and they became conflicting only once the alias was
declared: issued in the other order, `lend?` refuses the second. -/
theorem the_conflict_appears_after_issue :
    (separatelyLent.grants.lookup bufferLoan).isSome ∧
    (separatelyLent.grants.lookup secondBufferLoan).isSome ∧
    ((state₀.memory.alias bufferAlloc borrowedAlloc).lend? bufferLoan
        { kind := .loan, holder := thread₀, provenance := bufferProv
          range := ⟨0, 8⟩, rights := .readWrite }).isSome := by
  exact ⟨by decide, by decide, by decide⟩

/-- **And the thread's store is refused**, though it holds a covering write loan
and `lend?` was never given the chance to refuse anything. This is the case no
issue-time check can catch. -/
theorem an_alias_declared_after_issue_is_refused :
    aliasedAfterIssue.memory.authorityOf thread₀ bufferProv ⟨0, 8⟩ = AuthorityState.frozen ∧
    ∀ s, (step aliasedAfterIssue .store).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  refine ⟨by decide, ?_⟩
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- **Refusal is wider than `frozen`.** The engine holds a *read* loan; the thread
holds none, so its read is refused by the holder half while `authorityOf` calls the
state `sharedImmutable` and permits reads. Pinned because three reviewers found
prose claiming the provider refuses exactly the frozen accesses. -/
def readLentToEngine : MachineState :=
  { state₀ with
    memory := (state₀.memory.lend? bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readOnly }).getD state₀.memory }

theorem loan_refusal_is_wider_than_frozen :
    (state₀.memory.lend? bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readOnly }).isSome ∧
    readLentToEngine.memory.authorityOf thread₀ bufferProv ⟨0, 8⟩ =
      AuthorityState.sharedImmutable ∧
    ∀ s, (step readLentToEngine .load).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  refine ⟨by decide, by decide, ?_⟩
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

end Tests.Op.StandardLoan
