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
    memory := state₀.memory.lend bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨0, 8⟩, rights := .readWrite } }

/-- The lend really did freeze those bytes, so the refusal below is about lending
rather than about the state being odd. -/
theorem the_lend_freezes_the_head :
    ¬ lentToEngine.memory.Exclusive bufferProv ⟨0, 8⟩ ∧
    lentToEngine.memory.ownerAuthority bufferProv ⟨0, 8⟩ = .frozen := by
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

/-- Returning the loan restores the thread's access, so the refusal tracks the
loan rather than being permanent. -/
theorem returning_restores_access :
    ∀ s, (step { lentToEngine with
                 memory := lentToEngine.memory.returnLoan bufferLoan } .store).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

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
    memory := state₀.memory.lend bufferLoan
      { kind := .loan, holder := engine₀, provenance := bufferProv
        range := ⟨8, 8⟩, rights := .readWrite } }

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

end Tests.Op.StandardLoan
