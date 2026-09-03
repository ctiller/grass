import Grass.Memory.Loan
import Grass.Op.Step

/-!
# The standard loan authority provider

`Grass/Op/Step.lean`'s `AuthorityProvider` is open on purpose: `docs/MEMORY_MODEL.md`
has several kinds of authority and a memory profile cannot enumerate them. That
openness is why `Tests/Op/FakeIsa.lean` could write its own loan provider to
demonstrate the seam. It is not a reason for every profile to write one.

This is the rule §3 and §7.3 describe, once, so a profile takes it rather than
reinventing it — and so the rule a reviewer checks is one rule rather than one per
target.

## The rule, in two halves

**Lent bytes are reachable only through a loan.** If any loan is outstanding over
the bytes an access names, that access is refused unless the accessor holds a loan
covering it with sufficient rights. That is a *holder* test over the loan map.

**And no access may proceed against authority another context holds.** The state
`MemoryState.authorityOf` reports must permit the intent: `frozen` and
`unavailable` permit nothing, and `sharedImmutable` permits a read and not a write.

The second half was absent, and its absence was a hole rather than a nicety. The
holder test alone asks only whether *this* context holds a covering loan, so two
contexts each holding a write loan over the same bytes were both unrefused. The
issue-time check in `MemoryState.lend?` is supposed to make that pair impossible
and does not: `MemoryState.grant` installs a grant with no checks, and declaring an
alias *after* two non-conflicting grants are issued makes them conflict with
nothing re-examined. Review demonstrated both, end to end, with the write
committing and no violation recorded. A rule that depends on how the map was built
is not a rule about the map, so this one reads the map it finds.

## What the two halves are, and are not

They are not the same test and neither implies the other, which is the correction
this file has needed twice.

- `authorityOf` calls a context holding the *only* loan over the bytes `exclusive`,
  while `MemoryState.Exclusive` — §3's sentence about the relevant map being empty
  — is false there. The holder half is what refuses that context an access its own
  loan's rights do not cover.
- The holder half refuses a *read* of bytes another context holds only a read loan
  over, while `authorityOf` calls that state `sharedImmutable` and permits reads.

So refusal is strictly wider than `frozen`. `loan_refuses_the_frozen` and
`loan_refuses_a_write_when_shared` state the direction that matters — a state that
does not permit the intent is refused — and `loan_refusal_is_wider_than_frozen` in
`Tests/Op/StandardLoan.lean` exhibits the converse failing, so no reader has to
take "the two agree" on trust. An earlier version of this comment claimed they
agreed exactly and cited a theorem that mentioned neither `authorityOf` nor
`frozen`; three reviewers found it.

## What it deliberately does not decide

Who the owner is. `AllocationRecord` records no owner, and this rule does not need
one: it says authority is held rather than assumed, which is a statement about the
grant map and the accessor. A profile that wants "the owner may still read"
declares a loan to itself — and `authorityOf` agrees, because a grant you hold does
not freeze you.
-/

namespace Grass.Op

open Grass.Core Grass.Memory

/--
The loan rule of `docs/MEMORY_MODEL.md` §3 and §7.3, as a provider a profile can
adopt.

`authorityUnavailable` is the class it records, which every profile already
declares because it is in `AuditViolationClass.emittedByTransition` — so adopting
this provider does not widen a profile's declaration burden.
-/
def AuthorityProvider.loan : AuthorityProvider where
  id := ⟨"grass.loan"⟩
  violationClass := .authorityUnavailable
  refuses state d :=
    !decide ((state.memory.authorityOf d.context d.provenance d.range).PermitsIntent
        d.intent) ||
      (!decide (state.memory.Exclusive d.provenance d.range) &&
        !decide (state.memory.GrantedOfKind .loan d.context d.provenance d.range d.intent))

/-- **An access the held authority does not permit is refused.** The half that was
missing: whoever installed the conflicting grant, and however it came to conflict,
the access does not proceed. -/
theorem loan_refuses_the_unpermitted (state : MachineState) (d : AccessDescriptor)
    (h : ¬ (state.memory.authorityOf d.context d.provenance d.range).PermitsIntent d.intent) :
    AuthorityProvider.loan.refuses state d = true := by
  simp [AuthorityProvider.loan, h]

/-- **A frozen fragment is refused**, whatever the intent. This is the bridge from
`AuthorityState` to the transition, in the direction that carries the guarantee. -/
theorem loan_refuses_the_frozen (state : MachineState) (d : AccessDescriptor)
    (h : state.memory.authorityOf d.context d.provenance d.range = .frozen) :
    AuthorityProvider.loan.refuses state d = true :=
  loan_refuses_the_unpermitted state d (by rw [h]; exact fun hc => hc)

/-- **A write against shared immutable access is refused.** -/
theorem loan_refuses_a_write_when_shared (state : MachineState) (d : AccessDescriptor)
    (h : state.memory.authorityOf d.context d.provenance d.range = .sharedImmutable)
    (hw : d.intent.writes = true) :
    AuthorityProvider.loan.refuses state d = true := by
  refine loan_refuses_the_unpermitted state d ?_
  rw [h]
  simp [AuthorityState.PermitsIntent, hw]

/-- **Dead, absent or stale-epoch storage is refused.** `denialOf` refuses it too;
this provider does not rely on that, because a rule that holds only because another
gate happens to run first is not a rule. -/
theorem loan_refuses_the_unavailable (state : MachineState) (d : AccessDescriptor)
    (h : ¬ state.memory.Live d.provenance) :
    AuthorityProvider.loan.refuses state d = true := by
  refine loan_refuses_the_unpermitted state d ?_
  rw [(MemoryState.authorityOf_eq_unavailable_iff _ _ _ _).mpr h]
  exact fun hc => hc

/--
**An access to lent bytes without a loan is refused.**

The holder half. `Loan.lean`'s `not_permitsOrdinaryWrite_of_heldByAnother` says a
context may not write bytes another context holds; this is the transition declining
to let it, and it refuses reads as well — "lending stops the owner writing" is the
intuitive half, and a provider enforcing only that would pass everything else.
-/
theorem loan_refuses_the_unauthorized (state : MachineState) (d : AccessDescriptor)
    (hlent : ¬ state.memory.Exclusive d.provenance d.range)
    (hno : ¬ state.memory.GrantedOfKind .loan d.context d.provenance d.range d.intent) :
    AuthorityProvider.loan.refuses state d = true := by
  simp [AuthorityProvider.loan, hlent, hno]

/-- **Both halves must pass for an access to proceed**, which is the whole content
of the provider and is what makes each of the theorems above a refusal rather than
a preference. -/
theorem loan_does_not_refuse (state : MachineState) (d : AccessDescriptor)
    (hpermits :
      (state.memory.authorityOf d.context d.provenance d.range).PermitsIntent d.intent)
    (hholder : state.memory.Exclusive d.provenance d.range ∨
      state.memory.GrantedOfKind .loan d.context d.provenance d.range d.intent) :
    AuthorityProvider.loan.refuses state d = false := by
  unfold AuthorityProvider.loan
  cases hholder with
  | inl h => simp [hpermits, h]
  | inr h => simp [hpermits, h]

/-- **Refusal means the bytes are lent, or the held authority does not permit the
intent.** The exact converse of the definition, stated so a caller reasoning
backwards from a refusal has something to reason with — and so that nothing here
claims refusal is the same set as `frozen`, which it is not. -/
theorem loan_refuses_only_for_a_reason (state : MachineState) (d : AccessDescriptor)
    (h : AuthorityProvider.loan.refuses state d = true) :
    ¬ (state.memory.authorityOf d.context d.provenance d.range).PermitsIntent d.intent ∨
      ¬ state.memory.Exclusive d.provenance d.range := by
  unfold AuthorityProvider.loan at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  exact h.imp id (fun hc => hc.1)

/-- Its class is one every profile already declares, so a policy adopting it needs
no new vocabulary. -/
@[simp] theorem loan_violationClass :
    AuthorityProvider.loan.violationClass ∈ AuditViolationClass.emittedByTransition := by
  decide

end Grass.Op
