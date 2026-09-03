import Grass.Memory.Loan
import Grass.Op.Step

/-!
# The standard loan authority provider

`Grass/Op/Step.lean`'s `AuthorityProvider` is open on purpose: `docs/MEMORY_MODEL.md`
has several kinds of authority and a memory profile cannot enumerate them. That
openness is why `Tests/Op/FakeIsa.lean` could write its own loan provider to
demonstrate the seam. It is not a reason for every profile to write one.

This is the loan rule §3 describes, once, so a profile takes it rather than
reinventing it — and so the rule a reviewer checks is one rule rather than one per
target.

## The rule

**Lent bytes are reachable only through a loan.** If any loan is outstanding over
the bytes an access names, that access is refused unless the accessor holds a loan
covering it with sufficient rights.

That is `MemoryState.ownerAuthority`'s freeze made operational. `Loan.lean` proves
an owner holds `AuthorityState.frozen` while a loan exists and that `frozen`
permits no ordinary write; this refuses the access that would otherwise perform
one.

## What it deliberately does not decide

Who the owner is. `AllocationRecord` records no owner, and this rule does not need
one: it says lent bytes are reachable only through a loan, which is a statement
about the loan map and the accessor. A profile that wants "the owner may still
read" declares a loan to itself, which is the same fact written where the model
can see it.
-/

namespace Grass.Op

open Grass.Core Grass.Memory

/--
The loan rule of `docs/MEMORY_MODEL.md` §3, as a provider a profile can adopt.

`authorityUnavailable` is the class it records, which every profile already
declares because it is in `AuditViolationClass.emittedByTransition` — so adopting
this provider does not widen a profile's declaration burden.
-/
def AuthorityProvider.loan : AuthorityProvider where
  id := ⟨"grass.loan"⟩
  violationClass := .authorityUnavailable
  refuses state d :=
    !decide (state.memory.Exclusive d.provenance d.range) &&
      !decide (state.memory.GrantedOfKind .loan d.context d.provenance d.range d.intent)

/-- **Unlent bytes are not the loan rule's business.** A provider that refused
here would make every allocation unreachable until someone lent it to itself. -/
@[simp] theorem loan_does_not_refuse_when_exclusive (state : MachineState)
    (d : AccessDescriptor) (h : state.memory.Exclusive d.provenance d.range) :
    AuthorityProvider.loan.refuses state d = false := by
  simp [AuthorityProvider.loan, h]

/-- **A holder of a covering loan is not refused.** The loan is what makes the
bytes reachable, which is the whole point of lending them. -/
@[simp] theorem loan_does_not_refuse_the_holder (state : MachineState)
    (d : AccessDescriptor)
    (h : state.memory.GrantedOfKind .loan d.context d.provenance d.range d.intent) :
    AuthorityProvider.loan.refuses state d = false := by
  simp [AuthorityProvider.loan, h]

/--
**An access to lent bytes without a loan is refused.**

The freeze, operational. `Loan.lean`'s `not_permitsOrdinaryWrite_of_not_exclusive`
says an owner holding a frozen fragment may not write it; this is the transition
declining to let it.
-/
theorem loan_refuses_the_unauthorized (state : MachineState) (d : AccessDescriptor)
    (hlent : ¬ state.memory.Exclusive d.provenance d.range)
    (hno : ¬ state.memory.GrantedOfKind .loan d.context d.provenance d.range d.intent) :
    AuthorityProvider.loan.refuses state d = true := by
  simp [AuthorityProvider.loan, hlent, hno]

/-- Its class is one every profile already declares, so a policy adopting it needs
no new vocabulary. -/
@[simp] theorem loan_violationClass :
    AuthorityProvider.loan.violationClass ∈ AuditViolationClass.emittedByTransition := by
  decide

end Grass.Op
