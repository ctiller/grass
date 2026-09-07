import Grass.Process.Facet
import Tests.Process.M1CorrectFixtures

/-!
# The ordinary facet costs nothing, and the cancellable one carries its contract

`Grass/Process/Facet.lean` keeps two of `docs/PROCESS.md` §3's sentences, and
this file is where each stops being a claim.

* **"Pure serial functions, straight-line helpers, and uncancellable leaf
  processes gain no new author obligation."** `helperIsOrdinary` is a complete
  facet written as `.ordinary`, with no argument and no proof. If the
  constructor ever grew a field, this line would stop elaborating.
* **"The bridge cannot discard it after manufacturing a liveness contract."**
  `cancellable_oneShot_gives_its_contract_back` recovers the exact contract from
  the facet, and `supervisor_learns_it_cannot_force_a_stop` derives §3's "a
  supervisor cannot manufacture a safe forced stop" from the facet alone — which
  is the whole reason the contract is retained rather than summarised.

The process is `oneShot`, and its `TerminalRemainderLaw` is `strict` — the law
that accepts only an empty remainder. That is deliberate: an earlier draft of
`ProcessTerminationContract` let `permitted` see the state but not the
outstanding demands, and under exactly this law no disposition existed for a
non-empty bag, so the record was uninhabitable. `oneShotStops` below is the
contract that draft could not have.
-/

namespace Grass.Process.Tests.Facet

open Grass.Process
open Grass.Process.Tests

/-- This fixture takes no position on supervision or versioning. -/
abbrev NoPolicy : Type := Empty

/-! ## The ordinary facet costs nothing -/

/--
**A straight-line helper's facet, in full.**

No argument, no proof, no obligation. §3 promises exactly this, and what makes
it true is `terminal_transitions_have_exact_disposition`: the run relation's
`terminate` constructor cannot be formed without a demand classification, so the
disposition an ordinary facet would otherwise have had to supply is already
there.
-/
def helperIsOrdinary :
    TerminationFacet oneShotCorrect () NoPolicy NoPolicy .ordinary :=
  .ordinary

/-- And it retains no contract, which §3 says is correct rather than a loss. -/
theorem ordinary_promises_nothing : helperIsOrdinary.retainedContract = none := rfl

/--
The disposition it did not have to supply, recovered from the run relation.

This is the theorem the facet's freedom rests on, at a concrete process: any
transition of `oneShot` into a terminal state carries an exact classification of
whatever demands were outstanding.
-/
theorem oneShot_terminations_dispose_exactly :
    TerminalTransitionsHaveExactDisposition oneShotRemainder () :=
  terminal_transitions_have_exact_disposition oneShotRemainder ()

/-! ## A termination contract under the strictest law -/

/-- Why this process might be asked to stop. -/
inductive Reason
  | shutdown
  deriving DecidableEq, Repr

/--
`oneShot` stops safely only when it is finished, and only holding nothing.

The second conjunct is the one that matters. `oneShotRemainder` is
`TerminalRemainderLaw.strict`, which accepts only an empty remainder, so a
contract that permitted an orderly stop while holding anything would owe a
disposition the law rejects. `permitted` indexes on the outstanding bag for
exactly this reason.
-/
def oneShotStops : ProcessTerminationContract oneShotAcceptance.terminalRemainder () where
  SafePoint := fun state => state = true
  Cause := Reason
  requested := fun _ _ => True
  permitted := fun mode _ state outstanding =>
    match mode with
    | .faulted => True
    | _ => state = true ∧ outstanding = 0
  noArbitraryDeath := by
    intro mode cause state outstanding allowed
    cases mode with
    | faulted => exact Or.inr rfl
    | cooperative => exact Or.inl allowed.1
    | forcedAtSafePoint => exact Or.inl allowed.1
  disposition := by
    intro mode cause state outstanding allowed orderly
    have finished : state = true ∧ outstanding = 0 := by
      cases mode with
      | faulted => exact absurd rfl orderly
      | cooperative => exact allowed
      | forcedAtSafePoint => exact allowed
    refine
      { result := ()
        terminal := finished.1
        classification :=
          { resolved := 0
            transferred := 0
            pending := 0
            partition := by rw [finished.2]; simp
            permitted := ⟨rfl, rfl, rfl⟩ } }

/-! ## The cancellable facet carries it -/

/-- A `oneShot` that promises cooperative cancellation, backed by that contract. -/
def cancellableOneShot :
    TerminationFacet oneShotCorrect () NoPolicy NoPolicy
      (.cooperative oneShotStops.Cause) :=
  .cooperative oneShotStops

/--
**The contract comes back out, unchanged.**

§3: "the bridge cannot discard it after manufacturing a liveness contract." A
facet that stored a derived fact instead of the contract could not satisfy this,
and could not be written against the constructor at all.
-/
theorem cancellable_oneShot_gives_its_contract_back :
    cancellableOneShot.retainedContract = some oneShotStops := rfl

/--
**And a consumer derives that it cannot force a stop wherever it likes.**

§3: a supervisor "cannot manufacture a safe forced stop". Here that is derived
*from the facet* rather than supplied alongside it, which is what retaining the
whole contract buys.
-/
theorem supervisor_learns_it_cannot_force_a_stop :
    ∃ contract : ProcessTerminationContract oneShotAcceptance.terminalRemainder (),
      cancellableOneShot.retainedContract = some contract ∧
        ∀ (mode : TerminationMode) (cause : contract.Cause) (state : Bool)
          (outstanding : Bag oneShot.Demand),
          ¬ contract.SafePoint state →
          contract.permitted mode cause state outstanding → mode = .faulted :=
  cancellableOneShot.cancellable_facet_forbids_arbitrary_death
    (Or.inl ⟨oneShotStops.Cause, rfl⟩)

/-! ## And what it rejects -/

/-- Before it has finished, `oneShot` is not at a safe point. -/
theorem working_is_not_safe : ¬ oneShotStops.SafePoint false := by
  have notTrue : ¬ (false = true) := by decide
  exact notTrue

/--
So an unfinished `oneShot` may only fault.

The concrete form of the theorem above: at `false`, `forcedAtSafePoint` and
`cooperative` are both unavailable, and the fault path is the only way out.
-/
theorem only_a_fault_while_working {mode : TerminationMode}
    {outstanding : Bag oneShot.Demand}
    (allowed : oneShotStops.permitted mode .shutdown false outstanding) :
    mode = .faulted :=
  oneShotStops.only_a_fault_happens_off_a_safe_point working_is_not_safe allowed

/-- And a fault genuinely is permitted there, so the rejection is not vacuous. -/
theorem a_fault_is_permitted_while_working :
    oneShotStops.permitted .faulted .shutdown false 0 := trivial

end Grass.Process.Tests.Facet
