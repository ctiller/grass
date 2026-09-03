import Grass.Process.Termination
import Tests.Process.M1Fixtures

/-!
# Typed termination, and the stop that cannot be authored

`Grass/Process/Termination.lean` claims `noArbitraryDeath` is the field that
stops the contract being decoration. A field is worth what it rejects, so this
file builds a contract that satisfies it and then exhibits the one that cannot
exist.

* `countdownStops` is a real contract over `countdown`: stopping is safe exactly
  where it has reached zero, and every permitted orderly stop has an exact
  disposition.
* `forced_stop_midway_is_impossible` is the rejection, stated over an arbitrary
  contract. A contract permitting `forcedAtSafePoint` at a state it does not
  call safe cannot exist, because `noArbitraryDeath` has no way to discharge it.
* `a_fault_may_be_permitted_anywhere` is why that rejection is not vacuous: the
  mode that *is* allowed off a safe point is exactly the one `docs/PROCESS.md`
  §3 names as the separately modelled containment path.

The contrast between those two is the module's whole content. Rejecting all
three modes off a safe point would forbid faults, which is a fiction rather than
typed termination; rejecting none would be "let it crash".

This fixture is also what found two uninhabitability defects in the module's
first draft — see its note. Writing it was the check; reading the module was
not.
-/

namespace Grass.Process.Tests.Termination

open Grass.Process
open Grass.Process.Tests

/-! ## A contract over `countdown` -/

/-- Why this process might be asked to stop. -/
inductive Reason
  | shutdown
  deriving DecidableEq, Repr

/--
Stopping is safe exactly at zero.

`countdown`'s terminal states are `state = 0`, so this contract says the process
may be stopped in an orderly way only where it was going to finish anyway. That
is the strongest safe-point claim available for a countdown, and the one a
reviewer should expect it to make.

An orderly stop is permitted only when the outstanding bag is one the
specification's remainder law accepts — `countdownRemainder` takes up to two
pending ticks — which is why `permitted` indexes on the bag.
-/
def countdownStops : ProcessTerminationContract countdownRemainder 3 where
  SafePoint := fun state => state = 0
  Cause := Reason
  requested := fun _ _ => True
  permitted := fun mode _ state outstanding =>
    match mode with
    | .faulted => True
    | _ => state = 0 ∧ (∀ demand ∈ outstanding, demand = Demand.tick) ∧
        outstanding.card ≤ 2
  noArbitraryDeath := by
    intro mode cause state outstanding allowed
    cases mode with
    | faulted => exact Or.inr rfl
    | cooperative => exact Or.inl allowed.1
    | forcedAtSafePoint => exact Or.inl allowed.1
  disposition := by
    intro mode cause state outstanding allowed orderly
    refine
      { result := ()
        terminal := ?_
        classification :=
          { resolved := 0
            transferred := 0
            pending := outstanding
            partition := by simp
            permitted := ?_ } }
    · cases mode with
      | faulted => exact absurd rfl orderly
      | cooperative => exact allowed.1
      | forcedAtSafePoint => exact allowed.1
    · cases mode with
      | faulted => exact absurd rfl orderly
      | cooperative => exact ⟨rfl, rfl, allowed.2.1, allowed.2.2⟩
      | forcedAtSafePoint => exact ⟨rfl, rfl, allowed.2.1, allowed.2.2⟩

/-! ## What it says -/

/-- A cooperative stop at zero is permitted, holding one pending tick. -/
theorem cooperative_stop_at_zero :
    countdownStops.permitted .cooperative .shutdown 0 (Bag.singleton Demand.tick) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro demand present
    simpa [Bag.singleton] using present
  · simp [Bag.singleton]

/-- And it happens at a safe point, which is `noArbitraryDeath` read forwards. -/
theorem cooperative_stop_is_safe : countdownStops.SafePoint 0 :=
  countdownStops.cooperative_termination_is_safe cooperative_stop_at_zero

/-- Its disposition accounts for the pending tick rather than dropping it. -/
theorem cooperative_stop_accounts_for_the_tick :
    (Bag.singleton Demand.tick).card =
      (countdownStops.disposition .cooperative .shutdown 0 _
        cooperative_stop_at_zero (by decide)).classification.resolved.card +
      (countdownStops.disposition .cooperative .shutdown 0 _
        cooperative_stop_at_zero (by decide)).classification.transferred.card +
      (countdownStops.disposition .cooperative .shutdown 0 _
        cooperative_stop_at_zero (by decide)).classification.pending.card :=
  countdownStops.orderly_stops_account_for_everything cooperative_stop_at_zero (by decide)

/-! ## What it rejects -/

/--
**A forced stop away from a safe point cannot be authored.**

Stated over an arbitrary contract, because it is a property of the type rather
than of `countdownStops`. `docs/PROCESS.md` §3: forced termination "never
retroactively validates arbitrary partially executed instructions", and a
contract that permitted it would have no way to discharge `noArbitraryDeath` —
`forcedAtSafePoint` is not `faulted`, so the disjunction collapses.
-/
theorem forced_stop_midway_is_impossible {p : ProcessSpec.{0, 0}}
    {law : TerminalRemainderLaw p} {request : p.Request}
    (contract : ProcessTerminationContract law request)
    {cause : contract.Cause} {state : p.State} {outstanding : Bag p.Demand}
    (notSafe : ¬ contract.SafePoint state)
    (allowed : contract.permitted .forcedAtSafePoint cause state outstanding) :
    False :=
  notSafe (contract.forced_termination_is_safe allowed)

/-- The same for a cooperative stop: being asked nicely is not a safe point. -/
theorem cooperative_stop_midway_is_impossible {p : ProcessSpec.{0, 0}}
    {law : TerminalRemainderLaw p} {request : p.Request}
    (contract : ProcessTerminationContract law request)
    {cause : contract.Cause} {state : p.State} {outstanding : Bag p.Demand}
    (notSafe : ¬ contract.SafePoint state)
    (allowed : contract.permitted .cooperative cause state outstanding) :
    False :=
  notSafe (contract.cooperative_termination_is_safe allowed)

/-- Mid-countdown is not a safe point, which the next theorem needs. -/
theorem two_is_not_safe : ¬ countdownStops.SafePoint 2 := by
  have notZero : ¬ ((2 : Nat) = 0) := by decide
  exact notZero

/--
**But a fault may be permitted anywhere, and this contract permits it.**

Why the two rejections above are not vacuous. `countdownStops` allows a fault at
state 2, which is not a safe point — and that is `docs/PROCESS.md` §3's
separately modelled containment path, not a hole. A design that rejected this
too would forbid faults altogether.
-/
theorem a_fault_may_be_permitted_anywhere :
    countdownStops.permitted .faulted .shutdown 2 0 ∧
      ¬ countdownStops.SafePoint 2 :=
  ⟨trivial, two_is_not_safe⟩

/-- So at an unsafe state, `faulted` is the only mode this contract permits. -/
theorem only_a_fault_at_two {mode : TerminationMode} {outstanding : Bag Demand}
    (allowed : countdownStops.permitted mode .shutdown 2 outstanding) :
    mode = .faulted :=
  countdownStops.only_a_fault_happens_off_a_safe_point two_is_not_safe allowed

end Grass.Process.Tests.Termination
