import Grass.Process.Correct
import Tests.Process.M1Fixtures

/-!
# `countdown` is correct, and progresses, under its own remainder law

This file exists because it could not be written.

`Tests/Process/M1Fixtures.lean` opens by saying its point is that "a reviewer
can read one small process and check that the linearity claims in
`Grass/Process/Run.lean` are true of a thing that actually exists". Local
adversarial review then showed that `countdown` — that process — had **neither**
a `ProcessCorrect` nor a `MeetsProcessProgress`, for three independent reasons,
and that only `oneShot`, a two-state machine that terminates on its first step,
had either.

* `ProcessCorrect.terminalNoStep` quantified the request existentially — *terminal
  for some request implies no step for any* — while `p.Step` cannot see the
  request. That excluded every process whose `Terminal` depends on the request,
  and it excluded `countdown` for a second reason too: `countdown` accepted
  `.external .wake` at state 0, its own terminal state.
* `MeetsProcessProgress.productive` was quantified over every step from a state
  satisfying a caller's invariant, including steps no run can take.
  `countdown`'s `.result .log` case answers a demand the process never issues,
  leaves the state alone and reissues a `tick` — so it progresses under no
  measure, and the record was empty because of a step that cannot happen.
* `MeetsProcessProgress.notStuck` could not be discharged against
  `countdownRemainder` without knowing how many occurrences a reachable state
  holds.

All three are fixed, and this file is the check that they are. It is
deliberately a *positive* fixture: the corpus already had negative ones, and
none of them noticed that the record they were negative about was
uninhabitable.

## The run invariant, and the retraction it forced

An earlier version of this file used `TerminalRemainderLaw.unconstrained` and
said `countdownRemainder` made `countdown` stuck — that a run of request 3
"reaches state 0 holding three ticks", where the law refuses the partition.
**That is false**, and a second review pass built the counterexample: `countdown`
consumes exactly one occurrence per settling step and decrements the state on the
same step, `log` is never issued into the bag, and `.external .wake` moves
neither. So `outstanding.card = state` is a run invariant, and at state 0 the bag
is empty and the law grants the empty partition.

`Linked` below is that invariant, and having it is what lets this file use
`countdown`'s own law rather than one that permits everything. Without it the
headline was "`countdown` is correct" scoped to an acceptance no other fixture
in the corpus uses. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.46 recorded the
false claim and now records the retraction.
-/

namespace Grass.Process.Tests.CountdownCorrect

open Grass.Process
open Grass.Process.Tests

/-! ## The measure -/

/--
How much counting is left.

It ignores the outstanding bag, which is legal and is worth a sentence, because
`ProcessMeasure.rank` takes the bag precisely so that a process whose *state*
does not move can still descend. `countdown`'s does move: every settling step
decrements it. The bag would do as well — `linked` proves the two are equal along
every run — and the state is what a reader of this process expects.

It is now genuinely consulted. Under the four-disjunct `StepProgresses` every
`countdown` event was entropy or a settlement, so `rank := fun _ _ => 0` would
have done; with the demand-result disjunct folded into the measure, the `.result
.tick` and `.interrupted` cases are discharged by this rank descending and by
nothing else.
-/
def countdownMeasure : ProcessMeasure countdown where
  Rank := Nat
  lt := Nat.lt
  wellFounded := Nat.lt_wfRel.wf
  rank := fun state _ => state

/-! ## The acceptance: `countdown`'s own remainder law -/

/--
Everything is accepted, and the terminal remainder is the one
`Tests/Process/M1Fixtures.lean` presents as the interesting law.

`Demanded := fun _ => False` is the strict choice, so nothing below is
discharged by the emission disjunct. Note that *every* acceptance in this
repository makes that choice, so `StepProgresses`'s third disjunct is
unexercised in both directions corpus-wide;
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.49 carries it.
-/
@[reducible] def countdownAcceptance : ProcessAcceptance countdown where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  ViewAccepts := fun _ _ _ => True
  DemandsWellFormed := fun _ => True
  Demanded := fun _ => False
  terminalRemainder := countdownRemainder

/-! ## The run invariant -/

/-- A bag of no occurrences is the empty bag. -/
theorem bag_card_zero {α : Type} {bag : Bag α} (empty : bag.card = 0) : bag = 0 := by
  induction bag using Quotient.inductionOn with
  | _ elements =>
    cases elements with
    | nil => rfl
    | cons _ _ => exact (Nat.succ_ne_zero _ empty).elim

/--
**What a reachable `countdown` run holds.**

Every outstanding occurrence is a `tick`, and there are exactly as many of them
as the state counts. Both halves are needed and neither follows from the other:
the first is what makes `.result .log` unreachable, the second is what makes the
terminal partition legal under `countdownRemainder`.
-/
def Linked (request : Nat) : ProcessRunState countdown request → Prop
  | .running state outstanding _ =>
    (∀ demand ∈ outstanding, demand = Demand.tick) ∧ outstanding.card = state
  | .terminal _ _ _ => True

/--
**And it holds along every execution.**

By induction over `Reachable`. `Initial` issues `replicate request tick` and
sets the state to `request`, which is the base case; `.external .wake` moves
neither side; `.result .tick` and `.interrupted` each consume exactly one
occurrence and decrement the state together; `.result .log` is refuted by the
first half of the induction hypothesis, which is the point.
-/
theorem linked {request : Nat} {segmented : Segmented countdown.Observation}
    {runState : ProcessRunState countdown request}
    (reached : Reachable countdownAcceptance.terminalRemainder request segmented runState) :
    Linked request runState := by
  induction reached with
  | initial isInitial =>
    cases isInitial with
    | running initial =>
      obtain ⟨isState, isIssued, _⟩ := initial
      subst isState; subst isIssued
      refine ⟨?_, by simp⟩
      intro demand member
      simp at member
      exact member.2
  | initialTerminal _ => trivial
  | step _ transition _ ih =>
    cases transition with
    | @step _ _ _ issued _ _ event settlesNothing stepped =>
      obtain ⟨_, body⟩ := stepped
      match event, settlesNothing, body with
      | .external .wake, _, ⟨isAfter, isIssued, _⟩ =>
        subst isAfter; subst isIssued
        exact ⟨fun d m => ih.1 d (by simpa using m), by simpa using ih.2⟩
      | .fault fault, _, _ => exact fault.elim
      | .environmentViolation violation, _, _ => exact violation.elim
    | @settle _ _ _ remainder issued _ _ event demand settlesDemand consume stepped =>
      obtain ⟨_, body⟩ := stepped
      have inBag : demand ∈ (_ : Bag countdown.Demand) := consume.mem
      have onlyTicks : ∀ d ∈ remainder, d = Demand.tick := by
        intro d m
        exact ih.1 d (by rw [consume]; simpa using Or.inr m)
      have counted : remainder.card + 1 = _ := (consume.card).symm
      have ihCard : (_ : Bag countdown.Demand).card = _ := ih.2
      match event, settlesDemand, body with
      | .result .tick _, isDemand, ⟨isAfter, isIssued, _⟩ =>
        cases (Option.some.inj isDemand)
        subst isAfter; subst isIssued
        refine ⟨fun d m => onlyTicks d (by simpa using m), ?_⟩
        simp only [Bag.card_add, Bag.card_zero]
        omega
      | .result .log _, isDemand, _ =>
        cases (Option.some.inj isDemand)
        exact absurd (ih.1 Demand.log inBag) (by decide)
      | .interrupted d _, isDemand, ⟨isAfter, isIssued, _⟩ =>
        cases (Option.some.inj isDemand)
        subst isAfter; subst isIssued
        refine ⟨fun x m => onlyTicks x (by simpa using m), ?_⟩
        simp only [Bag.card_add, Bag.card_zero]
        omega
    | terminate _ _ => trivial

/--
**So a `log` result is never deliverable.**

The corollary `productive` runs on, and the reason `MeetsProcessProgress`
quantifies that field over reachable run states. `countdown`'s `.result .log`
case is a silent, state-preserving, demand-*reissuing* step — the exact shape
`Grass/Process/Progress.lean` now excludes — and it is fine for it to be
excluded, because no run can take it.
-/
theorem log_is_never_deliverable {request : Nat}
    {segmented : Segmented countdown.Observation} {state : countdown.State}
    {outstanding : Bag countdown.Demand} {observations : Trace countdown.Observation}
    (reached : Reachable countdownAcceptance.terminalRemainder request segmented
      (.running state outstanding observations))
    (result : countdown.Result Demand.log) :
    ¬ EventDeliverable outstanding (.result Demand.log result) := by
  intro deliverable
  exact absurd ((linked reached).1 Demand.log (deliverable Demand.log rfl)) (by decide)

/-! ## It progresses -/

/--
**`countdown` meets its progress contract, under `countdownRemainder`.**

`productive` is where the fixes show. `.external .wake` carries entropy;
`.result .tick` and `.interrupted` each decrement the state, which is the measure
descending; `.result .log` does neither and is discharged by
`log_is_never_deliverable`, through `eventDeliverable_of_successorBag`.

`notStuck`'s terminal branch is where the invariant earns its keep. At state 0
the bag is empty, so the partition `resolved = 0, transferred = 0, pending = 0`
is legal under a law that permits at most two pending `tick`s — the branch used
to be discharged by `trivial` against a law that permitted everything.
-/
def countdownProgress (request : Nat) :
    MeetsProcessProgress countdown countdownAcceptance (fun _ => True) request where
  measure := countdownMeasure
  handlesEveryEvent := by
    rintro _ state _ _ event _ notTerminal _
    have running : state ≠ 0 := by
      intro isZero
      exact notTerminal ⟨(), isZero⟩
    match event with
    | .external .wake => exact ⟨state, 0, [], running, rfl, rfl, rfl⟩
    | .result .tick _ =>
      exact ⟨state - 1, 0, [Observation.beep], running, rfl, rfl, rfl⟩
    | .result .log _ =>
      exact ⟨state, Bag.ofList [Demand.tick], [], running, rfl, rfl, rfl⟩
    | .interrupted _ _ => exact ⟨state - 1, 0, [], running, rfl, rfl, rfl⟩
    | .fault fault => exact fault.elim
    | .environmentViolation violation => exact violation.elim
  notStuck := by
    intro segmented state outstanding observations reached
    by_cases finished : state = 0
    · refine Or.inl ⟨(), finished, ⟨?_⟩⟩
      have empty : outstanding = 0 :=
        bag_card_zero (by rw [(linked reached).2, finished])
      refine
        { resolved := 0
          transferred := 0
          pending := 0
          partition := by rw [empty]; simp
          permitted := ⟨rfl, rfl, by simp, by decide⟩ }
    · exact Or.inr ⟨.external .wake,
        eventDeliverable_of_settles_none (by simp),
        state, 0, [], finished, rfl, rfl, rfl⟩
  productive := by
    intro _ state outstanding _ after _ event issued _ reached _ successor stepped
    obtain ⟨running, body⟩ := stepped
    match event, successor, body with
    | .external entropy, _, _ => exact Or.inl ⟨entropy, rfl⟩
    | .result .tick _, _, ⟨isAfter, _, _⟩ =>
      refine Or.inr (Or.inr ?_)
      subst isAfter
      show state - 1 < state
      exact Nat.sub_lt (Nat.pos_of_ne_zero running) Nat.one_pos
    | .result .log result, successor, _ =>
      exact absurd (eventDeliverable_of_successorBag successor)
        (log_is_never_deliverable reached result)
    | .interrupted _ _, _, ⟨isAfter, _, _⟩ =>
      refine Or.inr (Or.inr ?_)
      subst isAfter
      show state - 1 < state
      exact Nat.sub_lt (Nat.pos_of_ne_zero running) Nat.one_pos
    | .fault fault, _, _ => exact fault.elim
    | .environmentViolation violation, _, _ => exact violation.elim

/-! ## And it is correct -/

/--
**`countdown` is correct, with a trivial invariant.**

`terminalNoStep` is the field that could not be discharged. It now asks about
states terminal for *every* request, and `countdown.Step` requires `state ≠ 0`,
so the two meet: a state the specification calls finished, whatever it was
started with, has no transition.

Both halves of that sentence were wrong before. The field asked the wrong
question, and the process kept working after it had finished.

What this fixture does **not** witness is the weakening itself.
`countdown.Terminal` ignores its request, so "terminal for every request" and
"terminal for some request" coincide for it, and `countdown` discharges the old
stronger field just as well — `terminal_for_one_is_terminal_for_all` below says
so. `Tests/Process/PrefixFixtures.lean` carries the request-dependent process
that separates them.
-/
def countdownCorrect : ProcessCorrect countdown countdownAcceptance where
  Invariant := fun _ => True
  initial := by intros; trivial
  initialDemands := by intros; trivial
  preserved := by intros; trivial
  demandsWellFormed := by intros; trivial
  terminal := by intros; trivial
  terminalNoStep := by
    rintro state _ _ _ _ _ isTerminal ⟨running, _⟩
    exact running (isTerminal 0)
  viewAccepts := by
    intro facet hasView
    exact absurd hasView (by simp [countdown])
  observationsAccept := by intros; trivial
  progress := countdownProgress

/--
**`countdown` cannot tell the weakened terminal law from the strong one.**

`countdown.Terminal` does not read its request, so the existential and universal
forms of `ProcessCorrect.terminalNoStep` coincide here. Stated so that a reader
does not mistake `countdownCorrect` for evidence about the weakening; the
process that does separate them is in `Tests/Process/PrefixFixtures.lean`.
-/
theorem terminal_for_one_is_terminal_for_all {state : Nat} {result : Unit}
    (isTerminal : ∃ request, countdown.Terminal request state result)
    (request : Nat) : countdown.Terminal request state result :=
  isTerminal.elim fun _ terminal => terminal

end Grass.Process.Tests.CountdownCorrect
