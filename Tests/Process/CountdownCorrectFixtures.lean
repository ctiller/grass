import Grass.Process.Correct
import Tests.Process.M1Fixtures

/-!
# `countdown` is correct, and progresses

This file exists because it could not be written.

`Tests/Process/M1Fixtures.lean` opens by saying its point is that "a reviewer
can read one small process and check that the linearity claims in
`Grass/Process/Run.lean` are true of a thing that actually exists". Local
adversarial review then showed that `countdown` — that process — had **neither**
a `ProcessCorrect` nor a `MeetsProcessProgress`, for two independent reasons,
and that only `oneShot`, a two-state machine that terminates on its first step,
had either.

* `ProcessCorrect.terminalNoStep` quantified the request existentially — *terminal
  for some request implies no step for any* — while `p.Step` cannot see the
  request. That excluded every request-parameterised process outright, and it
  excluded `countdown` for a second reason too: `countdown` accepted
  `.external .wake` at state 0, its own terminal state.
* `MeetsProcessProgress.productive` offered three disjuncts where §7 lists an
  "external/**demand-result** frontier", and the demand-result half was missing.
  `countdown`'s `.result .log` case consumes a `log` occurrence and issues a
  `tick` without moving the state — real progress that
  `ProcessMeasure.rank : p.State → Rank` structurally cannot see.

Both are fixed. This file is the check that they are, and it is deliberately a
*positive* fixture: the corpus already had negative ones, and none of them
noticed that the record they were negative about was uninhabitable.
-/

namespace Grass.Process.Tests.CountdownCorrect

open Grass.Process
open Grass.Process.Tests

/-! ## The measure -/

/-- How much counting is left. -/
def countdownMeasure : ProcessMeasure countdown where
  Rank := Nat
  lt := Nat.lt
  wellFounded := Nat.lt_wfRel.wf
  rank := id

/-! ## An acceptance that asks for nothing but the remainder law -/

/--
Everything is accepted, and the terminal remainder is unconstrained.

Not `countdownRemainder`, and the reason is a third defect the same review pass
uncovered. `countdownRemainder` permits at most two pending `tick`s, and
`countdown.Initial` issues `replicate request tick` — so a run started with
three reaches state 0 holding three ticks, where it can neither terminate (the
law refuses the partition) nor step (state 0 is terminal, and terminal states do
not step). `MeetsProcessProgress.notStuck` is then unsatisfiable, and `countdown`
had no progress record for that reason too, independently of the other two.

`TerminalRemainderLaw.unconstrained` is honestly labelled in
`Grass/Process/Spec.lean` as the escape it is. Using it here is the right trade
for a fixture whose job is to show the *records* are inhabitable;
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.46 records the stuckness, which is a
fact about the specification's law and not about this layer.
-/
@[reducible] def countdownAcceptance : ProcessAcceptance countdown where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  ViewAccepts := fun _ _ => True
  DemandsWellFormed := fun _ => True
  Demanded := fun _ => False
  terminalRemainder := TerminalRemainderLaw.unconstrained countdown

/-! ## It progresses -/

/--
**`countdown` meets its progress contract.**

`productive` is where the fix shows. Every event of this process falls into one
of the two frontier disjuncts: `.external .wake` carries entropy, and
`.result`/`.interrupted` settle an outstanding demand. Before the demand-result
disjunct existed, the `.result .log` case — which leaves the state alone — could
not be discharged at all, so this definition did not typecheck.
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
    rintro _ state outstanding _ _
    by_cases finished : state = 0
    · refine Or.inl ⟨(), finished, ⟨?_⟩⟩
      exact
        { resolved := 0
          transferred := 0
          pending := outstanding
          partition := by simp
          permitted := trivial }
    · exact Or.inr ⟨.external .wake,
        eventDeliverable_of_settles_none (by simp),
        state, 0, [], finished, rfl, rfl, rfl⟩
  productive := by
    rintro state after event issued emitted _ ⟨running, stepped⟩
    match event with
    | .external entropy => exact Or.inl ⟨entropy, rfl⟩
    | .result demand _ => exact Or.inr (Or.inl ⟨demand, rfl⟩)
    | .interrupted demand _ => exact Or.inr (Or.inl ⟨demand, rfl⟩)
    | .fault fault => exact fault.elim
    | .environmentViolation violation => exact violation.elim

/-! ## And it is correct -/

/--
**`countdown` is correct, with a trivial invariant.**

`terminalNoStep` is the field that could not be discharged. It now asks about
states terminal for *every* request, and `countdown.Step` requires `state ≠ 0`,
so the two meet: a state the specification calls finished, whatever it was
started with, has no transition.

Both halves of that sentence were wrong before. The field asked the wrong
question, and the process kept working after it had finished.
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

end Grass.Process.Tests.CountdownCorrect
