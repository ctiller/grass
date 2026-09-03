import Grass.Process.Correct

/-!
# An acceptance that actually accepts something

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.62: of `ProcessCorrect`'s nine fields,
five had no non-vacuous instance anywhere in this repository. Every
`ProcessAcceptance` in the corpus set `TraceAccepts`, `DemandsWellFormed`,
`TerminalAccepts` and `ViewAccepts` to `fun _ => True`, so `initialDemands`,
`demandsWellFormed`, `terminal`, `observationsAccept` and `viewAccepts` were
discharged by `trivial` or `absurd` in all five correctness fixtures. §10.49 adds
a sixth: `Demanded` was `fun _ => False` everywhere, so `StepProgresses`'s
emission disjunct had never fired. And
`TerminalDemandClassification.transferred` was `0` at all six of its
construction sites, so §2's three-way partition had only ever been used two ways.

`hiccup` is the process that exercises them. It is not a realistic process — it
is a list of the constraints that had never been constrained, made into one small
machine:

* **`TraceAccepts`** forbids a `blip`, and `hiccup` never emits one, so
  `observationsAccept` is a claim about every reachable prefix and `no_blips` is
  the induction that discharges it. It is an honest induction and it is weaker
  than it looks: no `hiccup.Step` can emit a `blip` at all, so every case is
  settled by the literal shape of `emitted` rather than by anything about the
  state. A reviewer checked. What it does show is that the field is not
  discharged by `trivial`, which is what it was everywhere before.
* **`Demanded`** is "the observation is a `beep`", and `hiccup`'s `.result` case
  emits one. That is *not* the same as exercising it, and the first version of
  this file said it was: a reviewer rebuilt `productive` discharging all three
  cases from the measure alone, and rebuilt `hiccupCorrect` against an acceptance
  with `Demanded := fun _ => False`. §10.49 is not closed and §10.62's claim
  about it is withdrawn.

  The reason is worth stating, because it is not a gap in this fixture. A step
  that *requires* the emission disjunct is one that moves neither the state nor
  the outstanding bag and is not entropy — and a process that can take such a step
  repeatedly is a livelock. `Tests/Process/ChatterFixtures.lean` is that process,
  and it has a full `ProcessCorrect`. The emission disjunct can only be made
  load-bearing by something the layer should be excluding.
* **`LogicalFault`** is inhabited, and `hiccup` can take a silent fault step. So
  `MeetsProcessProgress.silent_fault_decreases` has an applicable process, which
  §10.62 records it did not: every specification here had
  `LogicalFault := PEmpty`, and the module note's motivating case — "a process
  that faults in a loop, emits nothing, and decreases no measure" — had no
  fixture in either direction.
* **`TerminalAccepts`** requires the result to be `true`, and `hiccup.Terminal`'s
  second conjunct is what supplies it — so `ProcessCorrect.terminal` is
  discharged by `.2` and the acceptance separates nothing this process can do.
  A reviewer said so plainly and is right. `TerminalAccepts` is a *refutation*
  tool: its non-vacuity is shown by a process whose terminal result the
  specification rejects, which is `unwanted_results_are_refused` below rather
  than anything about `hiccup`.
* **`DemandsWellFormed`** bounds an issued bag at one occurrence.
* **`transferred`** is where `hiccup`'s outstanding handle goes at the end: its
  remainder law permits *nothing* resolved and *nothing* pending, so the
  classification `notStuck` builds has a non-empty middle part and could not have
  a non-empty other one. `a_run_finishes_holding_the_handle` is the reachable
  instance, which the first version of this file left out — it stated the law
  algebra and not the run.

  This one is load-bearing in the strong sense: swap the remainder law for
  `TerminalRemainderLaw.strict` and `hiccup` has no progress record at all, since
  at state 0 holding the handle it can neither step nor terminate. A reviewer
  checked that too.

What it does not close is `ViewAccepts`. `ProcessSpec.view` is `none` in every
specification in the repository and `ViewFacet` is constructed nowhere; that is
§10.56, and it is a specification-layer question rather than one this file can
answer by picking a harder acceptance.
-/

namespace Grass.Process.Tests.Rich

open Grass.Process

/-! ## The vocabulary -/

/-- Two observations, one of which the specification refuses to see. -/
inductive Sound
  | beep
  | blip
  deriving DecidableEq, Repr

/--
One demand: a handle the process holds and does not have to give back.

`LogicalFault` and `EnvironmentViolation` are both inhabited, and both were
`PEmpty` in every specification in this repository — so `ProcessEvent.fault` and
`ProcessEvent.environmentViolation` had no instance anywhere,
`ProcessRunTransition.stepFault` and `stepEnvironmentViolation` were dead
introduction rules, and every `Step` case for them in every fixture was an
elimination. A reviewer found the second of those after the first was closed;
this closes both.
-/
@[reducible] def hiccupVocabulary : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := Unit
  Result := fun _ => Unit
  Observation := Sound
  InterruptReason := PEmpty
  LogicalFault := Unit
  EnvironmentViolation := Unit

/--
Count down, beeping; a glitch costs a count and says nothing.

The `.fault` case is the point of the process, twice over. Every other
specification in the corpus has `LogicalFault := PEmpty`, so the one thing
`Grass/Process/Progress.lean`'s module note says the measure is *for* — a silent
fault loop — had never been written down. And it is the only step that *issues*
anything: a glitch schedules a retry. Without that, every step of every process
in this corpus issued the empty bag and `ProcessCorrect.demandsWellFormed` was
discharged for the zero bag exactly as it always had been, which a reviewer
pointed out after the first version of this file claimed to have closed it.
-/
@[reducible] def hiccup : ProcessSpec.{0, 0} where
  vocabulary := hiccupVocabulary
  Request := Nat
  State := Nat
  TerminalResult := Bool
  Initial := fun request state issued emitted =>
    state = request ∧ issued = Bag.ofList [()] ∧ emitted = []
  Terminal := fun _ state result => state = 0 ∧ result = true
  Step := fun state event after issued emitted =>
    state ≠ 0 ∧
    match event with
    | .external _ => after = state - 1 ∧ issued = 0 ∧ emitted = [Sound.beep]
    | .result _ _ => after = state - 1 ∧ issued = 0 ∧ emitted = [Sound.beep]
    | .fault _ => after = state - 1 ∧ issued = Bag.ofList [()] ∧ emitted = []
    | .environmentViolation _ => after = state - 1 ∧ issued = 0 ∧ emitted = []
    | .interrupted _ reason => reason.elim
  view := none

/-! ## The law, and the acceptance -/

/--
**The handle is transferred, not resolved and not left pending.**

`resolved = 0 ∧ pending = 0` is the whole law, and it is what forces
`TerminalDemandClassification.transferred` to hold the outstanding bag. Every
other remainder law in this corpus is satisfied by the all-zero partition, so
the middle part of §2's three-way split had never carried anything.
-/
@[reducible] def hiccupRemainder : TerminalRemainderLaw hiccup where
  Accepts := fun _ _ _ resolved _ pending => resolved = 0 ∧ pending = 0

/--
An acceptance where every field is a constraint.

Read the five together: this is the shape §10.62 says the corpus was missing.
-/
@[reducible] def hiccupAcceptance : ProcessAcceptance hiccup where
  -- A run finishes successfully or not at all.
  TerminalAccepts := fun _ result => result = true
  -- And it never blips.
  TraceAccepts := fun trace => Sound.blip ∉ trace
  -- No step issues more than one occurrence.
  DemandsWellFormed := fun issued => issued.card ≤ 1
  ViewAccepts := fun _ _ _ => True
  -- A beep is what the specification asked for.
  Demanded := fun observation => observation = Sound.beep
  terminalRemainder := hiccupRemainder

/-! ## The run invariant the trace acceptance needs -/

/-- A `beep` segment is demanded; that is the disjunct nothing had exercised. -/
theorem beep_is_demanded : hiccupAcceptance.SegmentIsDemanded [Sound.beep] :=
  ⟨Sound.beep, List.mem_cons_self, rfl⟩

/--
**No reachable run has ever blipped.**

`ProcessCorrect.observationsAccept` is over *every reachable prefix*, so it is
not a fact about one state: it needs an induction over `Reachable`, and every
step has to be checked to emit only what the acceptance allows. That is the work
a trivial `TraceAccepts` was hiding.
-/
theorem no_blips {request : Nat} {segmented : Segmented hiccup.Observation}
    {runState : ProcessRunState hiccup request}
    (reached : Reachable hiccupAcceptance.terminalRemainder request segmented runState) :
    Sound.blip ∉ runState.history := by
  induction reached with
  | initial isInitial =>
    cases isInitial with
    | running initial => simp [ProcessRunState.history, initial.2.2]
  | initialTerminal isInitial =>
    cases isInitial with
    | terminal initial => simp [ProcessRunState.history, initial.2.2]
  | step _ transition _ ih =>
    cases transition with
    | @step _ _ _ _ emitted _ event _ stepped =>
      obtain ⟨_, body⟩ := stepped
      match event, body with
      | .external _, ⟨_, _, isEmitted⟩ =>
        subst isEmitted
        simp only [ProcessRunState.history] at ih ⊢
        simp only [List.mem_append, not_or]
        exact ⟨ih, by simp⟩
      | .fault _, ⟨_, _, isEmitted⟩ =>
        subst isEmitted
        simp only [ProcessRunState.history] at ih ⊢
        simpa using ih
      | .environmentViolation _, ⟨_, _, isEmitted⟩ =>
        subst isEmitted
        simp only [ProcessRunState.history] at ih ⊢
        simpa using ih
    | @settle _ _ _ _ _ _ emitted event _ _ _ stepped =>
      obtain ⟨_, body⟩ := stepped
      match event, body with
      | .result _ _, ⟨_, _, isEmitted⟩ =>
        subst isEmitted
        simp only [ProcessRunState.history] at ih ⊢
        simp only [List.mem_append, not_or]
        exact ⟨ih, by simp⟩
      | .interrupted _ reason, _ => exact reason.elim
    | terminate _ _ =>
      simpa [ProcessRunState.history] using ih

/-! ## It progresses -/

/-- How much counting is left. -/
def hiccupMeasure : ProcessMeasure hiccup where
  Rank := Nat
  lt := Nat.lt
  wellFounded := Nat.lt_wfRel.wf
  rank := fun state _ => state

/--
**`hiccup` meets its progress contract.**

Three events, three different disjuncts, which is why this fixture is worth
having: `.external` is entropy, `.result` emits a demanded `beep`, and `.fault`
is silent and pays with the measure. The corpus had no process that used the
second, and none that could use the third — every other specification's
`LogicalFault` is empty.
-/
def hiccupProgress (request : Nat) :
    MeetsProcessProgress hiccup hiccupAcceptance (fun _ => True) request where
  handlesEveryEvent := by
    rintro _ state _ _ event _ notTerminal _
    have running : state ≠ 0 := by
      intro isZero
      exact notTerminal ⟨true, isZero, rfl⟩
    match event with
    | .external _ => exact ⟨state - 1, 0, [Sound.beep], running, rfl, rfl, rfl⟩
    | .result _ _ => exact ⟨state - 1, 0, [Sound.beep], running, rfl, rfl, rfl⟩
    | .fault _ => exact ⟨state - 1, Bag.ofList [()], [], running, rfl, rfl, rfl⟩
    | .environmentViolation _ => exact ⟨state - 1, 0, [], running, rfl, rfl, rfl⟩
    | .interrupted _ reason => exact reason.elim
  notStuck := by
    intro _ state outstanding _ _
    by_cases finished : state = 0
    · refine Or.inl ⟨true, ⟨finished, rfl⟩, ⟨?_⟩⟩
      exact
        { resolved := 0
          transferred := outstanding
          pending := 0
          partition := by simp
          permitted := by exact ⟨rfl, rfl⟩ }
    · exact Or.inr ⟨.external (),
        eventDeliverable_of_settles_none (by simp),
        state - 1, 0, [Sound.beep], finished, rfl, rfl, rfl⟩
  measure := hiccupMeasure
  productive := by
    intro _ state _ _ after _ event _ _ _ _ _ stepped
    obtain ⟨running, body⟩ := stepped
    match event, body with
    | .external entropy, _ => exact Or.inl ⟨entropy, rfl⟩
    | .result _ _, ⟨_, _, isEmitted⟩ =>
      exact Or.inr (Or.inl (isEmitted ▸ beep_is_demanded))
    | .fault _, ⟨isAfter, _, _⟩ =>
      refine Or.inr (Or.inr ?_)
      subst isAfter
      show state - 1 < state
      exact Nat.sub_lt (Nat.pos_of_ne_zero running) Nat.one_pos
    | .environmentViolation _, ⟨isAfter, _, _⟩ =>
      refine Or.inr (Or.inr ?_)
      subst isAfter
      show state - 1 < state
      exact Nat.sub_lt (Nat.pos_of_ne_zero running) Nat.one_pos
    | .interrupted _ reason, _ => exact reason.elim

/-! ## And it is correct -/

/--
**`hiccup` is correct, and five of the nine fields do work.**

`initialDemands` and `demandsWellFormed` check a bound; `terminal` checks the
result; `observationsAccept` runs on `no_blips`; `progress` runs on
`hiccupProgress`. Only `viewAccepts` is vacuous, and §10.56 is why.
-/
def hiccupCorrect : ProcessCorrect hiccup hiccupAcceptance where
  Invariant := fun _ => True
  initial := by intros; trivial
  initialDemands := by
    rintro _ _ _ _ ⟨_, isIssued, _⟩
    rw [isIssued]
    simp
  preserved := by intros; trivial
  demandsWellFormed := by
    rintro _ _ event _ _ _ ⟨_, body⟩
    match event, body with
    | .external _, ⟨_, isIssued, _⟩ => rw [isIssued]; simp
    | .result _ _, ⟨_, isIssued, _⟩ => rw [isIssued]; simp
    | .fault _, ⟨_, isIssued, _⟩ => rw [isIssued]; simp
    | .environmentViolation _, ⟨_, isIssued, _⟩ => rw [isIssued]; simp
    | .interrupted _ reason, _ => exact reason.elim
  terminal := by
    rintro _ _ _ _ ⟨_, isTrue⟩
    exact isTrue
  terminalNoStep := by
    rintro state _ _ _ _ _ isTerminal ⟨running, _⟩
    exact running (isTerminal 0).1
  viewAccepts := by
    intro facet hasView
    exact absurd hasView (by simp [hiccup])
  observationsAccept := by
    intro _ _ _ reached
    exact no_blips reached
  progress := hiccupProgress

/-! ## What the fixture is for, stated -/

/-- **The middle part of the partition is not empty**, at any terminal state a
run reaches still holding its handle. -/
theorem the_handle_is_transferred (request state : Nat)
    (classification : TerminalDemandClassification hiccupRemainder request state true
      (Bag.ofList [()])) :
    classification.transferred = Bag.ofList [()] := by
  have partition := classification.partition
  rw [classification.permitted.1, classification.permitted.2] at partition
  simpa using partition.symm

/-- **And a silent fault of `hiccup` really does cost the measure**, which is the
theorem no process in the corpus could be handed. -/
theorem a_glitch_costs_a_count {request : Nat}
    {segmented : Segmented hiccup.Observation} {state : Nat}
    {outstanding : Bag hiccup.Demand} {observations : Trace hiccup.Observation}
    (reached : Reachable hiccupAcceptance.terminalRemainder request segmented
      (.running state outstanding observations))
    (running : state ≠ 0) :
    (hiccupProgress request).measure.Decreases state outstanding (state - 1)
      (outstanding + Bag.ofList [()]) :=
  (hiccupProgress request).silent_fault_decreases (fault := ()) reached trivial
    ⟨running, rfl, rfl, rfl⟩
    (fun demanded => by
      rcases demanded with ⟨_, member, _⟩
      exact absurd member (by simp))

/-! ## And a run that finishes still holding the handle -/

/--
**A run of request zero starts finished, and starts holding the handle.**

`hiccup.Initial` issues one occurrence whatever the request, and state 0 is
terminal — so the shortest run of this process is one that has nothing to do and
something outstanding, which is exactly the shape the remainder law is about.
-/
theorem a_run_starts_finished_holding_the_handle :
    Reachable hiccupAcceptance.terminalRemainder 0 (Segmented.empty.emit [])
      (.running 0 (Bag.ofList [()]) []) :=
  .initial (.running ⟨rfl, rfl, rfl⟩)

/--
**And it finishes by transferring it.**

The instance `the_handle_is_transferred` states as law algebra and did not
exhibit. `hiccupRemainder` permits nothing resolved and nothing pending, so the
only classification available at this run state puts the whole outstanding bag in
`transferred` — and `ProcessRunTransition.terminate` is the step that uses it.

Before this, `TerminalDemandClassification.transferred` was `0` at every
construction site in the corpus and §2's three-way partition had only ever been
used two ways.
-/
theorem a_run_finishes_holding_the_handle :
    ProcessRunTransition hiccupAcceptance.terminalRemainder 0
      (.running 0 (Bag.ofList [()]) []) (.terminal 0 true []) :=
  .terminate ⟨rfl, rfl⟩
    { resolved := 0
      transferred := Bag.ofList [()]
      pending := 0
      partition := by simp
      permitted := by exact ⟨rfl, rfl⟩ }

/--
**And an unwanted result is refused.**

What `TerminalAccepts` is for, which `hiccup` itself cannot show: its `Terminal`
supplies the acceptance's own condition, so the field separates nothing about
*this* process. It separates something about the class — a process that finishes
with `false` has no `ProcessCorrect` against this acceptance, because
`ProcessCorrect.terminal` would have to derive `false = true`.
-/
theorem unwanted_results_are_refused
    (correct : ProcessCorrect hiccup hiccupAcceptance)
    (state : Nat) (invariant : correct.Invariant state)
    (finished : hiccup.Terminal 0 state false) : False :=
  Bool.noConfusion (correct.terminal 0 state false invariant finished)

end Grass.Process.Tests.Rich
