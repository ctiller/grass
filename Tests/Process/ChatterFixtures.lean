import Grass.Process.Correct

/-!
# The livelock that logs

`Grass/Process/Progress.lean`'s module note lists three things
`no_infinite_silent_run` does not exclude: a process that routes its own work
through a self-delivered external event, a permissive `Demanded`, and a
specification with no initial state at all. `chatter` is a fourth shape, and it
is the one `ProcessAcceptance.Demanded`'s own docstring says the field exists to
prevent.

`chatter` faults forever. It never terminates, never moves its state, holds no
demands, and has no external events — so the entropy escape is unavailable to it
and so is the no-initial-state one. What it does have is a `Demanded` that picks
out one of two observation values, and a step that emits that value. Every step
therefore satisfies `StepProgresses`'s emission disjunct, and `chatterCorrect` is
a full `ProcessCorrect`.

`Demanded`'s docstring says the field exists so that "every process could satisfy
progress by logging" is false. This is a process satisfying progress by logging,
with a logged value the specification demands.

## Why this is not a fixable defect at this layer

`Demanded` is a predicate on observation *values*, so re-emitting one demanded
observation is indistinguishable from emitting a new one. Distinguishing them
needs a claim about the *trace* — that the run is making progress a specification
can see, not that each step emits something on a list — and that is a liveness
property over executions, which this layer has no model for. It is the same
shape as the entropy escape: the author supplies the predicate and the layer
cannot audit it.

What can be said, and is worth saying, is where the boundary now sits. Every
livelock this corpus knows about escapes through an author-supplied predicate:
`ExternalEvent` for the self-delivered tick, `Demanded` here. Nothing escapes
through the *measure*, which is what
`Tests/Process/SpinFixtures.lean` and `Tests/Process/OscillateFixtures.lean` cost
two rounds to establish. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.70 records it.

## And what it means for §10.62

`Tests/Process/RichAcceptanceFixtures.lean` was written to give the corpus an
acceptance whose fields are constraints, and claimed among other things to have
exercised `Demanded` for the first time. A reviewer refuted that — `hiccup`'s
measure covers every case, so the emission disjunct is chosen rather than
required. This file is why the claim cannot be repaired by picking a better
`hiccup`: a step that *requires* the emission disjunct moves neither the state
nor the bag and is not entropy, and a process that can take such a step
repeatedly is this one.
-/

namespace Grass.Process.Tests.Chatter

open Grass.Process

/-! ## The process -/

/-- Two observations, one of which the specification asked for. -/
inductive Chirp
  | beep
  | blip
  deriving DecidableEq, Repr

/--
No external events, no demands, and one fault.

`ExternalEvent := PEmpty` is what makes this a new shape rather than an instance
of the disclosed entropy escape: `chatter` cannot appeal to "the environment did
something" because in its vocabulary the environment cannot.
-/
@[reducible] def chatterVocabulary : ProcessVocabulary.{0} where
  ExternalEvent := PEmpty
  Demand := PEmpty
  Result := fun demand => demand.elim
  Observation := Chirp
  InterruptReason := PEmpty
  LogicalFault := Unit
  EnvironmentViolation := PEmpty

/-- Fault, beep, repeat. -/
@[reducible] def chatter : ProcessSpec.{0, 0} where
  vocabulary := chatterVocabulary
  Request := Unit
  State := Unit
  TerminalResult := PEmpty
  Initial := fun _ state issued emitted =>
    state = () ∧ issued = 0 ∧ emitted = []
  Terminal := fun _ _ result => result.elim
  Step := fun _ event after issued emitted =>
    match event with
    | .fault _ => after = () ∧ issued = 0 ∧ emitted = [Chirp.beep]
    | .external e => e.elim
    | .result demand _ => demand.elim
    | .interrupted demand _ => demand.elim
    | .environmentViolation violation => violation.elim
  view := none

/--
The acceptance, and the only field of it that matters.

`Demanded` picks out one of `Chirp`'s two values, so it is neither `fun _ => True`
— the degeneracy §10.49 records — nor `fun _ => False`, which is what every other
acceptance in this repository chooses. It is exactly the shape a real
specification would have.
-/
@[reducible] def chatterAcceptance : ProcessAcceptance chatter where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  DemandsWellFormed := fun _ => True
  ViewAccepts := fun _ _ => True
  Demanded := fun observation => observation = Chirp.beep
  terminalRemainder := TerminalRemainderLaw.strict chatter

/-! ## It never gets anywhere -/

/-- A beep is demanded, which is how every step of this process progresses. -/
theorem beep_is_demanded : chatterAcceptance.SegmentIsDemanded [Chirp.beep] :=
  ⟨Chirp.beep, List.mem_cons_self, rfl⟩

/-- The one step it can take. -/
theorem the_glitch : chatter.Step () (.fault ()) () 0 [Chirp.beep] :=
  ⟨rfl, rfl, rfl⟩

/-- Its bag does not move: nothing was settled and nothing issued. -/
theorem the_glitch_holds_nothing :
    SuccessorBag (p := chatter) 0 (.fault ()) 0 0 := by
  unfold SuccessorBag
  simp

/-- The run it starts. -/
theorem chatter_starts :
    Reachable chatterAcceptance.terminalRemainder () (Segmented.empty.emit [])
      (.running () 0 []) :=
  .initial (.running ⟨rfl, rfl, rfl⟩)

/--
**And it beeps forever.**

State and bag unchanged; only the trace grows, by one `beep` each time. Not a
cycle in the run state — the trace is append-only — which is exactly why
`Grass/Process/Network/Progress.lean` had to replace a cycle law with a
descent law, and exactly why a descent law does not catch this one.
-/
theorem chatter_beeps (observations : Trace chatter.Observation) :
    ProcessRunTransition chatterAcceptance.terminalRemainder ()
      (.running () 0 observations)
      (.running () (0 + 0) (observations ++ [Chirp.beep])) :=
  .step (event := .fault ()) rfl the_glitch

/-- It has no terminal result, so no run of it can ever finish. -/
theorem chatter_never_finishes (result : chatter.TerminalResult) : False := result.elim

/-! ## And it is correct -/

/-- The measure is never consulted, because every step emits a `beep`. -/
@[reducible] def chatterMeasure : ProcessMeasure chatter where
  Rank := Nat
  lt := Nat.lt
  wellFounded := Nat.lt_wfRel.wf
  rank := fun _ _ => 0

/--
**`chatter` meets its progress contract.**

`productive` is discharged by the emission disjunct in the only case there is.
The measure is constant and it does not matter: nothing ever asks it anything.
-/
def chatterProgress (request : Unit) :
    MeetsProcessProgress chatter chatterAcceptance (fun _ => True) request where
  measure := chatterMeasure
  handlesEveryEvent := by
    rintro _ _ _ _ event _ _ _
    match event with
    | .fault _ => exact ⟨(), 0, [Chirp.beep], rfl, rfl, rfl⟩
    | .external e => exact e.elim
    | .result demand _ => exact demand.elim
    | .interrupted demand _ => exact demand.elim
    | .environmentViolation violation => exact violation.elim
  notStuck := by
    rintro _ _ _ _ _
    exact Or.inr ⟨.fault (), eventDeliverable_of_settles_none (by simp),
      (), 0, [Chirp.beep], rfl, rfl, rfl⟩
  productive := by
    intro _ _ _ _ _ _ event _ emitted _ _ _ stepped
    match event, stepped with
    | .fault _, ⟨_, _, isEmitted⟩ => exact Or.inr (Or.inl (isEmitted ▸ beep_is_demanded))
    | .external e, _ => exact e.elim
    | .result demand _, _ => exact demand.elim
    | .interrupted demand _, _ => exact demand.elim
    | .environmentViolation violation, _ => exact violation.elim

/--
**And it is correct.**

The sentence this file exists for. A process that does nothing but log, forever,
with no external event to blame and no way to finish, satisfies every field of
`ProcessCorrect` against an acceptance that demands exactly one of its two
observations.

`terminalNoStep` and `terminal` are vacuous because `TerminalResult` is empty,
which is honest: this process genuinely never terminates, and that is the point
rather than a way of avoiding the field.
-/
def chatterCorrect : ProcessCorrect chatter chatterAcceptance where
  Invariant := fun _ => True
  initial := by intros; trivial
  initialDemands := by intros; trivial
  preserved := by intros; trivial
  demandsWellFormed := by intros; trivial
  terminal := by intros; trivial
  terminalNoStep := by
    rintro _ _ result _ _ _ _
    exact result.elim
  viewAccepts := by
    intro facet hasView
    exact absurd hasView (by simp [chatter])
  observationsAccept := by intros; trivial
  progress := chatterProgress

/-! ## Why the livelock theorems do not see it -/

/--
**Its step is not silent**, which is the whole of how it escapes.

`SilentStep` asks for a step that emits nothing demanded. `chatter`'s emits
something demanded on every step, so `no_infinite_silent_run` and
`no_silent_two_cycle` have nothing to say about it — correctly, on their own
terms.

Stated so the escape is a theorem rather than a remark. A future round that
believes the livelock theorems exclude everything can read this and see which
hypothesis fails.
-/
theorem the_glitch_is_not_silent :
    ¬ SilentStep chatterAcceptance () 0 () 0 := by
  rintro ⟨event, issued, emitted, stepped, _, _, undemanded⟩
  match event, stepped with
  | .fault _, ⟨_, _, isEmitted⟩ => exact undemanded (isEmitted ▸ beep_is_demanded)
  | .external e, _ => exact e.elim
  | .result demand _, _ => exact demand.elim
  | .interrupted demand _, _ => exact demand.elim
  | .environmentViolation violation, _ => exact violation.elim

/--
**And no measure would have caught it either.**

The state and the bag are unchanged across the step, so `ProcessMeasure` cannot
descend — which is what `Tests/Process/SpinFixtures.lean` and
`Tests/Process/OscillateFixtures.lean` are about. `chatter` differs from both in
where it escapes: they were let through by the *measure* being the wrong shape,
and this one is let through by a predicate the specification's author chose.
-/
theorem no_measure_would_have_caught_it (measure : ProcessMeasure chatter) :
    ¬ measure.Decreases () 0 () 0 :=
  measure.not_decreases_self () 0

end Grass.Process.Tests.Chatter
