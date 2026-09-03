import Tests.Process.M1CorrectFixtures

/-!
# A process that has a view

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.56: `ProcessSpec.view` is `none` in
every specification in the repository — `view := some` had zero occurrences — so
`ProcessCorrect.viewAccepts` is discharged by `absurd hasView` in all five
correctness fixtures and `ProcessAcceptance.ViewAccepts` is `fun _ _ => True` in
all five. `ViewFacet` was constructed nowhere. `docs/PROCESS.md` §2's "an
optional view facet is pure — it may be evaluated, duplicated, coalesced or
discarded" had no witness that it can be any of those.

The entry deferred it: "building one is a specification-layer question, not a
process-layer one". That was an argument, and `ProcessSpec` is this layer. This
file is the construction.

`gauge` is `Tests/Process/M1CorrectFixtures.lean`'s `oneShot` with a view: the
same two-state process, projecting how many steps of work remain. Nothing about
the process changed, which is the point — the view facet is *pure*, and a process
that acquires one is the same process.

## What makes the acceptance non-vacuous

`ViewAccepts := fun _ _ => True` is what the five existing fixtures use, and it
asks nothing. Here it is the **image of the render**: a rendered view is
acceptable exactly when some state renders to it. That is stateable for any
facet, it is what `viewAccepts` can always discharge, and it genuinely refuses
things — `remaining` renders into `{0, 1}` and
`a_view_no_state_renders_is_refused` is `2` being turned away.
-/

namespace Grass.Process.Tests.View

open Grass.Process
open Grass.Process.Tests

/--
**The view: how many steps of work remain.**

The corpus's first `ViewFacet`. Pure, total, and into a plain type — §2 requires
all three, and the second and third are what the structure's shape gives for
free. What it does not give for free is that the *projection* is a projection and
not a step, which is why `render` is a function and not a relation.
-/
@[reducible] def remaining : ViewFacet Bool where
  View := Nat
  render := fun finished => cond finished 0 1

/--
`oneShot`, with a view.

Every other field is `Tests/Process/M1CorrectFixtures.lean`'s, verbatim: `false`
is working, `true` is finished, one event moves it and nothing moves it
afterwards. A view facet is pure, so acquiring one changes no behaviour, and the
correctness record below differs from `oneShotCorrect` in exactly one field.
-/
@[reducible] def gauge : ProcessSpec.{0, 0} where
  vocabulary := oneShotVocabulary
  Request := Unit
  State := Bool
  TerminalResult := Unit
  Initial := fun _ state issued emitted =>
    state = false ∧ issued = 0 ∧ emitted = []
  Terminal := fun _ state _ => state = true
  Step := fun state _ after issued emitted =>
    state = false ∧ after = true ∧ issued = 0 ∧ emitted = []
  view := some remaining

/-- And it really carries it, which is the hypothesis `viewAccepts` waits on. -/
theorem gauge_has_a_view : gauge.view = some remaining := rfl

/-- The strictest terminal law: this process may only finish holding nothing. -/
@[reducible] def gaugeRemainder : TerminalRemainderLaw gauge :=
  TerminalRemainderLaw.strict gauge

/--
An acceptance whose view clause is the image of the render.

`fun _ _ => True` is what the five view-less fixtures use and it asks nothing.
This asks that an acceptable view is one the process can actually be in — which
is exactly what `ProcessCorrect.viewAccepts` promises, and which refuses every
value outside the render's range.
-/
@[reducible] def gaugeAcceptance : ProcessAcceptance gauge where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  DemandsWellFormed := fun _ => True
  ViewAccepts := fun facet value => ∃ state, facet.render state = value
  Demanded := fun _ => False
  terminalRemainder := gaugeRemainder

/-! ## It progresses -/

/-- The measure: one step of work remains while the state is `false`. -/
@[reducible] def gaugeMeasure : ProcessMeasure gauge where
  Rank := Nat
  lt := Nat.lt
  wellFounded := Nat.lt_wfRel.wf
  rank := fun state _ => if state then 0 else 1

/-- `gauge` meets its progress contract, exactly as `oneShot` does. -/
def gaugeProgress (request : Unit) :
    MeetsProcessProgress gauge gaugeAcceptance (fun _ => True) request where
  measure := gaugeMeasure
  handlesEveryEvent := by
    rintro _ state _ _ _ _ notTerminal
    intro _
    refine ⟨true, 0, [], ?_, rfl, rfl, rfl⟩
    cases state with
    | false => rfl
    | true => exact absurd ⟨(), rfl⟩ notTerminal
  notStuck := by
    rintro _ state outstanding _ _
    cases state with
    | false =>
      refine Or.inr ⟨.external (), ?_, true, 0, [], rfl, rfl, rfl, rfl⟩
      exact eventDeliverable_of_settles_none (by simp)
    | true =>
      refine Or.inl ⟨(), rfl, ⟨?_⟩⟩
      rw [bag_of_pempty_eq_zero outstanding]
      exact TerminalDemandClassification.empty gaugeRemainder request true ()
        ⟨rfl, rfl, rfl⟩
  productive := by
    rintro _ state _ _ after _ _ _ _ _ _ _ ⟨working, finished, _, _⟩
    subst working; subst finished
    refine Or.inr (Or.inr ?_)
    show (0 : Nat) < 1
    omega

/-! ## It is correct, and its view is accepted -/

/--
**`gauge` is correct, and `viewAccepts` is discharged rather than evaded.**

The one field that differs from `oneShotCorrect`. There it reads
`exact absurd hasView (by simp [oneShot])` — the obligation is discharged by the
spec having no view at all. Here the hypothesis holds, and the obligation is met.
-/
def gaugeCorrect : ProcessCorrect gauge gaugeAcceptance where
  Invariant := fun _ => True
  initial := by intros; trivial
  initialDemands := by intros; trivial
  preserved := by intros; trivial
  demandsWellFormed := by intros; trivial
  terminal := by intros; trivial
  terminalNoStep := by
    rintro state _ _ _ _ _ isTerminal ⟨working, _⟩
    rw [isTerminal ()] at working
    exact absurd working (by decide)
  viewAccepts := by
    intro facet _ state _
    exact ⟨state, rfl⟩
  observationsAccept := by intros; trivial
  progress := gaugeProgress

/--
The obligation, spent at the facet the specification actually carries.

`gauge_has_a_view` is what makes this a use of the field rather than a use of its
vacuity: the five existing correctness fixtures cannot state this theorem at all.
-/
theorem the_render_is_accepted (state : Bool) :
    gaugeAcceptance.ViewAccepts remaining (remaining.render state) :=
  gaugeCorrect.viewAccepts remaining gauge_has_a_view state trivial

/-- Working renders to one step remaining. -/
theorem working_renders_one : remaining.render false = 1 := rfl

/-- Finished renders to none. -/
theorem finished_renders_zero : remaining.render true = 0 := rfl

/--
**And a view no state renders is refused.**

What `ViewAccepts := fun _ _ => True` cannot say. `remaining` renders into
`{0, 1}`, so a claim that this process has two steps of work left is not an
acceptable view of it — and the acceptance says so rather than shrugging.
-/
theorem a_view_no_state_renders_is_refused :
    ¬ gaugeAcceptance.ViewAccepts remaining 2 := by
  rintro ⟨state, rendered⟩
  cases state <;> exact absurd rendered (by decide)

end Grass.Process.Tests.View
