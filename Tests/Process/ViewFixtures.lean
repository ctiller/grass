import Tests.Process.M1CorrectFixtures

/-!
# A process that has a view

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.56: `ProcessSpec.view` is `none` in
every specification the build elaborates, so `ProcessCorrect.viewAccepts` is
discharged by `absurd hasView` in all five correctness fixtures and
`ProcessAcceptance.ViewAccepts` is `fun _ _ => True` in all five. `ViewFacet` was
constructed nowhere.

(An earlier version of this note said `view := some` "had zero occurrences".
`Spikes/4_Web_Server/Process.lean` and `Spikes/5_Spinning_Cube/Process.lean` both
write it — `Spikes` is not a `lakefile.toml` target, so none of it elaborates.
A reviewer caught the overstatement; the claim is about the build, not the
repository.) `docs/PROCESS.md` §2's "an
optional view facet is pure — it may be evaluated, duplicated, coalesced or
discarded" had no witness that it can be any of those.

The entry deferred it: "building one is a specification-layer question, not a
process-layer one". That was an argument, and `ProcessSpec` is this layer. This
file is the construction.

`gauge` is `Tests/Process/M1CorrectFixtures.lean`'s `oneShot` with a view: the
same two-state process, projecting how many steps of work remain. Nothing about
the process changed, which is the point — the view facet is *pure*, and a process
that acquires one is the same process.

## What makes the obligation falsifiable

`ViewAccepts := fun _ _ _ => True` is what the five existing fixtures use, and it
asks nothing.

It took two rounds and a change to `ProcessAcceptance` to get this right, and
both wrong answers are worth recording because they are the same mistake.

The first version used the **image of the render** — acceptable exactly when some
state renders to it. `viewAccepts` is asked for
`ViewAccepts facet (facet.render state)`, and the witness `⟨state, rfl⟩`
discharges that for any facet, any render, any specification. A reviewer compiled
a bogus facet the spec does not carry and had it accepted.

The second was a **bound**: at most one step of remaining work. A second reviewer
mutated the render to the constant zero and the bound survived — a view reporting
"no work remains" at the working state was accepted, because the clause could not
see the state to disagree with. The file claimed at that point that mutating
`render` breaks the obligation; only mutating it *upward* did.

Both failures have one cause, and it was in `ProcessAcceptance` rather than here:
`ViewAccepts` received a facet and a value and **not the state**, so it could not
say a view *reflects* anything. §10.99 gave it the state.

What is here now is an **agreement**: `intendedView` is what this specification
says a view of `gauge` should report, and `ViewAccepts` asks the rendered value
to equal it *at that state*. `gaugeCorrect.viewAccepts` then obliges
`remaining.render` to agree with `intendedView` everywhere, so any mutation of
the render breaks it — constant, off-by-one or swapped alike.

It is still stated as `∀ same : facet = remaining, …`, because `ViewAccepts`
receives a facet and a value of *that facet's* view type, so an agreement about
this specification's view has to name the facet before it can compare values. At
any other facet it asks nothing, and `the_clause_is_only_about_this_facet` says
so rather than leaving a reader to find out.
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

/--
**What the specification says a view of this process should report.**

Written out separately from `remaining.render`, which is the point: the render is
the *process's* projection and this is the *specification's* intent, and
`ProcessCorrect.viewAccepts` is the obligation that they agree. Were they one
definition the obligation would be `rfl` and would test nothing.
-/
def intendedView : Bool → Nat := fun finished => cond finished 0 1

/-- The strictest terminal law: this process may only finish holding nothing. -/
@[reducible] def gaugeRemainder : TerminalRemainderLaw gauge :=
  TerminalRemainderLaw.strict gauge

/--
An acceptance whose view clause pins the rendered value at each state.

`fun _ _ _ => True` is what the five view-less fixtures use and it asks nothing.
This asks that a view of `gauge` reports exactly `intendedView` of the state it
was rendered from — a claim about `remaining.render`, which
`ProcessCorrect.viewAccepts` therefore has to establish and can fail to.
-/
@[reducible] def gaugeAcceptance : ProcessAcceptance gauge where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  DemandsWellFormed := fun _ => True
  ViewAccepts := fun facet state value =>
    ∀ same : facet = remaining, (same ▸ value : remaining.View) = intendedView state
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
    intro facet _ state _ same
    subst same
    show remaining.render state = intendedView state
    cases state <;> rfl
  observationsAccept := by intros; trivial
  progress := gaugeProgress

/--
The obligation, spent at the facet the specification actually carries.

`gauge_has_a_view` is what picks that facet out; the five existing correctness
fixtures cannot state this theorem at all, because there is no facet to state it
about.
-/
theorem the_render_is_accepted (state : Bool) :
    gaugeAcceptance.ViewAccepts remaining state (remaining.render state) :=
  gaugeCorrect.viewAccepts remaining gauge_has_a_view state trivial

/--
**And what it says is that the render implements the intent.**

The whole chain, ending in a fact relating two independently written definitions
rather than in a predicate satisfied by its own argument. Change `render` in any
way at all and this stops being true, and `gaugeCorrect` stops elaborating.
-/
theorem the_render_implements_the_intent (state : Bool) :
    remaining.render state = intendedView state :=
  the_render_is_accepted state rfl

/--
And the honest limit of it: at a facet `gauge` does not carry, this acceptance
asks nothing at all.

`ViewAccepts` receives a facet and a value of *that facet's* view type, so a
bound on a particular view has to name the facet before it can mention the value.
Saying so is better than a heading claiming more than the clause delivers, which
is what the first version of this file did.
-/
theorem the_clause_is_only_about_this_facet
    (facet : ViewFacet Bool) (different : facet ≠ remaining) (state : Bool)
    (value : facet.View) : gaugeAcceptance.ViewAccepts facet state value :=
  fun same => absurd same different

/-- Working renders to one step remaining. -/
theorem working_renders_one : remaining.render false = 1 := rfl

/-- Finished renders to none. -/
theorem finished_renders_zero : remaining.render true = 0 := rfl

/--
**And a view that disagrees with the state is refused.**

The thing neither earlier version could say. Zero is a perfectly good view value —
`finished_renders_zero` — and it is the *wrong* one at the working state. A clause
that cannot see the state accepts it; this one does not.
-/
theorem a_view_that_disagrees_with_the_state_is_refused :
    ¬ gaugeAcceptance.ViewAccepts remaining false 0 := by
  intro accepted
  exact absurd (accepted rfl) (by decide)

/-- And the same value at the other state is accepted, so the refusal is about
the disagreement and not about the number. -/
theorem the_same_view_is_accepted_where_it_is_right :
    gaugeAcceptance.ViewAccepts remaining true 0 := fun _ => rfl

end Grass.Process.Tests.View
