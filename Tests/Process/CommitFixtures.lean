import Grass.Process.Network.Commit
import Tests.Process.TransitionFixtures

/-!
# A reconciler that may coalesce, and one that may not

`Grass/Process/Network/Commit.lean` says a reconciler may replace several
pending renders by the latest one "only when no skipped render has a demanded
commit observation". A side condition is worth exactly as much as the cases it
rejects, so this file exhibits both sides.

* `quietRunCoalesces` skips two renders that emit nothing and commits the third.
  The filter demands `beep`, and neither skipped render carries one.
* `cannot_skip_a_demanded_render` is the rejection. With a `beep` on a skipped
  render, no `Coalescing` exists — not "the commit is wrong", but the
  reconciler's decision is unconstructible.
* `skipping_nothing_is_always_available` shows the law never forbids
  reconciliation outright: presenting every render in order is always a
  `Coalescing`, whatever the filter demands. A side condition that could make
  every commit impossible would be a bug, not a law.
-/

namespace Grass.Process.Tests.Commit

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.Transition (serverPlan)

/-- The filter: this fixture's specification demands every `beep`. -/
def demandsBeep : Observation → Prop := fun _ => True

/-- A render that emits nothing. -/
def silent : PendingRender Observation := ⟨[]⟩

/-- One that emits a `beep`. -/
def beeps : PendingRender Observation := ⟨[.beep]⟩

/-! ## Coalescing past silent renders -/

/--
Two silent renders skipped, the third committed.

`docs/PROCESS.md` §6's graphics case: several frames pending, only the latest
presented. It is admissible here because nothing skipped carried an observation
the specification demanded.
-/
def quietRunCoalesces : Coalescing demandsBeep where
  pending := [silent, silent, beeps]
  skipped := [silent, silent]
  committed := beeps
  rest := []
  exact := rfl
  skippedUndemanded := by
    intro render present
    have isSilent : render = silent := by
      simp at present
      exact present
    rw [isSilent]
    exact PendingRender.empty_not_demanded demandsBeep silent rfl

/-- Everything it accounts for was pending, including what it skipped. -/
theorem quiet_run_accounts_for_everything :
    quietRunCoalesces.committed ∈ quietRunCoalesces.pending ∧
      ∀ render ∈ quietRunCoalesces.skipped, render ∈ quietRunCoalesces.pending :=
  ⟨quietRunCoalesces.committed_was_pending,
    fun _ skipped => quietRunCoalesces.skipped_were_pending skipped⟩

/-! ## And the case the side condition rejects -/

/--
**A render carrying a demanded observation cannot be skipped.**

The rejection, stated over an arbitrary reconciler rather than a particular one,
because it is a property of the type. `docs/PROCESS.md` §6's condition is what
stands between a reconciler and dropping an observation a specification
required, and this is that standing.
-/
theorem cannot_skip_a_demanded_render (coalescing : Coalescing demandsBeep)
    (skipped : beeps ∈ coalescing.skipped) : False :=
  coalescing.no_demanded_observation_dropped (observation := Observation.beep) skipped
    (by simp [beeps]) trivial

/--
**But the law never forbids reconciling at all.**

Presenting every render in order is a `Coalescing` for any filter. A side
condition that could make every commit impossible would be a bug rather than a
law, so this is the satisfiability half that makes the rejection above mean
something.
-/
theorem skipping_nothing_is_always_available
    (first : PendingRender Observation) (rest : List (PendingRender Observation)) :
    (Coalescing.skipNothing demandsBeep first rest).skipped = [] := rfl

/-- Even when every render is demanded. -/
theorem can_still_commit_when_all_are_demanded :
    (Coalescing.skipNothing demandsBeep beeps [beeps]).committed = beeps := rfl

/-! ## The commit itself -/

/-- The world after committing a `beep`: it is in the committed trace, and it
is no longer pending. -/
noncomputable def afterBeep : World.ServerWorld :=
  { Transition.beforeReceive with observations := [.beep], pending := [] }

/--
Committing appends the survivor's observations and touches nothing else.

The scope is the observation fragment alone, which is what
`Grass/Process/Network/Transition.lean`'s `commit` constructor declares.
-/
theorem beep_is_committed :
    serverPlan.CommitsRender Transition.beforeReceive afterBeep quietRunCoalesces where
  appended := rfl
  scope := by
    intro fragment outside
    cases fragment with
    | observations => exact absurd ⟨by simp [quietRunCoalesces, beeps], Or.inl rfl⟩ outside
    | pending => exact absurd ⟨by simp [quietRunCoalesces, beeps], Or.inr rfl⟩ outside
    | _ => rfl

/-- And what was already observed stays observed. -/
theorem earlier_observations_survive (observation : Observation)
    (wasObserved : observation ∈ Transition.beforeReceive.observations) :
    observation ∈ afterBeep.observations :=
  beep_is_committed.earlier_observations_survive wasObserved

end Grass.Process.Tests.Commit
