import Grass.Process.Correct

/-!
# A process whose terminality depends on its request

`upto` reads items until it has `request` of them. Nothing else: one external
event, no demands, no observations. It exists for one reason — it is the class
`ProcessCorrect.terminalNoStep` was weakened to accommodate, and until this file
the corpus contained no member of that class.

`Grass/Process/Correct.lean` used to state the field existentially: *terminal
for some request implies no step for any*. `p.Step` cannot see the request, so
that excluded `upto` outright — state 3 is terminal for request 3 and must still
step for request 4. The field now asks about states terminal for **every**
request.

## What this fixture shows, including the part that is bad news

* `uptoCorrect` exists. The weakening was not cosmetic; without it this process
  had no correctness record at all.
* `upto_refutes_the_existential_terminal_law` is the refutation, stated against
  the old field verbatim so a future round cannot restore it without this file
  going red.
* `upto_is_never_universally_terminal` — **and no state of `upto` is terminal
  for every request**, so `terminalNoStep` is discharged *vacuously* here. That
  is the cost of the weakening, in the one place it can be seen: a driver
  holding a specific request and a state terminal only for it gets nothing from
  the field.

The corpus's other correctness fixtures cannot show either half.
`countdown.Terminal` and `oneShot.Terminal` both ignore their request, so for
them the two forms of the law coincide and both are discharged non-vacuously.
Local adversarial review found that `countdown` discharges the *old* field just
as well, which meant `countdownCorrect` witnessed the `state ≠ 0` guard and
nothing about the weakening.

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.45 proposes the real repair — index
`ProcessSpec.Step` by the request, as `Initial` and `Terminal` already are — and
that is a §2 change needing a ruling. This file is what makes the interim cost
visible rather than argued.
-/

namespace Grass.Process.Tests.Prefix

open Grass.Process

/-! ## The process -/

/-- One external event: an item arrived. Everything else is empty. -/
@[reducible] def uptoVocabulary : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := PEmpty
  Result := fun demand => demand.elim
  Observation := PEmpty
  InterruptReason := PEmpty
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

/--
Count arrivals; finish once there are `request` of them.

`Terminal` reads the request and `Step` does not, which is the whole point.
-/
@[reducible] def upto : ProcessSpec.{0, 0} where
  vocabulary := uptoVocabulary
  Request := Nat
  State := Nat
  TerminalResult := Unit
  Initial := fun _ state issued emitted => state = 0 ∧ issued = 0 ∧ emitted = []
  Terminal := fun request state _ => state = request
  Step := fun state event after issued emitted =>
    match event with
    | .external _ => after = state + 1 ∧ issued = 0 ∧ emitted = []
    | .result demand _ => demand.elim
    | .interrupted demand _ => demand.elim
    | .fault f => f.elim
    | .environmentViolation v => v.elim
  view := none

/-- Strict in every direction; there are no demands to dispose of. -/
@[reducible] def uptoAcceptance : ProcessAcceptance upto where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  DemandsWellFormed := fun _ => True
  ViewAccepts := fun _ _ => True
  Demanded := fun _ => False
  terminalRemainder := TerminalRemainderLaw.strict upto

/-! ## The separation -/

/-- State 3 is finished for a run of three, and must keep counting for a run of
four. -/
theorem three_is_terminal_and_steps :
    upto.Terminal 3 3 () ∧ upto.Step 3 (.external ()) 4 0 [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
**So the existential form of the terminal law is false for this process.**

Stated against the old field verbatim. `Grass/Process/Correct.lean`'s
`terminalNoStep` used to read exactly this, and restoring it would make this
theorem's own statement contradictory with `uptoCorrect` below.
-/
theorem upto_refutes_the_existential_terminal_law :
    ¬ (∀ (state after : upto.State) (result : upto.TerminalResult) (event : upto.Event)
        (issued : Bag upto.Demand) (emitted : upto.Segment),
      (∃ request, upto.Terminal request state result) →
      ¬ upto.Step state event after issued emitted) := by
  intro law
  exact law 3 4 () (.external ()) 0 [] ⟨3, rfl⟩ three_is_terminal_and_steps.2

/--
**And no state is terminal for every request**, so the weakened field is
vacuous here.

This is the honest half. `terminalNoStep` costs `upto` nothing and tells a
reader of `upto` nothing; what makes `uptoCorrect` exist is that the field stopped
asking the wrong question, not that it started asking a useful one.
-/
theorem upto_is_never_universally_terminal (state : upto.State) (result : upto.TerminalResult) :
    ¬ ∀ request, upto.Terminal request state result := by
  intro universal
  exact absurd (universal (state + 1)) (by omega)

/-! ## It progresses, and is correct -/

/-- Constant: every event of this process is entropy, so the measure is never
consulted. -/
@[reducible] def uptoMeasure : ProcessMeasure upto where
  Rank := Nat
  lt := Nat.lt
  wellFounded := Nat.lt_wfRel.wf
  rank := fun _ => 0

/--
`upto` meets its progress contract.

`notStuck` takes its right disjunct everywhere, including at states the
specification calls terminal for *some* request — which is legal precisely
because `terminalNoStep` no longer forbids stepping there.
-/
def uptoProgress (request : Nat) :
    MeetsProcessProgress upto uptoAcceptance (fun _ => True) request where
  measure := uptoMeasure
  handlesEveryEvent := by
    rintro _ state _ _ event _ _ _
    match event with
    | .external _ => exact ⟨state + 1, 0, [], rfl, rfl, rfl⟩
    | .result demand _ => exact demand.elim
    | .interrupted demand _ => exact demand.elim
    | .fault f => exact f.elim
    | .environmentViolation v => exact v.elim
  notStuck := by
    rintro _ state _ _ _
    exact Or.inr ⟨.external (),
      eventDeliverable_of_settles_none (by simp),
      state + 1, 0, [], rfl, rfl, rfl⟩
  productive := by
    rintro _ _ _ _ _ event _ _ _ _ _ _
    match event with
    | .external entropy => exact Or.inl ⟨entropy, rfl⟩
    | .result demand _ => exact demand.elim
    | .interrupted demand _ => exact demand.elim
    | .fault f => exact f.elim
    | .environmentViolation v => exact v.elim

/--
**`upto` is correct**, which is the fixture's headline: this record was empty
for every process of this shape.

`terminalNoStep` is discharged from `upto_is_never_universally_terminal` — see
that theorem for why discharging it this way is worth saying out loud.
-/
def uptoCorrect : ProcessCorrect upto uptoAcceptance where
  Invariant := fun _ => True
  initial := by intros; trivial
  initialDemands := by intros; trivial
  preserved := by intros; trivial
  demandsWellFormed := by intros; trivial
  terminal := by intros; trivial
  terminalNoStep := by
    intro state _ result _ _ _ universal
    exact absurd universal (upto_is_never_universally_terminal state result)
  viewAccepts := by
    intro facet hasView
    exact absurd hasView (by simp [upto])
  observationsAccept := by intros; trivial
  progress := uptoProgress

end Grass.Process.Tests.Prefix
