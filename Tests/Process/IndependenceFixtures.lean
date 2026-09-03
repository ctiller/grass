import Grass.Process.Trace.Linearization
import Tests.Process.LinearizationFixtures

/-!
# A diamond, built

`Grass/Process/Trace/Independence.lean` names `SwapsWith` as an obligation and
declines to discharge it, on the grounds that swapping two independent steps
means rebuilding each at a state it was not built at and every interesting
constructor carries a proof about its own before-state. That reasoning is right
about the general case. It leaves a risk the module names and does not close:
**a named obligation nobody discharges may be unsatisfiable**, and every theorem
conditioned on it — `swapped_execution_agrees_off_both` here,
`a_swap_only_moves_the_emission` in `Trace/Linearization.lean` — would then be
about nothing.

This file closes that risk with a concrete diamond.

The receive touches the wire's escrow and its session cursor. The commit touches
the observation trace. They are independent, and the four worlds

* `beforeReceive` — nothing delivered, nothing observed
* `afterBeep` — nothing delivered, one `beep`
* `afterReceive` — one delivered, nothing observed
* `afterBoth` — one delivered, one `beep`

close under both orders. `the_receive_and_the_commit_swap` is the witness, and
it is exactly the shape `SwapsWith` asks for: the reordered execution runs the
same two transitions, checked by the scope equations rather than by their names.

## Why this one was buildable when the general case is not

Both steps here are *definitionally* independent of the other's before-state.
`Delivers`'s fields are about `inFlight` and `sessions`, and a commit changes
neither; `Commits`' fields are about `observations`, and a delivery changes
none. So each proof transports by `rfl` rather than by a lemma. A pair where one
step's precondition mentioned a fragment the other wrote would need the
per-constructor argument `Independence.lean` describes, and this fixture does
not claim otherwise.
-/

namespace Grass.Process.Tests.Independence

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld)
open Grass.Process.Tests.Transition (serverPlan beforeReceive afterReceive receiveAsStep
  receiveStep cursorAt ledgerAt worlds_agree_off_wire cursorAt_off_wire escrowed
  pendingLedger settledLedger beforeReceive_wire afterReceive_wire settled_resolution)
open Grass.Process.Tests.Commit (quietRunCoalesces beeps)
open Grass.Process.Tests.Linearization (beepCommit)
open Grass.Process.Tests.Channel (wire)

/-! ## The fourth corner -/

/-- Both things have happened: the message was delivered and the `beep` committed. -/
noncomputable def afterBoth : ServerWorld :=
  { afterReceive with observations := [Observation.beep], pending := [] }

/-- The world with only the `beep` is the commit fixture's. -/
theorem afterBeep_is_quiet_but_noisy :
    Grass.Process.Tests.Commit.afterBeep.observations = [Observation.beep] := rfl

/-! ## The two ways round -/

/--
**The receive, taken after the commit.**

The same `Delivers` fields as the original at two worlds that differ from it
only in their observation trace — which `Delivers` does not mention, so every
field transports unchanged.
-/
theorem receiving_after_the_beep :
    serverPlan.Delivers Grass.Process.Tests.Commit.afterBeep afterBoth () wire escrowed where
  contractual := Transition.receiving_resolves_the_escrow.contractual
  onItsSession := rfl
  wasOutstanding := Transition.receiving_resolves_the_escrow.wasOutstanding
  nowResolved := Transition.receiving_resolves_the_escrow.nowResolved
  resolvesNothingElse := Transition.receiving_resolves_the_escrow.resolvesNothingElse
  ledgerExtends := Transition.receiving_resolves_the_escrow.ledgerExtends
  cursorAdvances := Transition.receiving_resolves_the_escrow.cursorAdvances
  statusUnchanged := Transition.receiving_resolves_the_escrow.statusUnchanged
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := by
        intro isWire
        subst isWire
        exact outside (Or.inl rfl)
      exact worlds_agree_off_wire notWire
    | session edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := by
        intro isWire
        subst isWire
        exact outside (Or.inr rfl)
      show cursorAt false session = cursorAt true session
      rw [cursorAt_off_wire notWire, cursorAt_off_wire notWire]
    | _ => rfl

/-- As a transition. -/
def receiveAfterBeep :
    serverPlan.NetworkTransition Grass.Process.Tests.Commit.afterBeep afterBoth :=
  .receive () wire escrowed receiving_after_the_beep

/--
**And the commit, taken after the receive.**

Likewise: `Commits` is about the two observation traces, and a delivery changes
neither.
-/
theorem committing_after_the_receive :
    serverPlan.Commits afterReceive afterBoth quietRunCoalesces.committed.observations where
  earned := rfl
  appended := rfl
  nonempty := by simp [quietRunCoalesces, beeps]
  scope := by
    intro fragment outside
    cases fragment with
    | observations =>
      exact absurd ⟨by simp [quietRunCoalesces, beeps], Or.inl rfl⟩ outside
    | pending =>
      exact absurd ⟨by simp [quietRunCoalesces, beeps], Or.inr rfl⟩ outside
    | _ => rfl

/-- As a transition. -/
def commitAfterReceive : serverPlan.NetworkTransition afterReceive afterBoth :=
  .commit quietRunCoalesces.committed.observations committing_after_the_receive

/-! ## As steps -/

/-- The receive-after-beep, as a step. Neither transition allocates. -/
def receiveAfterBeepStep :
    serverPlan.NetworkStep Grass.Process.Tests.Commit.afterBeep afterBoth where
  transition := receiveAfterBeep
  admissible := by
    intro nominal allocated
    exact absurd allocated (fun inEmpty => List.not_mem_nil inEmpty)
  historyExact := (NominalHistory.extend_empty _ _).symm

/-- And the commit-after-receive. -/
def commitAfterReceiveStep : serverPlan.NetworkStep afterReceive afterBoth where
  transition := commitAfterReceive
  admissible := by
    intro nominal allocated
    exact absurd allocated (fun inEmpty => List.not_mem_nil inEmpty)
  historyExact := (NominalHistory.extend_empty _ _).symm

/-- The commit at the start, as a step. -/
def beepCommitStep :
    serverPlan.NetworkStep beforeReceive Grass.Process.Tests.Commit.afterBeep where
  transition := beepCommit
  admissible := by
    intro nominal allocated
    exact absurd allocated (fun inEmpty => List.not_mem_nil inEmpty)
  historyExact := (NominalHistory.extend_empty _ _).symm

/-! ## The diamond -/

/--
**The receive and the commit are independent.**

Escrow and session on one side, the observation trace on the other.
-/
theorem the_receive_and_the_commit_are_independent :
    receiveStep.Independent commitAfterReceive := by
  intro fragment inReceive inCommit
  obtain ⟨_, isObservations⟩ := inCommit
  rcases (Transition.receive_scope_is_the_session fragment).mp inReceive with
    isEscrow | isSession
  · rw [isEscrow] at isObservations
    exact absurd isObservations (by simp)
  · rw [isSession] at isObservations
    exact absurd isObservations (by simp)

/--
**And they swap.**

`SwapsWith` discharged at a concrete pair — the obligation
`Grass/Process/Trace/Independence.lean` names and declines to prove in general.
Running the receive then the commit, and the commit then the receive, both reach
`afterBoth`; the scope equations are `Iff.rfl` because the reordered steps are
the same two transitions at different worlds.

This is what makes `swapped_execution_agrees_off_both` and
`Trace/Linearization.lean`'s `a_swap_only_moves_the_emission` theorems about
something. A named obligation nobody discharges may be unsatisfiable, and this
one is not.
-/
theorem the_receive_and_the_commit_swap :
    ProcessPlan.SwapsWith receiveAsStep commitAfterReceiveStep :=
  ⟨Grass.Process.Tests.Commit.afterBeep, beepCommitStep, receiveAfterBeepStep,
    fun _ => Iff.rfl, fun _ => Iff.rfl⟩

/--
**So an observer outside both scopes sees the same thing either way.**

`swapped_execution_agrees_off_both` at the witness. The route table is such an
observer: neither step names it, and it is the same at both ends whichever order
the scheduler chose.
-/
theorem the_route_table_agrees_either_way :
    LogicalProcessNetworkCore.Agrees (.region Region.routeTable) beforeReceive afterBoth :=
  ProcessPlan.swapped_execution_agrees_off_both the_receive_and_the_commit_swap
    (by
      rintro (isEscrow | isSession)
      · exact absurd isEscrow (by simp)
      · exact absurd isSession (by simp))
    (by rintro ⟨_, isObservations⟩; exact absurd isObservations (by simp))

/--
**And the swap only moved the emission**, which is the trace half of the same
fact.
-/
theorem the_swap_only_moved_the_beep :
    (beforeReceive.observations = afterReceive.observations ∨
        afterReceive.observations = afterBoth.observations) ∧
      ∃ (middle : serverPlan.LogicalProcessNetwork)
        (swappedRight : serverPlan.NetworkStep beforeReceive middle)
        (swappedLeft : serverPlan.NetworkStep middle afterBoth),
        (∀ fragment, swappedRight.transition.scope fragment ↔
          commitAfterReceiveStep.transition.scope fragment) ∧
        (∀ fragment, swappedLeft.transition.scope fragment ↔
          receiveAsStep.transition.scope fragment) ∧
        (beforeReceive.observations = middle.observations ∨
          middle.observations = afterBoth.observations) :=
  ProcessPlan.a_swap_only_moves_the_emission the_receive_and_the_commit_are_independent
    the_receive_and_the_commit_swap

end Grass.Process.Tests.Independence
