import Tests.Process.ProcessStepFixtures

/-!
# Ending a process, and the two endings that have to be earned

`Grass/Process/Network/Transition.lean`'s `EndsInstance` is shared by six
constructors — `interrupt`, `fault`, `environmentViolation`, `childCancelled`,
`childDied` and `processTermination` — and it had never been built.

That is the shape `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.54 warns about: a
record with no witness absorbs new fields without a single proof breaking, and
`EndsInstance` had absorbed three over four review rounds. This file is the
witness, and writing it is what turned §10.51 from a recorded question into a
field.

## What `endingIsEarned` says, and why only two of the six

`nowEnded` stores a `ProcessLifecycle` and nothing checked the stored value
against anything that happened. Two of the six endings are checkable here:

* `.terminated result` against `ProcessSpec.Terminal`, which is the
  specification's own word for finished. `an_honest_termination` is the witness
  and `a_process_may_not_be_declared_finished_early` is the attack — the same
  incarnation, still counting at three, tagged terminated.
* `.interrupted reason` against the outstanding bag. `docs/PROCESS.md` §2 calls
  an interruption "an outstanding demand of its own was abandoned", and
  `nothing_to_abandon_is_not_an_interruption` is a process holding nothing being
  said to abandon something.

The other four are unchecked and each for a different reason; the field's own
docstring gives them. The one worth repeating is `.cancelled`: it wants a prior
cancellation request, and no *instance* records one —
`Grass/Process/Network/Escrow.lean`'s `cancelRequested` is per occurrence on a
channel. That is a world change, not a field.

## What this fixture does not exercise

`custodyDeclared`'s second conjunct — that the declared custody relation is
single-valued at the before-state — is what stops `custody := fun _ _ _ => True`,
and it cannot bite here: `serverPlan`'s obligations are `Unit`, so every relation
is single-valued. The field's own docstring says it is refuted "at any plan whose
`Obligations` has two values", and no such plan exists in this corpus. §10.33 is
the neighbouring gap and is not this one.
-/

namespace Grass.Process.Tests.Ending

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet)
open Grass.Process.Tests.Transition (serverPlan)
open Grass.Process.Tests.Instances (counting finished)

/-! ## Three incarnations of one connection -/

/-- The slot it lives in. -/
def slot : serverTopology.InstanceId .connection := 7

/-- Still running, and its protocol says it is finished: state zero. -/
def settling : ProcessInstance serverTopology :=
  { counting with localState := ⟨0⟩ }

/-- Holding one outstanding demand, at three. -/
def waitingOnATick : ProcessInstance serverTopology :=
  { counting with outstanding := Bag.ofList [Demand.tick] }

/-- A network holding a given incarnation in that slot. -/
def holding (incarnation : ProcessInstance serverTopology) : ServerWorld :=
  { quiet with
      instances := fun kind current =>
        match kind, current with
        | .listener, _ => none
        | .connection, n => if n = slot then some incarnation else none }

theorem holding_slot (incarnation : ProcessInstance serverTopology) :
    (holding incarnation).instances .connection slot = some incarnation := by
  simp [holding]

/-- Nothing outside that slot moves between two such networks. -/
theorem holding_scope (left right : ProcessInstance serverTopology) :
    serverPlan.TouchesOnly (holding left) (holding right)
      (fun fragment => fragment = .instanceState .connection slot ∨
        (holding left).obligations ≠ (holding right).obligations ∧
          fragment = .obligations) := by
  intro fragment outside
  cases fragment with
  | instanceState kind current =>
    cases kind with
    | listener => rfl
    | connection =>
      simp only [LogicalProcessNetworkCore.Agrees, holding]
      split
      · rename_i isSlot
        exact absurd (Or.inl (by rw [isSlot])) outside
      · rfl
  | _ => rfl

/-! ## The witness -/

/--
**A process that its protocol calls finished may be ended as finished.**

Every field of `EndsInstance` at a concrete pair of worlds, and the record's
first witness. `endingIsEarned`'s termination clause is discharged from
`countdown.Terminal ⟨3⟩ ⟨0⟩ ⟨()⟩`, which is `0 = 0` — the protocol's own word,
not this fixture's assertion.
-/
theorem an_honest_termination :
    serverPlan.EndsInstance (holding settling) (holding finished) .connection slot
      (.terminated ⟨()⟩) (fun _ _ _ => True) where
  notRunning := by intro equal; cases equal
  wasLive := ⟨settling, holding_slot settling, trivial⟩
  nowEnded := ⟨finished, holding_slot finished, rfl, rfl⟩
  identityPreserved :=
    ⟨settling, finished, rfl, rfl, holding_slot settling, holding_slot finished,
      rfl, rfl, rfl, rfl⟩
  endingIsEarned :=
    ⟨settling, rfl, holding_slot settling,
      fun result isTerminated => by cases isTerminated; exact rfl,
      fun _ isInterrupted => by cases isInterrupted⟩
  custodyDeclared :=
    ⟨settling, holding_slot settling, rfl, trivial, fun other _ => by cases other; rfl⟩
  scope := holding_scope settling finished

/-! ## And the two endings it refuses -/

/--
**A process still counting may not be declared finished.**

`Tests/Process/InstanceFixtures.lean` has the same attack against
`ProcessInstance.LifecycleWitnessed`, which is a predicate on one incarnation. It
was not enforced by the *transition*, so a step could install the lie — and
`LifecycleWitnessed` is not a field of anything the family checks.
-/
theorem a_process_may_not_be_declared_finished_early :
    ¬ serverPlan.EndsInstance (holding counting) (holding Instances.lying) .connection slot
      (.terminated ⟨()⟩) (fun _ _ _ => True) := by
  intro ends
  obtain ⟨fromInstance, _, found, terminated, _⟩ := ends.endingIsEarned
  rw [holding_slot counting] at found
  injection found with same
  subst same
  have counted : (3 : Nat) = 0 := terminated ⟨()⟩ rfl
  exact absurd counted (by decide)

/--
**And a process holding nothing may not abandon something.**

`docs/PROCESS.md` §2's interruption is "an outstanding demand of its own was
abandoned". `counting`'s bag is empty, so there is nothing for the reason to be
about — and until `endingIsEarned` the ending was a label a plan could write
anyway.
-/
theorem nothing_to_abandon_is_not_an_interruption (reason : Interrupt) :
    ¬ serverPlan.EndsInstance (holding counting)
      (holding { counting with lifecycle := .interrupted reason }) .connection slot
      (.interrupted reason) (fun _ _ _ => True) := by
  intro ends
  obtain ⟨fromInstance, _, found, _, interrupted⟩ := ends.endingIsEarned
  rw [holding_slot counting] at found
  injection found with same
  subst same
  exact interrupted reason rfl rfl

/-- `waitingOnATick` really is holding one, which is what an interruption
abandons. -/
theorem holds_a_tick (empty : waitingOnATick.outstanding = 0) : False := by
  have present : Demand.tick ∈ waitingOnATick.outstanding := by
    show Demand.tick ∈ Bag.ofList [Demand.tick]
    simp
  rw [empty] at present
  exact Bag.mem_zero _ present

/--
**But a process that is holding one may.**

The positive half, so the field above is not merely a way of forbidding
interruptions. `waitingOnATick` holds a `tick`, which is what an interruption
abandons.
-/
theorem an_honest_interruption (reason : Interrupt) :
    serverPlan.EndsInstance (holding waitingOnATick)
      (holding { waitingOnATick with lifecycle := .interrupted reason })
      .connection slot (.interrupted reason) (fun _ _ _ => True) where
  notRunning := by intro equal; cases equal
  wasLive := ⟨waitingOnATick, holding_slot waitingOnATick, trivial⟩
  nowEnded := ⟨_, holding_slot _, rfl, rfl⟩
  identityPreserved :=
    ⟨waitingOnATick, _, rfl, rfl, holding_slot waitingOnATick, holding_slot _,
      rfl, rfl, rfl, rfl⟩
  endingIsEarned := by
    refine ⟨waitingOnATick, rfl, holding_slot waitingOnATick, ?_, ?_⟩
    · intro _ isTerminated
      exact absurd isTerminated (by simp)
    · intro _ _ empty
      exact holds_a_tick empty
  custodyDeclared :=
    ⟨waitingOnATick, holding_slot waitingOnATick, rfl, trivial,
      fun other _ => by cases other; rfl⟩
  scope := holding_scope waitingOnATick _

end Grass.Process.Tests.Ending
