import Tests.Process.ProcessStepFixtures

/-!
# Detaching a child, and the two things a detach may not do

`docs/PROCESS.md` §3 says the detach transition "changes only `.attached parent`
to `.detached parent`, proves the references identical, and establishes the
corresponding non-returning child disposition".
`Grass/Process/Network/Transition.lean`'s `Detaches` is the first two thirds of
that, and this file is what checks it — in both directions, because a structure
of this shape needs a positive witness *and* the attacks it is supposed to
refuse.

`an_honest_detach` is the witness: a running connection loses its parent's
authority and keeps everything else, including the fact that it is running and
the identity of the parent it no longer answers to.

The two negatives are the steps that were legal until the fifth review pass
found them:

* `a_detach_may_not_kill` — a "detach" that also ends the child. `Detaches`
  pinned four of `ProcessInstance`'s seven fields and left `lifecycle` free, so
  a live incarnation could become `.died .parentDied` with no `EndsInstance`, no
  custody partition and no stored classification. That is the unclassified death
  §3 forbids, and it was reachable through the constructor immediately beside the
  one `Joins.wasTerminated` protects.
* `a_detach_may_not_forge_its_parent` — a "detach" that records a different
  former parent. The old field asked only that *some* parent be remembered, which
  `IsDetached` already implies, so the structure paid for a redundancy and bought
  nothing. `Grass/Process/Network/Child.lean`'s `NonReturningReason.detached` is
  checked against exactly this record, so a forged one is a non-returning
  disposition justified by a history that did not happen.

`the_forgery_breaks_wellformedness` is why the second one is not merely untidy:
the forged step takes a `ParentageValid` network to one that is not, so a
`Detaches` could manufacture an ill-formed network from a well-formed one.

Both were found by construction. Reading the structure five times did not find
either; building the attack found both in one pass.
-/

namespace Grass.Process.Tests.Detach

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet)
open Grass.Process.Tests.Transition (serverPlan)
open Grass.Process.Tests.Instances (counting listenerZero)

/-! ## A network with one attached child -/

/-- The slot the connection lives in. -/
def slotSeven : serverTopology.InstanceId .connection := 7

/-- A network holding the running connection in slot 7. -/
def withChild : ServerWorld :=
  { quiet with
      instances := fun kind slot =>
        match kind, slot with
        | .listener, _ => none
        | .connection, n => if n = slotSeven then some counting else none }

theorem withChild_seven : withChild.instances .connection slotSeven = some counting := by
  simp [withChild]

/-- Its parent is the listener, and the listener holds authority. -/
theorem the_child_is_attached :
    counting.parentage.currentParent = some ⟨.listener, listenerZero⟩ := rfl

/-! ## The honest detach -/

/-- The same incarnation, with its parentage detached and nothing else touched. -/
def detachedChild : ProcessInstance serverTopology :=
  { counting with parentage := counting.parentage.detach }

/-- And the network holding it. -/
def afterDetach : ServerWorld :=
  { quiet with
      instances := fun kind slot =>
        match kind, slot with
        | .listener, _ => none
        | .connection, n => if n = slotSeven then some detachedChild else none }

theorem afterDetach_seven :
    afterDetach.instances .connection slotSeven = some detachedChild := by
  simp [afterDetach]

/-- Only slot 7 moved. -/
theorem detach_changes_one_instance :
    serverPlan.ChangesOneInstance withChild afterDetach .connection slotSeven where
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind slot =>
      cases kind with
      | listener => rfl
      | connection =>
        simp only [LogicalProcessNetworkCore.Agrees, withChild, afterDetach]
        split
        · rename_i isSeven
          exact absurd (by rw [isSeven]) outside
        · rfl
    | _ => rfl

/--
**A detach that does what §3 says a detach does.**

The positive witness. `identityPreserved` is `rfl` in all six components,
because `detachedChild` is `counting` with one field replaced by the transition
`Grass/Process/Network/Instance.lean` defines — which is the point of stating the
field as `parentage.detach` rather than as a predicate over the result.
-/
theorem an_honest_detach :
    serverPlan.Detaches withChild afterDetach .connection slotSeven where
  wasAttached := ⟨counting, withChild_seven, by intro equal; cases equal⟩
  identityPreserved :=
    ⟨counting, detachedChild, rfl, rfl, withChild_seven, afterDetach_seven,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  onlyThatSlot := detach_changes_one_instance

/-- It is detached afterwards, and it is still running. -/
theorem the_detached_child_is_alive_and_free :
    detachedChild.parentage.IsDetached ∧ detachedChild.Live ∧
      detachedChild.parentage.knownParent = some ⟨.listener, listenerZero⟩ :=
  ⟨trivial, trivial, rfl⟩

/-! ## What a detach may not do — 1: end the child -/

/-- The child, detached *and dead*. -/
def killedChild : ProcessInstance serverTopology :=
  { counting with
      parentage := counting.parentage.detach,
      lifecycle := .died .parentDied }

def afterKill : ServerWorld :=
  { quiet with
      instances := fun kind slot =>
        match kind, slot with
        | .listener, _ => none
        | .connection, n => if n = slotSeven then some killedChild else none }

theorem afterKill_seven : afterKill.instances .connection slotSeven = some killedChild := by
  simp [afterKill]

/-- It really is an ending: live before, not live after. -/
theorem the_kill_is_an_ending : counting.Live ∧ ¬ killedChild.Live :=
  ⟨trivial, fun live => live⟩

/--
**And it is not a detach.**

Refuted by `identityPreserved`'s `lifecycle` component, which was not there.
Without it this step is an ending with no `EndsInstance`: nothing partitions the
child's outstanding bag, nothing records why it ended, and
`moving_the_ledger_ends_an_instance` never sees it.
-/
theorem a_detach_may_not_kill :
    ¬ serverPlan.Detaches withChild afterKill .connection slotSeven := by
  intro detached
  obtain ⟨fromInstance, toInstance, foundBefore, foundAfter, sameLife⟩ :=
    detached.the_child_survives
  rw [withChild_seven] at foundBefore
  rw [afterKill_seven] at foundAfter
  injection foundBefore with fromIs
  injection foundAfter with toIs
  subst fromIs; subst toIs
  exact the_kill_is_an_ending.2 (sameLife.mpr the_kill_is_an_ending.1)

/-! ## What a detach may not do — 2: invent a former parent -/

/-- The child, detached from a connection it was never attached to. -/
def reparentedChild : ProcessInstance serverTopology :=
  { counting with parentage := .detached .connection (connectionSeven 3) }

def afterForgery : ServerWorld :=
  { quiet with
      instances := fun kind slot =>
        match kind, slot with
        | .listener, _ => none
        | .connection, n => if n = slotSeven then some reparentedChild else none }

theorem afterForgery_seven :
    afterForgery.instances .connection slotSeven = some reparentedChild := by
  simp [afterForgery]

/-- The recorded history really did change. -/
theorem the_forgery_changes_the_history :
    counting.parentage.knownParent = some ⟨.listener, listenerZero⟩ ∧
      reparentedChild.parentage.knownParent = some ⟨.connection, connectionSeven 3⟩ :=
  ⟨rfl, rfl⟩

/--
**And it is not a detach either.**

Refuted by `Detaches.former_parent_is_the_one_it_had`, which is §3's "proves the
references identical" and which the old `knownParent ≠ none` field did not say.
-/
theorem a_detach_may_not_forge_its_parent :
    ¬ serverPlan.Detaches withChild afterForgery .connection slotSeven := by
  intro detached
  obtain ⟨fromInstance, toInstance, foundBefore, foundAfter, sameParent⟩ :=
    detached.former_parent_is_the_one_it_had
  rw [withChild_seven] at foundBefore
  rw [afterForgery_seven] at foundAfter
  injection foundBefore with fromIs
  injection foundAfter with toIs
  subst fromIs; subst toIs
  have stated :
      (some ⟨.connection, connectionSeven 3⟩ :
        Option (Sigma fun parentKind => serverTopology.ProcessRef parentKind))
        = some ⟨.listener, listenerZero⟩ := sameParent
  injection stated with sigma
  exact absurd (congrArg Sigma.fst sigma) (by decide)

/-! ## Why the forgery mattered -/

/-- The network before is well formed in its parentage. -/
theorem before_parentage_valid : withChild.ParentageValid := by
  intro kind slot incarnation found parentKind parent known
  cases kind with
  | listener => exact absurd found (by simp [withChild, Grass.Process.Tests.World.quiet])
  | connection =>
    simp only [withChild, Grass.Process.Tests.World.quiet] at found
    split at found
    · injection found with same
      subst same
      injection known with sigma
      exact ⟨(congrArg Sigma.fst sigma).symm, rfl⟩
    · exact absurd found (by simp)

/--
**And the forged one is not.**

`ParentageValid` quantifies over `knownParent`, which a detached child still
has, so a fabricated former parent is a recorded parenthood the topology
forbids. Until the fifth pass, a `Detaches` could take this well-formed network
to this ill-formed one — the same shape as the `Spawns.slotAgrees` defect the
fourth pass closed, one constructor over.
-/
theorem the_forgery_breaks_wellformedness : ¬ afterForgery.ParentageValid := by
  intro valid
  have permitted := valid .connection slotSeven reparentedChild afterForgery_seven
    .connection (connectionSeven 3) rfl
  exact absurd permitted.1 (by decide)

/-- The honest detach keeps it. -/
theorem the_honest_detach_preserves_wellformedness : afterDetach.ParentageValid := by
  intro kind slot incarnation found parentKind parent known
  cases kind with
  | listener => exact absurd found (by simp [afterDetach, Grass.Process.Tests.World.quiet])
  | connection =>
    simp only [afterDetach, Grass.Process.Tests.World.quiet] at found
    split at found
    · injection found with same
      subst same
      injection known with sigma
      exact ⟨(congrArg Sigma.fst sigma).symm, rfl⟩
    · exact absurd found (by simp)

end Grass.Process.Tests.Detach
