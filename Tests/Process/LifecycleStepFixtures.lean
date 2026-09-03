import Tests.Process.EndingFixtures

/-!
# The two lifecycle constructors nothing had built

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.83. `Spawns` and `Joins` are the
constructors that create and reap a child, they carry ten and four Prop fields
between them, and **neither had ever been inhabited**. Both had absorbed fields
over several review rounds — `Joins` took `wasTerminated` and `wasChild`,
`Spawns` took `slotAgrees`, `startsInitial` and `spawnsAChild` — with, by their
own docstrings, no proof breaking. That is this milestone's seven-for-seven
signal, and here it fired twice.

Building them was not hard. `the_join` went through first try, and `the_spawn`
needed only the existing `holding` world and one allocated generation. What that
means is the usual thing: they were empty for want of trying, and every field
either structure gained had been checked by nothing.

## The negative halves

Two of `Spawns`'s guard fields are shown to bite:

* `a_spawn_may_not_install_an_orphan` — `spawnsAChild` refuses an incarnation
  with no current parent, so a spawn cannot produce a parentless process.
* `a_spawn_may_not_prestock` — `startsInitial` refuses an incarnation already
  holding a demand it never issued, which is the hole §7's `SettlesDemands`
  closes at every *step* and this field closes at the start.

One correction to `Spawns.spawnsAChild`'s docstring, which says the field stops a
spawn installing a **root**. At this topology that is not what stops it:
`ProcessParentage.root` is indexed at the graph's root kind, so `.root` does not
typecheck for a `.connection` at all. The reachable attack is the *orphan*, which
is what the negative test above uses. The field is right; its stated
justification is one case wider than the type permits.

## What these two fixtures do not test

A reviewer mutated every field of both and each mutation killed exactly one, so
the fields are load-bearing. Three things they cannot reach, at this topology:

* `Joins.wasTerminated` says the child ended "with exactly this result", and
  `TerminalResult` here is `ULift Unit` — any two results are equal, so that half
  cannot be falsified. It needs a protocol with two terminal results.
* `emittedIsProjected` and `producesPending` are checked only at the empty
  segment, where they hold for *every* `observeAt`. A spawn that emits would
  exercise them.
* There is no parent incarnation in either world. "A parent may spawn a child" is
  the shape of the step, not a fact about a listener that exists — the listener
  slot is empty in `quiet` and in `holding newborn` alike.

And see `Tests/Process/PreservationFixtures.lean`: `the_spawn`'s after-world does
not record the generation it allocates, so it fails `NominalsAllocated` and no
`NetworkStep` wraps it. §10.89.
-/

namespace Grass.Process.Tests.LifecycleStep

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet)
open Grass.Process.Tests.Transition (serverPlan)
open Grass.Process.Tests.Instances (finished listenerZero)
open Grass.Process.Tests (connectionSeven)
open Grass.Process.Tests.Ending (slot holding holding_slot)

/-! ## Joining a terminated child -/

/-- `holding x` and `quiet` differ in exactly the one connection slot. -/
theorem emptying_scope (incarnation : ProcessInstance serverTopology) :
    serverPlan.TouchesOnly (holding incarnation) quiet
      (fun fragment => fragment = .instanceState .connection slot) := by
  intro fragment outside
  cases fragment with
  | instanceState kind current =>
    cases kind with
    | listener => rfl
    | connection =>
      simp only [LogicalProcessNetworkCore.Agrees, holding, Tests.World.quiet]
      split
      · rename_i isSlot
        exact absurd (by rw [isSlot] : (Grass.Process.NetworkFragment.instanceState
          (topology := serverTopology) .connection current)
            = .instanceState .connection slot) outside
      · rfl
  | _ => rfl

/--
**A terminated child may be joined.** The corpus's first `Joins`.

`wasTerminated` and `wasChild` are the two fields review added to this structure
without breaking a proof, because there was no proof to break.
-/
theorem the_join : serverPlan.Joins (holding finished) quiet .connection slot ⟨()⟩ where
  wasTerminated := ⟨finished, holding_slot finished, rfl, rfl⟩
  wasChild := by
    intro incarnation held
    rw [holding_slot finished] at held
    cases held
    intro noParent
    cases noParent
  nowFree := rfl
  scope := emptying_scope finished

/-! ## Spawning a child -/

/-- A newly spawned connection: request zero, state zero, nothing outstanding. -/
def newborn : ProcessInstance serverTopology where
  kind := .connection
  ref := connectionSeven 0
  parentage := .attached .listener listenerZero
  request := ⟨0⟩
  localState := ⟨0⟩
  outstanding := 0
  lifecycle := .running

/-- The generation this spawn allocates. -/
def theGeneration : Allocation serverTopology.Carrier where
  entries := [⟨.processGeneration, 0⟩]
  distinct := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

/-- A spawn fills the slot and allocates, and touches nothing else. -/
theorem spawn_scope (incarnation : ProcessInstance serverTopology) :
    serverPlan.TouchesOnly quiet (holding incarnation)
      (fun fragment => fragment = .instanceState .connection slot ∨
        fragment = .nominals ∨
        (([] : Trace fixtureBoundary.Observation) ≠ [] ∧ fragment = .pending)) := by
  intro fragment outside
  cases fragment with
  | instanceState kind current =>
    cases kind with
    | listener => rfl
    | connection =>
      simp only [LogicalProcessNetworkCore.Agrees, holding, Tests.World.quiet]
      split
      · rename_i isSlot
        exact absurd (Or.inl (by rw [isSlot] : (Grass.Process.NetworkFragment.instanceState
          (topology := serverTopology) .connection current)
            = .instanceState .connection slot)) outside
      · rfl
  | _ => rfl

/--
**A parent may spawn a child into an empty slot.** The corpus's first `Spawns`.

Every one of its ten Prop fields is discharged here for the first time, including
the three local adversarial review added — `slotAgrees`, `startsInitial` and
`spawnsAChild`.
-/
theorem the_spawn :
    serverPlan.Spawns quiet (holding newborn) .connection slot theGeneration [] [] where
  wasEmpty := rfl
  nowLive := ⟨newborn, holding_slot newborn, trivial, rfl⟩
  spawnsAChild := by
    intro incarnation held
    rw [holding_slot newborn] at held
    cases held
    intro noParent
    cases noParent
  authorized := by
    intro incarnation held parentKind parent known
    rw [holding_slot newborn] at held
    cases held
    cases known
    exact ⟨rfl, rfl⟩
  allocatesTheGeneration := by
    intro incarnation held
    rw [holding_slot newborn] at held
    cases held
    exact List.mem_cons_self
  slotAgrees := by
    intro incarnation held
    rw [holding_slot newborn] at held
    cases held
    exact ⟨rfl, rfl⟩
  startsInitial := by
    intro incarnation held
    rw [holding_slot newborn] at held
    cases held
    exact ⟨rfl, rfl, rfl, rfl⟩
  emittedIsProjected := rfl
  producesPending := rfl
  scope := spawn_scope newborn

/-! ## And what its guards refuse -/

/-- The same newborn, but already let go by its parent: no current parent. -/
def orphan : ProcessInstance serverTopology where
  kind := .connection
  ref := connectionSeven 0
  parentage := .detached .listener listenerZero
  request := ⟨0⟩
  localState := ⟨0⟩
  outstanding := 0
  lifecycle := .running

/--
**A spawn may not install a parentless incarnation.**

`spawnsAChild`, refusing. `authorized` does not catch this — and, a reviewer
noted, not because it is *vacuous* here: `.detached .listener listenerZero` has
`knownParent = some ⟨.listener, listenerZero⟩`, so `authorized` is satisfied,
non-vacuously, and the mutant confirms it elaborates. The point is that
`authorized` reads `knownParent`, which a detachment does not change, so it
cannot see that the authority is gone. `spawnsAChild` reads `currentParent`,
which is what detachment empties.
-/
theorem a_spawn_may_not_install_an_orphan :
    ¬ serverPlan.Spawns quiet (holding orphan) .connection slot theGeneration [] [] := by
  intro spawns
  exact spawns.spawnsAChild orphan (holding_slot orphan) rfl

/-- The same newborn, but already holding a tick it never issued. -/
def prestocked : ProcessInstance serverTopology where
  kind := .connection
  ref := connectionSeven 0
  parentage := .attached .listener listenerZero
  request := ⟨0⟩
  localState := ⟨0⟩
  outstanding := Bag.ofList [Demand.tick]
  lifecycle := .running

/--
**A spawn may not install an instance already holding demands.**

`startsInitial`, refusing. A process spawned holding three outstanding demands
could answer them later perfectly legally, and every step law would be satisfied.
-/
theorem a_spawn_may_not_prestock :
    ¬ serverPlan.Spawns quiet (holding prestocked) .connection slot theGeneration [] [] := by
  intro spawns
  obtain ⟨_, initial⟩ := spawns.startsInitial prestocked (holding_slot prestocked)
  have issued : (Bag.ofList [Demand.tick]) = Bag.ofList (List.replicate 0 Demand.tick) :=
    initial.2.1
  have counted := congrArg Bag.card issued
  simp at counted

end Grass.Process.Tests.LifecycleStep
