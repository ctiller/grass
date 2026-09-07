import Tests.Process.EndingFixtures

/-!
# Restarting a supervised child

`Grass/Process/Network/Transition.lean`'s `Restarts` is the sixth record this
milestone found with no witness, and it was found the same way as the other
five: a field was added to it and not one proof broke.

That field is `restartsAChild`, and the argument for it is a clause of the
well-formedness capstone. `authorized` reads the permitted-parent law off the new
incarnation's own `knownParent`, so an incarnation recording *no* parent
discharged it vacuously — and a restart could install a **root**, which
`LogicalProcessNetworkCore.RootUnique` forbids a second of. Restarting the root
is not a network step under any reading: a supervisor restarts a child, a root
has no supervisor, and if a root ends the program is over.
`Grass/Process/Network/Transition.lean`'s `Spawns` had the same hole and was
fixed in the same pass.

## What this fixture pins

`a_supervised_restart` is the witness: connection 7 died, and its supervisor
starts a fresh incarnation of it in the same slot, at a **new generation** the
step allocates.

The two negatives are the two the structure's fields are for:

* `a_restart_may_not_reuse_a_generation` — `docs/FOUNDATION.md` law 22 is that
  freshness is absence from the monotone history, so an incarnation carrying the
  dead one's generation is a stale reference that would pass a dispatch check.
  `NetworkStep.admissible` is what refuses it, and this is that refusal at a
  concrete pair of worlds.
* `a_restart_may_not_install_a_root` — `restartsAChild`.

`startsInitial` is the third field with content here and has no negative of its
own: it forces the fresh incarnation to be at a state, request and outstanding
bag its own `ProcessSpec.Initial` relates, so a restart cannot resume a child
mid-flight while calling it fresh.
-/

namespace Grass.Process.Tests.Restart

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet)
open Grass.Process.Tests.Transition (serverPlan)
open Grass.Process.Tests.Instances (counting listenerZero)
open Grass.Process.Tests.Ending (slot holding holding_slot)

/-! ## Three incarnations, two generations -/

/-- Connection 7, dead. -/
def deadChild : ProcessInstance serverTopology :=
  { counting with lifecycle := .died .supervised }

/--
A fresh incarnation of connection 7, at generation one and at its own initial
state.

`request := ⟨0⟩` because `countdown.Initial` issues `replicate request tick`, and
a restart that started holding demands would be the defect `Spawns.startsInitial`
was added to close.
-/
def freshChild : ProcessInstance serverTopology where
  kind := .connection
  ref := connectionSeven 1
  parentage := .attached .listener listenerZero
  request := ⟨0⟩
  localState := ⟨0⟩
  outstanding := 0
  lifecycle := .running

/-- The generation the restart allocates. -/
def theNewGeneration : Allocation serverTopology.Carrier where
  entries := [⟨.processGeneration, 1⟩]
  distinct := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem theNewGeneration_admissible :
    (quiet.usedNominals).Admissible theNewGeneration := by
  intro nominal _ used
  exact absurd used (by simp [Grass.Process.Tests.World.quiet])

/-- The world after: the fresh incarnation, and a history that records its
generation. -/
def afterRestart : ServerWorld :=
  { holding freshChild with
      usedNominals := quiet.usedNominals.extend theNewGeneration theNewGeneration_admissible }

theorem afterRestart_slot : afterRestart.instances .connection slot = some freshChild := by
  simp [afterRestart, holding]

/-! ## The witness -/

/--
**A supervisor restarts its dead child.**

Every field of `Restarts` at a concrete pair of worlds, and the record's first
witness. `restartsAChild` and `authorized` are both about the listener: the fresh
incarnation records it as its parent, and `serverGraph.maySpawn` permits a
listener to create connections.
-/
theorem a_supervised_restart :
    serverPlan.Restarts (holding deadChild) afterRestart .connection slot
      theNewGeneration [] [] where
  wasEnded := ⟨deadChild, holding_slot deadChild, fun live => live⟩
  nowLive := ⟨freshChild, afterRestart_slot, trivial, rfl⟩
  restartsAChild := fun incarnation found => by
    rw [afterRestart_slot] at found
    injection found with same
    subst same
    intro equal
    cases equal
  authorized := fun incarnation found _ _ known => by
    rw [afterRestart_slot] at found
    injection found with same
    subst same
    injection known with sigma
    cases sigma
    exact ⟨rfl, rfl⟩
  allocatesTheGeneration := fun incarnation found => by
    rw [afterRestart_slot] at found
    injection found with same
    subst same
    exact List.mem_cons_self
  slotAgrees := fun incarnation found => by
    rw [afterRestart_slot] at found
    injection found with same
    subst same
    exact ⟨rfl, rfl⟩
  startsInitial := fun incarnation found => by
    rw [afterRestart_slot] at found
    injection found with same
    subst same
    exact ⟨rfl, rfl, rfl, rfl⟩
  emittedIsProjected := rfl
  producesPending := by simp [afterRestart, holding, Grass.Process.Tests.World.quiet]
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind current =>
      cases kind with
      | listener => rfl
      | connection =>
        simp only [LogicalProcessNetworkCore.Agrees, afterRestart, holding]
        split
        · rename_i isSlot
          exact absurd (Or.inl (by rw [isSlot])) outside
        · rfl
    | nominals => exact absurd (Or.inr (Or.inl rfl)) outside
    | _ => rfl

/-- As a step: the generation it allocates was never allocated before. -/
def restartStep : serverPlan.NetworkStep (holding deadChild) afterRestart where
  transition := .restart .connection slot theNewGeneration [] [] a_supervised_restart
  admissible := theNewGeneration_admissible
  historyExact := rfl

/-! ## And the two it refuses -/

/--
**A restart may not reuse the dead incarnation's generation.**

`docs/FOUNDATION.md` law 22: freshness is absence from the *monotone history*,
not from the live set. `NetworkStep.admissible` is where that is spent, and this
is the refusal at a concrete step: the world before the restart already records
generation zero, so an incarnation carrying it is stale and a dispatch check
would let it through.
-/
theorem a_restart_may_not_reuse_a_generation
    (history : NominalHistory serverTopology.Carrier)
    (used : (⟨.processGeneration, 0⟩ : LogicalNominal serverTopology.Carrier) ∈ history.used)
    (reuse : Allocation serverTopology.Carrier)
    (contains : (⟨.processGeneration, 0⟩ : LogicalNominal serverTopology.Carrier) ∈ reuse.entries) :
    ¬ history.Admissible reuse :=
  fun admissible => admissible _ contains used

/--
**And a restart may not install a root.**

`restartsAChild`. Before it, `authorized` was vacuous for an incarnation
recording no parent, so a restart could put the program's root into a slot whose
previous occupant had ended — a program restarting itself, through a constructor
that means a supervisor restarting a child.
-/
theorem a_restart_may_not_install_a_root
    (rootLike : ProcessInstance serverTopology)
    (isRoot : rootLike.parentage.currentParent = none)
    (present : afterRestart.instances .connection slot = some rootLike) :
    ¬ serverPlan.Restarts (holding deadChild) afterRestart .connection slot
      theNewGeneration [] [] :=
  fun restarts => restarts.restartsAChild rootLike present isRoot

end Grass.Process.Tests.Restart
