import Grass.Process.Network.World
import Tests.Process.InstanceFixtures

/-!
# An assertion over the real world

`Tests/Process/AssertionFixtures.lean` discharges `agreesGlue` at a world built
for the purpose: eight fields, one per fragment family, chosen to make the law
provable. That is the right fixture for the assertion language, and it proves
nothing about the world the plan actually uses.

This file is the other half. `Grass/Process/Network/World.lean` claims that
`LogicalProcessNetworkCore` — the carrier `docs/DECISIONS.md` decision 128
requires — has the same shape, and that `logicalWorldAgreement` therefore
discharges the same law. Here it is at the M2 fixture topology, with an
assertion framed across a step that touches a different fragment.

It also pins `WellFormed`'s clauses as things a network can *fail*. Each of
these is a network that satisfies every other clause:

* `lying_network_is_not_witnessed` — an instance tagged `terminated` whose state
  is not terminal. Decision 129 puts this at the network, and
  `Grass/Process/Network/Instance.lean` says plainly it cannot enforce it.
* `mislabelled_slot_fails` — a slot holding an incarnation of another kind.
* `misplaced_instance_fails` — the half an earlier revision of `SlotsAgree`
  left open: an incarnation whose own `ref` names a *different* slot of the
  right kind, so a lookup disagrees with what it found. The old clause checked
  only the kind, and the fixture that claimed to cover it did not.
* `unallocated_generation_fails` — an incarnation whose generation is not in
  `usedNominals`. `docs/FOUNDATION.md` law 22 is the network's to enforce or
  nobody's, and an earlier revision of `WellFormed` had no clause for it at all.
* `unauthorized_parent_fails` — a recorded parent the topology's `maySpawn` does
  not permit. Decision 130 asks for this beside root uniqueness.

Root uniqueness has no failing fixture here and that is recorded rather than
papered over: `serverTopology`'s root kind has `InstanceId = Unit`, so it has
exactly one slot and two roots cannot be placed. An earlier revision claimed a
fixture for it whose hypotheses were jointly unsatisfiable — a connection
instance cannot be a root, because `ProcessParentage.root` is indexed at the
topology's root kind — so it proved nothing. `root_is_unique_here` states the
weaker true thing.
-/

namespace Grass.Process.Tests.World

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.Instances (counting finished lying listenerZero)

/-- One message type per edge; there is one edge. -/
@[reducible] def serverMessage : serverTopology.ChannelKind → Type 1 :=
  fun _ => ULift.{1, 0} Nat

/-- This fixture takes no position on obligations, which are another layer's. -/
@[reducible] def NoObligations : Type := Unit

abbrev ServerWorld :=
  LogicalProcessNetworkCore serverTopology serverMessage NoObligations

/-- A quiet network: no instances, nothing in flight, no history. -/
def quiet : ServerWorld where
  instances := fun kind _ =>
    match kind with
    | .listener => none
    | .connection => none
  shared := fun
    | .routeTable => ⟨[]⟩
    | .acceptCount => ⟨0⟩
  inFlight := fun _ _ => EscrowLedger.empty
  sessions := fun _ _ => ⟨.open, 0⟩
  obligations := ()
  observations := []
  usedNominals := NominalHistory.initial

/-- One connection accepted: the counter moved, and nothing else. -/
def afterAccept : ServerWorld :=
  { quiet with
    shared := fun
      | .routeTable => ⟨[]⟩
      | .acceptCount => ⟨1⟩ }

/-! ## An assertion over the canonical agreement -/

noncomputable abbrev serverAgreement :=
  logicalWorldAgreement serverTopology serverMessage NoObligations

/-- The route table is empty. Reads one region and nothing else. -/
def routeTableEmpty : NetworkAssertion serverAgreement where
  holds := fun network => network.shared .routeTable = ⟨[]⟩
  footprint := fun fragment => fragment = .region .routeTable
  framed := by
    intro left right agrees
    have same : left.shared .routeTable = right.shared .routeTable := agrees _ rfl
    rw [same]

/-- Nothing is in flight on the one session. -/
def nothingInFlight (session : serverTopology.ChannelId ()) :
    NetworkAssertion serverAgreement where
  holds := fun network => (network.inFlight () session).created = []
  footprint := fun fragment => fragment = .escrow () session
  framed := by
    intro left right agrees
    have same : left.inFlight () session = right.inFlight () session := agrees _ rfl
    rw [same]

/-- They read different fragments, so they are separate. -/
theorem regions_and_escrow_are_separate (session : serverTopology.ChannelId ()) :
    NetworkAssertion.Separate routeTableEmpty (nothingInFlight session) := by
  rintro fragment (rfl : fragment = _) (overlap : _ = _)
  simp at overlap

/--
**Framing, over the world a plan actually steps through.**

Accepting a connection writes `acceptCount` and leaves the route table alone, so
the route-table assertion survives without being re-proved. This is
`frame_of_disjoint_scope` in the shape `docs/PROCESS.md` §8 states it, at
`logicalWorldAgreement` rather than at a world invented for the fixture.
-/
theorem routeTable_survives_accept : routeTableEmpty.holds afterAccept :=
  routeTableEmpty.frame_of_disjoint_scope
    (scope := fun fragment => fragment = .region .acceptCount)
    (fun _ inScope overlap => by
      rw [inScope] at overlap
      injection overlap with regions
      exact absurd regions (by decide))
    (before := quiet)
    (fun fragment outside => by
      cases fragment with
      | region region =>
        cases region
        · rfl
        · exact absurd rfl outside
      | _ => rfl)
    rfl

/-- And so does the escrow assertion, which the same step also leaves alone. -/
theorem escrow_survives_accept (session : serverTopology.ChannelId ()) :
    (nothingInFlight session).holds afterAccept :=
  (nothingInFlight session).frame_of_disjoint_scope
    (scope := fun fragment => fragment = .region .acceptCount)
    (fun _ inScope overlap => by
      subst inScope
      have named : NetworkFragment.region (topology := serverTopology)
          Region.acceptCount = NetworkFragment.escrow () session := overlap
      exact absurd named (by simp))
    (before := quiet)
    (fun fragment outside => by
      cases fragment with
      | region region =>
        cases region
        · rfl
        · exact absurd rfl outside
      | _ => rfl)
    rfl

/-! ## Well-formedness, and the three ways to fail it -/

/-- The quiet network is well formed: it holds no instances to be wrong about. -/
theorem quiet_is_wellFormed : quiet.WellFormed where
  slotsAgree := by
    intro kind slot incarnation found
    cases kind <;> exact absurd found (by simp [quiet])
  lifecyclesWitnessed := by
    intro kind slot incarnation found
    cases kind <;> exact absurd found (by simp [quiet])
  rootUnique := by
    intro _ _ _ _ found _ _ _
    exact absurd found (by simp [quiet])
  parentageValid := by
    intro kind slot incarnation found
    cases kind <;> exact absurd found (by simp [quiet])
  nominalsAllocated := by
    intro kind slot incarnation found
    cases kind <;> exact absurd found (by simp [quiet])
  reroutesLand := by
    intro _ _ _ _ rerouted
    exact absurd rerouted (by simp [quiet, EscrowLedger.empty])

/-! ### The ways a network fails

Each of these differs from `quiet` in exactly one respect.
-/

/-- The listener slot, and the one incarnation this fixture puts in it. -/
def listenerSlot : serverTopology.InstanceId .listener := ()

/-- A listener incarnation that is the root, correctly placed and allocated. -/
def rootListener : ProcessInstance serverTopology where
  kind := .listener
  ref := Instances.listenerZero
  parentage := .root
  request := ⟨0⟩
  localState := ⟨0⟩
  lifecycle := .running

/-- A network holding it, with its generation actually allocated. -/
def withRoot : ServerWorld :=
  { quiet with
    instances := fun kind _ =>
      match kind with
      | .listener => some rootListener
      | .connection => none
    usedNominals := ⟨[⟨.processGeneration, 0⟩], by decide⟩ }

/--
**Root uniqueness holds here, and cannot fail here.**

`serverTopology`'s root kind has `InstanceId = Unit`, so there is one root slot
and two roots cannot be placed. The clause is real — it says two root
incarnations occupy the *same slot* — but this topology cannot witness its
failure, and saying so is better than a fixture whose hypotheses are jointly
unsatisfiable, which is what an earlier revision had.
-/
theorem root_is_unique_here : withRoot.RootUnique := by
  intro leftSlot rightSlot _ _ _ _ _ _
  exact Subsingleton.elim leftSlot rightSlot

/--
**A network cannot hold a process tagged terminated that has not terminated.**

Decision 129's obligation, biting. `lying` is `counting` with its tag changed
and nothing else.
-/
theorem lying_network_is_not_witnessed :
    ¬ ({ quiet with
        instances := fun kind _ =>
          match kind with
          | .listener => none
          | .connection => some lying } : ServerWorld).LifecyclesWitnessed := by
  intro witnessed
  exact Instances.terminated_at_three_is_not_witnessed
    (witnessed .connection 7 lying rfl)

/--
**A slot holds an incarnation of its own kind.**

Putting the connection incarnation in a listener slot fails the first half of
`SlotsAgree`.
-/
theorem mislabelled_slot_fails :
    ¬ ({ quiet with
        instances := fun kind _ =>
          match kind with
          | .listener => some counting
          | .connection => none } : ServerWorld).SlotsAgree := by
  intro agree
  obtain ⟨sameKind, _⟩ := agree .listener () counting rfl
  exact absurd sameKind (by decide)

/--
**And it holds the incarnation whose reference names *that* slot.**

The second half, and the one an earlier revision left open. `counting`'s `ref`
is `connectionSeven 0`, whose instance id is 7, so putting it in connection slot
3 is a network where a lookup disagrees with the thing it found — and under the
old kind-only clause it was well formed.
-/
theorem misplaced_instance_fails :
    ¬ ({ quiet with
        instances := fun kind _ =>
          match kind with
          | .listener => none
          | .connection => some counting } : ServerWorld).SlotsAgree := by
  intro agree
  obtain ⟨sameKind, sameSlot⟩ := agree .connection 3 counting rfl
  cases sameKind
  exact absurd sameSlot (by decide)

/--
**A live incarnation's generation was allocated.**

`docs/FOUNDATION.md` law 22. `quiet.usedNominals` is empty, so any instance in
it has a generation that was never allocated — and every other clause is
satisfied.
-/
theorem unallocated_generation_fails :
    ¬ ({ quiet with
        instances := fun kind _ =>
          match kind with
          | .listener => some rootListener
          | .connection => none } : ServerWorld).NominalsAllocated := by
  intro allocated
  have inHistory := allocated .listener () rootListener rfl
  exact absurd inHistory (by simp [quiet, ProcessTopologyCore.ProcessRef.Allocated,
    NominalHistory.initial, rootListener])

/-- With the generation allocated, the same network passes. -/
theorem withRoot_nominals_allocated : withRoot.NominalsAllocated := by
  intro kind slot incarnation found
  cases kind with
  | listener =>
    have same : incarnation = rootListener := by
      simp [withRoot, quiet] at found
      exact found.symm
    rw [same]
    simp [ProcessTopologyCore.ProcessRef.Allocated, withRoot, rootListener,
      Instances.listenerZero]
  | connection => exact absurd found (by simp [withRoot, quiet])

/--
**A recorded parent is one the topology permits.**

`serverTopology.maySpawn` allows only listener-spawns-connection, so a listener
claiming a connection parent fails. Decision 130 puts this at the network beside
root uniqueness, and an earlier revision had no clause for it.
-/
theorem unauthorized_parent_fails :
    ¬ ({ quiet with
        instances := fun kind _ =>
          match kind with
          | .listener =>
            some { rootListener with
                    parentage := .attached .connection (connectionSeven 0) }
          | .connection => none } : ServerWorld).ParentageValid := by
  intro valid
  have permitted := valid .listener () _ rfl .connection (connectionSeven 0) rfl
  exact absurd permitted.1 (by decide)

/-- A network holding the finished connection, in its own slot. -/
def withFinished : ServerWorld :=
  { quiet with
    instances := fun kind slot =>
      match kind, slot with
      | .listener, _ => none
      | .connection, n => if n = 7 then some finished else none }

/-- Which is well formed on the lifecycle clause: the stored result is reachable. -/
theorem withFinished_lifecycles_witnessed : withFinished.LifecyclesWitnessed := by
  intro kind slot incarnation found
  cases kind with
  | listener => exact absurd found (by simp [withFinished, quiet])
  | connection =>
    by_cases isSeven : slot = 7
    · have same : incarnation = finished := by
        simp [withFinished, quiet, isSeven] at found
        exact found.symm
      rw [same]
      exact Instances.terminated_at_zero_is_witnessed
    · exact absurd found (by simp [withFinished, quiet, isSeven])

/-- And it is correctly placed, which the old clause could not have said. -/
theorem withFinished_slots_agree : withFinished.SlotsAgree := by
  intro kind slot incarnation found
  cases kind with
  | listener => exact absurd found (by simp [withFinished, quiet])
  | connection =>
    by_cases isSeven : slot = 7
    · have same : incarnation = finished := by
        simp [withFinished, quiet, isSeven] at found
        exact found.symm
      subst same
      exact ⟨rfl, by simp [finished, Instances.finished, Instances.counting, isSeven]⟩
    · exact absurd found (by simp [withFinished, quiet, isSeven])

end Grass.Process.Tests.World
