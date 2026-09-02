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

It also pins `WellFormed`'s three clauses as things a network can *fail*:

* `lying_network_is_not_witnessed` — a network holding an instance tagged
  `terminated` whose state is not terminal. Decision 129 puts this obligation at
  the network, and `Grass/Process/Network/Instance.lean` says plainly it cannot
  enforce it, having no network to enforce it over. This is the enforcement, and
  this is it biting.
* `two_roots_are_not_unique` — decision 130 puts root uniqueness at the network
  rather than on each instance's author, so a network with two roots is a
  network that fails a law, not an instance that fails one.
* `mislabelled_slot_fails` — a slot holding an incarnation of another kind.
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

/-- A quiet network: the listener is running, nothing is in flight. -/
def quiet : ServerWorld where
  instances := fun kind _ =>
    match kind with
    | .listener => none
    | .connection => none
  shared := fun
    | .routeTable => ⟨[]⟩
    | .acceptCount => ⟨0⟩
  inFlight := fun _ _ => EscrowLedger.empty
  sessions := fun _ _ => .open
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
    intro leftKind _ _ _ _ _ found _ _ _
    cases leftKind <;> exact absurd found (by simp [quiet])

/-- A network holding the finished connection, in its slot. -/
def withFinished : ServerWorld :=
  { quiet with
    instances := fun kind _ =>
      match kind with
      | .listener => none
      | .connection => some finished }

/-- Which is well formed: the stored result is one the protocol reaches. -/
theorem withFinished_lifecycles_witnessed : withFinished.LifecyclesWitnessed := by
  intro kind slot incarnation found
  cases kind with
  | listener => exact absurd found (by simp [withFinished, quiet])
  | connection =>
    have same : incarnation = finished := by
      simp [withFinished, quiet] at found
      exact found.symm
    rw [same]
    exact Instances.terminated_at_zero_is_witnessed

/--
**A network cannot hold a process tagged terminated that has not terminated.**

Decision 129's network-level obligation, biting. `lying` is `counting` with its
tag changed and nothing else, and putting it in a slot makes the network fail.
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
**A slot holds what it says it holds.**

Putting the connection incarnation in a listener slot fails `SlotsAgree`. Without
it a lookup would disagree with the thing it found.
-/
theorem mislabelled_slot_fails :
    ¬ ({ quiet with
        instances := fun kind _ =>
          match kind with
          | .listener => some counting
          | .connection => none } : ServerWorld).SlotsAgree := by
  intro agree
  exact absurd (agree .listener () counting rfl) (by decide)

/--
**Two roots are a network defect, not an instance defect.**

Decision 130 puts root uniqueness at the network "rather than proof fields paid
by each instance author", so both instances below are perfectly well formed on
their own and the network holding both is not.
-/
theorem two_roots_are_not_unique
    (listenerRoot : ProcessInstance serverTopology)
    (connectionRoot : ProcessInstance serverTopology)
    (_listenerIsListener : listenerRoot.kind = .listener)
    (_connectionIsConnection : connectionRoot.kind = .connection)
    (bothRoots : listenerRoot.IsRoot ∧ connectionRoot.IsRoot) :
    ¬ ({ quiet with
        instances := fun kind _ =>
          match kind with
          | .listener => some listenerRoot
          | .connection => some connectionRoot } : ServerWorld).RootUnique := by
  intro unique
  have sameKind :=
    unique .listener () listenerRoot .connection 7 connectionRoot rfl rfl
      bothRoots.1 bothRoots.2
  exact absurd sameKind (by decide)

end Grass.Process.Tests.World
