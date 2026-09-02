import Grass.Process.Network.Transition
import Tests.Process.ChannelFixtures

/-!
# A plan, and a step of it

`Grass/Process/Network/Transition.lean` says what one step of a logical process
network is, over an abstract plan. This file builds a plan — the first one, at
the M2 fixture topology — and takes a step of it.

What it pins:

* `serverPlan` exists. `ProcessPlan` ties a topology, a message family, the send
  and receive relations, and a contract per edge into one object at the
  canonical agreement for the full network. Until now nothing had shown the four
  could be satisfied together.
* `receiving_resolves_the_escrow` builds a `ResolvesEscrow`: an occurrence that
  was outstanding is now `received`, the ledger only moved forward, and nothing
  outside that session's escrow changed.
* `cannot_receive_twice` is the teeth — an occurrence already ended cannot be
  the subject of another resolution, which is the affine half of `docs/PROCESS.md`
  §3's resolve token stated at the step rather than at the ledger.
* `observations_did_not_move` reads the scope back out: the step's own
  `TouchesOnly` proof says the observation trace is unchanged, so a weave
  invariant over observations frames past this step without knowing what it was.

The ledgers here decide occurrence equality classically. Occurrences are
`LogicalNominal`-indexed sigma types with no `DecidableEq`, and the alternative
— a uniform `resolution` — cannot satisfy `noFabrication`, since it would claim
to have ended occurrences the ledger never escrowed.
-/

namespace Grass.Process.Tests.Transition

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld NoObligations quiet)
open Grass.Process.Tests.Channel (ServerMessage wire liveSteps liveChannel)

/--
The plan.

Its `steps` and `channel` are `Tests/Process/ChannelFixtures.lean`'s, which is
the point: the contract that file checks in isolation is the contract this plan
installs, at the same agreement.
-/
noncomputable def serverPlan : ProcessPlan graphRegistry fixtureBoundary NoObligations where
  topology := serverTopology
  message := World.serverMessage
  steps := fun _ => liveSteps
  channel := fun _ => liveChannel

/-- The world a step of it moves through is the one the other fixtures use. -/
theorem plan_world_is_the_fixture_world :
    serverPlan.LogicalProcessNetwork = ServerWorld := rfl

/-! ## One occurrence, in flight and then received -/

/-- The payload. -/
def payload : ServerMessage := ⟨7⟩

/-- Its occurrence on `wire`. -/
def occurrenceOf : serverTopology.ChannelOccurrence () payload :=
  ⟨wire, { id := ⟨.messageOccurrence, 0⟩, isMessage := rfl }⟩

/-- The escrow entry it becomes. -/
def escrowed : EdgeOccurrence serverTopology World.serverMessage () :=
  ⟨payload, occurrenceOf⟩

open Classical in
/-- A ledger holding it, in flight. -/
noncomputable def pendingLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun _ => none
  noFabrication := by simp
  coalesceCarrierLater := by simp
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by simp

open Classical in
/-- And the same ledger after the receiver consumed it. -/
noncomputable def settledLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun occurrence => if occurrence = escrowed then some .received else none
  noFabrication := by
    intro occurrence resolved
    by_cases isIt : occurrence = escrowed
    · simp [isIt]
    · simp [isIt] at resolved
  coalesceCarrierLater := by
    intro occurrence carrier merged
    by_cases isIt : occurrence = escrowed
    · simp [isIt] at merged
    · simp [isIt] at merged
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by
    intro occurrence reason acknowledged
    by_cases isIt : occurrence = escrowed
    · simp [isIt] at acknowledged
    · simp [isIt] at acknowledged

open Classical in
/--
What each session holds, before (`false`) and after (`true`) the receive.

One function rather than two inline lambdas, so that "off `wire` the two worlds
agree" is a lemma with clean types rather than a tactic block fighting the
classical decidability instance.

Only `wire` holds anything. That matters for the step's scope proof: a world
whose every session changed would not have touched one fragment.
-/
noncomputable def ledgerAt (settled : Bool) (session : serverTopology.ChannelId ()) :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) :=
  if session = wire then (if settled then settledLedger else pendingLedger)
  else EscrowLedger.empty

/-- On `wire`, it is the ledger the step is about. -/
@[simp] theorem ledgerAt_wire (settled : Bool) :
    ledgerAt settled wire = if settled then settledLedger else pendingLedger := by
  simp [ledgerAt]

/-- Off `wire`, the two worlds hold the same thing — which is the scope claim. -/
theorem ledgerAt_off_wire {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) : ledgerAt false session = ledgerAt true session := by
  simp [ledgerAt, notWire]

/-- The world before the receive. -/
noncomputable def beforeReceive : ServerWorld :=
  { quiet with inFlight := fun _ => ledgerAt false }

/-- And after it. -/
noncomputable def afterReceive : ServerWorld :=
  { quiet with inFlight := fun _ => ledgerAt true }

/-- What each world holds on `wire`. -/
@[simp] theorem beforeReceive_wire :
    beforeReceive.inFlight () wire = pendingLedger := by
  simp [beforeReceive]

@[simp] theorem afterReceive_wire :
    afterReceive.inFlight () wire = settledLedger := by
  simp [afterReceive]

/-- And off it, the two agree. -/
theorem worlds_agree_off_wire {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) :
    beforeReceive.inFlight () session = afterReceive.inFlight () session :=
  ledgerAt_off_wire notWire

/-- And what `settledLedger` says about the occurrence. -/
@[simp] theorem settled_resolution :
    settledLedger.resolution escrowed = some .received := by
  simp [settledLedger]

@[simp] theorem pending_resolution :
    pendingLedger.resolution escrowed = none := rfl

/-! ## The step -/

/--
**A receive resolves the escrow.**

Every field of `ResolvesEscrow` at a concrete pair of worlds: the occurrence was
outstanding, it is now `received` and nothing else, the ledger only moved
forward, and the step's scope is this session's escrow fragment alone.
-/
theorem receiving_resolves_the_escrow :
    serverPlan.ResolvesEscrow beforeReceive afterReceive () wire escrowed .received where
  wasOutstanding := by
    rw [beforeReceive_wire]
    exact ⟨List.mem_cons_self, rfl⟩
  nowResolved := by
    rw [afterReceive_wire]
    exact settled_resolution
  ledgerExtends := by
    rw [beforeReceive_wire, afterReceive_wire]
    exact
      { createdPrefix := List.prefix_refl _
        resolutionPermanent := by
          intro occurrence resolution ended
          exact absurd ended (by simp [pendingLedger])
        cancelRequestMonotone := by
          intro occurrence requested
          exact absurd requested (by simp [pendingLedger]) }
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := by
        intro isWire
        subst isWire
        exact outside rfl
      exact worlds_agree_off_wire notWire
    | _ => rfl

/--
**And it cannot happen twice.**

The affine half of §3's resolve token, at the step. `ResolvesEscrow` demands the
occurrence was outstanding *before*, so a second receive of the same occurrence
— from the world the first one produced — is unconstructible.
-/
theorem cannot_receive_twice
    (again : serverPlan.ResolvesEscrow afterReceive afterReceive () wire escrowed .received) :
    False :=
  again.cannot_resolve_twice (earlier := .received) (by rw [afterReceive_wire]; exact settled_resolution)

/--
**The observation trace did not move.**

Read straight out of the step's own scope proof. A weave invariant over
observations frames past this step without knowing what the step was, which is
what `docs/PROCESS.md` §8's `Disjoint (TransitionScope step) Scope` buys.
-/
theorem observations_did_not_move :
    beforeReceive.observations = afterReceive.observations :=
  receiving_resolves_the_escrow.observations_untouched

/-- As did every instance slot, which the same proof gives. -/
theorem instances_did_not_move (kind : serverTopology.ProcessKind)
    (slot : serverTopology.InstanceId kind) :
    beforeReceive.instances kind slot = afterReceive.instances kind slot :=
  receiving_resolves_the_escrow.scope (.instanceState kind slot) (by simp)

end Grass.Process.Tests.Transition
