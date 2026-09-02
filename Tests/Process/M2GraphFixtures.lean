import Grass.Process.Network.Topology
import Tests.Process.M1Fixtures

/-!
# Fixtures for the M2 graph and topology

M2 is not finished — the transition family, the channel contracts, and the
escrow laws are still to come — so these are not its exit criteria. They are the
checks that the two landed modules say what their docstrings claim, on a graph
small enough that a reviewer can hold it in their head.

The graph is a two-role server: one `listener` singleton that may spawn
`connection` instances, one immutable route table both read, and one counter
only the listener writes.
-/

namespace Grass.Process.Tests

open Grass.Process

/-! ## A two-role graph -/

/-- The roles. -/
inductive Role
  | listener
  | connection
  deriving DecidableEq, Repr

/-- The shared regions. -/
inductive Region
  | routeTable
  | acceptCount
  deriving DecidableEq, Repr

/-- The boundary this graph's root faces. Nothing is required of the platform. -/
@[reducible] def fixtureBoundary : DriverBoundary.{0} where
  ExternalEvent := ExternalEvent
  Demand := Demand
  Result := Result
  Observation := Observation
  requirements := RequirementSet.empty

/-- The root protocol exposes the boundary: every event is delivered, every
demand is exported, every observation is visible. -/
@[reducible] def fixtureExposure :
    ProtocolExposesBoundary countdownLifted fixtureBoundary where
  deliver := id
  exportDemand := some
  accept := fun equal result => by
    cases equal
    exact result
  observe := some

/-- The scope this fixture's registry fragment owns. -/
@[reducible] def graphScope : ScopeId := ⟨["Tests", "Process", "Graph"]⟩

/-- Both roles speak the same protocol; the fixture is about the graph, not the
protocols. -/
@[reducible] def graphRegistry : ProtocolRegistry.{0, 1, 0} :=
  (⟨graphScope, Unit, fun _ => countdownLifted⟩ :
    RegistryFragment.{0, 1, 0}).toRegistry

/-- The graph. -/
@[reducible] def serverGraph :
    ProcessGraph.{0, 1, 0, 0} graphRegistry fixtureBoundary where
  ProcessKind := Role
  SharedRegion := Region
  SharedState := fun
    | .routeTable => ULift (List String)
    | .acceptCount => ULift Nat
  protocolKey := fun _ => ()
  root := .listener
  rootBoundary := fixtureExposure
  maySpawn := fun parent child => parent = .listener ∧ child = .connection
  sharedAccess := fun role region =>
    match role, region with
    | .listener, .routeTable => .readOnly
    | .listener, .acceptCount => .readWrite
    | .connection, .routeTable => .readOnly
    | .connection, .acceptCount => .none
  population :=
    { bound := fun
        | .listener => .exactlyOne
        | .connection => .boundedByResourcePolicy
      identity := fun
        | .listener => .static
        | .connection => .generational }

/-! ## What the graph says -/

/-- The route table is immutable: no role may write it. -/
theorem routeTable_immutable : serverGraph.Immutable .routeTable := by
  intro role; cases role <;> rfl

/-- So no pair of roles conflicts over it, whatever they do elsewhere. -/
theorem no_conflict_over_routeTable (left right : Role) :
    ¬ serverGraph.Conflicting left right .routeTable :=
  serverGraph.immutable_no_conflict routeTable_immutable left right

/-- The accept counter is *not* immutable: the listener writes it. -/
theorem acceptCount_not_immutable : ¬ serverGraph.Immutable .acceptCount := by
  intro immutable
  exact absurd (immutable .listener) (by decide)

/--
The listener does not conflict with a connection over the counter, because a
connection has no access to it at all.

This is the fixture that matters for law 20: the counter can be charged to the
listener alone, and no interference invariant is owed.
-/
theorem no_conflict_over_acceptCount :
    ¬ serverGraph.Conflicting .listener .connection .acceptCount := by
  intro conflict
  exact absurd conflict.2.1 LogicalAccess.not_touches_none

/-- The listener conflicts with *itself* over the counter — which is exactly why
its population is `exactlyOne`. -/
theorem listener_self_conflict_over_acceptCount :
    serverGraph.Conflicting .listener .listener .acceptCount :=
  ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

/--
Two roles that only ever touch a region atomically still conflict.

The counter is `readWrite` here, so this is stated on the access values
directly. It is the case an atomic exemption would have discharged for free:
two roles atomically incrementing a shared counter do not race, and they do
still owe the invariant that bounds it.
-/
theorem atomic_pair_still_interferes :
    LogicalAccess.atomicReadWrite.Interferes LogicalAccess.atomicReadWrite :=
  LogicalAccess.atomic_interferes_atomic

/-- And they provably do not race, which is the other half of the split. -/
theorem atomic_pair_does_not_race :
    ¬ LogicalAccess.atomicReadWrite.DataRaces LogicalAccess.atomicReadWrite :=
  LogicalAccess.atomic_not_dataRaces_atomic

/-- Every role can actually occur. -/
theorem no_dead_roles : serverGraph.NoDeadRoles := by
  intro role
  cases role with
  | listener => exact .root
  | connection => exact .spawned .root ⟨rfl, rfl⟩

/--
The connection role's bound is deferred to a resource certificate.

This is the fixture a reviewer should look for: the graph type-checks, the
population law is total, and yet the number of live connections is bounded by
nothing in this file. `PopulationBound.boundedByResourcePolicy` is where that
debt is written down.
-/
theorem connection_bound_is_deferred :
    serverGraph.population.DeferredToResources .connection := rfl

/-- The listener's bound is not deferred; it is `exactlyOne` here. -/
theorem listener_bound_is_not_deferred :
    ¬ serverGraph.population.DeferredToResources .listener := by
  intro deferred
  exact PopulationBound.noConfusion deferred

/-! ## Identity and staleness -/

/-- The topology over that graph. Connections are identified by a number. -/
@[reducible] def serverTopology :
    ProcessTopology.{0, 1, 0, 0} graphRegistry fixtureBoundary where
  toProcessGraph := serverGraph
  Carrier := Nat
  carrierDecidableEq := inferInstance
  InstanceId := fun
    | .listener => Unit
    | .connection => Nat
  ChannelKind := Unit
  endpoints := fun _ => (.listener, .connection)
  spawnAuthority := fun _ _ _ _ _ => True

/-- Connection 7, first incarnation. -/
@[reducible] def connectionSeven (generation : Nat) :
    serverTopology.ProcessRef .connection where
  instanceId := 7
  generation := ⟨.processGeneration, generation⟩
  isGeneration := rfl

/--
Reusing instance number 7 in a new incarnation is a different reference.

This is the law 22 property a driver relies on when it recycles a numeric slot:
the instance identity is the same, and the reference is still stale.
-/
theorem reused_instance_is_stale :
    (connectionSeven 0).Stale (connectionSeven 1) := by
  apply ProcessTopology.ProcessRef.stale_of_generation_ne
  intro equal
  exact absurd (congrArg LogicalNominal.carrier equal) (by decide)

/-- The same incarnation is not stale. -/
theorem same_incarnation_is_not_stale :
    ¬ (connectionSeven 3).Stale (connectionSeven 3) := by
  intro stale
  exact stale rfl

/--
A reference whose generation is in the history cannot be one a spawn is handing
out now.

The two halves of a dispatch check are independent: this is the half that stops
a fabricated reference, and `Stale` is the half that stops a late one.
-/
theorem allocated_is_not_fresh
    (history : NominalHistory Nat)
    (allocated : (connectionSeven 2).Allocated history) :
    ¬ history.Fresh (connectionSeven 2).generation :=
  ProcessTopology.ProcessRef.not_fresh_of_allocated allocated

/-- A message occurrence's identity is never a process generation. -/
theorem occurrence_is_not_a_generation
    {channel : serverTopology.ChannelId ()}
    (occurrence :
      serverTopology.MessageOccurrence channel (Message := ULift Unit) (.up ())) :
    occurrence.id ≠ (connectionSeven 0).generation :=
  ProcessTopology.occurrence_kind_distinct occurrence (connectionSeven 0)

end Grass.Process.Tests
