import Grass.Process.Cancellation

/-!
# The cancellation facet is sufficient, and its bound runs the other way

This file imports **only** `Grass.Process.Cancellation`. A cancellation author
writes a scope summary, a policy and a certificate against exactly this, and the
guards at the end show what they do *not* get: no plan, no channel contract, no
assertion, no transition family.

That direction is the interesting one. `Grass/Process.lean` excludes
cancellation; this excludes the network. Neither facet is a subset of the other,
which is why `docs/DECISIONS.md` decision 134 makes them two rather than one
with a bigger closure.

It is also `docs/PROCESS_SHARDING.md` §4's argument made visible in the import
graph: a policy is exact against one scope's discovered blocking calls, so it
has no business seeing a channel, and adding a `Sleep` rebuilds that scope's
certificate and the bounded aggregate path above it rather than anything
network-shaped.
-/

namespace Grass.Process.Tests.FacadeCancellation

open Grass.Process
open Grass.Specification

/-! ## A cancellation certificate, authored against the facet alone -/

/-- The scope this fixture's process owns. -/
def scope : ScopeId := ⟨["Tests", "Process", "Facade"]⟩

/-- Its one declared cancellation point. -/
def shutdown : CancellationPointId := ⟨scope, "shutdown"⟩

/-- And the one blocking call discovered inside it. -/
def sleep : BlockingCallId := ⟨scope, "sleep"⟩

/-- What the scope publishes. -/
def summary : ProcessScopeSummary where
  scope := scope
  publicCancellationPoints := [shutdown]
  blockingCalls := [sleep]
  pointsDistinct := by simp
  callsDistinct := by simp

/--
The policy: the one blocking call is cancellable at the one declared point.

The point of this declaration is that it typechecks against
`import Grass.Process.Cancellation` and nothing else — `CancellationPolicy`,
`CancellationPointPolicy`, `CancellationMask` and `BlockingCallDisposition` all
arrive through the facet.
-/
def policy : CancellationPolicy where
  points := [shutdown]
  pointPolicy := fun _ =>
    { id := shutdown, entryMask := .cancellationPoint, exitMask := .interruptible }
  atomicRegions := []
  blockingCalls := [sleep]
  callDisposition := fun _ => .cancellableAt shutdown

/-- It covers the scope exactly, which is what `Covers` is list equality for. -/
theorem policy_covers : policy.Covers summary := ⟨rfl, rfl⟩

/-- Every region it names is declared — vacuously, since it names none. -/
theorem policy_regions_declared : policy.RegionsDeclared := by
  intro call _ region disposition
  exact absurd disposition (by simp [policy])

/-- And every point it names is declared, which here is the one. -/
theorem policy_points_declared : policy.PointsDeclared := by
  intro call _ point disposition
  have isShutdown : point = shutdown := by
    simp [policy] at disposition
    exact disposition.symm
  rw [isShutdown]
  exact List.mem_cons_self

/-- A cancellation reason is nameable too: it is the point that acknowledged it. -/
def acknowledgedAtShutdown : CancelReason := ⟨shutdown⟩

/-! ## And the facet is bounded

Each name below belongs to the network, which a cancellation author has no
business seeing. If `Grass/Process/Cancellation.lean`'s two imports ever grow to
reach one, the guard stops matching and this file fails.
-/

/-! The plan. -/

/--
error: Unknown identifier `Grass.Process.ProcessPlan`
-/
#guard_msgs in
example := Grass.Process.ProcessPlan

/-! Channel contracts. -/

/--
error: Unknown identifier `Grass.Process.ChannelContract`
-/
#guard_msgs in
example := Grass.Process.ChannelContract

/-! The assertion language. -/

/--
error: Unknown identifier `Grass.Process.NetworkAssertion`
-/
#guard_msgs in
example := Grass.Process.NetworkAssertion

/-! The escrow ledger. -/

/--
error: Unknown identifier `Grass.Process.EscrowLedger`
-/
#guard_msgs in
example := Grass.Process.EscrowLedger

/-!
And the topology.

This is the guard that matters most for §4's argument: a policy indexed by a
plan would make `callsExact` a global equality, so adding one `Sleep` anywhere
would invalidate every cancellation proof in the program. A facet that cannot
name a topology cannot accidentally acquire one.
-/

/--
error: Unknown identifier `Grass.Process.ProcessTopologyCore`
-/
#guard_msgs in
example := Grass.Process.ProcessTopologyCore

end Grass.Process.Tests.FacadeCancellation
