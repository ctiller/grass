import Grass.Process.Cancellation.Identity
import Grass.Process.Spec

/-!
# Scoped cancellation policy

`agent-bus` disposition `coord1:6`, ruling on issue `c-process:5`:

> the scalable scope-indexed cancellation form is canonical. Define exactly one
> core `CancellationPolicy` indexed by a scoped cancellation-point family, use
> `blockingCalls` consistently, and let `ScopedCancellationCertificate` tie that
> policy exactly to a `ProcessScopeSummary` including discovered blocking calls.
> Whole-plan cancellation is hierarchical composition of scoped certificates.
> Spike syntax may infer the root scope from the named process, but that is
> elaborator sugar, not another Lean arity.

The defect that ruling settles was three types with one name: `docs/PROCESS.md`
§5 indexed a policy by a network and a machine source, `docs/PROCESS_SHARDING.md`
§4 by a scope summary, and `Spikes/4_Web_Server/Cancellation.lean` by a bare
`ProcessSpec` — with the same field spelled `blockingCalls` in one document and
`calls` in the other.

## Why the scope-indexed form is the one that scales

`docs/PROCESS_SHARDING.md` §4 gives the reason directly:

> `callsExact` compares only the calls discovered in that scope. An added
> blocking call rebuilds its local certificate and the bounded aggregate path.
> It does not change a million-entry global key-set equality.

A policy indexed by the whole plan makes `callsExact` a global equality, so
adding one `Sleep` anywhere invalidates every cancellation proof in the program.
Indexed by a scope, the same edit invalidates one certificate and the aggregate
path above it. `Tests/Process/CancellationFixtures.lean` proves both halves:
that a new blocking call rejects the scope's own old certificate, and that it
leaves a sibling scope's certificate untouched.

## What is here and what is not

This module is the policy, the scope summary it is exact against, and the
composition that makes whole-plan cancellation a fold rather than a monolith.
The nominal identities it is written over — masks, point, call and region ids,
and `CancelReason` — are `Grass/Process/Cancellation/Identity.lean`'s, so that
a consumer needing only an identity does not import a policy.

The *liveness* half of cancellation — that a requested cancellation actually
reaches a disposition under declared premises, which `docs/PROCESS.md` §3 states
as `ProcessTerminationContract.reachesSafePoint` — is not here. It needs the
network transition family, and it is M3 in
`docs/PROCESS_IMPLEMENTATION_PLAN.md`. What this module gives that argument is
the exact set of points and calls it must range over.
-/

namespace Grass.Process

open Grass.Specification (ScopeId)

/--
A region that refuses cancellation, and the bound that makes the refusal
acceptable.

`docs/PROCESS.md` §3: "A call may be uncancellable only inside a named bounded
atomic region." The bound is a field rather than a promise because an
unbounded uncancellable region is exactly how a cooperative-cancellation claim
becomes false.
-/
structure BoundedAtomicRegion where
  /-- Which region. -/
  id : AtomicRegionId
  /-- The bound on internal steps before it ends. -/
  stepBound : Nat
  /-- A zero-step region is not a region; it would refuse nothing. -/
  positive : 0 < stepBound

/-- What a declared cancellation point does with a pending request. -/
structure CancellationPointPolicy where
  /-- Which point. -/
  id : CancellationPointId
  /-- The mask on entry to the point. -/
  entryMask : CancellationMask
  /-- The mask after it. -/
  exitMask : CancellationMask
  deriving DecidableEq, Repr

/-- How a discovered blocking call is made acceptable. -/
inductive BlockingCallDisposition
  /-- The call is cancellable at this declared point. -/
  | cancellableAt (point : CancellationPointId)
  /-- The call sits inside this bounded atomic region and refuses cancellation. -/
  | withinAtomicRegion (region : AtomicRegionId)
  /-- The call returns within a declared frontier bound without a point. -/
  | boundedFrontier (stepBound : Nat)
  deriving DecidableEq, Repr

/--
What one scope publishes about its cancellation structure.

`publicCancellationPoints` are the points a *caller* may address;
`blockingCalls` are the calls discovered inside the scope. Both are local: a
sibling scope's points and calls do not appear.
-/
structure ProcessScopeSummary where
  /-- The scope this summarizes. -/
  scope : ScopeId
  /-- The cancellation points this scope exposes to its callers. -/
  publicCancellationPoints : List CancellationPointId
  /-- The blocking calls discovered inside this scope. -/
  blockingCalls : List BlockingCallId
  /-- Each point once. -/
  pointsDistinct : publicCancellationPoints.Nodup
  /-- Each call once. -/
  callsDistinct : blockingCalls.Nodup

/--
The one core cancellation policy, indexed by nothing.

It carries the points it policies and the calls it classifies as *data*, so that
being exact against a scope summary is a comparison rather than a type-level
coincidence. `ScopedCancellationCertificate` is where the comparison is
required.

`blockingCalls` is the field name, per `coord1:6`. `docs/PROCESS_SHARDING.md`
previously spelled it `calls`, which made its composition law refer to a field
the other document did not declare.
-/
structure CancellationPolicy where
  /-- The points this policy governs. -/
  points : List CancellationPointId
  /-- What each of them does. -/
  pointPolicy : CancellationPointId → CancellationPointPolicy
  /-- The bounded regions in which cancellation is refused. -/
  atomicRegions : List BoundedAtomicRegion
  /-- The blocking calls this policy has classified. -/
  blockingCalls : List BlockingCallId
  /-- How each is made acceptable. -/
  callDisposition : BlockingCallId → BlockingCallDisposition

namespace CancellationPolicy

/--
Every call classified as sitting in an atomic region names a region this policy
declares.

Without it, `withinAtomicRegion` would be a way to declare a call uncancellable
by naming a region that does not exist and therefore has no bound.
-/
def RegionsDeclared (policy : CancellationPolicy) : Prop :=
  ∀ call ∈ policy.blockingCalls,
    ∀ region, policy.callDisposition call = .withinAtomicRegion region →
      ∃ bounded ∈ policy.atomicRegions, bounded.id = region

/--
Every call classified as cancellable names a point this policy governs.

The same hole on the other constructor: a disposition may not point at a
cancellation point outside the policy.
-/
def PointsDeclared (policy : CancellationPolicy) : Prop :=
  ∀ call ∈ policy.blockingCalls,
    ∀ point, policy.callDisposition call = .cancellableAt point →
      point ∈ policy.points

/--
This policy is exact against a scope summary: the same points, the same calls.

Equality of lists rather than containment in either direction, and that is the
whole scalability claim. A policy that classified *more* calls than the scope
discovered would be describing code that is not there; one that classified fewer
would leave a blocking call unaccounted. Both are rejected, and both are checked
against one scope's lists rather than the program's.
-/
def Covers (policy : CancellationPolicy) (summary : ProcessScopeSummary) : Prop :=
  policy.points = summary.publicCancellationPoints ∧
    policy.blockingCalls = summary.blockingCalls

theorem covers_points {policy : CancellationPolicy} {summary : ProcessScopeSummary}
    (covers : policy.Covers summary) :
    policy.points = summary.publicCancellationPoints := covers.1

theorem covers_calls {policy : CancellationPolicy} {summary : ProcessScopeSummary}
    (covers : policy.Covers summary) :
    policy.blockingCalls = summary.blockingCalls := covers.2

/--
A policy cannot cover a summary that discovered a call it has not classified.

This is the local-invalidation property stated negatively, and it is what makes
`callsExact` bite: adding a `Sleep` to a scope changes `summary.blockingCalls`,
and the old policy no longer covers it.
-/
theorem not_covers_of_unclassified {policy : CancellationPolicy}
    {summary : ProcessScopeSummary} {call : BlockingCallId}
    (discovered : call ∈ summary.blockingCalls)
    (unclassified : call ∉ policy.blockingCalls) :
    ¬ policy.Covers summary := by
  intro covers
  exact unclassified (covers.2 ▸ discovered)

end CancellationPolicy

/--
A scope's cancellation certificate: a policy, proved exact against that scope
and internally well formed.

`docs/PROCESS_SHARDING.md` §4's `ScopedCancellationCertificate`, with
`coord1:6`'s field name.
-/
structure ScopedCancellationCertificate (summary : ProcessScopeSummary) where
  /-- The policy. -/
  policy : CancellationPolicy
  /-- Exact against this scope, and only this scope. -/
  exact : policy.Covers summary
  /-- Every atomic-region disposition names a declared, bounded region. -/
  regionsDeclared : policy.RegionsDeclared
  /-- Every cancellable disposition names a governed point. -/
  pointsDeclared : policy.PointsDeclared

namespace ScopedCancellationCertificate

/--
Two scopes may be composed when their nominal scopes differ.

Disjointness of scope identity, not of point or call names: two scopes may
perfectly well both declare a point called `shutdown`, and the `CancellationPointId`
carries the scope that disambiguates them.
-/
def Compatible (left right : ProcessScopeSummary) : Prop :=
  left.scope ≠ right.scope

/--
The composed summary.

Whole-plan cancellation is this fold, per `coord1:6`, and not a separate
whole-plan type. The lists concatenate because the scopes are distinct and each
identity carries its scope.
-/
def composeSummary (left right : ProcessScopeSummary)
    (_compatible : Compatible left right)
    (pointsDistinct :
      (left.publicCancellationPoints ++ right.publicCancellationPoints).Nodup)
    (callsDistinct : (left.blockingCalls ++ right.blockingCalls).Nodup)
    (scope : ScopeId) : ProcessScopeSummary where
  scope := scope
  publicCancellationPoints :=
    left.publicCancellationPoints ++ right.publicCancellationPoints
  blockingCalls := left.blockingCalls ++ right.blockingCalls
  pointsDistinct := pointsDistinct
  callsDistinct := callsDistinct

/--
The composed policy: governs both scopes' points and classifies both scopes'
calls, dispatching each to the side that declared it.

`dispatch` is by list membership rather than by scope equality so that the
composition needs no decidability assumption about `ScopeId` beyond the derived
one.
-/
def composePolicy (left right : CancellationPolicy) : CancellationPolicy where
  points := left.points ++ right.points
  pointPolicy := fun id =>
    if id ∈ left.points then left.pointPolicy id else right.pointPolicy id
  atomicRegions := left.atomicRegions ++ right.atomicRegions
  blockingCalls := left.blockingCalls ++ right.blockingCalls
  callDisposition := fun call =>
    if call ∈ left.blockingCalls then left.callDisposition call
    else right.callDisposition call

/--
Composition preserves exactness.

The fold's key step: the composed policy covers the composed summary, so an
aggregate certificate is assembled from child certificates rather than proved
against the whole program.
-/
theorem composePolicy_covers {leftSummary rightSummary : ProcessScopeSummary}
    {leftPolicy rightPolicy : CancellationPolicy}
    (leftCovers : leftPolicy.Covers leftSummary)
    (rightCovers : rightPolicy.Covers rightSummary)
    (compatible : Compatible leftSummary rightSummary)
    (pointsDistinct :
      (leftSummary.publicCancellationPoints ++
        rightSummary.publicCancellationPoints).Nodup)
    (callsDistinct :
      (leftSummary.blockingCalls ++ rightSummary.blockingCalls).Nodup)
    (scope : ScopeId) :
    (composePolicy leftPolicy rightPolicy).Covers
      (composeSummary leftSummary rightSummary compatible pointsDistinct
        callsDistinct scope) := by
  refine ⟨?_, ?_⟩
  · show leftPolicy.points ++ rightPolicy.points =
      leftSummary.publicCancellationPoints ++ rightSummary.publicCancellationPoints
    rw [leftCovers.1, rightCovers.1]
  · show leftPolicy.blockingCalls ++ rightPolicy.blockingCalls =
      leftSummary.blockingCalls ++ rightSummary.blockingCalls
    rw [leftCovers.2, rightCovers.2]

end ScopedCancellationCertificate

end Grass.Process
