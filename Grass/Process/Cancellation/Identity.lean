import Grass.Specification.Scope

/-!
# Cancellation identities

The nominal identities cancellation is written over, in their own module because
two layers need them and neither should have to import the other's reasoning to
get them. `Grass/Process/Cancellation/Policy.lean` builds policies and
certificates out of them; `Grass/Process/Network/Instance.lean` stores a
`CancelReason` in the lifecycle of a process whose cancellation was
acknowledged, and has no other use for a policy.

This module imports only `Grass/Specification/Scope.lean`, which every identity
here is scoped by.

## `CancelReason` is a place, not a taxonomy

`docs/PROCESS.md` §3 uses `CancelReason` in `ChildLifecycleEvent` and in the
byte-flow phases and declares it nowhere, so this module declares it — and
declares the one thing the corpus actually determines rather than an invented
list of motives.

§3 says a pending request "is observed here and resolved into a disposition"
only at a `cancellationPoint`, and `CancellationMask` below makes that the sole
mask at which a request may be acted on. So every acknowledgement happens at
some declared point, and *which* point is both the complete answer and a
checkable one: `CancellationPolicy.Covers` and `PointsDeclared` already range
over exactly that set, so a network law can require an acknowledgement's point
to be one the governing policy declares.

An enumeration of motives — caller asked, deadline elapsed, scope collapsed —
would have been an invention, and one that overlaps `ProcessDeathReason` and
the escrow ledger's `timedOut` at two of its three cases.
-/

namespace Grass.Process

open Grass.Specification (ScopeId)

/--
Where a process may be cancelled.

`docs/PROCESS.md` §3's three-way mask. `cancellationPoint` is the only one at
which a pending request may be acted on; `uncancellable` latches it; and
`interruptible` admits delivery between any two steps.
-/
inductive CancellationMask
  /-- A pending request is latched, not acted on and not dropped. -/
  | uncancellable
  /-- A pending request is observed here and resolved into a disposition. -/
  | cancellationPoint
  /-- Delivery may occur between any two steps of this region. -/
  | interruptible
  deriving DecidableEq, Repr

/-- The nominal identity of a declared cancellation point. -/
structure CancellationPointId where
  /-- The scope that declared it. -/
  scope : ScopeId
  /-- Its name within that scope. -/
  name : String
  deriving DecidableEq, Repr

/--
The nominal identity of a call that may block.

`docs/PROCESS.md` §5 calls these *discovered*, not declared: they come from
scanning a machine source, which is why adding a `Sleep` or a provider wait
changes the family and must reject the old certificate.
-/
structure BlockingCallId where
  /-- The scope the call occurs in. -/
  scope : ScopeId
  /-- Its name within that scope. -/
  name : String
  deriving DecidableEq, Repr

/-- The nominal identity of a bounded region in which cancellation is refused. -/
structure AtomicRegionId where
  /-- The scope that declared it. -/
  scope : ScopeId
  /-- Its name within that scope. -/
  name : String
  deriving DecidableEq, Repr

/--
Why a process's cancellation was acknowledged: the declared point at which it
happened.

See the module note. `docs/PROCESS.md` §3 admits acknowledgement only at a
declared cancellation point, so the point is the whole content, and it is
checkable against `CancellationPolicy.points`.
-/
structure CancelReason where
  /-- The point at which the pending request was observed and resolved. -/
  acknowledgedAt : CancellationPointId
  deriving DecidableEq, Repr

end Grass.Process
