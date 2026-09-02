import Grass.Process.Network.Topology

/-!
# Process instances and their lifecycle

`docs/PROCESS.md` §3 gives the logical network's instance record, with `kind`,
`ref`, `parent`, `request`, `local`, and `lifecycle`.

`ProcessLifecycle` is named there and declared nowhere in the corpus, so this
module declares it. Two questions had to be answered to do that, and the answers
are the content of this file.

## Which states exist

Not a taxonomy invented here. Every state below is entered by a transition
`docs/PROCESS.md` §4 names in `NetworkTransition`, and no state is added that no
transition reaches:

| state | entered by |
|---|---|
| `running` | `spawn`, and the network's initial root |
| `terminated` | `processTermination` |
| `faulted` | `fault` |
| `violated` | `environmentViolation` |
| `died` | `senderDeath`, `receiverDeath`, supervisor shutdown |

`restart` reaches none of them, which is the point: a restarted process is a new
generation, so it is a *different* `ProcessRef` in `running`, and the old one is
already `died`. `detach` reaches none either — it changes `parent`, not
liveness. And `requestCancel`/`acknowledgeCancel` reach none, which is the case
worth stating out loud: **a process with an outstanding cancellation is still
running**. It keeps stepping until it acknowledges. Making "cancelling" a
lifecycle state would say otherwise, and would put a second, weaker copy of the
cancellation record next to `Grass/Process/Cancellation/Policy.lean`'s.

## Why the terminal states carry no payload

`terminated` does not carry the protocol's `TerminalResult`, and this is
deliberate rather than an omission. A parent learns a child's result through
`ChildDemandBinding.classify` at the moment the child ends
(`Grass/Process/Network/Child.lean`), not by reading it out of a tombstone
later. If the tombstone also carried the result there would be two records of
one fact, and a join could hand back a result the parent's own transition never
received.

That would be entropy in the sense `docs/FOUNDATION.md` law 5 forbids, so what
makes the tag safe is that nothing is lost: the private state is still there,
and `LifecycleWitnessed` below requires a terminated instance's state to be an
actual terminal state of its protocol. `terminated_has_result` then recovers the
result. The tag is a claim about the state, not a substitute for it.

`LifecycleWitnessed` is stated here and required by
`Grass/Process/Network/Plan.lean` at the network, not carried as a field of the
instance, because `docs/PROCESS.md` declares the record without it and an
instance in isolation is not the thing a well-formedness law is about.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r

/--
Why a process stopped existing without finishing its protocol.

Formerly `ChildDeathReason` in `Grass/Process/Network/Child.lean`. The name was
wrong: none of the three reasons is about being a child, and `docs/PROCESS.md`
§4 gives `senderDeath` and `receiverDeath` transitions to processes that may be
roots. It is declared here, where the lifecycle it belongs to lives, and the
child binding consumes it.
-/
inductive ProcessDeathReason
  /-- Its parent died, and it was not detached. -/
  | parentDied
  /-- A supervisor stopped it. -/
  | supervised
  /-- The provider realizing it disappeared. -/
  | providerLost
  deriving DecidableEq, Repr

/--
Where a process instance is in its life.

Closed, and each constructor is reached by a named `NetworkTransition`; see the
module note for the table and for the three transitions that deliberately reach
none of them.
-/
inductive ProcessLifecycle
  /-- Stepping. Includes a process with an outstanding, unacknowledged cancel. -/
  | running
  /-- Finished its protocol. Its state is terminal; see `LifecycleWitnessed`. -/
  | terminated
  /-- Ended by a logical fault of its own. -/
  | faulted
  /-- Ended because its environment broke a contract. -/
  | violated
  /-- Stopped existing without finishing. -/
  | died (reason : ProcessDeathReason)
  deriving DecidableEq, Repr

namespace ProcessLifecycle

/-- A process that may still take a transition. -/
def Live : ProcessLifecycle → Prop
  | .running => True
  | _ => False

/-- Exactly one state is live, which makes `Live` a decision and not a hint. -/
theorem live_iff_running {lifecycle : ProcessLifecycle} :
    lifecycle.Live ↔ lifecycle = .running := by
  cases lifecycle <;> simp [Live]

/--
An outstanding cancellation does not end a process.

Stated as a theorem rather than left to the reader, because it is the shape of
the mistake this enumeration exists to prevent: there is no state between
`running` and the four terminal ones, so a cancelling process is live by
construction and a transition family cannot quietly stop scheduling it.
-/
theorem cancelling_is_live : ProcessLifecycle.running.Live := trivial

end ProcessLifecycle

/--
One incarnation in the logical network.

`docs/PROCESS.md` §3's record, with `local` spelled `localState` because `local`
is a Lean keyword. `parent` is an `Option` of a dependent pair because a parent
may be of a different kind, and because a root — and a detached child — has none.
-/
structure ProcessInstance {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary) :
    Type (max u w r) where
  /-- Which role this is. -/
  kind : topology.ProcessKind
  /-- Which incarnation of it. -/
  ref : topology.ProcessRef kind
  /-- Its parent incarnation, if it has one. -/
  parent : Option (Sigma fun parentKind => topology.ProcessRef parentKind)
  /-- The request it was spawned with. -/
  request : (topology.protocol kind).Request
  /-- Its private state. -/
  localState : (topology.protocol kind).State
  /-- Where it is in its life. -/
  lifecycle : ProcessLifecycle

namespace ProcessInstance

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}

/-- This instance may still take a transition. -/
def Live (incarnation : ProcessInstance topology) : Prop :=
  incarnation.lifecycle.Live

/--
**The lifecycle tag is a claim about the state, not a label on it.**

A terminated instance's state is an actual terminal state of its protocol.
Required of every instance in a well-formed `LogicalProcessNetwork` rather than
carried as a field, for the reason in the module note.

Only `terminated` is constrained. `faulted`, `violated` and `died` are ends that
`docs/PROCESS.md` §3 does not require to be protocol-terminal — a faulting
process stops in whatever state it faulted from — and demanding a terminal state
of them would make those transitions unconstructible.
-/
def LifecycleWitnessed (incarnation : ProcessInstance topology) : Prop :=
  incarnation.lifecycle = .terminated →
    ∃ result, (topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState result

/--
And the payoff: a terminated instance still yields its result.

This is what makes the payload-free tag lossless. Nothing was dropped when
`terminated` was chosen over a constructor carrying a `TerminalResult`; the
result is recoverable, and there is only one record of it.
-/
theorem terminated_has_result {incarnation : ProcessInstance topology}
    (witnessed : incarnation.LifecycleWitnessed)
    (ended : incarnation.lifecycle = .terminated) :
    ∃ result, (topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState result :=
  witnessed ended

/--
A live instance is subject to no terminal obligation.

`LifecycleWitnessed` is vacuous at `running`, which is correct and worth pinning:
a running process must *not* be required to be in a terminal state, and a reader
checking that this predicate is not accidentally universal can see it here.
-/
theorem live_witnessed_vacuously {incarnation : ProcessInstance topology}
    (live : incarnation.Live) : incarnation.LifecycleWitnessed := by
  intro ended
  rw [ProcessLifecycle.live_iff_running.mp live] at ended
  exact absurd ended (by decide)

/-- A root instance is one with no parent. -/
def IsRoot (incarnation : ProcessInstance topology) : Prop :=
  incarnation.parent = none

end ProcessInstance

end Grass.Process
