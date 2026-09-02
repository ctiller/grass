import Grass.Process.Network.Death
import Grass.Process.Network.Topology

/-!
# Process instances and their lifecycle

`docs/PROCESS.md` §3 gives the logical network's instance record, with `kind`,
`ref`, `parent`, `request`, `local`, and `lifecycle`.

`ProcessLifecycle` is named there and declared nowhere in the corpus, so this
module declares it. Three questions had to be answered to do that, and the
answers are the content of this file.

## Which states exist

Not a taxonomy invented here, and not derived from the transition family either
— an earlier revision tried that and got it wrong in four separate ways, because
"which transitions enter this state" is the wrong question. `NetworkTransition`
says how a network moves; it does not enumerate the ways a process can have
ended.

§3 does enumerate them, in `ChildLifecycleEvent`, and the states below are
exactly its non-continuing cases:

| `ChildLifecycleEvent` | state |
|---|---|
| `pending`, `intermediate` | `running` |
| `succeeded`, `failed` | `terminated` |
| `cancellationAcknowledged` | `cancelled` |
| `interrupted` | `interrupted` |
| `faulted` | `faulted` |
| `environmentViolation` | `violated` |
| `died` | `died` |

`succeeded` and `failed` collapse into one state because
`Grass/Process/Spec.lean` has a single `TerminalResult` rather than the corpus's
`TerminalSuccess`/`TerminalFailure` split: at this layer both are "the protocol
reached a terminal state", and *which* terminal state is the result, not the
tag.

§3 covers non-children too — "`processTermination` performs the corresponding
operation for a non-child/root instance" — so this enumeration is the whole
population's, not the child population's.

Three transitions deliberately reach no state here. `restart` produces a *new*
incarnation, so the fresh process is a different `ProcessRef` in `running` and
the old one keeps whatever ending it already had — usually `faulted`, which is
why it was restarted. `detach` changes `parent`, not liveness. And
`requestCancel` reaches none, which is the case worth stating out loud: **a
process with an outstanding cancellation request is still running**. It keeps
stepping until acknowledgement. §3 agrees — "a mere request does not prove
acknowledgement or recover its resources" — and it is *acknowledgement* that
ends the process, which is why `cancelled` is a state and "cancelling" is not.

## What a tag carries, and what it does not

The rule this module follows: **a tag carries a payload exactly when the
instance's other fields do not determine it.**

`died` carries its reason because nothing else does. A dead process produced no
protocol event; its state is whatever it was. If the tag is silent, the reason
is unrecoverable.

`terminated` carries no result because `localState` is still there and
`LifecycleWitnessed` requires it to be a terminal state of the protocol, so
`terminated_has_result` recovers one. Carrying it as well would mean two records
of one fact, and a join could hand back a result the parent's own transition
never received.

`faulted`, `violated`, `interrupted` and `cancelled` carry nothing, and **they
do not satisfy the rule**. A faulted instance's state does not determine its
`LogicalFault`; a cancelled one's does not determine its `CancelReason`. They
would have to, and the type would have to be indexed by the protocol to say so,
which `docs/PROCESS.md`'s unindexed `lifecycle : ProcessLifecycle` forbids. The
class is recorded where the event went — `ChildLifecycleOutcome.faulted` for a
child, the boundary for a root — but it is not recoverable from instance state
alone. That is a real gap and it is filed, not papered over.

`terminated` is on the edge of the same gap for a different reason:
`ProcessSpec.Terminal` is a *relation*, so a state may be terminal with more
than one result and `terminated_has_result` recovers *some* result rather than
*the* result. `TerminatedWith` below is the predicate that names a specific one,
and `terminated_result_unique` shows the two coincide exactly when the protocol
is deterministic. An earlier revision of this note claimed there was "only one
record" of the result without that hypothesis; that was false.

## Where the witnessing obligation lives

`LifecycleWitnessed` is stated here and will be required by
`Grass/Process/Network/Plan.lean` of every instance in a well-formed
`LogicalProcessNetwork`. That module does not exist yet, so the requirement is
recorded in `docs/PROCESS_IMPLEMENTATION_PLAN.md` §4's exit criteria as well as
here — a docstring in one module is not a place an obligation can safely live.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r

/--
Where a process instance is in its life.

Closed, and its constructors are exactly the non-continuing cases of
`docs/PROCESS.md` §3's `ChildLifecycleEvent`; see the module note for the table
and for what each tag does and does not carry.
-/
inductive ProcessLifecycle
  /-- Stepping. Includes a process with an outstanding, unacknowledged cancel. -/
  | running
  /-- Reached a terminal state of its protocol; see `LifecycleWitnessed`. -/
  | terminated
  /-- A cancellation was *acknowledged*. Requesting one does not reach here. -/
  | cancelled
  /-- An outstanding demand of its own was abandoned. -/
  | interrupted
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
**Requesting a cancellation and acknowledging one are different states.**

The distinction this enumeration exists to make. `docs/PROCESS.md` §3: "a mere
request does not prove acknowledgement or recover its resources", so a process
under an unacknowledged request is `running` and still schedulable, while
acknowledgement is a `ChildLifecycleEvent` terminal outcome and ends it.

An earlier revision of this module had a single claim covering both, and no
`cancelled` state at all, so an acknowledged cancellation reached no state — a
way for a process to end that the enumeration did not name.
-/
theorem request_and_acknowledgement_differ :
    ProcessLifecycle.running.Live ∧ ¬ ProcessLifecycle.cancelled.Live :=
  ⟨trivial, fun live => live⟩

end ProcessLifecycle

/--
One incarnation in the logical network.

`docs/PROCESS.md` §3's record, with `local` spelled `localState` because `local`
is a Lean keyword. `parent` is an `Option` of a dependent pair because a parent
may be of a different kind.
-/
structure ProcessInstance {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary) :
    Type (max u w r) where
  /-- Which role this is. -/
  kind : topology.ProcessKind
  /-- Which incarnation of it. -/
  ref : topology.ProcessRef kind
  /--
  Its parent incarnation, if it has one.

  `none` covers two different situations — a root, and a detached child — which
  `IsRoot` below is careful not to conflate.
  -/
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

/-! ## Parenthood -/

/--
This instance has no parent recorded.

Deliberately *not* called `IsRoot`. `docs/PROCESS.md` §3 detaches children, and
a detached child has no parent either, so the two are indistinguishable by this
field alone.
-/
def HasNoParent (incarnation : ProcessInstance topology) : Prop :=
  incarnation.parent = none

/--
The root: the one kind whose protocol faces the driver boundary, with no parent.

`ProcessGraph.root` is what makes a root a root — it is the kind whose
`rootBoundary` exposure exists — so the kind is the load-bearing half and the
absent parent is the consistency check.
-/
def IsRoot (incarnation : ProcessInstance topology) : Prop :=
  incarnation.kind = topology.root ∧ incarnation.parent = none

theorem isRoot_hasNoParent {incarnation : ProcessInstance topology}
    (root : incarnation.IsRoot) : incarnation.HasNoParent := root.2

/-! ## The terminal tag as a claim about the state -/

/--
**The lifecycle tag is a claim about the state, not a label on it.**

A terminated instance's state is a terminal state of its protocol. Required of
every instance in a well-formed `LogicalProcessNetwork` rather than carried as a
field, for the reason in the module note.

Only `terminated` is constrained. `cancelled`, `interrupted`, `faulted`,
`violated` and `died` are ends that `docs/PROCESS.md` §3 does not require to be
protocol-terminal — a faulting process stops in whatever state it faulted from —
and demanding a terminal state of them would make those transitions
unconstructible.
-/
def LifecycleWitnessed (incarnation : ProcessInstance topology) : Prop :=
  incarnation.lifecycle = .terminated →
    ∃ result, (topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState result

/--
The same claim about a *named* result: this instance ended, with this answer.

`LifecycleWitnessed` only says some result exists, because
`ProcessSpec.Terminal` is a relation. When a consumer — a join, a parent's
`ChildDemandBinding` — has a specific result in hand, this is the predicate that
says the instance agrees with it.
-/
def TerminatedWith (incarnation : ProcessInstance topology)
    (result : (topology.protocol incarnation.kind).TerminalResult) : Prop :=
  incarnation.lifecycle = .terminated ∧
    (topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState result

theorem terminatedWith_witnessed {incarnation : ProcessInstance topology}
    {result : (topology.protocol incarnation.kind).TerminalResult}
    (agreed : incarnation.TerminatedWith result) : incarnation.LifecycleWitnessed :=
  fun _ => ⟨result, agreed.2⟩

/--
A terminated instance yields *a* result — not necessarily the one a parent
recorded.

`ProcessSpec.Terminal` is a relation, so a state may be terminal with several
results and this recovers an arbitrary one. That is enough for the tag to be
lossless about *whether* the process finished, and not enough for it to be
lossless about *what it answered*; `terminated_result_unique` says when the two
coincide.
-/
theorem terminated_has_result {incarnation : ProcessInstance topology}
    (witnessed : incarnation.LifecycleWitnessed)
    (ended : incarnation.lifecycle = .terminated) :
    ∃ result, (topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState result :=
  witnessed ended

/--
**When the recovered result is the result.**

If the protocol's terminal relation is functional at this instance — which
`Grass/Process/Spec.lean`'s `DeterministicProcess.terminal_functional` supplies
for the deterministic construction — then any two results the state is terminal
for are equal, so `terminated_has_result` recovers the one a parent recorded.

Stated with the hypothesis explicit rather than assumed, because a nondetermin-
istic protocol is legal and at one the payload-free tag does *not* determine the
answer. That is the gap the module note names.
-/
theorem terminated_result_unique {incarnation : ProcessInstance topology}
    (functional : ∀ left right : (topology.protocol incarnation.kind).TerminalResult,
      (topology.protocol incarnation.kind).Terminal
        incarnation.request incarnation.localState left →
      (topology.protocol incarnation.kind).Terminal
        incarnation.request incarnation.localState right → left = right)
    {recorded : (topology.protocol incarnation.kind).TerminalResult}
    (agreed : incarnation.TerminatedWith recorded)
    {recovered : (topology.protocol incarnation.kind).TerminalResult}
    (alsoTerminal : (topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState recovered) :
    recovered = recorded :=
  functional recovered recorded alsoTerminal agreed.2

/--
A live instance is subject to no terminal obligation.

`LifecycleWitnessed` is vacuous at `running`, which is what makes a running
process representable at all: a running process must not be required to be in a
terminal state. What shows the predicate is not *universally* vacuous is the
fixture, which exhibits an instance that fails it.
-/
theorem live_witnessed_vacuously {incarnation : ProcessInstance topology}
    (live : incarnation.Live) : incarnation.LifecycleWitnessed := by
  intro ended
  rw [ProcessLifecycle.live_iff_running.mp live] at ended
  exact absurd ended (by decide)

end ProcessInstance

end Grass.Process
