import Grass.Process.Cancellation.Identity
import Grass.Process.Network.Death
import Grass.Process.Network.Topology

/-!
# Process instances, their parentage, and their lifecycle

`docs/PROCESS.md` §3's instance record, and the two types it is written over
that the corpus named and did not declare.

Both were declared here in a weaker form first, and both are now the form
`docs/DECISIONS.md` decisions 129 and 130 ruled after c-process filed the
weakness as a defect. The history is kept in the notes below because in each
case the weaker form was *reasonable* and still wrong, and the reason it was
wrong is the design content.

## `ProcessLifecycle` stores the ending, not a tag for it

The states are exactly §3's `ChildLifecycleEvent` non-continuing cases —
`succeeded` and `failed` collapse into `terminated` because
`Grass/Process/Spec.lean` has a single `TerminalResult` rather than the corpus's
success/failure split, so which terminal state was reached is the result, not
the tag.

An earlier revision made every tag payload-free and argued that nothing was lost
because `localState` plus `LifecycleWitnessed` recovers the result. That is
false twice. `ProcessSpec.Terminal` is a *relation*, so a state may be terminal
with several results and the recovery returns *a* result rather than *the* one
the parent's `ChildDemandBinding` routed — reintroducing exactly the hazard the
argument cited against carrying it. And a faulted instance's state determines no
`LogicalFault` at all, nor a violated one's `EnvironmentViolation`, nor a
cancelled one's `CancelReason`, so for four of the endings the tag simply did
not say what happened.

Decision 129 rules the type indexed by the instance's protocol, storing the
exact payload. §3 states the reason and the cost: "an ending must remain
recoverable from network state without replaying the parent transition", and
"carrying the payload does not duplicate an independent fact: the transition
owns one value and records that same value in the child event, parent projection
when applicable, and resulting instance state through equality proofs."

`LifecycleWitnessed` remains, and its job is now sharper. It does not recover
the result — the tag has it. It ties the stored result to the protocol, so a
network cannot store an answer the protocol never reaches from that state.

## `ProcessParentage` keeps the history detachment destroys

An earlier revision used §3's `parent : Option (Sigma ...)`, which is what the
corpus declared. §3 also detaches children, and a detached child's `parent`
becomes `none` — indistinguishable from a root's. Two things broke. "The root is
the instance with no parent" was false as a network law, and
`Grass/Process/Network/Child.lean`'s `NonReturningReason.detached` became
unjustifiable from state: a binding could say an outcome does not return because
the child was detached, with nothing in the network recording that it ever was.

Decision 130 rules the three-way form. `root` is indexed at exactly the
topology's root kind, so a root is a root by construction rather than by an
absent field; `attached` names the current parent; `detached` records the exact
incarnation the process was detached from while granting it no continuing
authority. `detach` below is the whole transition: it maps `attached parent` to
`detached parent` with the same reference, and `detach_preserves_reference` is
§3's "proves the references identical".

## Where the witnessing obligation lives

`LifecycleWitnessed` is stated here and will be required by
`Grass/Process/Network/Plan.lean` of every instance in a well-formed
`LogicalProcessNetwork`, along with root uniqueness and the validity of attached
parent relationships, which decision 130 also puts at the network rather than on
each instance's author. That module does not exist yet, so the requirement is
recorded in `docs/PROCESS_IMPLEMENTATION_PLAN.md` §4's exit criteria as well as
here — a docstring in one module is not a place an obligation can safely live.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r

/--
Where a process instance is in its life, and what put it there.

Indexed by the protocol so that each ending carries its exact payload;
`docs/DECISIONS.md` decision 129, and the module note for why the payload-free
version was wrong.
-/
inductive ProcessLifecycle (protocol : ProcessSpec.{u, w}) : Type (max u w)
  /-- Stepping. Includes a process with an outstanding, unacknowledged cancel. -/
  | running
  /-- Reached a terminal state of its protocol, with this answer. -/
  | terminated (result : protocol.TerminalResult)
  /-- A cancellation was *acknowledged*, at this point. Requesting one does not
  reach here. -/
  | cancelled (reason : CancelReason)
  /-- An outstanding demand of its own was abandoned, for this reason. -/
  | interrupted (reason : protocol.InterruptReason)
  /-- Ended by this logical fault of its own. -/
  | faulted (fault : protocol.LogicalFault)
  /-- Ended because its environment broke a contract, this way. -/
  | violated (violation : protocol.EnvironmentViolation)
  /-- Stopped existing without finishing, for this reason. -/
  | died (reason : ProcessDeathReason)

namespace ProcessLifecycle

variable {protocol : ProcessSpec.{u, w}}

/-- A process that may still take a transition. -/
def Live : ProcessLifecycle protocol → Prop
  | .running => True
  | _ => False

/--
Transporting a lifecycle across an equation of kinds does not change whether it
is live.

The `Live` counterpart of `ProcessParentage.knownParent_cast`, and needed for
the same reason: `Grass/Process/Network/Transition.lean` compares two
incarnations of one slot, and an incarnation carries its own `kind`.
-/
theorem live_cast {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
    {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
    {left right : topology.ProcessKind} (sameKind : left = right)
    (lifecycle : ProcessLifecycle (topology.protocol left)) :
    (sameKind ▸ lifecycle : ProcessLifecycle (topology.protocol right)).Live ↔ lifecycle.Live := by
  cases sameKind; exact Iff.rfl

/-- Exactly one state is live, which makes `Live` a decision and not a hint. -/
theorem live_iff_running {lifecycle : ProcessLifecycle protocol} :
    lifecycle.Live ↔ lifecycle = .running := by
  constructor
  · intro live
    cases lifecycle with
    | running => rfl
    | _ => exact absurd live (fun h => h)
  · intro isRunning
    rw [isRunning]
    trivial

/--
**Requesting a cancellation and acknowledging one are different states.**

The distinction this enumeration exists to make. `docs/PROCESS.md` §3: "a mere
request does not prove acknowledgement or recover its resources", so a process
under an unacknowledged request is `running` and still schedulable, while
acknowledgement is a terminal `ChildLifecycleEvent` and ends it.

An earlier revision had no `cancelled` state at all, so an acknowledged
cancellation reached no state — a way for a process to end that the enumeration
did not name.
-/
theorem request_and_acknowledgement_differ (reason : CancelReason) :
    (ProcessLifecycle.running (protocol := protocol)).Live ∧
      ¬ (ProcessLifecycle.cancelled (protocol := protocol) reason).Live :=
  ⟨trivial, fun live => live⟩

end ProcessLifecycle

/--
Whether a process has a parent, had one, or never did.

`docs/DECISIONS.md` decision 130. The `root` constructor is indexed at the
topology's root kind, so the root is a root by construction; `detached` keeps
the incarnation it was detached from without granting it authority. See the
module note for what the `Option` this replaces could not say.
-/
inductive ProcessParentage {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary) :
    topology.ProcessKind → Type r
  /-- The root. There is no parent because there was never one. -/
  | root : ProcessParentage topology topology.root
  /-- A child of this incarnation, which currently holds parent authority. -/
  | attached {kind : topology.ProcessKind} (parentKind : topology.ProcessKind)
      (parent : topology.ProcessRef parentKind) : ProcessParentage topology kind
  /-- Detached from this incarnation, which no longer holds any authority. -/
  | detached {kind : topology.ProcessKind}
      (formerParentKind : topology.ProcessKind)
      (formerParent : topology.ProcessRef formerParentKind) :
      ProcessParentage topology kind

namespace ProcessParentage

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
  {kind : topology.ProcessKind}

/-- The incarnation that currently holds parent authority, if any. -/
def currentParent : ProcessParentage topology kind →
    Option (Sigma fun parentKind => topology.ProcessRef parentKind)
  | .root => none
  | .attached parentKind parent => some ⟨parentKind, parent⟩
  | .detached _ _ => none

/--
The incarnation this process was spawned by, whether or not it still holds
authority.

The half the `Option` could not express. `currentParent` and `knownParent`
differ exactly on a detached child, which is what makes
`Grass/Process/Network/Child.lean`'s `NonReturningReason.detached` checkable
against state.
-/
def knownParent : ProcessParentage topology kind →
    Option (Sigma fun parentKind => topology.ProcessRef parentKind)
  | .root => none
  | .attached parentKind parent => some ⟨parentKind, parent⟩
  | .detached formerParentKind formerParent => some ⟨formerParentKind, formerParent⟩

/-- This process is the root. -/
def IsRoot : ProcessParentage topology kind → Prop
  | .root => True
  | _ => False

/-- This process was spawned by a parent that has since let it go. -/
def IsDetached : ProcessParentage topology kind → Prop
  | .detached _ _ => True
  | _ => False

/--
**Detachment.**

`docs/PROCESS.md` §3: the transition "changes only `.attached parent` to
`.detached parent`, proves the references identical, and establishes the
corresponding non-returning child disposition." This is the first two thirds;
the disposition is `Child.lean`'s.

A root and an already-detached process are unchanged, because neither has parent
authority to give up.
-/
def detach : ProcessParentage topology kind → ProcessParentage topology kind
  | .attached parentKind parent => .detached parentKind parent
  | other => other

/-- Detaching gives up authority. -/
theorem detach_drops_authority (parentKind : topology.ProcessKind)
    (parent : topology.ProcessRef parentKind) :
    (ProcessParentage.attached (kind := kind) parentKind parent).detach.currentParent
      = none := rfl

/-- **And keeps the reference.** §3's "proves the references identical". -/
theorem detach_preserves_reference (parentKind : topology.ProcessKind)
    (parent : topology.ProcessRef parentKind) :
    (ProcessParentage.attached (kind := kind) parentKind parent).detach.knownParent
      = some ⟨parentKind, parent⟩ := rfl

/--
**Detaching anything keeps whatever reference it had.**

`detach_preserves_reference` says it for the case that moves; this says it for
all three, which is the form a transition consumes.
`Grass/Process/Network/Transition.lean`'s `Detaches` uses it to say the
*recorded former parent is the one it was attached to* — a claim its earlier
`knownParent ≠ none` field did not make, and which local adversarial review
exploited by building a detach that reparented a child onto a fabricated
ancestor.
-/
theorem detach_preserves_knownParent (parentage : ProcessParentage topology kind) :
    parentage.detach.knownParent = parentage.knownParent := by
  cases parentage <;> rfl

/--
Transporting a parentage across an equation of kinds does not change which
parent it remembers.

`knownParent`'s result type does not mention the kind, so the transport is
inert. Needed because `Grass/Process/Network/Transition.lean` states its
instance-identity fields over transported values — an instance carries its own
`kind` field, so two incarnations in one slot are only comparable after both are
carried to that slot's kind.
-/
theorem knownParent_cast {left right : topology.ProcessKind} (sameKind : left = right)
    (parentage : ProcessParentage topology left) :
    (sameKind ▸ parentage : ProcessParentage topology right).knownParent
      = parentage.knownParent := by
  cases sameKind; rfl

/--
**And detaching something that had authority produces a detached parentage.**

The other half `Detaches` needs. Without it `IsDetached` had to be asserted as a
separate field, and a separate field can be satisfied by a *different*
detachment than the one the structure's own `wasAttached` found.
-/
theorem detach_isDetached {parentage : ProcessParentage topology kind}
    (hadAuthority : parentage.currentParent ≠ none) : parentage.detach.IsDetached := by
  cases parentage with
  | root => exact absurd rfl hadAuthority
  | attached _ _ => trivial
  | detached _ _ => exact absurd rfl hadAuthority

/--
**A root and a detached child are distinguishable.**

The defect decision 130 closes, stated as the property it buys. Under the
`Option` both had `parent = none` and nothing separated them.
-/
theorem root_is_not_detached (parentKind : topology.ProcessKind)
    (parent : topology.ProcessRef parentKind) :
    (ProcessParentage.root (topology := topology)).knownParent = none ∧
      (ProcessParentage.detached (kind := kind) parentKind parent).knownParent
        = some ⟨parentKind, parent⟩ :=
  ⟨rfl, rfl⟩

/--
**A root has no parent, known or former.**

The `Option` half of decision 130's distinction, in the direction a
well-formedness proof consumes: `ParentageValid` quantifies over recorded
parenthood, and at a network holding only the root there is none to check.
-/
theorem knownParent_eq_none_of_isRoot {parentage : ProcessParentage topology kind}
    (root : parentage.IsRoot) : parentage.knownParent = none := by
  cases parentage with
  | root => rfl
  | _ => exact absurd root (fun h => h)

/-- A root's kind is the topology's root kind, by construction. -/
theorem isRoot_kind {parentage : ProcessParentage topology kind}
    (root : parentage.IsRoot) : kind = topology.root := by
  cases parentage with
  | root => rfl
  | _ => exact absurd root (fun h => h)

/--
**And only the root has no known parent.**

`knownParent_eq_none_of_isRoot`'s converse, and the half a preservation proof needs.
`LogicalProcessNetworkCore.RootUnique` is a claim about which incarnations are
roots, and the only thing a step carrying an incarnation across a slot agrees on
is `knownParent` — so without this, root-ness cannot be carried and the clause
cannot be proved for `processStep`, `detach` or any ending.
-/
theorem isRoot_of_knownParent_none {parentage : ProcessParentage topology kind}
    (unparented : parentage.knownParent = none) : parentage.IsRoot := by
  cases parentage with
  | root => trivial
  | attached _ _ => exact absurd unparented (by intro equal; cases equal)
  | detached _ _ => exact absurd unparented (by intro equal; cases equal)

/--
A root holds no parent authority either, which is the form
`Spawns.spawnsAChild` refutes.

That field says a spawned incarnation has a current parent; this says a root has
none. Together they are why a spawn cannot install a second root.
-/
theorem root_currentParent {parentage : ProcessParentage topology kind}
    (root : parentage.IsRoot) : parentage.currentParent = none := by
  cases parentage with
  | root => rfl
  | _ => exact absurd root (fun h => h)

/-- Neither a detached nor an attached process is the root. -/
theorem detached_not_root (parentKind : topology.ProcessKind)
    (parent : topology.ProcessRef parentKind) :
    ¬ (ProcessParentage.detached (kind := kind) parentKind parent).IsRoot :=
  fun isRoot => isRoot

end ProcessParentage

/--
One incarnation in the logical network.

`docs/PROCESS.md` §3's record, with `local` spelled `localState` because `local`
is a Lean keyword, and with `parent` replaced by `parentage` under decision 130.
-/
structure ProcessInstance {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary) :
    Type (max u w r) where
  /-- Which role this is. -/
  kind : topology.ProcessKind
  /-- Which incarnation of it. -/
  ref : topology.ProcessRef kind
  /-- Whether it has a parent, had one, or never did. -/
  parentage : ProcessParentage topology kind
  /-- The request it was spawned with. -/
  request : (topology.protocol kind).Request
  /-- Its private state. -/
  localState : (topology.protocol kind).State
  /--
  The demands it has issued and not yet had answered.

  `docs/PROCESS.md` §2's `ProcessRunState.running` carries `outstanding` beside
  the local state, and until this field existed the network had nowhere to put
  it: `StepsLocally` required the protocol's `Step` relation, which produces an
  issued bag, and then discarded the bag. Demands could be issued and never
  recorded, so nothing could ever be outstanding at a network instance and §2's
  linear multiplicity had no image here.

  Private, like `localState`: it lives inside `NetworkFragment.instanceState`,
  so a parent cannot read it and a weave mixin about it is scoped to the slot.
  -/
  outstanding : Bag (topology.protocol kind).Demand
  /-- Where it is in its life, and what put it there. -/
  lifecycle : ProcessLifecycle (topology.protocol kind)

namespace ProcessInstance

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}

/-- This instance may still take a transition. -/
def Live (incarnation : ProcessInstance topology) : Prop :=
  incarnation.lifecycle.Live

/-- This instance is the root. -/
def IsRoot (incarnation : ProcessInstance topology) : Prop :=
  incarnation.parentage.IsRoot

/-- This instance was spawned by a parent that has since let it go. -/
def IsDetached (incarnation : ProcessInstance topology) : Prop :=
  incarnation.parentage.IsDetached

/--
**The stored result is one the protocol actually reaches.**

Required of every instance in a well-formed `LogicalProcessNetwork` rather than
carried as a field, for the reason in the module note. Since decision 129 the
tag *has* the result, so this no longer recovers anything — it stops a network
from storing an answer the protocol never reaches from that state, which is the
half a stored payload cannot check for itself.

Only `terminated` is constrained. The other endings' payloads are their own
witnesses: a `LogicalFault` is a fault, and there is no state relation to hold
it against.
-/
def LifecycleWitnessed (incarnation : ProcessInstance topology) : Prop :=
  ∀ result, incarnation.lifecycle = .terminated result →
    (topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState result

/--
**The ending is exact.**

`docs/PROCESS.md` §3's requirement that "an ending must remain recoverable from
network state without replaying the parent transition", at the terminal case:
the result is the one stored, and it is a genuine terminal result of the
protocol.

Under the payload-free predecessor this theorem could only produce *some*
result, which at a protocol whose terminal relation is not functional was not
the parent's. That is why decision 129 exists.
-/
theorem terminated_result_is_exact {incarnation : ProcessInstance topology}
    (witnessed : incarnation.LifecycleWitnessed)
    {result : (topology.protocol incarnation.kind).TerminalResult}
    (ended : incarnation.lifecycle = .terminated result) :
    (topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState result :=
  witnessed result ended

/--
A live instance is subject to no terminal obligation.

`LifecycleWitnessed` is vacuous at `running`, which is what makes a running
process representable at all. What shows the predicate is not *universally*
vacuous is the fixture, which exhibits an instance that fails it.
-/
theorem live_witnessed_vacuously {incarnation : ProcessInstance topology}
    (live : incarnation.Live) : incarnation.LifecycleWitnessed := by
  intro result ended
  rw [ProcessLifecycle.live_iff_running.mp live] at ended
  exact absurd ended (by simp)

/--
Two incarnations carried to a common role, agreeing on the three fields
`LifecycleWitnessed` reads, witness the same lifecycles.

`Grass/Process/Network/Transition.lean` states its identity fields over
transported values — an incarnation carries its own `kind`, so two of them in one
slot are only comparable after both are carried to that slot's kind — and
`LifecycleWitnessed` is stated at the incarnation's *own* kind. This is the
bridge, and `Grass/Process/Network/WellFormedness.lean` is what needs it:
`processStep`, `detach` and the six endings all pin these three fields, and none
of them can hand the clause over without it.
-/
theorem lifecycleWitnessed_transfer {left right : ProcessInstance topology}
    {kind : topology.ProcessKind}
    (leftKind : left.kind = kind) (rightKind : right.kind = kind)
    (sameLifecycle : leftKind ▸ left.lifecycle = rightKind ▸ right.lifecycle)
    (sameRequest : leftKind ▸ left.request = rightKind ▸ right.request)
    (sameLocal : leftKind ▸ left.localState = rightKind ▸ right.localState)
    (witnessed : right.LifecycleWitnessed) : left.LifecycleWitnessed := by
  cases left with
  | mk leftRole leftRef leftParentage leftRequest leftLocal leftOutstanding leftLifecycle =>
  cases right with
  | mk _ rightRef rightParentage rightRequest rightLocal rightOutstanding rightLifecycle =>
  cases leftKind
  cases rightKind
  have life : leftLifecycle = rightLifecycle := sameLifecycle
  have request : leftRequest = rightRequest := sameRequest
  have local' : leftLocal = rightLocal := sameLocal
  subst life; subst request; subst local'
  exact witnessed

/-- Detaching this instance: parentage only, and only where there is authority. -/
def detach (incarnation : ProcessInstance topology) : ProcessInstance topology :=
  { incarnation with parentage := incarnation.parentage.detach }

/-- Detaching changes nothing else — not the state, not the lifecycle. -/
theorem detach_preserves_run (incarnation : ProcessInstance topology) :
    incarnation.detach.kind = incarnation.kind ∧
      incarnation.detach.lifecycle = incarnation.lifecycle :=
  ⟨rfl, rfl⟩

end ProcessInstance

end Grass.Process
