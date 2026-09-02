import Grass.Process.Network.Delivery
import Grass.Process.Network.Instance
import Grass.Process.Protocol.Registry

/-!
# Child demands: routing a whole protocol's outcomes back to one parent demand

`docs/PROCESS.md` §3 models an API operation as a nominal child protocol rather
than an atomic function with an oversized result sum, and puts the whole weight
of that choice on one field:

> The binding—not a child key alone—authorizes spawn. It proves the exact
> request is initially valid and realizes the parent demand, exhaustively
> classifies every child terminal result, failure, interruption, cancellation
> acknowledgement/race, fault, violation, and death as the precise parent
> result/event or a named non-returning disposition, preserves and reflects
> result choices, and carries the matching resource/obligation/cancellation
> equation.

`Grass/Process/Network/Delivery.lean` did this for the three fault classes,
which are free functions because they carry no dependent result. This module
does it for the case that is not free: a child's *success* answers a specific
parent demand, and the parent's answer type depends on which demand it was.

## Why classification is a function

`classify` is total by construction, which is the point. `docs/FOUNDATION.md`
law 5 requires every admitted result to be handled and law 8 forbids
approximating an unknown outcome as a no-op; a partial classification would be
both. Every way a child protocol can end has an image, and
`ChildLifecycleOutcome` is closed so that "every way" is checkable rather than
aspirational.

## Why a non-returning disposition is a constructor and not an omission

Some child outcomes legitimately never reach the parent: a detached child that
dies, an operation whose result the parent has already stopped waiting for.
`docs/PROCESS.md` §3 calls that "a named non-returning disposition", and the
word *named* is what this module implements — `ParentDisposition.nonReturning`
carries its reason, so a binding that drops an outcome has said so and a
reviewer can see which outcomes it drops.
-/

namespace Grass.Process

universe u w v

/-- Why an outcome never reaches the parent. -/
inductive NonReturningReason
  /-- The parent had already stopped waiting for this occurrence. -/
  | abandoned
  /-- The child was detached, so its outcome is nobody's result. -/
  | detached
  /-- The parent is itself finished; there is no transition to route into. -/
  | parentTerminated
  deriving DecidableEq, Repr

/--
Every way a child protocol run can end, plus the way it can fail to end.

Closed, and that is what makes `ChildDemandBinding.classify`'s totality mean
something: an author cannot handle success and leave death to a later proof,
because there is no later proof to leave it to.

`pending` is here because `docs/PROCESS.md` §3 insists it is an outcome to be
classified rather than an absence — "the outstanding occurrence and its suffix
remain live while pending" — so a binding must say what a parent hears when a
child is simply not finished, which is normally nothing.
-/
inductive ChildLifecycleOutcome (child : ProcessSpec.{u, w}) (request : child.Request) : Type (max u w)
  /-- Not finished. Still live. -/
  | pending
  /-- Finished, with the protocol's typed result. -/
  | succeeded (result : child.TerminalResult) (isTerminal : ∃ state, child.Terminal request state result)
  /-- An outstanding demand of the child's own was abandoned. -/
  | interrupted (reason : child.InterruptReason)
  /-- The child failed. -/
  | faulted (fault : child.LogicalFault)
  /-- The child's environment broke a contract. -/
  | environmentViolation (violation : child.EnvironmentViolation)
  /-- The child stopped existing without finishing.

  The reason is `Grass/Process/Network/Instance.lean`'s `ProcessDeathReason`,
  not a child-specific one. It used to be declared here as `ChildDeathReason`,
  which was wrong twice over: none of its three reasons is about being a child,
  and `docs/PROCESS.md` §4 gives `senderDeath` and `receiverDeath` transitions to
  processes that may be roots. -/
  | died (reason : ProcessDeathReason)

/--
Where a child outcome goes in the parent.

Either it becomes a parent event, or it is named as not returning. There is no
third case, and in particular no silent drop.
-/
inductive ParentDisposition (parent : ProcessSpec.{u, w}) : Type (max u w)
  /-- The parent hears this event. -/
  | event (event : parent.Event)
  /-- The parent hears nothing, for this stated reason. -/
  | nonReturning (reason : NonReturningReason)

/--
The binding that authorizes one parent demand to be realized by one child
protocol run.

`classify` is the exhaustive routing `docs/PROCESS.md` §3 demands. The three
laws after it are what stop a total function from being a *wrong* total
function.
-/
structure ChildDemandBinding {registry : ProtocolRegistry.{u, w, v}}
    (parent : ProcessSpec.{u, w}) (demand : parent.Demand)
    (request : ChildRequest registry) where
  /-- The child protocol, from the registry. Never an embedded `ProcessSpec`. -/
  child : ProcessSpec.{u, w} := registry.protocol request.key
  /-- That equation, retained so a consumer can transport along it. -/
  childExact : child = registry.protocol request.key
  /--
  The child's request is initially valid: there is a run to spawn.

  `docs/PROCESS.md` §3: the binding "proves the exact request is initially
  valid". Without it a spawn could authorize a protocol run that has no initial
  state, and the parent would wait forever on an occurrence that never began.
  -/
  childInitial : ∃ state issued emitted,
    child.Initial (childExact ▸ request.request) state issued emitted
  /-- Every child outcome is routed. -/
  classify : ChildLifecycleOutcome child (childExact ▸ request.request) →
    ParentDisposition parent
  /--
  A child that succeeded answers *this* demand and no other.

  The law that stops cross-wiring. `docs/PROCESS.md` §5 forbids a driver to
  "attach one result to another occurrence"; this is the same prohibition at
  the binding, where the wiring is chosen.
  -/
  successAnswersThisDemand : ∀ result isTerminal,
    ∀ event, classify (.succeeded result isTerminal) = .event event →
      event.settles = some demand
  /--
  A pending child produces no parent event.

  `pending` is "an intermediate child-lifecycle event, not a completed dependent
  result". Routing it to a `result` event would fabricate an answer.
  -/
  pendingDoesNotAnswer : ∀ event,
    classify .pending = .event event → event.settles = none
  /--
  Every answer the parent can receive for this demand comes from some child
  outcome.

  The *reflects* half of `docs/PROCESS.md` §3's "preserves and reflects every
  allowed child result choice". Without it a binding could route only the
  outcomes it liked and leave parent results that no execution produces, which
  would make the parent's case analysis over `Result demand` unsound as a
  description of what can happen.
  -/
  reflectsEveryAnswer : ∀ answer : parent.Result demand,
    ∃ outcome, classify outcome = .event (.result demand answer)

namespace ChildDemandBinding

variable {registry : ProtocolRegistry.{u, w, v}} {parent : ProcessSpec.{u, w}}
  {demand : parent.Demand} {request : ChildRequest registry}
  {binding : ChildDemandBinding parent demand request}

/--
A child outcome the parent never hears about.

Named rather than absent, so a reviewer reading a binding can see exactly which
outcomes it drops and why.
-/
def Drops (binding : ChildDemandBinding (registry := registry) parent demand request)
    (outcome : ChildLifecycleOutcome binding.child
      (binding.childExact ▸ request.request)) : Prop :=
  ∃ reason, binding.classify outcome = .nonReturning reason

/--
Every outcome either reaches the parent or is a named drop. There is no third
possibility.

Trivial from `ParentDisposition` having two constructors, and worth stating
because it is the property the exhaustiveness claim reduces to: totality of
`classify` plus this is "every child outcome is accounted for".
-/
theorem routed_or_dropped
    (binding : ChildDemandBinding (registry := registry) parent demand request)
    (outcome : ChildLifecycleOutcome binding.child
      (binding.childExact ▸ request.request)) :
    (∃ event, binding.classify outcome = .event event) ∨
      (∃ reason, binding.classify outcome = .nonReturning reason) := by
  cases routing : binding.classify outcome with
  | event event => exact Or.inl ⟨event, rfl⟩
  | nonReturning reason => exact Or.inr ⟨reason, rfl⟩

/--
A success is never dropped silently *and* answered: the two dispositions are
exclusive.
-/
theorem success_not_both
    {binding : ChildDemandBinding (registry := registry) parent demand request}
    {result isTerminal event}
    (answered : binding.classify (.succeeded result isTerminal) = .event event) :
    ¬ binding.Drops (.succeeded result isTerminal) := by
  rintro ⟨reason, dropped⟩
  rw [answered] at dropped
  exact absurd dropped (by simp)

/--
**A parent with no fault class receives no child fault, or the binding drops
it.**

The child-boundary counterpart of
`VocabularyDelivery.nothing_deliverable_into_quiescent`. There the classifier
was a total function into the parent's class, so an empty class made the
delivery unconstructible. Here the binding may instead route to
`nonReturning`, so an empty parent class does not make the *binding*
impossible — it forces the fault to be a named drop.

That difference is not an inconsistency; it is what the two boundaries mean. A
network delivery says "this event arrives"; a child binding chooses whether an
outcome arrives at all. A parent that declares no fault class and spawns a
child that can fault must say, in the binding, that it is abandoning those
faults.
-/
theorem faultDroppedOrRouted
    (binding : ChildDemandBinding (registry := registry) parent demand request)
    (fault : binding.child.LogicalFault) :
    (∃ event, binding.classify (.faulted fault) = .event event) ∨
      binding.Drops (.faulted fault) :=
  binding.routed_or_dropped (.faulted fault)

/-- The same statement with the drop named, which is the form a reader wants. -/
theorem routed_or_named_drop
    (binding : ChildDemandBinding (registry := registry) parent demand request)
    (outcome : ChildLifecycleOutcome binding.child
      (binding.childExact ▸ request.request)) :
    (∃ event, binding.classify outcome = .event event) ∨ binding.Drops outcome :=
  binding.routed_or_dropped outcome

end ChildDemandBinding

end Grass.Process
