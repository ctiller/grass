import Grass.Process.Vocabulary

/-!
# Cross-vocabulary delivery

`agent-bus` disposition `g-design:4`, ruling on issue `c-process:9`:

> Per-`ProcessVocabulary` classes are ratified, but vocabulary selection belongs
> at a reusable network/protocol boundary rather than adding bespoke fields to
> every ordinary `ProcessSpec` author surface. **Cross-vocabulary delivery owes
> a total classifier; an empty target class proves unreachability.**

This module is that classifier, and the emphasis is the whole of it.

## The obligation the per-vocabulary decision created

With one global fault classification, "the network may deliver an environment
violation to this process" is an obligation every process discharges by
construction. Carrying the classes per vocabulary removes that guarantee: a
process whose `EnvironmentViolation` is `PEmpty` has made the corresponding
event *unconstructible*, and `Grass/Process/Vocabulary.lean` said honestly that
this was an assumption rather than a discharged obligation until a classifier
existed.

Here is why the classifier discharges it. `VocabularyDelivery` is three *total*
functions. A total function into `PEmpty` cannot exist unless its domain is also
empty — that is `interrupt_source_empty_of_target_empty` below. So a delivery
into a process that declares no interruption reason is available only from a
side that can produce none, and the empty class is a *theorem* about what can
arrive rather than a hole in what is handled.

`docs/FOUNDATION.md` law 8 is what makes this the right shape: an unclassified
event must be rejected rather than approximated, so the classifier is total and
there is no `other` constructor to fall through to.

## What it does not cover

The three fault classes only. External events and demands also differ between
two vocabularies, but their translation is not a free function: a demand's
answer is dependent on the demand, so carrying one across a boundary is a child
binding, with an occurrence and a result correlation. That is
`Grass/Process/Network/Child.lean` and is M2 work. This module is the part the
ruling names, and it is separable precisely because faults carry no dependent
result.
-/

namespace Grass.Process

universe u

/--
A total classification of one vocabulary's fault classes into another's.

Three total functions and nothing else. `docs/PROCESS.md` §3 requires the same
shape of `ChildDemandBinding.classify` — "exhaustively classifies every child
terminal result, failure, interruption, cancellation acknowledgement/race,
fault, violation, and death as the precise parent result/event" — and this is
that requirement for the three classes that have no dependent result.
-/
structure VocabularyDelivery (source target : ProcessVocabulary.{u}) where
  /-- Every way the source can fail is a way this process can fail. -/
  fault : source.LogicalFault → target.LogicalFault
  /-- Every environment contract the source can see broken is one this sees. -/
  violation : source.EnvironmentViolation → target.EnvironmentViolation

/--
**The interruption half, which needs a demand translation and therefore cannot
live in `VocabularyDelivery`.**

`ProcessVocabulary.InterruptReason` is indexed by the demand abandoned
(`agent-bus` ruling `g-design:67`), so classifying a reason means saying which
of the target's demands the abandoned one becomes. That is a translation
`VocabularyDelivery` deliberately does not have: the module's own argument is
that a fault "carries no dependent result", and `carries_fault_without_demand`
is the fixture holding it — a target whose `Demand` is `PEmpty` still receives
faults from a source that has demands.

Bundling the two would destroy that. A `demand : source.Demand → target.Demand`
field makes `VocabularyDelivery` unconstructible whenever the target names no
demands, which would take the fault classification down with it. So the bundle
splits along the line the indexing drew: the demand-free classes stay together,
and the one that is now dependent gets its own record.

Decision 121's totality is unchanged and now says more. Where a
`VocabularyDelivery` says every fault is classified, this says every reason for
abandoning *each particular demand* is classified as a reason for abandoning the
demand it becomes — so a target cannot receive an interruption attributed to a
demand it does not have.
-/
structure InterruptDelivery (source target : ProcessVocabulary.{u}) where
  /-- Which of the target's demands an abandoned source demand becomes. -/
  demand : source.Demand → target.Demand
  /-- And every reason the source can abandon it for is a reason to abandon
  that one. -/
  reason : ∀ {abandoned : source.Demand},
    source.InterruptReason abandoned → target.InterruptReason (demand abandoned)

namespace VocabularyDelivery

variable {source target further : ProcessVocabulary.{u}}

/-- Delivery into itself: the identity classification. -/
def refl (vocabulary : ProcessVocabulary.{u}) : VocabularyDelivery vocabulary vocabulary where
  fault := id
  violation := id

/--
Deliveries compose, so a fault crossing two boundaries is classified once at
each and not re-derived.

This is what makes the obligation payable in a deep network: a stream's fault
reaches the root through the connection, and each hop owes only its own
classification.
-/
def trans (first : VocabularyDelivery source target)
    (second : VocabularyDelivery target further) :
    VocabularyDelivery source further where
  fault := second.fault ∘ first.fault
  violation := second.violation ∘ first.violation

@[simp] theorem refl_fault (vocabulary : ProcessVocabulary.{u})
    (value : vocabulary.LogicalFault) :
    (refl vocabulary).fault value = value := rfl

@[simp] theorem trans_fault (first : VocabularyDelivery source target)
    (second : VocabularyDelivery target further) (value : source.LogicalFault) :
    (first.trans second).fault value = second.fault (first.fault value) := rfl

/-! ### An empty target class proves unreachability

The three theorems the ruling turns on. Each says: if a delivery exists and the
target declares the class empty, then the source can produce no such value
either. The process that declared `PEmpty` is therefore not ignoring an event it
should handle — no such event can arrive.
-/

/-- A process that declares no fault class receives no fault. -/
theorem fault_source_empty_of_target_empty
    (delivery : VocabularyDelivery source target)
    (targetEmpty : target.LogicalFault → False)
    (value : source.LogicalFault) : False :=
  targetEmpty (delivery.fault value)

/-- A process that assumes nothing of its environment is told of no violation. -/
theorem violation_source_empty_of_target_empty
    (delivery : VocabularyDelivery source target)
    (targetEmpty : target.EnvironmentViolation → False)
    (violation : source.EnvironmentViolation) : False :=
  targetEmpty (delivery.violation violation)

/--
The events a delivery carries.

`.external` and `.result` are absent by construction: this family is the three
fault-class events, because those are the ones whose translation is a free
function. A demand crossing a boundary needs a child binding, not this.
-/
inductive Deliverable (vocabulary : ProcessVocabulary.{u}) : Type u
  /-- An outstanding demand was abandoned. -/
  | interrupted (demand : vocabulary.Demand) (reason : vocabulary.InterruptReason demand)
  /-- The process failed. -/
  | fault (value : vocabulary.LogicalFault)
  /-- The environment broke a contract. -/
  | environmentViolation (violation : vocabulary.EnvironmentViolation)

/-!
### Carrying, one entry point per class

A first version of this had a single `carry` returning
`target.Demand → Deliverable target` for *every* source event. That was wrong,
and `g-reviewer` caught it in the round it was written: a fault carries no
demand, so making its delivery depend on one meant a target with
`Demand := PEmpty` could not receive a fault *even when its fault class was
inhabited and correctly classified*. The module claimed faults separate cleanly
because they carry no dependent result, and then wrote code that did not.

There are three entry points now. Two of them mention no demand at all.
-/

/--
Carry a fault. No demand is involved, and none is required.

`carries_fault_without_demand` in the fixtures is the adversarial case: a target
whose `Demand` is `PEmpty` and whose `LogicalFault` is inhabited still receives
faults.
-/
def carryFault (delivery : VocabularyDelivery source target)
    (value : source.LogicalFault) : Deliverable target :=
  .fault (delivery.fault value)

/-- Carry an environment violation. Also demand-free. -/
def carryViolation (delivery : VocabularyDelivery source target)
    (violation : source.EnvironmentViolation) : Deliverable target :=
  .environmentViolation (delivery.violation violation)

end VocabularyDelivery

namespace InterruptDelivery

variable {source target further : ProcessVocabulary.{u}}

/-- Delivery into itself: the identity classification, at the identity demand
translation. -/
def refl (vocabulary : ProcessVocabulary.{u}) : InterruptDelivery vocabulary vocabulary where
  demand := id
  reason := id

/-- These compose too, and the demand translations compose with them. -/
def trans (first : InterruptDelivery source target)
    (second : InterruptDelivery target further) :
    InterruptDelivery source further where
  demand := second.demand ∘ first.demand
  reason := fun reason => second.reason (first.reason reason)

/--
**A process that declares no reason for abandoning the demand this one becomes
receives no interruption of it.**

`VocabularyDelivery.interrupt_source_empty_of_target_empty` was the un-indexed
form and said less: it needed the target's *whole* interruption class empty.
This needs only the class at the one demand, so a target that can be interrupted
while writing but not while sleeping proves the sleeping case unreachable
without claiming anything about writing.
-/
theorem source_empty_of_target_empty (delivery : InterruptDelivery source target)
    (targetEmpty : ∀ demand, target.InterruptReason demand → False)
    {abandoned : source.Demand} (reason : source.InterruptReason abandoned) : False :=
  targetEmpty _ (delivery.reason reason)

/--
Carry an interruption. The demand it settles on the receiving side is the
delivery's own translation of the demand it abandoned here, not a value the
caller chooses.

That is the substantive change demand-indexing made. The un-indexed version took
the target demand as an argument and could attribute a `Sleep`'s interruption to
a `WriteFile`; there was no field relating the two, because there could not be
one while the reason's type did not mention a demand.
-/
def carryInterrupted (delivery : InterruptDelivery source target)
    {abandoned : source.Demand} (reason : source.InterruptReason abandoned) :
    VocabularyDelivery.Deliverable target :=
  .interrupted (delivery.demand abandoned) (delivery.reason reason)

end InterruptDelivery

namespace VocabularyDelivery

variable {source target : ProcessVocabulary.{u}}

/--
Carry any deliverable, given both classifications.

The interruption case needs an `InterruptDelivery` and the other two do not,
which is the split stated as a signature. A caller that only has faults to carry
uses `carryFault` and never mentions a demand or an `InterruptDelivery` at all.
-/
def carry (delivery : VocabularyDelivery source target)
    (interrupts : InterruptDelivery source target) :
    Deliverable source → Deliverable target
  | .interrupted _demand reason => interrupts.carryInterrupted reason
  | .fault value => delivery.carryFault value
  | .environmentViolation violation => delivery.carryViolation violation

@[simp] theorem carry_fault (delivery : VocabularyDelivery source target)
    (interrupts : InterruptDelivery source target) (value : source.LogicalFault) :
    delivery.carry interrupts (.fault value) = delivery.carryFault value := rfl

/--
Nothing is deliverable into a quiescent vocabulary except from one that can
produce nothing.

The headline consequence, and the one a reviewer should check:
`ProcessVocabulary.quiescent` sets all three classes to `PEmpty`, and its
docstring claims that is an assertion rather than an omission. This is that
assertion discharged — given a delivery into it, the source's own deliverable
events are uninhabited.
-/
theorem nothing_deliverable_into_quiescent
    {ExternalEvent Demand : Type u} {Result : Demand → Type u} {Observation : Type u}
    (delivery : VocabularyDelivery source
      (ProcessVocabulary.quiescent ExternalEvent Demand Result Observation))
    (interrupts : InterruptDelivery source
      (ProcessVocabulary.quiescent ExternalEvent Demand Result Observation))
    (event : Deliverable source) : False := by
  cases event with
  | interrupted _ reason =>
    exact InterruptDelivery.source_empty_of_target_empty interrupts
      (fun _ empty => empty.elim) reason
  | fault value =>
    exact fault_source_empty_of_target_empty delivery (fun empty => empty.elim) value
  | environmentViolation violation =>
    exact violation_source_empty_of_target_empty delivery (fun empty => empty.elim) violation

end VocabularyDelivery

end Grass.Process
