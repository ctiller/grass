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
  /-- Every reason the source can abandon a demand for is a reason here. -/
  interrupt : source.InterruptReason → target.InterruptReason
  /-- Every way the source can fail is a way this process can fail. -/
  fault : source.LogicalFault → target.LogicalFault
  /-- Every environment contract the source can see broken is one this sees. -/
  violation : source.EnvironmentViolation → target.EnvironmentViolation

namespace VocabularyDelivery

variable {source target further : ProcessVocabulary.{u}}

/-- Delivery into itself: the identity classification. -/
def refl (vocabulary : ProcessVocabulary.{u}) : VocabularyDelivery vocabulary vocabulary where
  interrupt := id
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
  interrupt := second.interrupt ∘ first.interrupt
  fault := second.fault ∘ first.fault
  violation := second.violation ∘ first.violation

@[simp] theorem refl_interrupt (vocabulary : ProcessVocabulary.{u})
    (reason : vocabulary.InterruptReason) :
    (refl vocabulary).interrupt reason = reason := rfl

@[simp] theorem trans_fault (first : VocabularyDelivery source target)
    (second : VocabularyDelivery target further) (value : source.LogicalFault) :
    (first.trans second).fault value = second.fault (first.fault value) := rfl

/-! ### An empty target class proves unreachability

The three theorems the ruling turns on. Each says: if a delivery exists and the
target declares the class empty, then the source can produce no such value
either. The process that declared `PEmpty` is therefore not ignoring an event it
should handle — no such event can arrive.
-/

/-- A process that declares no interruption reason receives none. -/
theorem interrupt_source_empty_of_target_empty
    (delivery : VocabularyDelivery source target)
    (targetEmpty : target.InterruptReason → False)
    (reason : source.InterruptReason) : False :=
  targetEmpty (delivery.interrupt reason)

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
The event a delivery carries.

`.external` and `.result` are absent by construction: this function's domain is
the three fault-class events, because those are the ones whose translation is a
free function. A demand crossing a boundary needs a child binding, not this.
-/
inductive Deliverable (vocabulary : ProcessVocabulary.{u}) : Type u
  /-- An outstanding demand was abandoned. -/
  | interrupted (demand : vocabulary.Demand) (reason : vocabulary.InterruptReason)
  /-- The process failed. -/
  | fault (value : vocabulary.LogicalFault)
  /-- The environment broke a contract. -/
  | environmentViolation (violation : vocabulary.EnvironmentViolation)

/--
Carry a deliverable event across the boundary, given the demand it settles on
the receiving side.

The demand is supplied by the caller rather than translated here, because that
translation is the child binding's job — see the module note. What this function
guarantees is that the *reason* is classified, totally.
-/
def carry (delivery : VocabularyDelivery source target) :
    Deliverable source → (target.Demand → Deliverable target)
  | .interrupted _ reason => fun demand => .interrupted demand (delivery.interrupt reason)
  | .fault value => fun _ => .fault (delivery.fault value)
  | .environmentViolation violation =>
      fun _ => .environmentViolation (delivery.violation violation)

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
    (event : Deliverable source) : False := by
  cases event with
  | interrupted _ reason =>
    exact interrupt_source_empty_of_target_empty delivery (fun empty => empty.elim) reason
  | fault value =>
    exact fault_source_empty_of_target_empty delivery (fun empty => empty.elim) value
  | environmentViolation violation =>
    exact violation_source_empty_of_target_empty delivery (fun empty => empty.elim) violation

end VocabularyDelivery

end Grass.Process
