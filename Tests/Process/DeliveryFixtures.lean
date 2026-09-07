import Grass.Process.Network.Delivery

/-!
# An empty fault class is a theorem, not a hole

`agent-bus` disposition `g-design:4` ratified per-vocabulary fault classes on
condition that cross-vocabulary delivery owe a total classifier, so that an
empty target class *proves* unreachability. These fixtures are the two sides of
that claim on concrete vocabularies.

`worker` can fail and be cancelled. `auditor` cannot do either. The fixtures
show that a delivery from `worker` into `auditor` cannot be built at all — so
`auditor` is not ignoring faults it should handle, it is provably never sent
one — while a delivery into a vocabulary that *does* declare the classes is
ordinary and total.
-/

namespace Grass.Process.Tests.Delivery

open Grass.Process

/-! ## Two vocabularies -/

inductive WorkerFault
  | outOfMemory
  | providerLost
  deriving DecidableEq, Repr

inductive WorkerInterrupt
  | deadline
  | shutdown
  deriving DecidableEq, Repr

/-- A worker: it can fail, and it can be cancelled. -/
@[reducible] def worker : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := Unit
  Result := fun _ => Unit
  Observation := Unit
  InterruptReason := fun _ => WorkerInterrupt
  LogicalFault := WorkerFault
  EnvironmentViolation := PEmpty

/-- A supervisor that admits the same classes plus one of its own. -/
inductive SupervisorFault
  | childFailed (cause : WorkerFault)
  | policyExhausted
  deriving DecidableEq, Repr

@[reducible] def supervisor : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := Unit
  Result := fun _ => Unit
  Observation := Unit
  InterruptReason := fun _ => WorkerInterrupt
  LogicalFault := SupervisorFault
  EnvironmentViolation := PEmpty

/-- An auditor that claims it cannot fail, cannot be cancelled, and assumes
nothing of its environment. -/
@[reducible] def auditor : ProcessVocabulary.{0} :=
  ProcessVocabulary.quiescent Unit Unit (fun _ => Unit) Unit

/-! ## Delivering into a vocabulary that admits the classes

Ordinary and total: every worker fault is classified as a supervisor fault, and
every worker interrupt reason is a supervisor one.
-/

def workerToSupervisor : VocabularyDelivery worker supervisor where
  fault := .childFailed
  violation := fun empty => empty.elim

/--
And the interruption half, which is a separate record since `InterruptReason`
became demand-indexed.

`demand := id` is the content that had nowhere to live before: it says which of
the supervisor's demands a worker's abandoned demand becomes, and the reason
classifier is indexed by it. The un-indexed version could classify a reason
without saying anything about the demand at all.
-/
def workerInterruptsSupervisor : InterruptDelivery worker supervisor where
  demand := id
  reason := id

/-- Classification is total: a fault the worker can raise has an image. -/
theorem every_worker_fault_classified (value : WorkerFault) :
    workerToSupervisor.fault value = .childFailed value := rfl

/-- And it carries: a worker fault arrives as the supervisor's own fault. -/
theorem carries_fault :
    workerToSupervisor.carryFault .outOfMemory =
      .fault (.childFailed .outOfMemory) := rfl

/-- Deliveries compose, so a two-hop fault is classified once per hop. -/
theorem composes (value : WorkerFault) :
    (workerToSupervisor.trans (VocabularyDelivery.refl supervisor)).fault value =
      .childFailed value := rfl

/-! ## A fault reaches a target that has no demands at all

The adversarial case `g-reviewer:18` asked for. `ledger` declares
`Demand := PEmpty` — it asks the environment for nothing — and an inhabited
fault class. An earlier version of `carry` returned
`target.Demand → Deliverable target` for every event, so a fault could not be
carried here at all, even though the classification was total and correct.
-/

inductive LedgerFault
  | corrupted
  deriving DecidableEq, Repr

/-- A process that asks for nothing and can still fail. -/
@[reducible] def ledger : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := PEmpty
  Result := fun demand => demand.elim
  Observation := Unit
  InterruptReason := fun _ => WorkerInterrupt
  LogicalFault := LedgerFault
  EnvironmentViolation := PEmpty

/--
A delivery into it.

The interrupt classes line up, so this is an ordinary total classifier. The
interesting field is the one that is *not* here: nothing about demands.
-/
def workerToLedger : VocabularyDelivery worker ledger where
  fault := fun _ => LedgerFault.corrupted
  violation := fun empty => empty.elim

/--
**A fault is carried with no demand in sight.**

`ledger.Demand` is uninhabited, so nothing of that type can be supplied. The
fault arrives anyway, which is what "faults carry no dependent result" has to
mean if it means anything.
-/
theorem carries_fault_without_demand :
    workerToLedger.carryFault .outOfMemory =
      VocabularyDelivery.Deliverable.fault LedgerFault.corrupted := rfl

/--
And no demand *could* have been supplied: `ledger.Demand` is uninhabited.

Stated so the previous theorem is not read as "a demand happened to be
available". There is no such value, and the fault arrives regardless.
-/
theorem ledger_has_no_demand (demand : ledger.Demand) : False := demand.elim

/--
**And the same target can receive no interruption at all**, which is the
distinction demand-indexing bought and the reason `InterruptDelivery` is a
separate record.

An interruption abandons one exact demand and arrives attributed to one exact
demand of the receiver. The ledger has none, so there is nothing for an arriving
interruption to be about — while a fault, which is about no demand, arrives
perfectly well. Both facts hold of the same pair of vocabularies, and a single
bundled record could state neither: adding the demand translation to
`VocabularyDelivery` would have made `carries_fault_without_demand`
unconstructible, and leaving it out left the reason classifier unable to say
which demand it was talking about.
-/
theorem no_interrupt_delivery_worker_to_ledger :
    ¬ Nonempty (InterruptDelivery worker ledger) := by
  rintro ⟨delivery⟩
  exact (delivery.demand ()).elim

/-! ## Delivering into the auditor is impossible

Not "discouraged" and not "unhandled": there is no such value. A total function
`WorkerFault → PEmpty` would give an element of `PEmpty` from `outOfMemory`.
-/

/-- The classifier a delivery into the auditor would have to supply cannot exist. -/
theorem no_delivery_worker_to_auditor :
    ¬ Nonempty (VocabularyDelivery worker auditor) := by
  rintro ⟨delivery⟩
  exact (delivery.fault .outOfMemory).elim

/--
So the auditor's `PEmpty` fault class is discharged, not assumed.

This is the theorem `Grass/Process/Vocabulary.lean` promised when it said a
`PEmpty` class was an assumption until the classifier existed: given any
delivery into a quiescent vocabulary, the sender's deliverable events are
uninhabited.
-/
theorem auditor_receives_nothing
    (delivery : VocabularyDelivery worker auditor)
    (interrupts : InterruptDelivery worker auditor)
    (event : VocabularyDelivery.Deliverable worker) : False :=
  VocabularyDelivery.nothing_deliverable_into_quiescent delivery interrupts event

/--
The auditor may still deliver into itself.

Worth stating so the previous theorem is not misread as "quiescent vocabularies
cannot participate": the identity delivery exists, and it carries nothing
because there is nothing to carry.
-/
def auditorToItself : VocabularyDelivery auditor auditor :=
  VocabularyDelivery.refl auditor

/-- Both halves of it. -/
def auditorInterruptsItself : InterruptDelivery auditor auditor :=
  InterruptDelivery.refl auditor

theorem auditor_deliverables_uninhabited
    (event : VocabularyDelivery.Deliverable auditor) : False :=
  VocabularyDelivery.nothing_deliverable_into_quiescent auditorToItself
    auditorInterruptsItself event

/-! ## A reason that is valid for one demand and unrepresentable for another

The whole point of the indexing, and the corpus had no fixture for it while the
class was flat. `docs/DECISIONS.md` decision 121 asks the type to make a reason
invalid for a demand unrepresentable; this is that, at a vocabulary with two
demands whose interruption classes differ.
-/

inductive TwoDemands
  | write
  | compute
  deriving DecidableEq, Repr

inductive WriteInterrupt
  | diskFull
  deriving DecidableEq, Repr

/--
A process that can be interrupted while writing and not while computing.

`compute`'s reason class is `PEmpty`, which is a claim: a computation of this
process, once started, is never abandoned. Under the flat spelling there was no
way to say that without also saying the write could not be abandoned either.
-/
@[reducible] def mixed : ProcessVocabulary.{0} where
  ExternalEvent := Unit
  Demand := TwoDemands
  Result := fun _ => Unit
  Observation := Unit
  InterruptReason := fun demand =>
    match demand with
    | .write => WriteInterrupt
    | .compute => PEmpty
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

/-- The write can be abandoned. -/
theorem writing_can_be_interrupted : Nonempty (mixed.InterruptReason .write) :=
  ⟨WriteInterrupt.diskFull⟩

/-- The computation cannot, and that is a theorem rather than an omission. -/
theorem computing_cannot_be_interrupted (reason : mixed.InterruptReason .compute) :
    False :=
  reason.elim

/--
**And a delivery proves it of the sender too, one demand at a time.**

`InterruptDelivery.source_empty_of_target_empty` needs only the target's class
at the demand in question, so a source delivering into `mixed` at `.compute`
has no reason to abandon a computation either — while saying nothing about
whether it can abandon a write. The flat lemma had to empty the target's whole
interruption class to conclude anything.
-/
theorem no_reason_survives_into_compute
    (delivery : InterruptDelivery mixed mixed)
    (computeStays : delivery.demand .compute = .compute)
    (reason : mixed.InterruptReason .compute) : False :=
  (computeStays ▸ delivery.reason reason : mixed.InterruptReason .compute).elim

end Grass.Process.Tests.Delivery
