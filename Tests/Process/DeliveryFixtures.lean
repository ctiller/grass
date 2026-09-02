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
  InterruptReason := WorkerInterrupt
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
  InterruptReason := WorkerInterrupt
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
  interrupt := id
  fault := .childFailed
  violation := fun empty => empty.elim

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
  InterruptReason := WorkerInterrupt
  LogicalFault := LedgerFault
  EnvironmentViolation := PEmpty

/--
A delivery into it.

The interrupt classes line up, so this is an ordinary total classifier. The
interesting field is the one that is *not* here: nothing about demands.
-/
def workerToLedger : VocabularyDelivery worker ledger where
  interrupt := id
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
    (event : VocabularyDelivery.Deliverable worker) : False :=
  VocabularyDelivery.nothing_deliverable_into_quiescent delivery event

/--
The auditor may still deliver into itself.

Worth stating so the previous theorem is not misread as "quiescent vocabularies
cannot participate": the identity delivery exists, and it carries nothing
because there is nothing to carry.
-/
def auditorToItself : VocabularyDelivery auditor auditor :=
  VocabularyDelivery.refl auditor

theorem auditor_deliverables_uninhabited
    (event : VocabularyDelivery.Deliverable auditor) : False :=
  VocabularyDelivery.nothing_deliverable_into_quiescent auditorToItself event

end Grass.Process.Tests.Delivery
