import Grass.Op.Completion

/-!
# Events derived from clean prepared completions

These laws expose the existing checked transition. They do not equate `.ran`
with success: the caller must connect the actual transition and prove its final
violation ledger empty. Event existence follows from a well-formed descriptor
and a complete answer, rather than being an assumed output receipt.
-/

namespace Grass.Op

open Grass.Core Grass.Memory

/-- A non-inert intent has an event kind. -/
theorem kindOf_exists_of_notInert (intent : AccessIntent)
    (active : ¬ intent.IsInert) :
    ∃ kind, MemoryEvent.kindOf intent = some kind := by
  rcases intent with ⟨reads, writes, executes, atomic⟩
  cases reads <;> cases writes <;>
    simp_all [AccessIntent.IsInert, MemoryEvent.kindOf]

/-- Complete answers to well-formed accesses produce a certified event. -/
theorem completedEvent_exists (id : EventId) (contextKind : ContextKind)
    (cause : EventCause) (space : AddressSpace) (d : AccessDescriptor)
    (complete : CompleteCommitted d) (mapping : Coordinates.Mapping)
    (wellFormed : d.WellFormedIn space) :
    ∃ valid, MemoryEvent.ofOutcome id contextKind cause space d
      (.completed complete) mapping = some valid := by
  obtain ⟨kind, hkind⟩ := kindOf_exists_of_notInert d.intent wellFormed.notInert
  have hspace : space.id = d.provenance.space :=
    wellFormed.spaceResolved.trans wellFormed.spaceAgrees.symm
  unfold MemoryEvent.ofOutcome
  simp only [hspace, ne_eq, not_true_eq_false, ↓reduceDIte, AccessOutcome.committed?]
  split
  · rename_i impossible
    rw [hkind] at impossible
    contradiction
  · exact ⟨_, rfl⟩

/-- A completed event records the supplied access and exact committed values. -/
theorem completedEvent_fields {id : EventId} {contextKind : ContextKind}
    {cause : EventCause} {space : AddressSpace} {d : AccessDescriptor}
    {complete : CompleteCommitted d} {mapping : Coordinates.Mapping}
    {valid : ValidMemoryEvent}
    (event : MemoryEvent.ofOutcome id contextKind cause space d
      (.completed complete) mapping = some valid) :
    valid.event.id = id ∧
    valid.event.context.id = d.context ∧
    valid.event.context.kind = contextKind ∧
    valid.event.provenance = d.provenance ∧
    valid.event.range = d.range ∧
    valid.event.mapping = mapping ∧
    valid.event.status = .completed complete.committed.readCount complete.committed.writeCount ∧
    valid.event.valueRead = complete.committed.observed ∧
    valid.event.valueWritten = complete.committed.written := by
  unfold MemoryEvent.ofOutcome at event
  split at event
  · contradiction
  simp only [AccessOutcome.committed?] at event
  split at event
  · contradiction
  cases Option.some.inj event
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `clean_prepared_completion_event` derives the exact event produced by
the checked constructor, advances its supply, and preserves fault history. -/
theorem clean_prepared_completion_event (policy : StepPolicy) (before after : MachineState)
    (d : AccessDescriptor) (resolved : before.memory.ResolvedAccess d.provenance d.range)
    (prepared : prepareAccess before.memory d = .ok resolved)
    (complete : CompleteCommitted d) (contextKind : ContextKind) (cause : EventCause)
    (space : AddressSpace)
    (found : policy.profile.vocabulary.addressSpaces.find? d.space = some space)
    (wellFormed : d.WellFormedIn space)
    (ran : after = performPreparedAccess policy before d resolved prepared
      (.completed complete) contextKind cause)
    (clean : after.violations.IsEmpty) :
    ∃ valid,
      MemoryEvent.ofOutcome before.eventSupply.fresh.1 contextKind cause space d
        (.completed complete) resolved.allocation.mapping = some valid ∧
      after.events = before.events ++ [valid] ∧
      after.eventSupply = before.eventSupply.fresh.2 ∧
      after.faults = before.faults ∧
      after.violations = before.violations ∧
      refusalOfResolved policy before d resolved (some valid.event) = Option.none := by
  obtain ⟨valid, event⟩ := completedEvent_exists before.eventSupply.fresh.1
    contextKind cause space d complete resolved.allocation.mapping wellFormed
  subst after
  unfold performPreparedAccess at clean ⊢
  simp only [found] at clean ⊢
  simp only [event] at clean ⊢
  split at clean
  · exact (AuditViolationLedger.not_isEmpty_append _ _ clean).elim
  next noRefusal =>
    split at clean
    · exact (AuditViolationLedger.not_isEmpty_append _ _ clean).elim
    next ledger ledgerApplied =>
      split at clean
      · exact (AuditViolationLedger.not_isEmpty_append _ _ clean).elim
      next lent authorityApplied =>
        exact ⟨valid, rfl, rfl, rfl, rfl, rfl, noRefusal⟩

/-- A clean singleton completion of the actual selected operation emits its
certified event. Descriptor admission is extracted from the same actual step;
the caller supplies neither a second admission claim nor an asserted event. -/
theorem ran_clean_singleton_event (policy : StepPolicy) (before : MachineState)
    (operation : SomeOperation) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (faultAt : (sequence : SubstepSequence) → FaultPlan sequence)
    (sequence : SubstepSequence) (d : AccessDescriptor) (after : MachineState)
    (selected : operation.facets.substeps? = some sequence)
    (singleton : sequence.accesses = [d]) (noFault : faultAt sequence = .none)
    (ran : step policy before operation context contextKind cause faultAt = .ran after)
    (resolved : (before.noteContext context contextKind).memory.ResolvedAccess
      d.provenance d.range)
    (prepared : prepareAccess (before.noteContext context contextKind).memory d = .ok resolved)
    (complete : CompleteCommitted d)
    (answered : policy.oracle.answerResolved (before.noteContext context contextKind)
      d resolved = some complete)
    (clean : after.violations.IsEmpty) :
    ∃ space valid,
      policy.profile.vocabulary.addressSpaces.find? d.space = some space ∧
      MemoryEvent.ofOutcome before.eventSupply.fresh.1 contextKind cause space d
        (.completed complete) resolved.allocation.mapping = some valid ∧
      after.events = before.events ++ [valid] ∧
      after.eventSupply = before.eventSupply.fresh.2 ∧
      after.faults = before.faults ∧ after.violations = before.violations := by
  obtain ⟨space, found, wellFormed⟩ := ran_selected_access_wellFormed policy before
    operation context contextKind cause faultAt sequence after d selected ran
    (by simp [singleton])
  have completed := ran_singleton_prepared_eq_performPreparedAccess policy before
    operation context contextKind cause faultAt sequence d after selected singleton noFault
    ran resolved prepared complete answered
  obtain ⟨valid, event, appended, supply, faults, violations, _⟩ :=
    clean_prepared_completion_event policy (before.noteContext context contextKind) after
      d resolved prepared complete contextKind cause space found wellFormed completed clean
  exact ⟨space, valid, found, event, appended, supply, faults, violations⟩

end Grass.Op
