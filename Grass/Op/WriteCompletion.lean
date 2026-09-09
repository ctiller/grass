import Grass.Op.CompletedAccess

/-!
# Write completion facts

These laws connect a complete memory-backed oracle answer to the byte commit made
by the checked prepared-access transition.  They do not turn a caller-supplied
post-state into a write: the post-state must be the actual clean transition.
-/

namespace Grass.Op

open Grass.Core Grass.Memory Grass.Std.Logical

/-- A successful `Oracle.ofMemory` answer records exactly the supplied write
data prefix for a writing descriptor. -/
theorem Oracle.ofMemory_written_of_answerResolved
    (writeData : MachineState → AccessDescriptor → ByteSeq)
    (indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte)
    (state : MachineState) (d : AccessDescriptor)
    (resolved : state.memory.ResolvedAccess d.provenance d.range)
    (complete : CompleteCommitted d)
    (answer : (Oracle.ofMemory writeData indeterminate).answerResolved state d resolved =
      some complete)
    (writes : d.intent.writes = true) :
    complete.committed.written = some ((writeData state d).take d.range.size) := by
  simp only [Oracle.ofMemory] at answer
  split at answer
  · injection answer with same
    subst complete
    simp
  · contradiction

/-- A clean completed write with neutral ledger and authority effects has the
exact memory produced by committing the answer's written bytes through the
prepared resolution. The result is the actual `performPreparedAccess`
transition, not a caller-supplied post-state. -/
theorem clean_prepared_complete_memory_eq_commitResolved
    (policy : StepPolicy) (before after : MachineState) (d : AccessDescriptor)
    (resolved : before.memory.ResolvedAccess d.provenance d.range)
    (prepared : prepareAccess before.memory d = .ok resolved)
    (complete : CompleteCommitted d) (contextKind : ContextKind) (cause : EventCause)
    (space : AddressSpace)
    (found : policy.profile.vocabulary.addressSpaces.find? d.space = some space)
    (wellFormed : d.WellFormedIn space)
    (ran : after = performPreparedAccess policy before d resolved prepared
      (.completed complete) contextKind cause)
    (clean : after.violations.IsEmpty)
    (noLedgerEffect : d.ledgerEffect = [])
    (noAuthorityEffect : d.authorityEffect = []) :
    after.memory = before.memory.commitResolved d resolved complete.committed.written
      complete.committed.writtenFits := by
  obtain ⟨valid, event, _, _, _, _, noRefusal⟩ := clean_prepared_completion_event
    policy before after d resolved prepared complete contextKind cause space found wellFormed ran clean
  subst after
  unfold performPreparedAccess
  simp only [found]
  simp [event]
  rw [noRefusal]
  simp [noLedgerEffect, applyLedgerEffect?,
    AccessOutcome.committed?, MemoryState.commitResolved]
  split
  · rename_i authorityAbsent
    rw [noAuthorityEffect, MemoryState.applyAuthorityEffect?_nil] at authorityAbsent
    contradiction
  · rename_i lent authorityApplied
    have memorySame : lent = before.memory := by
      rw [noAuthorityEffect, MemoryState.applyAuthorityEffect?_nil] at authorityApplied
      exact Option.some.inj authorityApplied.symm
    subst lent
    rfl

/-- `performPreparedAccess_noLedgerEffect_obligations` frames obligations on every prepared branch. -/
theorem performPreparedAccess_noLedgerEffect_obligations
    (policy : StepPolicy) (before : MachineState) (d : AccessDescriptor)
    (resolved : before.memory.ResolvedAccess d.provenance d.range)
    (prepared : prepareAccess before.memory d = .ok resolved)
    (outcome : AccessOutcome d) (contextKind : ContextKind) (cause : EventCause)
    (noLedgerEffect : d.ledgerEffect = []) :
    (performPreparedAccess policy before d resolved prepared outcome contextKind cause).obligations =
      before.obligations := by
  unfold performPreparedAccess
  repeat' split
  all_goals first
    | rfl
    | (rename_i ledger ledgerApplied lent authorityApplied
       rw [noLedgerEffect] at ledgerApplied
       exact Option.some.inj ledgerApplied.symm)

end Grass.Op
