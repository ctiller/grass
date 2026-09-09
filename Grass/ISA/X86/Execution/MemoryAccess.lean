import Grass.ISA.X86.Execution.Fetch

/-! Continuous fetched data accesses used by the source-frame adapters.
`MemoryAccess` supplies conditional clean normal branches, not an exhaustive instruction
semantics or a claim that faults and rejected accesses cannot occur. -/

namespace Grass.ISA.X86.Execution
open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Std.Logical

/-- The actual data step starts at the actual fetch result, with the same
policy and execution context. Source-specific adapters supply operand facts. -/
structure MemoryAccess {before : State} {afterFetch : MachineState}
    (fetch : FetchedSite before afterFetch) (after : MachineState) where
  descriptor : AccessDescriptor
  run : AccessRun afterFetch after descriptor
  policy : run.policy = fetch.run.policy
  context : run.context = fetch.run.context
  contextKind : run.contextKind = fetch.run.contextKind
  cause : run.cause = fetch.run.cause
  fetchContext : fetch.descriptor.context = fetch.run.context
  dataContext : descriptor.context = run.context
  space : descriptor.space = .cpuVirtual
  ordering : descriptor.ordering = .plain
  ledgerEffect : descriptor.ledgerEffect = []
  authorityEffect : descriptor.authorityEffect = []

namespace MemoryAccess

/-- `memoryOracle` transports the fetch policy to the continuous data run. -/
theorem memoryOracle {before : State} {afterFetch after : MachineState}
    {fetch : FetchedSite before afterFetch} (access : MemoryAccess fetch after) :
    access.run.policy.oracle = Oracle.ofMemory fetch.writeData fetch.indeterminate := by
  rw [access.policy, fetch.memoryOracle]

/-- `address_of_rsp` derives operand/address agreement from the actual prepared
allocation placement. Typed source adapters supply the displacement and its
signed-width proof; preparation supplies the nonwrapping placement check. -/
theorem address_of_rsp {before : State} {afterFetch after : MachineState}
    {fetch : FetchedSite before afterFetch} (access : MemoryAccess fetch after)
    (base : MachineAddress) (rootOffset displacement : Nat)
    (placed : access.run.resolved.allocation.base = some base)
    (rsp : before.gpr .rsp = addressOf base rootOffset)
    (range : access.descriptor.range.start = rootOffset + displacement)
    (signed : BitVec.signExtend 64 (BitVec.ofNat 32 displacement) =
      BitVec.ofNat 64 displacement) :
    access.descriptor.address = .numeric
      (before.gpr .rsp + BitVec.signExtend 64 (BitVec.ofNat 32 displacement)) := by
  obtain ⟨_, address⟩ := prepared_base_fits_and_address access.run.prepared placed
  rw [address, rsp, range, signed]
  congr 1
  simp only [addressOf, BitVec.ofNat_add]
  exact (BitVec.add_assoc _ _ _).symm

/-- `read_state_frame` derives memory and obligation preservation for the
continuous read-only data step, including the preceding instruction fetch. -/
theorem read_state_frame {before : State} {afterFetch after : MachineState}
    {fetch : FetchedSite before afterFetch} (access : MemoryAccess fetch after)
    (readOnly : access.descriptor.intent.writes = false) :
    after.memory = before.machine.memory ∧ after.obligations = before.machine.obligations := by
  have actual := ran_singleton_prepared_eq_performPreparedAccess access.run.policy afterFetch
    access.run.operation access.run.context access.run.contextKind access.run.cause access.run.faultAt
    access.run.sequence access.descriptor after access.run.selected access.run.accesses_exact
    access.run.noFault access.run.ran access.run.resolved access.run.prepared access.run.complete
    access.run.answerResolved
  have frame := performPreparedAccess_readOnly_noEffects_frame access.run.policy
    (afterFetch.noteContext access.run.context access.run.contextKind) access.descriptor
    access.run.resolved access.run.prepared (.completed access.run.complete) access.run.contextKind
    access.run.cause readOnly access.ledgerEffect access.authorityEffect
  rw [actual]
  exact ⟨frame.1.trans fetch.state_frame.1, frame.2.trans fetch.state_frame.2⟩

/-- `events_exact` derives both appended events from their actual step results. -/
theorem events_exact {before : State} {afterFetch after : MachineState}
    {fetch : FetchedSite before afterFetch} (access : MemoryAccess fetch after) :
    ∃ fetched data, after.events = before.machine.events ++ [fetched, data] ∧
      fetched.event.valueRead = some fetch.site.encoding.toBytes ∧
      data.event.valueRead = access.run.complete.committed.observed ∧
      data.event.valueWritten = access.run.complete.committed.written := by
  obtain ⟨fetched, fetchEvents, bytes, _⟩ := fetch.completed_event
  obtain ⟨_, data, _, event, dataEvents, _, _, _⟩ := access.run.completed_event
  have fields := completedEvent_fields event
  refine ⟨fetched, data, ?_, bytes, ?_, ?_⟩
  · rw [dataEvents, fetchEvents, List.append_assoc]; rfl
  · exact fields.2.2.2.2.2.2.2.1
  · exact fields.2.2.2.2.2.2.2.2

end MemoryAccess
end Grass.ISA.X86.Execution
