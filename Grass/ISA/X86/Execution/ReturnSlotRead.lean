import Grass.ISA.X86.Execution.CallNormal
import Grass.ISA.X86.Execution.ReadValue64

/-!
# Current-state read of a CALL return slot

`ReturnSlotRead` uses the current machine state, which may follow provider
activity. Exact slot identity and target equality are retained as checked read
facts. `restoredRsp` is an arithmetic equation; this module supplies no CPU
return transition or provider-continuity proof.
-/

namespace Grass.ISA.X86.Execution

open Grass.Core Grass.Memory Grass.Op

/-- Actual initialized read of the return slot previously written by CALL. -/
structure ReturnSlotRead {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32} (call : CallNormal callBefore afterFetch afterTarget afterCall displacement)
    (beforeReturn : State) (afterRead : MachineState) where
  descriptor : AccessDescriptor
  run : AccessRun beforeReturn.machine afterRead descriptor
  read : ReadValue64 run
  slotProvenance : descriptor.provenance = call.storeDescriptor.provenance
  slotRange : descriptor.range = call.storeDescriptor.range
  slotAddress : descriptor.address = call.storeDescriptor.address
  context : run.context = call.storeRun.context
  contextKind : run.contextKind = call.storeRun.contextKind
  descriptorContext : descriptor.context = run.context
  intent : descriptor.intent = .read
  space : descriptor.space = .cpuVirtual
  ordering : descriptor.ordering = .plain
  ledgerEffect : descriptor.ledgerEffect = []
  authorityEffect : descriptor.authorityEffect = []
  address : descriptor.address = .numeric (beforeReturn.gpr .rsp)
  placed : ∃ base, run.resolved.allocation.base = some base
  targetMatches : read.value = call.fetch.site.fallthroughRip

namespace ReturnSlotRead

theorem target_exact {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    {beforeReturn : State} {afterRead : MachineState}
    (receipt : ReturnSlotRead call beforeReturn afterRead) :
    receipt.read.value = call.fetch.site.fallthroughRip := receipt.targetMatches

theorem restoredRsp {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    {beforeReturn : State} {afterRead : MachineState}
    (receipt : ReturnSlotRead call beforeReturn afterRead) :
    beforeReturn.gpr .rsp + 8 = callBefore.gpr .rsp := by
  have sameAddress : beforeReturn.gpr .rsp = callBefore.gpr .rsp - 8 := by
    apply Address.numeric.inj
    exact receipt.address.symm.trans (receipt.slotAddress.trans call.storeAddress)
  rw [sameAddress]
  exact BitVec.sub_add_cancel _ _

theorem state_frame {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    {beforeReturn : State} {afterRead : MachineState}
    (receipt : ReturnSlotRead call beforeReturn afterRead) :
    afterRead.memory = beforeReturn.machine.memory ∧
      afterRead.obligations = beforeReturn.machine.obligations := by
  rw [receipt.run.prepared_result]
  exact performPreparedAccess_readOnly_noEffects_frame receipt.run.policy
    (beforeReturn.machine.noteContext receipt.run.context receipt.run.contextKind)
    receipt.descriptor receipt.run.resolved receipt.run.prepared (.completed receipt.run.complete)
    receipt.run.contextKind receipt.run.cause receipt.read.writes receipt.ledgerEffect
    receipt.authorityEffect

theorem event {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    {beforeReturn : State} {afterRead : MachineState}
    (receipt : ReturnSlotRead call beforeReturn afterRead) :
    ∃ valid, afterRead.events = beforeReturn.machine.events ++ [valid] ∧
      valid.event.valueRead = some receipt.read.observed := by
  obtain ⟨_, valid, _, event, appended, _, _, _⟩ := receipt.run.completed_event
  have fields := completedEvent_fields event
  exact ⟨valid, appended, fields.2.2.2.2.2.2.2.1.trans receipt.read.observed_exact⟩

end ReturnSlotRead
end Grass.ISA.X86.Execution
