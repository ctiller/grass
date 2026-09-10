import Grass.Op.CallProtocol
import Tests.Memory.CallProtocol
import Tests.Memory.Spike1Policy

/-!
# Checked call-boundary ordering over actual memory history

This fixture runs a concrete plain caller store, a checked handoff, a concrete
provider store, the exact checked return, and a caller reload.  The only ordering
admitted is the synchronization state produced by those successful boundaries;
it makes no native or general happens-before claim.
-/

namespace Grass.Tests.CallProtocolOrdering

open Grass.Core Grass.Memory Grass.Op Grass.Op.CallProtocol Grass.Std.Logical
open Grass.Tests.Spike1 Tests.Memory.Spike1Block Grass.Tests.Spike1Policy
open Grass.Tests.CallProtocol

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The provider reports a nonzero completion count, unlike the caller's
initializing store. -/
private def writeData (_ : MachineState) (descriptor : AccessDescriptor) : ByteSeq :=
  if descriptor = agentWrite then transferredCount
  else if descriptor.intent.writes then List.replicate descriptor.range.size 0
  else []

private def policy : StepPolicy :=
  { Grass.Tests.Spike1Policy.policy with
    oracle := .ofMemory writeData Grass.Tests.Spike1Policy.indeterminateByte }

private def cause (name : String) : EventCause := ⟨⟨name⟩⟩

private def initial : CallProtocol.State Nat :=
  CallProtocol.initial (machine₀.noteContext mainThread .thread) FreshSupply.initial (by decide)

private def callerStore? :=
  CallProtocol.step? initial policy (SomeOperation.of Op.movTransferredZero)
    mainThread .thread (cause "caller-count-store")

private theorem callerStore_succeeds : callerStore?.isSome := by decide

private def afterCallerStore : CallProtocol.State Nat :=
  callerStore?.get callerStore_succeeds

private def handoff? :=
  CallProtocol.handoff? afterCallerStore mainThread apiAgent request loans

private theorem handoff_succeeds : handoff?.isSome := by decide

private def handed : CallId × CallProtocol.State Nat := handoff?.get handoff_succeeds
private def call : CallId := handed.1
private def pending : CallProtocol.State Nat := handed.2
private def record : Pending Nat := (pending.pending.lookup call).get (by decide)

private def providerWrite? :=
  CallProtocol.step? pending policy (SomeOperation.of Op.agentWrite)
    apiAgent .externalAgent (cause "provider-count-write")

private theorem providerWrite_succeeds : providerWrite?.isSome := by decide

private def afterProviderWrite : CallProtocol.State Nat :=
  providerWrite?.get providerWrite_succeeds

private def return? :=
  CallProtocol.return? afterProviderWrite call mainThread apiAgent record.ids

private theorem return_succeeds : return?.isSome := by decide

private def returned : Pending Nat × CallProtocol.State Nat := return?.get return_succeeds
private def afterReturn : CallProtocol.State Nat := returned.2

private def callerLoad? :=
  CallProtocol.step? afterReturn policy (SomeOperation.of Op.movEaxTransferred)
    mainThread .thread (cause "caller-count-load")

private theorem callerLoad_succeeds : callerLoad?.isSome := by decide

private def afterCallerLoad : CallProtocol.State Nat :=
  callerLoad?.get callerLoad_succeeds

/-- These are retained from actual committed outcomes, rather than being
synthetic candidates for the synchronization door. -/
private def callerStoreEvent : MemoryEvent :=
  (afterCallerStore.machine.events.get ⟨0, by decide⟩).event

private def providerEvent : MemoryEvent :=
  (afterProviderWrite.machine.events.get ⟨1, by decide⟩).event

private def callerLoadEvent : MemoryEvent :=
  (afterCallerLoad.machine.events.get ⟨2, by decide⟩).event

/-- The caller is suspended while the exact pending occurrence exists. -/
example : CallProtocol.step? pending policy (SomeOperation.of Op.movEaxTransferred)
    mainThread .thread (cause "caller-before-return") = none := by decide

/-- The actual completed path retains each value-bearing event in order. -/
example : afterCallerLoad.machine.events.map (fun valid =>
    (valid.event.context.id, valid.event.valueRead, valid.event.valueWritten)) =
    [(mainThread, none, some (List.replicate 4 0)),
      (apiAgent, none, some transferredCount),
      (mainThread, some transferredCount, none)] := by decide

example : afterCallerLoad.machine.memory.byteAt? stackAlloc transferredRange.start = some 13 := by
  decide

example : afterCallerLoad.machine.events.length = 3 ∧
    afterCallerLoad.machine.violations.IsEmpty := by decide

/-- A caller's ordinary program-order event supplies no cross-context order
before a checked handoff. -/
example : afterCallerStore.machine.synchronization.ordered
    (afterCallerStore.machine.events.map (·.event))
    afterCallerStore.machine.eventSupply.fresh.1 callerStoreEvent providerEvent = false := by
  decide

/-- The provider result is not visible to a prospective caller event before its
matched return, while the exact same generated event is ordered after return. -/
example : afterProviderWrite.machine.synchronization.ordered
    (afterProviderWrite.machine.events.map (·.event))
    afterProviderWrite.machine.eventSupply.fresh.1 providerEvent callerLoadEvent = false := by
  decide

example : afterReturn.machine.synchronization.ordered
    (afterReturn.machine.events.map (·.event))
    afterReturn.machine.eventSupply.fresh.1 providerEvent callerLoadEvent = true := by
  decide

/-- A synchronization observation cannot reinterpret a stale history or treat a
later actual event as an earlier predecessor. -/
example : afterReturn.machine.synchronization.ordered []
    afterReturn.machine.eventSupply.fresh.1 providerEvent callerLoadEvent = false := by
  decide

example : afterReturn.machine.synchronization.ordered
    (afterReturn.machine.events.map (·.event)).reverse
    afterReturn.machine.eventSupply.fresh.1 providerEvent callerLoadEvent = false := by
  decide

example : afterReturn.machine.synchronization.ordered
    (afterReturn.machine.events.map (·.event))
    afterReturn.machine.eventSupply.fresh.1 callerLoadEvent callerLoadEvent = false := by
  decide

/-- Return accepts only the exact call and complete stored loan tuple. -/
example : CallProtocol.return? afterProviderWrite call mainThread apiAgent
    (record.ids.take 1) = none := by decide

example : CallProtocol.return? afterProviderWrite pending.callSupply.fresh.1
    mainThread apiAgent record.ids = none := by decide

example : CallProtocol.return? afterReturn call mainThread apiAgent record.ids = none := by decide

/-- The low-level synchronization occurrence retains the issued call identity
after return, so a retired identity cannot be installed as a new handoff. -/
example : afterReturn.machine.synchronization.handoff?
    (afterReturn.machine.events.map (·.event)) call mainThread apiAgent record.ids = none := by
  decide

/-- Without a call-boundary cut, the same cross-context plain write remains a
conflicting-access denial. -/
private def providerWithoutHandoff? :=
  CallProtocol.step? afterCallerStore policy (SomeOperation.of Op.agentWrite)
    apiAgent .externalAgent (cause "provider-without-handoff")

private theorem providerWithoutHandoff_runs : providerWithoutHandoff?.isSome := by decide

private def afterProviderWithoutHandoff : CallProtocol.State Nat :=
  providerWithoutHandoff?.get providerWithoutHandoff_runs

example : afterProviderWithoutHandoff.machine.events.length = 1 ∧
    afterProviderWithoutHandoff.machine.violations.records?.map (fun record => record.class_) =
      [AuditViolationClass.conflictingAccess] := by decide

/-- A third external context used only by the negative ordering control. -/
private def thirdAgent : ContextId :=
  (FreshSupply.initial : FreshSupply ContextTag).fresh.2.fresh.2.fresh.1

private def thirdWrite : AccessDescriptor := { agentWrite with context := thirdAgent }

private inductive ThirdOp where | write

private instance : HasOperationFacets ThirdOp where
  facets
    | .write =>
        { memoryEffects := some (.single thirdWrite)
          faults := some [.pageFault, .generalProtection]
          restartability := some .notRestartable
          ordering := some .plain }

/-- Give the caller a real frontier on a disjoint range, then admit a third
plain write. A later handoff orders the caller frontier to the provider, not this
third-context event. -/
private def callerPrefix? :=
  CallProtocol.step? initial policy (SomeOperation.of Op.movWriteFileOverlappedZero)
    mainThread .thread (cause "caller-disjoint-prefix")

private theorem callerPrefix_succeeds : callerPrefix?.isSome := by decide

private def afterCallerPrefix : CallProtocol.State Nat :=
  callerPrefix?.get callerPrefix_succeeds

private def thirdWrite? :=
  CallProtocol.step? afterCallerPrefix policy (SomeOperation.of ThirdOp.write)
    thirdAgent .externalAgent (cause "unrelated-third-write")

private theorem thirdWrite_succeeds : thirdWrite?.isSome := by decide

private def afterThirdWrite : CallProtocol.State Nat :=
  thirdWrite?.get thirdWrite_succeeds

private def thirdHistoryHandoff? :=
  CallProtocol.handoff? afterThirdWrite mainThread apiAgent request loans

private theorem thirdHistoryHandoff_succeeds : thirdHistoryHandoff?.isSome := by decide

private def thirdHistoryHanded : CallId × CallProtocol.State Nat :=
  thirdHistoryHandoff?.get thirdHistoryHandoff_succeeds

private def thirdHistoryProvider? :=
  CallProtocol.step? thirdHistoryHanded.2 policy (SomeOperation.of Op.agentWrite)
    apiAgent .externalAgent (cause "provider-after-unrelated-third")

private theorem thirdHistoryProvider_runs : thirdHistoryProvider?.isSome := by decide

private def afterThirdHistoryProvider : CallProtocol.State Nat :=
  thirdHistoryProvider?.get thirdHistoryProvider_runs

/-- The handoff does not authorize an unrelated third predecessor to race with
the provider: its conflicting event remains unordered and no fourth event commits. -/
example : afterThirdHistoryProvider.machine.events.length = 2 ∧
    afterThirdHistoryProvider.machine.violations.records?.map (fun record => record.class_) =
      [AuditViolationClass.conflictingAccess] := by decide

/-- Return joins the provider's learned predecessor into the caller.  A second
actual handoff from that caller carries the predecessor transitively to a third
agent, which can perform the overlapping write. -/
private def transitiveHandoff? :=
  CallProtocol.handoff? afterReturn mainThread thirdAgent request loans

private theorem transitiveHandoff_succeeds : transitiveHandoff?.isSome := by decide

private def transitiveHanded : CallId × CallProtocol.State Nat :=
  transitiveHandoff?.get transitiveHandoff_succeeds

private def transitiveThirdWrite? :=
  CallProtocol.step? transitiveHanded.2 policy (SomeOperation.of ThirdOp.write)
    thirdAgent .externalAgent (cause "third-after-return")

private theorem transitiveThirdWrite_succeeds : transitiveThirdWrite?.isSome := by decide

private def afterTransitiveThirdWrite : CallProtocol.State Nat :=
  transitiveThirdWrite?.get transitiveThirdWrite_succeeds

private def transitiveThirdEvent : MemoryEvent :=
  (afterTransitiveThirdWrite.machine.events.get ⟨2, by decide⟩).event

example : transitiveHanded.2.machine.synchronization.ordered
    (transitiveHanded.2.machine.events.map (·.event))
    transitiveHanded.2.machine.eventSupply.fresh.1 providerEvent transitiveThirdEvent = true := by
  decide

example : afterTransitiveThirdWrite.machine.events.length = 3 ∧
    afterTransitiveThirdWrite.machine.violations.IsEmpty := by decide

end Grass.Tests.CallProtocolOrdering
