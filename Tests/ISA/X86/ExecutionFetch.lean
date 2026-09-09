import Grass.ISA.X86.Execution.Fetch
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionFetch

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def fetchBacking : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1

private def fetchBytes : ByteStore :=
  (ByteStore.empty.write 0 [0x41, 0x54] true)

private def fetchRecord : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual, source := .virtualAlloc
    owners := [thread₀], permission := .readExecute, live := true, backing := fetchBacking
    origin := 0, base := some 0x1000 }

private def fetchMemory : MemoryState :=
  let backed := (MemoryState.empty.installBacking? fetchBacking ⟨64, fetchBytes⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, fetchRecord)]).getD .empty

private def fetchMachine : MachineState := .initial fetchMemory

private def nonExecutableRecord : AllocationRecord :=
  { fetchRecord with permission := .readWrite }

private def nonExecutableMemory : MemoryState :=
  let backed := (MemoryState.empty.installBacking? fetchBacking ⟨64, fetchBytes⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, nonExecutableRecord)]).getD .empty

private def nonExecutableReached : MachineState :=
  (MachineState.initial nonExecutableMemory).noteContext thread₀ .thread

private def fetchDescriptor : AccessDescriptor :=
  acc bufferProv ⟨0, 2⟩ 0x1000 .execute .readExecute true false

private def wrongAddressDescriptor : AccessDescriptor :=
  { fetchDescriptor with address := .numeric 0x1002 }

private def ledgerEffectDescriptor : AccessDescriptor :=
  { fetchDescriptor with
    ledgerEffect := [.discharge bufferProtocol bufferAuthority releaseObligationId] }

private def authorityEffectDescriptor : AccessDescriptor :=
  { fetchDescriptor with authorityEffect := [.returnGrant bufferLoan] }

private inductive FetchOperation where | fetch

private instance : HasOperationFacets FetchOperation where
  facets
    | .fetch =>
      { memoryEffects := some (.single fetchDescriptor), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }

private def fetchBefore : State :=
  { machine := fetchMachine, gpr := fun _ => 0, rip := 0x1000, rflags := 0 }

private def fetchStep : StepOutcome :=
  step policy fetchMachine (SomeOperation.of FetchOperation.fetch) thread₀ .thread ⟨⟨"fetch"⟩⟩

private def reached : MachineState := fetchMachine.noteContext thread₀ .thread

private def resolved : reached.memory.ResolvedAccess fetchDescriptor.provenance fetchDescriptor.range :=
  (prepareAccess reached.memory fetchDescriptor).toOption.get (by decide)

private theorem resolved_prepared :
    prepareAccess reached.memory fetchDescriptor = .ok resolved := by
  rfl

private theorem resolved_base : resolved.allocation.base = some 0x1000 := by
  rfl

private def complete : CompleteCommitted fetchDescriptor :=
  (policy.oracle.answerResolved reached fetchDescriptor resolved).get (by decide)

private def after : MachineState :=
  match fetchStep with | .ran state => state | .rejected _ => fetchMachine

private def observed : ByteSeq := observedBytes resolved (indeterminateByte reached fetchDescriptor)

private def site : DecodedSite fetchBefore.rip observed :=
  (DecodedSite.check fetchBefore.rip observed).toOption.get (by decide)

private theorem site_noTrailing : site.rest = [] := by
  decide

-- The custom backing is executable, initialized, placed at RIP, and contains
-- exactly the production PUSH r12 bytes.
example : ∃ after, fetchStep = .ran after := by
  refine ⟨_, rfl⟩
example : DecodedSite.check fetchBefore.rip [0x41, 0x54] |>.isOk := by decide
example : (BasicInstructions.push .r12).toBytes = [0x41, 0x54] := by decide

private theorem pushR12_bytes : (BasicInstructions.push .r12).toBytes = [0x41, 0x54] := by
  decide

private theorem pushR12_size : (BasicInstructions.push .r12).size = 2 := by
  decide

example : ∃ (fetch : FetchedSite fetchBefore after),
    fetch.site.encoding = BasicInstructions.push .r12 ∧ fetch.site.rest = [] ∧
    (∃ valid, after.events = fetchBefore.machine.events ++ [valid] ∧
      valid.event.valueRead = some [0x41, 0x54] ∧ valid.event.status = .completed 2 0) ∧
    (∃ base, addressOf base fetch.descriptor.range.start = fetchBefore.rip) := by
  have ran : fetchStep = .ran after := by rfl
  have clean : after.violations.IsEmpty := by decide
  let run : AccessRun fetchMachine after fetchDescriptor :=
    { policy := policy, operation := SomeOperation.of FetchOperation.fetch
      context := thread₀, contextKind := .thread, cause := ⟨⟨"fetch"⟩⟩
      faultAt := fun _ => .none, sequence := .single fetchDescriptor
      selected := by rfl, substeps_exact := by rfl, noFault := by rfl, ran := ran
      resolved := resolved, prepared := by
        change prepareAccess reached.memory fetchDescriptor = .ok resolved
        exact resolved_prepared
      complete := complete, answerResolved := by simp [complete, reached]
      clean := clean }
  let fetch : FetchedSite fetchBefore after :=
    { descriptor := fetchDescriptor, run := run, writeData := storedBytes
      indeterminate := indeterminateByte, memoryOracle := by rfl
      intent := by rfl, initialization := by rfl
      ledgerEffect := by rfl, authorityEffect := by rfl, address := by rfl
      placed := ⟨0x1000, resolved_base⟩, site := site, noTrailing := site_noTrailing }
  obtain ⟨valid, appended, read, status⟩ := FetchedSite.completed_event fetch
  obtain ⟨base, _, _, address⟩ := FetchedSite.placement fetch
  have encoding : fetch.site.encoding = BasicInstructions.push .r12 := rfl
  rw [encoding] at read status
  refine ⟨fetch, rfl, fetch.noTrailing, ⟨valid, appended, ?_, ?_⟩, ⟨base, address⟩⟩
  · simpa [pushR12_bytes] using read
  · simpa [pushR12_size] using status

-- Controls: fetch permission and architectural placement are not decorative.
example : prepareAccess reached.memory wrongAddressDescriptor = .error .addressDisagreesWithPlacement := by
  rfl

example : prepareAccess nonExecutableReached.memory fetchDescriptor = .error .permissionDenied := by
  rfl

example (fetch : FetchedSite fetchBefore after)
    (mutated : fetch.descriptor = ledgerEffectDescriptor) : False := by
  have empty := fetch.ledgerEffect
  rw [mutated] at empty
  exact (by decide : ledgerEffectDescriptor.ledgerEffect ≠ []) empty

example (fetch : FetchedSite fetchBefore after)
    (mutated : fetch.descriptor = authorityEffectDescriptor) : False := by
  have empty := fetch.authorityEffect
  rw [mutated] at empty
  exact (by decide : authorityEffectDescriptor.authorityEffect ≠ []) empty

example :
    ((DecodedSite.check fetchBefore.rip [0x41, 0x54, 0x90]).toOption.get (by decide)).rest = [0x90] := by
  decide

end Grass.Tests.ISA.X86.ExecutionFetch
