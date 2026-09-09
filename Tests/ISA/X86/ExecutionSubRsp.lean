import Grass.ISA.X86.Execution.SubRspNormal
import Grass.Assembly.FrameAllocationExecution
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionSubRsp

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def fetchBacking : StorageId :=
  (FreshSupply.initial : FreshSupply StorageTag).fresh.1

private def fetchBytes : ByteStore :=
  ByteStore.empty.write 0 [0x48, 0x83, 0xEC, 0x30] true

private def fetchRecord : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
    source := .virtualAlloc, owners := [thread₀], permission := .readExecute
    live := true, backing := fetchBacking, origin := 0, base := some 0x1000 }

private def fetchMemory : MemoryState :=
  let backed :=
    (MemoryState.empty.installBacking? fetchBacking ⟨64, fetchBytes⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, fetchRecord)]).getD .empty

private def fetchMachine : MachineState := .initial fetchMemory

private def fetchDescriptor : AccessDescriptor :=
  acc bufferProv ⟨0, 4⟩ 0x1000 .execute .readExecute true false

private inductive FetchOperation where | fetch

private instance : HasOperationFacets FetchOperation where
  facets
    | .fetch =>
      { memoryEffects := some (.single fetchDescriptor), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }

private inductive ComputeOperation where | subRsp

private instance : HasOperationFacets ComputeOperation where
  facets
    | .subRsp =>
      { memoryEffects := some .none_, faults := some []
        restartability := some .restartable, ordering := some .plain }

private def before : State :=
  { machine := fetchMachine
    gpr := fun register => if register = .rsp then 0x3040 else 0xCAFE
    rip := 0x1000
    rflags := 0x10602 }

private def fetchStep : StepOutcome :=
  step policy fetchMachine (SomeOperation.of FetchOperation.fetch) thread₀ .thread
    ⟨⟨"sub-rsp.fetch"⟩⟩

private def afterFetch : MachineState :=
  match fetchStep with | .ran state => state | .rejected _ => fetchMachine

private def reached : MachineState := fetchMachine.noteContext thread₀ .thread

private def resolved : reached.memory.ResolvedAccess
    fetchDescriptor.provenance fetchDescriptor.range :=
  (prepareAccess reached.memory fetchDescriptor).toOption.get (by decide)

private def complete : CompleteCommitted fetchDescriptor :=
  (policy.oracle.answerResolved reached fetchDescriptor resolved).get (by decide)

private def observed : ByteSeq :=
  observedBytes resolved (indeterminateByte reached fetchDescriptor)

private def site : DecodedSite before.rip observed :=
  (DecodedSite.check before.rip observed).toOption.get (by decide)

private def fetch : FetchedSite before afterFetch := by
  let run : AccessRun fetchMachine afterFetch fetchDescriptor :=
    { policy := policy
      operation := SomeOperation.of FetchOperation.fetch
      context := thread₀
      contextKind := .thread
      cause := ⟨⟨"sub-rsp.fetch"⟩⟩
      faultAt := fun _ => .none
      sequence := .single fetchDescriptor
      selected := by rfl
      substeps_exact := by rfl
      noFault := by rfl
      ran := by rfl
      resolved := resolved
      prepared := by rfl
      complete := complete
      answerResolved := by simp [complete, reached]
      clean := by decide }
  exact
    { descriptor := fetchDescriptor
      run := run
      writeData := storedBytes
      indeterminate := indeterminateByte
      memoryOracle := by rfl
      intent := by rfl
      initialization := by rfl
      ledgerEffect := by rfl
      authorityEffect := by rfl
      address := by rfl
      placed := ⟨0x1000, by rfl⟩
      site := site
      noTrailing := by decide }

private def computeOperation : SomeOperation := SomeOperation.of ComputeOperation.subRsp
private def computeSequence : SubstepSequence := .none_
private def computeFaultAt : (sequence : SubstepSequence) → FaultPlan sequence := fun _ => .none

private def computeStep : StepOutcome :=
  step policy afterFetch computeOperation fetch.run.context fetch.run.contextKind
    fetch.run.cause computeFaultAt

private def afterCompute : MachineState :=
  match computeStep with | .ran state => state | .rejected _ => afterFetch

private def immediate : ImmediateArithmetic.Immediate := .i8 0x30

private def receipt : SubRspNormal before afterFetch afterCompute immediate :=
  { fetch := fetch
    encoding := by decide
    operation := computeOperation
    sequence := computeSequence
    selected := by rfl
    noDataSubsteps := by rfl
    faultAt := computeFaultAt
    noFault := by rfl
    ran := by rfl }

example : fetch.site.encoding = (StackInstruction.subRsp immediate).encoding := by decide
example : fetch.site.encoding.toBytes = [0x48, 0x83, 0xEC, 0x30] := by decide

example : receipt.result.gpr .rsp = 0x3010 := by decide
example : receipt.result.rip = 0x1004 := by decide
example : receipt.result.rflags = 0x602 := by decide

example : receipt.result.gpr .r12 = before.gpr .r12 :=
  receipt.gpr_frame .r12 (by decide)

private def layout : Grass.ABI.Win64.CallFrameLayout :=
  ⟨5, 4, 4, [.r12, .r13, .r14]⟩

private def allocation : Grass.Assembly.FrameAllocation.Resolved :=
  (Grass.Assembly.FrameAllocation.resolve? layout).get (by decide)

private def layoutReceipt : SubRspNormal before afterFetch afterCompute allocation.immediate :=
  receipt

example : fetch.site.encoding = allocation.encoding :=
  Grass.Assembly.FrameAllocation.allocation_encoding_of_observation allocation fetch (by decide)

-- The actual fetched fixture accepts the operand derived from frame parameters.
example : layoutReceipt.result.gpr .rsp = before.gpr .rsp -
    BitVec.ofNat 64 allocation.layout.callAllocationBytes :=
  Grass.Assembly.FrameAllocation.rsp_allocation_exact allocation layoutReceipt

example : (layoutReceipt.result.gpr .rsp).toNat =
    (before.gpr .rsp).toNat - allocation.layout.callAllocationBytes :=
  Grass.Assembly.FrameAllocation.rsp_allocation_natural allocation layoutReceipt (by decide)

/-- An immediate different from the fetched byte cannot satisfy the constructor's
encoding equality. -/
example (mutated : SubRspNormal before afterFetch afterCompute (.i8 0x20))
    (sameFetch : mutated.fetch.site.encoding = fetch.site.encoding) : False := by
  have rejected : fetch.site.encoding ≠ (StackInstruction.subRsp (.i8 0x20)).encoding := by
    decide
  exact rejected (sameFetch.symm.trans mutated.encoding)

end Grass.Tests.ISA.X86.ExecutionSubRsp
