import Grass.ISA.X86.Execution.MoveNormal
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionMove

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private inductive Case where | reg64 | reg32 | imm32
deriving DecidableEq, Repr

private def instruction : Case → MoveInstruction
  | .reg64 => .regReg .w64 .rbx .rax
  | .reg32 => .regReg .w32 .r10 .r11
  | .imm32 => .imm32 .r12 0x89ABCDEF

private def bytes (c : Case) : ByteSeq := (instruction c).encoding.toBytes

private def fetchBacking : StorageId :=
  (FreshSupply.initial : FreshSupply StorageTag).fresh.1

private def fetchMemory (c : Case) : MemoryState :=
  let store := ByteStore.empty.write 0 (bytes c) true
  let record : AllocationRecord :=
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
      source := .virtualAlloc, owners := [thread₀], permission := .readExecute
      live := true, backing := fetchBacking, origin := 0, base := some 0x1000 }
  let backed :=
    (MemoryState.empty.installBacking? fetchBacking ⟨64, store⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty

private def fetchMachine (c : Case) : MachineState := .initial (fetchMemory c)

private def descriptor (c : Case) : AccessDescriptor :=
  acc bufferProv ⟨0, (bytes c).length⟩ 0x1000 .execute .readExecute true false

private inductive FetchOperation where | fetch (c : Case)

private instance : HasOperationFacets FetchOperation where
  facets
    | .fetch c =>
      { memoryEffects := some (.single (descriptor c)), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }

private inductive ComputeOperation where | mov

private instance : HasOperationFacets ComputeOperation where
  facets
    | .mov =>
      { memoryEffects := some .none_, faults := some []
        restartability := some .restartable, ordering := some .plain }

private def before (c : Case) : State :=
  { machine := fetchMachine c
    gpr := fun register =>
      if register = .rax then 0xFEDCBA9876543210
      else if register = .r11 then 0xFFFF000012345678
      else 0xAAAAAAAAAAAAAAAA
    rip := 0x1000
    rflags := 0x106D5 }

private def fetchStep (c : Case) : StepOutcome :=
  step policy (fetchMachine c) (SomeOperation.of (FetchOperation.fetch c)) thread₀ .thread
    ⟨⟨"move.fetch"⟩⟩

private def afterFetch (c : Case) : MachineState :=
  match fetchStep c with | .ran state => state | .rejected _ => fetchMachine c

private def reached (c : Case) : MachineState := (fetchMachine c).noteContext thread₀ .thread

private def resolved (c : Case) : (reached c).memory.ResolvedAccess
    (descriptor c).provenance (descriptor c).range :=
  (prepareAccess (reached c).memory (descriptor c)).toOption.get (by cases c <;> decide)

private def complete (c : Case) : CompleteCommitted (descriptor c) :=
  (policy.oracle.answerResolved (reached c) (descriptor c) (resolved c)).get
    (by cases c <;> decide)

private def observed (c : Case) : ByteSeq :=
  observedBytes (resolved c) (indeterminateByte (reached c) (descriptor c))

private def site (c : Case) : DecodedSite (before c).rip (observed c) :=
  (DecodedSite.check (before c).rip (observed c)).toOption.get (by cases c <;> decide)

private def fetch (c : Case) : FetchedSite (before c) (afterFetch c) := by
  let run : AccessRun (fetchMachine c) (afterFetch c) (descriptor c) :=
    { policy := policy
      operation := SomeOperation.of (FetchOperation.fetch c)
      context := thread₀
      contextKind := .thread
      cause := ⟨⟨"move.fetch"⟩⟩
      faultAt := fun _ => .none
      sequence := .single (descriptor c)
      selected := by rfl
      substeps_exact := by rfl
      noFault := by rfl
      ran := by cases c <;> rfl
      resolved := resolved c
      prepared := by cases c <;> rfl
      complete := complete c
      answerResolved := by cases c <;> simp [complete, reached]
      clean := by cases c <;> decide }
  exact
    { descriptor := descriptor c
      run := run
      writeData := storedBytes
      indeterminate := indeterminateByte
      memoryOracle := by rfl
      intent := by rfl
      initialization := by rfl
      ledgerEffect := by rfl
      authorityEffect := by rfl
      address := by rfl
      placed := ⟨0x1000, by cases c <;> decide⟩
      site := site c
      noTrailing := by cases c <;> decide }

private def computeOperation : SomeOperation := SomeOperation.of ComputeOperation.mov
private def computeSequence : SubstepSequence := .none_
private def computeFaultAt : (sequence : SubstepSequence) → FaultPlan sequence := fun _ => .none

private def computeStep (c : Case) : StepOutcome :=
  step policy (afterFetch c) computeOperation (fetch c).run.context (fetch c).run.contextKind
    (fetch c).run.cause computeFaultAt

private def afterCompute (c : Case) : MachineState :=
  match computeStep c with | .ran state => state | .rejected _ => afterFetch c

private def accessFree (c : Case) : AccessFree (before c) (afterFetch c) (afterCompute c) :=
  { fetch := fetch c
    operation := computeOperation
    sequence := computeSequence
    selected := by rfl
    noDataSubsteps := by rfl
    faultAt := computeFaultAt
    noFault := by rfl
    ran := by cases c <;> rfl }

private def receipt (c : Case) :
    MoveNormal (before c) (afterFetch c) (afterCompute c) (instruction c) :=
  { execution := accessFree c
    encoding := by cases c <;> decide }

-- Each admitted form is tied to bytes observed by a real execute access.
example : (fetch .reg64).site.encoding.toBytes = [0x48, 0x89, 0xC3] := by decide
example : (fetch .reg32).site.encoding.toBytes = [0x45, 0x89, 0xDA] := by decide
example : (fetch .imm32).site.encoding.toBytes = [0x41, 0xBC, 0xEF, 0xCD, 0xAB, 0x89] := by decide

example : (receipt .reg64).result.gpr .rbx = 0xFEDCBA9876543210 := by decide
example : (receipt .reg32).result.gpr .r10 = 0x12345678 := by decide
example : (receipt .imm32).result.gpr .r12 = 0x89ABCDEF := by decide

example : BitVec.extractLsb' 32 32 ((receipt .reg32).result.gpr .r10) = 0 :=
  (receipt .reg32).regReg_w32_high_clear
example : BitVec.extractLsb' 32 32 ((receipt .imm32).result.gpr .r12) = 0 :=
  (receipt .imm32).imm32_high_clear

example : (receipt .reg64).result.gpr .r12 = (before .reg64).gpr .r12 :=
  (receipt .reg64).gpr_frame .r12 (by decide)
example : (receipt .reg64).result.rflags = 0x6D5 := by decide

-- A distinct destination cannot be attached to the same fetched encoding.
example (mutated : MoveNormal (before .reg64) (afterFetch .reg64) (afterCompute .reg64)
    (.regReg .w64 .r12 .rax))
    (sameFetch : mutated.execution.fetch.site.encoding = (fetch .reg64).site.encoding) : False := by
  have wrong : (fetch .reg64).site.encoding ≠
      (MoveInstruction.regReg .w64 .r12 .rax).encoding := by decide
  exact wrong (sameFetch.symm.trans mutated.encoding)

-- A wrong immediate encoding likewise cannot reuse the actual fetched receipt.
example (mutated : MoveNormal (before .imm32) (afterFetch .imm32) (afterCompute .imm32)
    (.imm32 .r12 0x89ABCDEE))
    (sameFetch : mutated.execution.fetch.site.encoding = (fetch .imm32).site.encoding) : False := by
  have wrong : (fetch .imm32).site.encoding ≠
      (MoveInstruction.imm32 .r12 0x89ABCDEE).encoding := by decide
  exact wrong (sameFetch.symm.trans mutated.encoding)

end Grass.Tests.ISA.X86.ExecutionMove
