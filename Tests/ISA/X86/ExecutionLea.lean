import Grass.ISA.X86.Execution.LeaNormal
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionLea

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private inductive Case where | payload | frame
deriving DecidableEq, Repr

private def instruction : Case → LeaInstruction
  | .payload => ⟨.ripRelative, .r13, 0x3AB⟩
  | .frame => ⟨.rsp, .r9, 40⟩

private def bytes (c : Case) : ByteSeq :=
  ((instruction c).encoding?.get (by cases c <;> decide)).toBytes

private def instructionRip : Case → Nat
  | .payload => 1054
  | .frame => 1108

private def fetchBacking : StorageId :=
  (FreshSupply.initial : FreshSupply StorageTag).fresh.1

private def fetchMemory (c : Case) : MemoryState :=
  let store := ByteStore.empty.write 0 (bytes c) true
  let record : AllocationRecord :=
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
      source := .virtualAlloc, owners := [thread₀], permission := .readExecute
      live := true, backing := fetchBacking, origin := 0, base := some (instructionRip c) }
  let backed :=
    (MemoryState.empty.installBacking? fetchBacking ⟨64, store⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty

private def fetchMachine (c : Case) : MachineState := .initial (fetchMemory c)

private def descriptor (c : Case) : AccessDescriptor :=
  acc bufferProv ⟨0, (bytes c).length⟩ (instructionRip c) .execute .readExecute true false

private inductive FetchOperation where | fetch (c : Case)
private instance : HasOperationFacets FetchOperation where
  facets
    | .fetch c =>
      { memoryEffects := some (.single (descriptor c)), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }

private inductive ComputeOperation where | lea
private instance : HasOperationFacets ComputeOperation where
  facets
    | .lea =>
      { memoryEffects := some .none_, faults := some []
        restartability := some .restartable, ordering := some .plain }

private def before (c : Case) : State :=
  { machine := fetchMachine c
    gpr := fun register => if register = .rsp then 0x3000 else 0xCAFE
    rip := BitVec.ofNat 64 (instructionRip c)
    rflags := 0x106D5 }

private def fetchStep (c : Case) :=
  step policy (fetchMachine c) (SomeOperation.of (FetchOperation.fetch c)) thread₀ .thread
    ⟨⟨"lea.fetch"⟩⟩
private def afterFetch (c : Case) :=
  match fetchStep c with | .ran state => state | .rejected _ => fetchMachine c
private def reached (c : Case) := (fetchMachine c).noteContext thread₀ .thread
private def resolved (c : Case) : (reached c).memory.ResolvedAccess
    (descriptor c).provenance (descriptor c).range :=
  (prepareAccess (reached c).memory (descriptor c)).toOption.get (by cases c <;> decide)
private def complete (c : Case) : CompleteCommitted (descriptor c) :=
  (policy.oracle.answerResolved (reached c) (descriptor c) (resolved c)).get
    (by cases c <;> decide)
private def observed (c : Case) :=
  observedBytes (resolved c) (indeterminateByte (reached c) (descriptor c))
private def site (c : Case) : DecodedSite (before c).rip (observed c) :=
  (DecodedSite.check (before c).rip (observed c)).toOption.get (by cases c <;> decide)

private def fetch (c : Case) : FetchedSite (before c) (afterFetch c) := by
  let run : AccessRun (fetchMachine c) (afterFetch c) (descriptor c) :=
    { policy := policy, operation := SomeOperation.of (FetchOperation.fetch c)
      context := thread₀, contextKind := .thread, cause := ⟨⟨"lea.fetch"⟩⟩
      faultAt := fun _ => .none, sequence := .single (descriptor c)
      selected := by rfl, substeps_exact := by rfl, noFault := by rfl
      ran := by cases c <;> rfl, resolved := resolved c
      prepared := by cases c <;> rfl, complete := complete c
      answerResolved := by cases c <;> simp [complete, reached]
      clean := by cases c <;> decide }
  exact
    { descriptor := descriptor c, run := run, writeData := storedBytes
      indeterminate := indeterminateByte, memoryOracle := by rfl
      intent := by rfl, initialization := by rfl, ledgerEffect := by rfl
      authorityEffect := by rfl, address := by cases c <;> rfl
      placed := ⟨BitVec.ofNat 64 (instructionRip c), by cases c <;> decide⟩
      site := site c, noTrailing := by cases c <;> decide }

private def computeOperation : SomeOperation := SomeOperation.of ComputeOperation.lea
private def computeSequence : SubstepSequence := .none_
private def computeFaultAt : (sequence : SubstepSequence) → FaultPlan sequence := fun _ => .none
private def computeStep (c : Case) :=
  step policy (afterFetch c) computeOperation (fetch c).run.context (fetch c).run.contextKind
    (fetch c).run.cause computeFaultAt
private def afterCompute (c : Case) :=
  match computeStep c with | .ran state => state | .rejected _ => afterFetch c
private def execution (c : Case) : AccessFree (before c) (afterFetch c) (afterCompute c) :=
  { fetch := fetch c, operation := computeOperation, sequence := computeSequence
    selected := by rfl, noDataSubsteps := by rfl, faultAt := computeFaultAt
    noFault := by rfl, ran := by cases c <;> rfl }
private def receipt (c : Case) :
    LeaNormal (before c) (afterFetch c) (afterCompute c) (instruction c) :=
  { execution := execution c, encoding := by cases c <;> decide }

example : (fetch .payload).site.encoding.toBytes = [0x4C, 0x8D, 0x2D, 0xAB, 0x03, 0, 0] := by decide
example : (fetch .frame).site.encoding.toBytes = [0x4C, 0x8D, 0x8C, 0x24, 0x28, 0, 0, 0] := by decide
example : LeaInstruction.select (fetch .payload).site.encoding = some (instruction .payload) := by decide
example : LeaInstruction.select (fetch .frame).site.encoding = some (instruction .frame) := by decide
example : LeaInstruction.select (movRegImm32 .r9 40) = none := by decide

example : (instruction .payload).encoding? = some (fetch .payload).site.encoding :=
  LeaInstruction.select_sound (by decide)
example : (instruction .frame).encoding? = some (fetch .frame).site.encoding :=
  LeaInstruction.select_sound (by decide)
example : (receipt .payload).result.gpr .r13 = 2000 := by decide
example : (receipt .frame).result.gpr .r9 = 0x3028 := by decide
example : (receipt .payload).result.rip = 1061 := by decide
example : (receipt .frame).result.rip = 1116 := by decide
example : (receipt .payload).result.rflags = 0x6D5 := by decide
example : (receipt .frame).result.gpr .rsp = (before .frame).gpr .rsp :=
  (receipt .frame).gpr_frame .rsp (by decide)
example : (receipt .payload).result.machine.memory = (before .payload).machine.memory :=
  (receipt .payload).state_frame.1

example (mutated : LeaNormal (before .payload) (afterFetch .payload) (afterCompute .payload)
    ⟨.ripRelative, .r12, 0x3AB⟩)
    (sameFetch : mutated.execution.fetch.site.encoding = (fetch .payload).site.encoding) : False := by
  have wrong : (LeaInstruction.mk .ripRelative .r12 0x3AB).encoding? ≠
      (instruction .payload).encoding? := by decide
  have actual : (instruction .payload).encoding? =
      some (fetch .payload).site.encoding := by decide
  exact wrong (mutated.encoding.trans (congrArg some sameFetch) |>.trans actual.symm)

example (mutated : LeaNormal (before .frame) (afterFetch .frame) (afterCompute .frame)
    ⟨.ripRelative, .r9, 40⟩)
    (sameFetch : mutated.execution.fetch.site.encoding = (fetch .frame).site.encoding) : False := by
  have wrong : (LeaInstruction.mk .ripRelative .r9 40).encoding? ≠
      (instruction .frame).encoding? := by decide
  have actual : (instruction .frame).encoding? =
      some (fetch .frame).site.encoding := by decide
  exact wrong (mutated.encoding.trans (congrArg some sameFetch) |>.trans actual.symm)

end Grass.Tests.ISA.X86.ExecutionLea
