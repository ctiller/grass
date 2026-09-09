import Grass.ISA.X86.Execution.BranchNormal
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionBranch

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private inductive Case where | jump | equalTaken | equalNotTaken | aboveTaken
deriving DecidableEq, Repr
private def instruction : Case → BranchInstruction
  | .jump => .jump 0x20 | .equalTaken | .equalNotTaken => .equal 0xFFFFFFF0
  | .aboveTaken => .above 0x30
private def flags : Case → BitVec 64
  | .equalTaken => 0x10040 | .equalNotTaken => 0x10001 | _ => 0x10000
private def code (c : Case) := (instruction c).encoding.toBytes
private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def memory (c : Case) : MemoryState :=
  let store := ByteStore.empty.write 0 (code c) true
  let record : AllocationRecord :=
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
      source := .virtualAlloc, owners := [thread₀], permission := .readExecute
      live := true, backing := backing, origin := 0, base := some 0x1000 }
  let backed := (MemoryState.empty.installBacking? backing ⟨64, store⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty
private def machine (c : Case) := MachineState.initial (memory c)
private def descriptor (c : Case) :=
  acc bufferProv ⟨0, (code c).length⟩ 0x1000 .execute .readExecute true false
private inductive FetchOp where | fetch (c : Case)
private instance : HasOperationFacets FetchOp where
  facets
    | .fetch c =>
      { memoryEffects := some (.single (descriptor c)), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }
private inductive ComputeOp where | branch
private instance : HasOperationFacets ComputeOp where
  facets
    | .branch =>
      { memoryEffects := some .none_, faults := some []
        restartability := some .restartable, ordering := some .plain }
private def before (c : Case) : State :=
  { machine := machine c
    gpr := fun _ => 0xCAFE
    rip := 0x1000
    rflags := flags c }
private def fetchOutcome (c : Case) := step policy (machine c)
  (SomeOperation.of (FetchOp.fetch c)) thread₀ .thread ⟨⟨"branch.fetch"⟩⟩
private def afterFetch (c : Case) := match fetchOutcome c with | .ran s => s | _ => machine c
private def reached (c : Case) := (machine c).noteContext thread₀ .thread
private def resolved (c : Case) : (reached c).memory.ResolvedAccess
    (descriptor c).provenance (descriptor c).range :=
  (prepareAccess (reached c).memory (descriptor c)).toOption.get (by cases c <;> decide)
private def complete (c : Case) : CompleteCommitted (descriptor c) :=
  (policy.oracle.answerResolved (reached c) (descriptor c) (resolved c)).get
    (by cases c <;> decide)
private def observed (c : Case) := observedBytes (resolved c) (indeterminateByte (reached c) (descriptor c))
private def site (c : Case) : DecodedSite (before c).rip (observed c) :=
  (DecodedSite.check (before c).rip (observed c)).toOption.get (by cases c <;> decide)
private def fetch (c : Case) : FetchedSite (before c) (afterFetch c) := by
  let run : AccessRun (machine c) (afterFetch c) (descriptor c) :=
    { policy := policy
      operation := SomeOperation.of (FetchOp.fetch c)
      context := thread₀
      contextKind := .thread
      cause := ⟨⟨"branch.fetch"⟩⟩
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
private def operation := SomeOperation.of ComputeOp.branch
private def faultAt : (s : SubstepSequence) → FaultPlan s := fun _ => .none
private def computeOutcome (c : Case) := step policy (afterFetch c) operation thread₀ .thread
  ⟨⟨"branch.fetch"⟩⟩ faultAt
private def afterCompute (c : Case) := match computeOutcome c with | .ran s => s | _ => afterFetch c
private def execution (c : Case) : AccessFree (before c) (afterFetch c) (afterCompute c) :=
  { fetch := fetch c
    operation := operation
    sequence := .none_
    selected := by rfl
    noDataSubsteps := by rfl
    faultAt := faultAt
    noFault := by rfl
    ran := by cases c <;> rfl }
private def receipt (c : Case) : BranchNormal (before c) (afterFetch c) (afterCompute c)
    (instruction c) :=
  { execution := execution c
    encoding := by cases c <;> decide
    targetFits := by cases c <;> decide }

example : (receipt .jump).result.rip = 0x1025 := by decide
example : (receipt .equalTaken).result.rip = 0x0FF6 := by decide
example : (receipt .equalNotTaken).result.rip = 0x1006 := by decide
example : (receipt .aboveTaken).result.rip = 0x1036 := by decide
example (c : Case) : (fetch c).site.encoding = (instruction c).encoding := by cases c <;> decide
example (c : Case) : (BranchInstruction.select (instruction c).encoding).isSome = true := by
  cases c <;> decide
example : (receipt .jump).result.gpr = (before .jump).gpr := (receipt .jump).gpr_frame
example : (receipt .jump).result.rflags = 0 := by decide

end Grass.Tests.ISA.X86.ExecutionBranch
