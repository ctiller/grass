import Grass.ISA.X86.Execution.ArithmeticNormal
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionArithmetic

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private inductive Case where
  | add32 | add64 | sub32 | sub64 | cmp32 | cmp64
  | test32 | test64 | xor32 | xor64 | cmpImmediate
deriving DecidableEq, Repr

private def instruction : Case → ArithmeticInstruction
  | .add32 => .add .w32 .r10 .r11 | .add64 => .add .w64 .r10 .r11
  | .sub32 => .sub .w32 .r10 .r11 | .sub64 => .sub .w64 .r10 .r11
  | .cmp32 => .cmp .w32 .r10 .r11 | .cmp64 => .cmp .w64 .r10 .r11
  | .test32 => .test .w32 .r10 .r11 | .test64 => .test .w64 .r10 .r11
  | .xor32 => .xor .w32 .r10 .r11 | .xor64 => .xor .w64 .r10 .r11
  | .cmpImmediate => .cmpImmediate .w64 .rax (.i32 0xFFFFFFFF)

private def code (c : Case) : ByteSeq := (instruction c).encoding.toBytes
private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def memory (c : Case) : MemoryState :=
  let store := ByteStore.empty.write 0 (code c) true
  let record : AllocationRecord :=
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual, source := .virtualAlloc
      owners := [thread₀], permission := .readExecute, live := true, backing := backing
      origin := 0, base := some 0x1000 }
  let backed := (MemoryState.empty.installBacking? backing ⟨64, store⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty
private def machine (c : Case) : MachineState := .initial (memory c)
private def descriptor (c : Case) : AccessDescriptor :=
  acc bufferProv ⟨0, (code c).length⟩ 0x1000 .execute .readExecute true false

private inductive FetchOp where | fetch (c : Case)
private instance : HasOperationFacets FetchOp where
  facets
    | .fetch c =>
      { memoryEffects := some (.single (descriptor c)), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }
private inductive ComputeOp where | arithmetic
private instance : HasOperationFacets ComputeOp where
  facets
    | .arithmetic =>
      { memoryEffects := some .none_, faults := some []
        restartability := some .restartable, ordering := some .plain }

private def before (c : Case) : State :=
  { machine := machine c
    gpr := fun r => if r = .r10 then 0xFFFF000000000010
      else if r = .r11 then 3 else if r = .rax then 0xFFFFFFFFFFFFFFFF else 0xCAFE
    rip := 0x1000
    rflags := 0x10602 }
private def fetchOutcome (c : Case) :=
  step policy (machine c) (SomeOperation.of (FetchOp.fetch c)) thread₀ .thread
    ⟨⟨"arithmetic.fetch"⟩⟩
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
      cause := ⟨⟨"arithmetic.fetch"⟩⟩
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

private def computeOperation := SomeOperation.of ComputeOp.arithmetic
private def faultAt : (s : SubstepSequence) → FaultPlan s := fun _ => .none
private def computeOutcome (c : Case) := step policy (afterFetch c) computeOperation thread₀ .thread
  ⟨⟨"arithmetic.fetch"⟩⟩ faultAt
private def afterCompute (c : Case) := match computeOutcome c with | .ran s => s | _ => afterFetch c
private def execution (c : Case) : AccessFree (before c) (afterFetch c) (afterCompute c) :=
  { fetch := fetch c
    operation := computeOperation
    sequence := .none_
    selected := by rfl
    noDataSubsteps := by rfl
    faultAt := faultAt
    noFault := by rfl
    ran := by cases c <;> rfl }

/-- A concrete full-flags outcome. For TEST/XOR, `af` independently selects the
undefined AF bit; both choices satisfy the production relation. -/
private def flags (c : Case) (af : Bool) : BitVec 64 :=
  let effect := (instruction c).effect (before c)
  let base := (((before c).rflags &&& ~~~statusMask) &&& ~~~resumeMask) |||
    effect.flags.valueBits
  if effect.flags.af.isNone && af then base ||| 0x10 else base

private def receipt (c : Case) (af : Bool) :
    ArithmeticNormal (before c) (afterFetch c) (afterCompute c) (instruction c) :=
  { execution := execution c
    encoding := by cases c <;> decide
    afterRflags := flags c af
    flagsAllowed := by cases c <;> cases af <;> decide
    outsideStatusFrame := by cases c <;> cases af <;> decide
    resumeCleared := by cases c <;> cases af <;> decide }

example : (receipt .add32 false).result.gpr .r10 = 0x13 := by decide
example : (receipt .add64 false).result.gpr .r10 = 0xFFFF000000000013 := by decide
example : (receipt .sub32 false).result.gpr .r10 = 0xD := by decide
example : (receipt .sub64 false).result.gpr .r10 = 0xFFFF00000000000D := by decide
example : (receipt .cmpImmediate false).result.gpr .rax = (before .cmpImmediate).gpr .rax := by decide
example : (receipt .test32 true).result.statusFlags.af = true := by decide
example : (receipt .test32 false).result.statusFlags.af = false := by decide
example : ((instruction .xor64).effect (before .xor64)).flags.Allows
    (receipt .xor64 true).result.statusFlags :=
  (receipt .xor64 true).flags_conform

-- All direct width/operation combinations and CMP-immediate were actually fetched.
example (c : Case) : (fetch c).site.encoding = (instruction c).encoding := by cases c <;> decide
example (c : Case) : (ArithmeticInstruction.select (instruction c).encoding).isSome = true := by
  cases c <;> decide

end Grass.Tests.ISA.X86.ExecutionArithmetic
