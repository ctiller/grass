import Grass.ISA.X86.Execution.Dispatch
import Tests.Assembly.SourceResolve
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.InstructionDispatch

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Assembly
  Grass.Assembly.SourceResolve Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

-- Embed here so the source-freshness gate rechecks this consumer against the current authored file.
private def authored : List Char := include_source_chars "../../../Spikes/1_Hello_World/Program.lean"

private def inventory : Option (Nat × List Nat × List Nat) := do
  let symbols ← Grass.Tests.Assembly.SourceResolve.checkedSymbols
  let body ← (SourceInput.extractHelloSourceChars authored).toOption
  let frame ← SourceFrame.derive? body
  let splice ← SourceSplice.derive? frame 0
  let result ← resolve? splice symbols 1000
  let selected := result.outputs.filterMap fun output =>
    if (Instruction.select output.encoding).isSome then some output.index else none
  let unsupported := result.outputs.filterMap fun output =>
    if (Instruction.select output.encoding).isSome then none else some output.index
  pure (result.outputs.length, selected, unsupported)

example : inventory = some (44,
    [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22,
      23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
      42, 43], [4, 16, 17, 25]) := by decide +kernel

private inductive Case where | push | truncated | unsupported | trailing
deriving DecidableEq, Repr

private def rawBytes : Case → ByteSeq
  | .push => [0x41, 0x54]
  | .truncated => [0x41]
  | .unsupported => [0x90]
  | .trailing => [0x41, 0x54, 0x90]

private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def memory (c : Case) : MemoryState :=
  let bytes := ByteStore.empty.write 0 (rawBytes c) true
  let record : AllocationRecord :=
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual, source := .virtualAlloc
      owners := [thread₀], permission := .readExecute, live := true, backing := backing
      origin := 0, base := some 0x1000 }
  let backed := (MemoryState.empty.installBacking? backing ⟨64, bytes⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty
private def machine (c : Case) : MachineState := .initial (memory c)
private def descriptor (c : Case) : AccessDescriptor :=
  acc bufferProv ⟨0, (rawBytes c).length⟩ 0x1000 .execute .readExecute true false
private inductive Operation where | fetch (c : Case)
private instance : HasOperationFacets Operation where
  facets
    | .fetch c =>
      { memoryEffects := some (.single (descriptor c)), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }
private def before (c : Case) : State :=
  { machine := machine c, gpr := fun _ => 0, rip := 0x1000, rflags := 0 }
private def reached (c : Case) := (machine c).noteContext thread₀ .thread
private def resolved (c : Case) : (reached c).memory.ResolvedAccess
    (descriptor c).provenance (descriptor c).range :=
  (prepareAccess (reached c).memory (descriptor c)).toOption.get (by cases c <;> decide)
private def complete (c : Case) : CompleteCommitted (descriptor c) :=
  (policy.oracle.answerResolved (reached c) (descriptor c) (resolved c)).get
    (by cases c <;> decide)
private def stepResult (c : Case) :=
  step policy (machine c) (SomeOperation.of (Operation.fetch c)) thread₀ .thread
    ⟨⟨"dispatch.fetch"⟩⟩
private def after (c : Case) :=
  match stepResult c with | .ran state => state | .rejected _ => machine c
private def fetch (c : Case) : ObservedFetch (before c) (after c) :=
  { descriptor := descriptor c
    run :=
      { policy := policy, operation := SomeOperation.of (Operation.fetch c)
        context := thread₀, contextKind := .thread, cause := ⟨⟨"dispatch.fetch"⟩⟩
        faultAt := fun _ => .none, sequence := .single (descriptor c)
        selected := by rfl, substeps_exact := by rfl, noFault := by rfl
        ran := by cases c <;> rfl, resolved := resolved c
        prepared := by cases c <;> rfl, complete := complete c
        answerResolved := by cases c <;> simp [complete, reached, before]
        clean := by cases c <;> decide }
    writeData := storedBytes, indeterminate := indeterminateByte, memoryOracle := by rfl
    intent := by rfl, initialization := by rfl, ledgerEffect := by rfl
    authorityEffect := by rfl, address := by rfl
    placed := ⟨0x1000, by cases c <;> decide⟩ }

private def dispatchClass (c : Case) : Nat :=
  match (fetch c).dispatch with
  | .ok _ => 0
  | .error (.decode _) => 1
  | .error .trailingBytes => 2
  | .error (.instruction _) => 3
  | .error _ => 4

example : dispatchClass .push = 0 := by decide
example : dispatchClass .truncated = 1 := by decide
example : dispatchClass .unsupported = 3 := by decide
example : dispatchClass .trailing = 2 := by decide

example (c : Case) (reason : ApplicabilityFailure)
    (failed : (fetch c).dispatch = .error reason) :
    ((fetch c).failureOutcome reason failed).state.machine = after c ∧
      ((fetch c).failureOutcome reason failed).state.machine.events = (after c).events :=
  ⟨ObservedFetch.failureOutcome_machine _ _ _, rfl⟩

end Grass.Tests.ISA.X86.InstructionDispatch
