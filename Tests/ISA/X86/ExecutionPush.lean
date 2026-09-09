import Grass.ISA.X86.Execution.PushNormal
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionPush

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def storage0 : FreshSupply StorageTag := .initial
private def codeBacking : StorageId := storage0.fresh.1
private def stackBacking : StorageId := storage0.fresh.2.fresh.1

private def codeRecord : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
    source := .virtualAlloc, owners := [thread₀], permission := .readExecute
    live := true, backing := codeBacking, origin := 0, base := some 0x1000 }

private def stackRecord : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
    source := .mappedFile, owners := [thread₀], permission := .readWrite
    live := true, backing := stackBacking, origin := 0, base := some 0x3000 }

private def initialMemory : MemoryState :=
  let codeBytes := ByteStore.empty.write 0 [0x41, 0x54] true
  let stackBytes := ByteStore.empty.write 0 (List.replicate 64 0) true
  let withCode :=
    (MemoryState.empty.installBacking? codeBacking ⟨64, codeBytes⟩).getD .empty
  let withStack :=
    (withCode.installBacking? stackBacking ⟨64, stackBytes⟩).getD .empty
  (withStack.allocateAll? [(bufferAlloc, codeRecord), (viewAlloc, stackRecord)]).getD .empty

private def initialMachine : MachineState := .initial initialMemory

private def before : State :=
  { machine := initialMachine
    gpr := fun register =>
      if register = .rsp then 0x3040 else if register = .r12 then 0x1122334455667788 else 0xCAFE
    rip := 0x1000
    rflags := 0x10602 }

private def fetchDescriptor : AccessDescriptor :=
  acc bufferProv ⟨0, 2⟩ 0x1000 .execute .readExecute true false

private def stackProv : Provenance := viewProv

private def storeDescriptor : AccessDescriptor :=
  acc stackProv ⟨56, 8⟩ 0x3038 .write .readWrite false true

private def writeData : MachineState → AccessDescriptor → ByteSeq :=
  fun _ _ => le64 (before.gpr .r12)

private def zeroByte : MachineState → (d : AccessDescriptor) → Nat → Byte :=
  fun _ _ _ => 0

private def pushPolicy : StepPolicy :=
  { policy with oracle := Oracle.ofMemory writeData zeroByte }

private theorem pushPolicy_oracle :
    pushPolicy.oracle = Oracle.ofMemory (fun _ _ => le64 (before.gpr .r12))
      (fun _ _ _ => 0) := by rfl

private inductive FetchOperation where | fetch
private instance : HasOperationFacets FetchOperation where
  facets
    | .fetch =>
      { memoryEffects := some (.single fetchDescriptor), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }

private inductive StoreOperation where | store
private instance : HasOperationFacets StoreOperation where
  facets
    | .store =>
      { memoryEffects := some (.single storeDescriptor), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }

private def fetchStep :=
  step pushPolicy initialMachine (SomeOperation.of FetchOperation.fetch) thread₀ .thread
    ⟨⟨"push.fetch"⟩⟩
private def afterFetch := match fetchStep with | .ran s => s | .rejected _ => initialMachine
private def fetchReached := initialMachine.noteContext thread₀ .thread
private def fetchResolved : fetchReached.memory.ResolvedAccess
    fetchDescriptor.provenance fetchDescriptor.range :=
  (prepareAccess fetchReached.memory fetchDescriptor).toOption.get (by decide)
private def fetchComplete : CompleteCommitted fetchDescriptor :=
  (pushPolicy.oracle.answerResolved fetchReached fetchDescriptor fetchResolved).get (by decide)
private def fetchObserved := observedBytes fetchResolved (zeroByte fetchReached fetchDescriptor)
private def site : DecodedSite before.rip fetchObserved :=
  (DecodedSite.check before.rip fetchObserved).toOption.get (by decide)

private def fetched : FetchedSite before afterFetch := by
  let run : AccessRun initialMachine afterFetch fetchDescriptor :=
    { policy := pushPolicy, operation := SomeOperation.of FetchOperation.fetch
      context := thread₀, contextKind := .thread, cause := ⟨⟨"push.fetch"⟩⟩
      faultAt := fun _ => .none, sequence := .single fetchDescriptor
      selected := by rfl, substeps_exact := by rfl, noFault := by rfl, ran := by rfl
      resolved := fetchResolved, prepared := by rfl, complete := fetchComplete
      answerResolved := by simp [fetchComplete, fetchReached], clean := by decide }
  exact
    { descriptor := fetchDescriptor, run := run, writeData := writeData
      indeterminate := zeroByte, memoryOracle := by rfl
      intent := by rfl, initialization := by rfl, ledgerEffect := by rfl
      authorityEffect := by rfl, address := by rfl, placed := ⟨0x1000, by rfl⟩
      site := site, noTrailing := by decide }

private def storeStep :=
  step pushPolicy afterFetch (SomeOperation.of StoreOperation.store) thread₀ .thread
    ⟨⟨"push.fetch"⟩⟩
private def afterStore := match storeStep with | .ran s => s | .rejected _ => afterFetch
private def storeReached := afterFetch.noteContext thread₀ .thread
private def storeResolved : storeReached.memory.ResolvedAccess
    storeDescriptor.provenance storeDescriptor.range :=
  (prepareAccess storeReached.memory storeDescriptor).toOption.get (by decide)
private def storeComplete : CompleteCommitted storeDescriptor :=
  (pushPolicy.oracle.answerResolved storeReached storeDescriptor storeResolved).get (by decide)

private def receipt : PushNormal before afterFetch afterStore .r12 :=
  { fetch := fetched, encoding := by decide, descriptor := storeDescriptor
    store :=
      { policy := pushPolicy, operation := SomeOperation.of StoreOperation.store
        context := thread₀, contextKind := .thread, cause := ⟨⟨"push.fetch"⟩⟩
        faultAt := fun _ => .none, sequence := .single storeDescriptor
        selected := by rfl, substeps_exact := by rfl, noFault := by rfl, ran := by rfl
        resolved := storeResolved, prepared := by rfl, complete := storeComplete
        answerResolved := by simp [storeComplete, storeReached], clean := by decide }
    fetchContext := by rfl, storeContext := by rfl
    policy := by rfl, context := by rfl, contextKind := by rfl, cause := by rfl
    memoryOracle := pushPolicy_oracle
    intent := by rfl, extent := by rfl, initialized := by rfl
    initialization := by rfl, ordering := by rfl
    ledgerEffect := by rfl, authorityEffect := by rfl, stackNoUnderflow := by decide
    address := by rfl, placed := ⟨0x3000, by rfl⟩ }

example : receipt.result.gpr .rsp = 0x3038 := by decide
example : receipt.result.rip = 0x1002 := by decide
example : receipt.result.rflags = 0x602 := by decide
example : receipt.result.gpr .r13 = before.gpr .r13 := receipt.gpr_frame .r13 (by decide)

example : List.ofFn (fun i : Fin 8 =>
    receipt.result.machine.memory.byteAt? viewAlloc (56 + i)) =
    (le64 (before.gpr .r12)).map some := by decide

example (i : Fin 8) :
    receipt.result.machine.memory.cellAt? viewAlloc (56 + i) =
      ((le64 (before.gpr .r12))[i]?).map (·, true) := by
  have covered : receipt.descriptor.range.Covers (56 + i) := by
    change storeDescriptor.range.Covers (56 + i)
    simp only [ByteRange.covers_def, storeDescriptor, acc]
    exact ⟨Nat.le_add_right 56 i, by simpa using Nat.add_lt_add_left i.isLt 56⟩
  have saved := receipt.saved_cell (56 + i) covered
  change afterStore.memory.cellAt? viewAlloc (56 + i) = _
  simpa [receipt, storeDescriptor, acc, stackProv, viewProv, bufferProv] using saved

-- The carrier's payload law also covers PUSH RSP: it saves the pre-decrement value.
example {pre : State} {fetchedState storedState : MachineState}
    (pushRsp : PushNormal pre fetchedState storedState .rsp) :
    pushRsp.store.complete.committed.written = some (le64 (pre.gpr .rsp)) :=
  pushRsp.written_exact

example (mutated : PushNormal before afterFetch afterStore .r12)
    (wrong : mutated.descriptor.address = .numeric 0x3030) : False := by
  rw [mutated.address] at wrong
  exact (by decide : (Address.numeric (before.gpr .rsp - 8)) ≠ .numeric 0x3030) wrong

example (mutated : PushNormal before afterFetch afterStore .r12)
    (wrong : mutated.descriptor.range.size = 4) : False := by
  rw [mutated.extent] at wrong
  contradiction

example (mutated : PushNormal before afterFetch afterStore .r12)
    (wrongOracle : mutated.store.policy.oracle =
      Oracle.ofMemory (fun _ _ => List.replicate 8 0) (fun _ _ _ => 0)) : False := by
  rw [mutated.memoryOracle] at wrongOracle
  have payload := congrFun (congrFun
    (congrArg Oracle.answerResolved wrongOracle) storeReached) storeDescriptor
  have answer := congrFun payload storeResolved
  have written := congrArg (fun x => x.map (fun c => c.committed.written)) answer
  simp [Oracle.ofMemory, storeDescriptor, acc, AccessIntent.write, before, le64] at written

end Grass.Tests.ISA.X86.ExecutionPush






