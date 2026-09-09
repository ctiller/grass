import Grass.ISA.X86.Execution.PushSavedRead
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

private def readDescriptor : AccessDescriptor :=
  acc stackProv ⟨56, 8⟩ 0x3038 .read .readWrite true false

private inductive ReadOperation where | read
private instance : HasOperationFacets ReadOperation where
  facets
    | .read =>
      { memoryEffects := some (.single readDescriptor), faults := some [.pageFault]
        restartability := some .restartable, ordering := some .plain }

private def readStep :=
  step pushPolicy afterStore (SomeOperation.of ReadOperation.read) thread₀ .thread
    ⟨⟨"push.saved.read"⟩⟩
private def afterRead := match readStep with | .ran s => s | .rejected _ => afterStore
private def readReached := afterStore.noteContext thread₀ .thread
private def readResolved : readReached.memory.ResolvedAccess
    readDescriptor.provenance readDescriptor.range :=
  (prepareAccess readReached.memory readDescriptor).toOption.get (by decide)
private def readComplete : CompleteCommitted readDescriptor :=
  (pushPolicy.oracle.answerResolved readReached readDescriptor readResolved).get (by decide)

private def savedRead : PushSavedRead receipt (afterRead := afterRead) :=
  { descriptor := readDescriptor
    intent := by rfl
    read :=
      { policy := pushPolicy, operation := SomeOperation.of ReadOperation.read
        context := thread₀, contextKind := .thread, cause := ⟨⟨"push.saved.read"⟩⟩
        faultAt := fun _ => .none, sequence := .single readDescriptor
        selected := by rfl, substeps_exact := by rfl, noFault := by rfl, ran := by rfl
        resolved := readResolved, prepared := by rfl, complete := readComplete
        answerResolved := by simp [readComplete, readReached], clean := by decide }
    policy := by rfl, contextExact := by rfl, contextKind := by rfl
    root := by rfl, range := by rfl, address := by rfl, ordering := by rfl
    ledgerEffect := by rfl, authorityEffect := by rfl
    valueRead :=
      { writeData := writeData, indeterminate := zeroByte, memoryOracle := by rfl
        reads := by rfl, writes := by rfl, width := by rfl, initialization := by rfl } }

example : savedRead.valueRead.value = before.gpr .r12 := savedRead.value_exact receipt

example : ∃ valid, afterRead.events = afterStore.events ++ [valid] ∧
    valid.event.valueRead = some (le64 (before.gpr .r12)) ∧
    valid.event.status = .completed 8 0 :=
  savedRead.read_event receipt

example : afterRead.memory = afterStore.memory ∧ afterRead.obligations = afterStore.obligations :=
  savedRead.read_frame receipt

-- A changed range is excluded by the receipt's exact saved-span equality.
example (candidate : PushSavedRead receipt (afterRead := afterRead))
    (wrong : candidate.descriptor.range = ⟨0, 8⟩) : False := by
  rw [candidate.range] at wrong
  have distinct : (⟨56, 8⟩ : ByteRange) ≠ ⟨0, 8⟩ := by decide
  apply distinct
  simp [receipt, storeDescriptor, acc] at wrong

end Grass.Tests.ISA.X86.ExecutionPush
