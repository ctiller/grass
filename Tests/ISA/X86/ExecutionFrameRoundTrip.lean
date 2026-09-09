import Grass.Assembly.FrameMemoryExecution
import Grass.Assembly.SourceBytes
import Tests.Memory.Spike1Policy

/-!
# Continuous source-selected frame store and load

This fixture resolves a minimal source body through the ordinary Hello source
pipeline. It then runs four actual steps over one machine history: fetch the
authored DWORD store, perform its data write, fetch the immediately following
DWORD load, and perform its data read. The frame begins uninitialized, so the
loaded value depends on the committed store rather than on fixture preload.
-/

namespace Grass.Tests.ISA.X86.ExecutionFrameRoundTrip

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 512

open Grass.Assembly Grass.Assembly.FrameMemoryExecution Grass.Assembly.SourceResolve
open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution

private def authored : List Char :=
  ("def helloSource : MachineSource plan := " ++
    "withStack (transferred : UInt32 := 0) " ++
    "withCallFrame WriteFile asm_source (statics := statics) {\n" ++
    "mov transferred, 42\n" ++
    "mov eax, transferred\n" ++
    "ud2\n}").toList

private def rootOffset : Nat := 16

private def body : SourceInput.Body :=
  (SourceInput.extractHelloSourceChars authored).toOption.get (by decide)

private def frame : SourceFrame.Result :=
  (SourceFrame.derive? body).get (by decide)

private def splice : SourceSplice.Result frame rootOffset :=
  (SourceSplice.derive? frame rootOffset).get (by decide)

private def symbols : SourceResolve.Symbols :=
  (SourceResolve.Symbols.mk? [] []).get (by decide)

private def source : SourceResolve.Result frame rootOffset :=
  (SourceResolve.resolve? splice symbols 0).get (by decide)

private def storeItem : X86ControlFlow.CodeItem :=
  frame.program.collected.code[0]

private def loadItem : X86ControlFlow.CodeItem :=
  frame.program.collected.code[1]

private def store : Store32.Resolved :=
  (FrameStore.resolve? frame rootOffset storeItem).get (by decide)

private theorem storeExact : FrameStore.resolve? frame rootOffset storeItem = some store := by
  rfl

private def load : FrameLoad.Result :=
  (FrameLoad.resolve? frame rootOffset loadItem).get (by decide)

private theorem loadExact : FrameLoad.resolve? frame rootOffset loadItem = some load := by
  rfl

private theorem storeSourceAt :
    source.splice.source.outputs[0]? =
      some (.store storeItem store storeExact) := by
  rfl

private theorem loadSourceAt :
    source.splice.source.outputs[1]? =
      some (.load loadItem load loadExact) := by
  rfl

private def storeSelection : StoreSelection source :=
  source.storeSelectionOfSourceAt storeSourceAt

private def loadSelection : LoadSelection source :=
  source.loadSelectionOfSourceAt loadSourceAt

private def storeOutput : SourceResolve.Output source.splice source.symbols source.codeBase :=
  storeSelection.output

private def loadOutput : SourceResolve.Output source.splice source.symbols source.codeBase :=
  loadSelection.output

private theorem selected_store_payload : storeSelection.store.writeBytes = le32 42 := by
  exact storeSelection.payloadExact

private theorem selected_load_destination : loadSelection.result.destination = .rax := by
  rfl

private def allocSupply : FreshSupply AllocTag := .initial
private def codeAlloc : AllocId := allocSupply.fresh.1
private def frameAlloc : AllocId := allocSupply.fresh.2.fresh.1

private def backingSupply : FreshSupply StorageTag := .initial
private def codeBacking : StorageId := backingSupply.fresh.1
private def frameBacking : StorageId := backingSupply.fresh.2.fresh.1

private def epoch : EpochId := (FreshSupply.initial : FreshSupply EpochTag).fresh.1
private def thread : ContextId := (FreshSupply.initial : FreshSupply ContextTag).fresh.1

private def codeBase : MachineAddress := 0x4000
private def frameBase : MachineAddress := 0x8000

private def codeExtent : ByteRange := ⟨0, source.bytes.length⟩
private def frameExtent : ByteRange := ⟨0, 4096⟩

private def codeProvenance : Provenance :=
  { space := .cpuVirtual, root := codeAlloc, epoch := epoch
    source := .imageMapping, rootExtent := codeExtent, path := [] }

private def frameProvenance : Provenance :=
  { space := .cpuVirtual, root := frameAlloc, epoch := epoch
    source := .stack, rootExtent := frameExtent, path := [] }

private def codeRecord : AllocationRecord :=
  { extent := codeExtent, epoch := epoch, space := .cpuVirtual
    source := .imageMapping, owners := [thread], permission := .readExecute
    live := true, backing := codeBacking, origin := 0, base := some codeBase }

private def frameRecord : AllocationRecord :=
  { extent := frameExtent, epoch := epoch, space := .cpuVirtual
    source := .stack, owners := [thread], permission := .readWrite
    live := true, backing := frameBacking, origin := 0, base := some frameBase }

private def initialMemory? : Option MemoryState := do
  let memory ← MemoryState.empty.installBacking? codeBacking
    ⟨source.bytes.length, ByteStore.empty.write 0 source.bytes.toList true⟩
  let memory ← memory.installBacking? frameBacking ⟨4096, .empty⟩
  memory.allocateAll? [(codeAlloc, codeRecord), (frameAlloc, frameRecord)]

private def initialMemory : MemoryState := initialMemory?.get (by decide)
private def initialMachine : MachineState := .initial initialMemory

private def outputRange
    (output : SourceResolve.Output source.splice source.symbols source.codeBase) : ByteRange :=
  ⟨ByteLayout.offset source.splice.finalSizes output.index, output.encoding.size⟩

private def fetchDescriptor
    (output : SourceResolve.Output source.splice source.symbols source.codeBase) :
    AccessDescriptor :=
  { context := thread
    address := .numeric (addressOf codeBase (outputRange output).start)
    space := .cpuVirtual
    provenance := codeProvenance
    range := outputRange output
    intent := .execute
    requiredPermission := .readExecute
    alignment := 1
    initialization := .allBytesInitialized
    producesInitialized := false
    admittedFaults := [.pageFault, .generalProtection] }

private def storeFetchDescriptor : AccessDescriptor := fetchDescriptor storeOutput
private def loadFetchDescriptor : AccessDescriptor := fetchDescriptor loadOutput

private def storeDescriptor : AccessDescriptor :=
  { context := thread
    address := .numeric (addressOf frameBase store.range.start)
    space := .cpuVirtual
    provenance := frameProvenance
    range := store.range
    intent := .write
    requiredPermission := .readWrite
    alignment := 4
    initialization := .readsNothing
    producesInitialized := true
    admittedFaults := [.pageFault, .generalProtection] }

private def loadDescriptor : AccessDescriptor :=
  { context := thread
    address := .numeric (addressOf frameBase load.address.range.start)
    space := .cpuVirtual
    provenance := frameProvenance
    range := load.address.range
    intent := .read
    requiredPermission := .readWrite
    alignment := 4
    initialization := .allBytesInitialized
    producesInitialized := false
    admittedFaults := [.pageFault, .generalProtection] }

private def writeData (_state : MachineState) (descriptor : AccessDescriptor) : ByteSeq :=
  if descriptor = storeDescriptor then store.writeBytes else []

private def indeterminate (_state : MachineState) (_descriptor : AccessDescriptor)
    (_offset : Nat) : Byte := 0xCC

private def policy : StepPolicy :=
  { Grass.Tests.Spike1Policy.policy with oracle := .ofMemory writeData indeterminate }

private structure Operation where
  descriptor : AccessDescriptor

private instance : HasOperationFacets Operation where
  facets operation :=
    { memoryEffects := some (.single operation.descriptor)
      faults := some operation.descriptor.admittedFaults
      restartability := some operation.descriptor.restartability
      ordering := some operation.descriptor.ordering }

private def operation (descriptor : AccessDescriptor) : SomeOperation :=
  SomeOperation.of (Operation.mk descriptor)

private def stepAccess (state : MachineState) (descriptor : AccessDescriptor) : StepOutcome :=
  Grass.Op.step policy state (operation descriptor) thread .thread
    ⟨⟨"frame-round-trip"⟩⟩ (fun _ => .none)

private def beforeStore : State :=
  { machine := initialMachine
    gpr := fun register =>
      if register = .rsp then addressOf frameBase rootOffset
      else if register = .rax then 0xFFFFFFFF00000000
      else 0
    rip := addressOf codeBase (outputRange storeOutput).start
    rflags := 0x10602 }

private theorem frame_starts_uninitialized :
    ¬ initialMemory.RangeInitialized frameAlloc store.range := by
  decide

private def cause : EventCause := ⟨⟨"frame-round-trip"⟩⟩
private def noFault : (sequence : SubstepSequence) → FaultPlan sequence := fun _ => .none

private def storeFetchStep : StepOutcome :=
  stepAccess beforeStore.machine storeFetchDescriptor

private def afterStoreFetch : MachineState :=
  match storeFetchStep with
  | .ran state => state
  | .rejected _ => beforeStore.machine

private def storeFetchReached : MachineState :=
  beforeStore.machine.noteContext thread .thread

private def storeFetchResolved : storeFetchReached.memory.ResolvedAccess
    storeFetchDescriptor.provenance storeFetchDescriptor.range :=
  (prepareAccess storeFetchReached.memory storeFetchDescriptor).toOption.get (by decide)

private def storeFetchComplete : CompleteCommitted storeFetchDescriptor :=
  (policy.oracle.answerResolved storeFetchReached storeFetchDescriptor storeFetchResolved).get
    (by decide)

private def storeFetchObserved : ByteSeq :=
  observedBytes storeFetchResolved (indeterminate storeFetchReached storeFetchDescriptor)

private def storeDecoded : DecodedSite beforeStore.rip storeFetchObserved :=
  (DecodedSite.check beforeStore.rip storeFetchObserved).toOption.get (by decide)

private def storeFetchRun : AccessRun beforeStore.machine afterStoreFetch storeFetchDescriptor :=
  { policy := policy
    operation := operation storeFetchDescriptor
    context := thread
    contextKind := .thread
    cause := cause
    faultAt := noFault
    sequence := .single storeFetchDescriptor
    selected := by rfl
    substeps_exact := by rfl
    noFault := by rfl
    ran := by rfl
    resolved := storeFetchResolved
    prepared := by rfl
    complete := storeFetchComplete
    answerResolved := by simp [storeFetchComplete, storeFetchReached]
    clean := by decide }

private def storeFetch : FetchedSite beforeStore afterStoreFetch :=
  { descriptor := storeFetchDescriptor
    run := storeFetchRun
    writeData := writeData
    indeterminate := indeterminate
    memoryOracle := by rfl
    intent := by rfl
    initialization := by rfl
    ledgerEffect := by rfl
    authorityEffect := by rfl
    address := by rfl
    placed := ⟨codeBase, by rfl⟩
    site := storeDecoded
    noTrailing := by decide }

private def storeSite : SourceFetch.SourceSite source beforeStore afterStoreFetch :=
  { output := storeOutput
    outputAt := by rfl
    fetch := storeFetch
    space := by rfl
    observed := by rfl
    base := codeBase
    baseExact := by rfl
    codeRootOffset := 0
    loadedImageBase := codeBase.toNat
    placementExact := by rfl
    descriptorStart := by rfl }

private def storeStep : StepOutcome := stepAccess afterStoreFetch storeDescriptor

private def afterStore : MachineState :=
  match storeStep with
  | .ran state => state
  | .rejected _ => afterStoreFetch

private def storeReached : MachineState := afterStoreFetch.noteContext thread .thread

private def storeResolved : storeReached.memory.ResolvedAccess
    storeDescriptor.provenance storeDescriptor.range :=
  (prepareAccess storeReached.memory storeDescriptor).toOption.get (by decide)

private def storeComplete : CompleteCommitted storeDescriptor :=
  (policy.oracle.answerResolved storeReached storeDescriptor storeResolved).get (by decide)

private def storeRun : AccessRun afterStoreFetch afterStore storeDescriptor :=
  { policy := policy
    operation := operation storeDescriptor
    context := thread
    contextKind := .thread
    cause := cause
    faultAt := noFault
    sequence := .single storeDescriptor
    selected := by rfl
    substeps_exact := by rfl
    noFault := by rfl
    ran := by rfl
    resolved := storeResolved
    prepared := by rfl
    complete := storeComplete
    answerResolved := by simp [storeComplete, storeReached]
    clean := by decide }

private def storeAccess : MemoryAccess storeSite.fetch afterStore :=
  { descriptor := storeDescriptor
    run := storeRun
    policy := by rfl
    context := by rfl
    contextKind := by rfl
    cause := by rfl
    fetchContext := by rfl
    dataContext := by rfl
    space := by rfl
    ordering := by rfl
    ledgerEffect := by rfl
    authorityEffect := by rfl }

private def storeNormal : StoreNormal source beforeStore afterStoreFetch afterStore :=
  { instruction := .local storeSelection
    site := storeSite
    selected := by rfl
    access := storeAccess
    intent := by rfl
    initialization := by rfl
    producesInitialized := by rfl
    range := by rfl
    base := frameBase
    placed := by rfl
    rsp := by rfl
    supplied := by
      change store.writeBytes = storeSelection.store.writeBytes
      exact congrArg Store32.Resolved.writeBytes
        (source.storeSelectionOfSourceAt_store storeSourceAt).symm }

private def beforeLoad : State := storeNormal.result

private theorem store_falls_through_to_load :
    beforeLoad.rip = addressOf codeBase (outputRange loadOutput).start := by
  decide

private def loadFetchStep : StepOutcome :=
  stepAccess beforeLoad.machine loadFetchDescriptor

private def afterLoadFetch : MachineState :=
  match loadFetchStep with
  | .ran state => state
  | .rejected _ => beforeLoad.machine

private def loadFetchReached : MachineState :=
  beforeLoad.machine.noteContext thread .thread

private def loadFetchResolved : loadFetchReached.memory.ResolvedAccess
    loadFetchDescriptor.provenance loadFetchDescriptor.range :=
  (prepareAccess loadFetchReached.memory loadFetchDescriptor).toOption.get (by decide)

private def loadFetchComplete : CompleteCommitted loadFetchDescriptor :=
  (policy.oracle.answerResolved loadFetchReached loadFetchDescriptor loadFetchResolved).get
    (by decide)

private def loadFetchObserved : ByteSeq :=
  observedBytes loadFetchResolved (indeterminate loadFetchReached loadFetchDescriptor)

private def loadDecoded : DecodedSite beforeLoad.rip loadFetchObserved :=
  (DecodedSite.check beforeLoad.rip loadFetchObserved).toOption.get (by decide)

private def loadFetchRun : AccessRun beforeLoad.machine afterLoadFetch loadFetchDescriptor :=
  { policy := policy
    operation := operation loadFetchDescriptor
    context := thread
    contextKind := .thread
    cause := cause
    faultAt := noFault
    sequence := .single loadFetchDescriptor
    selected := by rfl
    substeps_exact := by rfl
    noFault := by rfl
    ran := by rfl
    resolved := loadFetchResolved
    prepared := by rfl
    complete := loadFetchComplete
    answerResolved := by simp [loadFetchComplete, loadFetchReached]
    clean := by decide }

private def loadFetch : FetchedSite beforeLoad afterLoadFetch :=
  { descriptor := loadFetchDescriptor
    run := loadFetchRun
    writeData := writeData
    indeterminate := indeterminate
    memoryOracle := by rfl
    intent := by rfl
    initialization := by rfl
    ledgerEffect := by rfl
    authorityEffect := by rfl
    address := by
      simpa [loadFetchDescriptor, fetchDescriptor] using
        congrArg Address.numeric store_falls_through_to_load.symm
    placed := ⟨codeBase, by rfl⟩
    site := loadDecoded
    noTrailing := by decide }

private def loadSite : SourceFetch.SourceSite source beforeLoad afterLoadFetch :=
  { output := loadOutput
    outputAt := by rfl
    fetch := loadFetch
    space := by rfl
    observed := by rfl
    base := codeBase
    baseExact := by rfl
    codeRootOffset := 0
    loadedImageBase := codeBase.toNat
    placementExact := by rfl
    descriptorStart := by rfl }

private def loadStep : StepOutcome := stepAccess afterLoadFetch loadDescriptor

private def afterLoad : MachineState :=
  match loadStep with
  | .ran state => state
  | .rejected _ => afterLoadFetch

private def loadReached : MachineState := afterLoadFetch.noteContext thread .thread

private def loadResolved : loadReached.memory.ResolvedAccess
    loadDescriptor.provenance loadDescriptor.range :=
  (prepareAccess loadReached.memory loadDescriptor).toOption.get (by decide)

private def loadComplete : CompleteCommitted loadDescriptor :=
  (policy.oracle.answerResolved loadReached loadDescriptor loadResolved).get (by decide)

private def loadRun : AccessRun afterLoadFetch afterLoad loadDescriptor :=
  { policy := policy
    operation := operation loadDescriptor
    context := thread
    contextKind := .thread
    cause := cause
    faultAt := noFault
    sequence := .single loadDescriptor
    selected := by rfl
    substeps_exact := by rfl
    noFault := by rfl
    ran := by rfl
    resolved := loadResolved
    prepared := by rfl
    complete := loadComplete
    answerResolved := by simp [loadComplete, loadReached]
    clean := by decide }

private def loadAccess : MemoryAccess loadSite.fetch afterLoad :=
  { descriptor := loadDescriptor
    run := loadRun
    policy := by rfl
    context := by rfl
    contextKind := by rfl
    cause := by rfl
    fetchContext := by rfl
    dataContext := by rfl
    space := by rfl
    ordering := by rfl
    ledgerEffect := by rfl
    authorityEffect := by rfl }

private def loadNormal : LoadNormal source beforeLoad afterLoadFetch afterLoad :=
  { selection := loadSelection
    site := loadSite
    selected := by rfl
    access := loadAccess
    intent := by rfl
    initialization := by rfl
    range := by rfl
    base := frameBase
    placed := by rfl
    rsp := by rfl }

private theorem load_observed_store_payload :
    loadNormal.access.run.complete.committed.observed = some (le32 42) := by
  decide

example : storeNormal.instruction.payload = le32 42 := by rfl

example : loadNormal.read.observed = le32 42 := by
  exact Option.some.inj (loadNormal.read.observed_exact.symm.trans load_observed_store_payload)

example : loadNormal.read.value = (42 : BitVec 32) :=
  loadNormal.read.value_of_observed_eq_le32 42 load_observed_store_payload

example : BitVec.setWidth 32 (loadNormal.result.gpr .rax) = (42 : BitVec 32) := by
  change BitVec.setWidth 32
    (loadNormal.result.gpr loadNormal.selection.result.destination) = (42 : BitVec 32)
  exact loadNormal.loaded_value.trans
    (loadNormal.read.value_of_observed_eq_le32 42 load_observed_store_payload)

example : BitVec.extractLsb' 32 32 (loadNormal.result.gpr .rax) = 0 := by
  change BitVec.extractLsb' 32 32
    (loadNormal.result.gpr loadNormal.selection.result.destination) = 0
  exact loadNormal.clears_high

example : afterLoad.events.length = 4 := by decide

example : loadNormal.read.observed = observedBytes loadNormal.access.run.resolved
    (indeterminate loadReached loadDescriptor) :=
  loadNormal.read.observed_backing

example : loadNormal.access.run.resolved.RangeInitialized :=
  loadNormal.read.initialized

end Grass.Tests.ISA.X86.ExecutionFrameRoundTrip
