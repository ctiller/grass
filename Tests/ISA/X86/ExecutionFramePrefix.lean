import Grass.Assembly.FrameMemoryExecution
import Grass.Assembly.SourceBytes
import Tests.Memory.Spike1Policy

/-! Continuous generated local initialization followed by the adjacent authored
Win64 qword argument store, both selected from one resolved source. -/

namespace Grass.Tests.ISA.X86.ExecutionFramePrefix

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
    "arg WriteFile.overlapped, 0\n" ++
    "ud2\n}").toList

private def rootOffset : Nat := 16
private def body : SourceInput.Body :=
  (SourceInput.extractHelloSourceChars authored).toOption.get (by decide)
private def frame : SourceFrame.Result := (SourceFrame.derive? body).get (by decide)
private def splice : SourceSplice.Result frame rootOffset :=
  (SourceSplice.derive? frame rootOffset).get (by decide)
private def symbols : SourceResolve.Symbols :=
  (SourceResolve.Symbols.mk? [] []).get (by decide)
private def source : SourceResolve.Result frame rootOffset :=
  (SourceResolve.resolve? splice symbols 0).get (by decide)

private def initializer : SourceInitialization.Entry :=
  source.splice.initialization.entries[0]
private theorem initializerAt :
    source.splice.initialization.entries[0]? = some initializer := by rfl
private def initializerSelection : StoreSelection source :=
  source.storeSelectionOfInitializerAt 0 initializer initializerAt
private def initializerOutput :
    SourceResolve.Output source.splice source.symbols source.codeBase :=
  initializerSelection.output

private def argumentItem : X86ControlFlow.CodeItem := frame.program.collected.code[0]
private def argument : FrameArgument.Result :=
  (FrameArgument.resolve? frame rootOffset argumentItem).get (by decide)
private theorem argumentExact :
    FrameArgument.resolve? frame rootOffset argumentItem = some argument := by rfl
private theorem argumentSourceAt :
    source.splice.source.outputs[0]? =
      some (.argument argumentItem argument argumentExact) := by rfl
private def argumentSelection : ArgumentSelection source :=
  source.argumentSelectionOfSourceAt argumentSourceAt
private def argumentOutput :
    SourceResolve.Output source.splice source.symbols source.codeBase :=
  argumentSelection.output

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
    space := .cpuVirtual, provenance := codeProvenance, range := outputRange output
    intent := .execute, requiredPermission := .readExecute, alignment := 1
    initialization := .allBytesInitialized, producesInitialized := false
    admittedFaults := [.pageFault, .generalProtection] }

private def initializerFetchDescriptor := fetchDescriptor initializerOutput
private def argumentFetchDescriptor := fetchDescriptor argumentOutput

private def initializerDescriptor : AccessDescriptor :=
  { context := thread
    address := .numeric (addressOf frameBase initializerSelection.store.range.start)
    space := .cpuVirtual, provenance := frameProvenance
    range := initializerSelection.store.range, intent := .write
    requiredPermission := .readWrite, alignment := 4
    initialization := .readsNothing, producesInitialized := true
    admittedFaults := [.pageFault, .generalProtection] }
private def argumentDescriptor : AccessDescriptor :=
  { context := thread
    address := .numeric (addressOf frameBase argumentSelection.result.range.start)
    space := .cpuVirtual, provenance := frameProvenance
    range := argumentSelection.result.range, intent := .write
    requiredPermission := .readWrite, alignment := 8
    initialization := .readsNothing, producesInitialized := true
    admittedFaults := [.pageFault, .generalProtection] }

private def argumentPayload : ByteSeq :=
  le64 (BitVec.signExtend 64 (BitVec.ofNat 32 argumentSelection.result.value))
private def writeData (_state : MachineState) (descriptor : AccessDescriptor) : ByteSeq :=
  if descriptor = initializerDescriptor then initializerSelection.store.writeBytes
  else if descriptor = argumentDescriptor then argumentPayload
  else []
private def indeterminate (_state : MachineState) (_descriptor : AccessDescriptor)
    (_offset : Nat) : Byte := 0xCC
private def policy : StepPolicy :=
  { Grass.Tests.Spike1Policy.policy with oracle := .ofMemory writeData indeterminate }

private structure Operation where descriptor : AccessDescriptor
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
    ⟨⟨"frame-prefix"⟩⟩ (fun _ => .none)

private def beforeInitializer : State :=
  { machine := initialMachine
    gpr := fun register => if register = .rsp then addressOf frameBase rootOffset else 0
    rip := addressOf codeBase (outputRange initializerOutput).start
    rflags := 0x10602 }

private theorem local_starts_uninitialized :
    ¬ initialMemory.RangeInitialized frameAlloc initializerSelection.store.range := by decide

private def cause : EventCause := ⟨⟨"frame-prefix"⟩⟩
private def noFault : (sequence : SubstepSequence) → FaultPlan sequence := fun _ => .none

private def initializerFetchStep := stepAccess beforeInitializer.machine initializerFetchDescriptor
private def afterInitializerFetch : MachineState :=
  match initializerFetchStep with | .ran state => state | .rejected _ => beforeInitializer.machine
private def initializerFetchReached := beforeInitializer.machine.noteContext thread .thread
private def initializerFetchResolved : initializerFetchReached.memory.ResolvedAccess
    initializerFetchDescriptor.provenance initializerFetchDescriptor.range :=
  (prepareAccess initializerFetchReached.memory initializerFetchDescriptor).toOption.get (by decide)
private def initializerFetchComplete : CompleteCommitted initializerFetchDescriptor :=
  (policy.oracle.answerResolved initializerFetchReached initializerFetchDescriptor
    initializerFetchResolved).get (by decide)
private def initializerFetchObserved :=
  observedBytes initializerFetchResolved
    (indeterminate initializerFetchReached initializerFetchDescriptor)
private def initializerDecoded : DecodedSite beforeInitializer.rip initializerFetchObserved :=
  (DecodedSite.check beforeInitializer.rip initializerFetchObserved).toOption.get (by decide)
private def initializerFetchRun :
    AccessRun beforeInitializer.machine afterInitializerFetch initializerFetchDescriptor :=
  { policy, operation := operation initializerFetchDescriptor, context := thread
    contextKind := .thread, cause, faultAt := noFault
    sequence := .single initializerFetchDescriptor, selected := by rfl
    substeps_exact := by rfl, noFault := by rfl, ran := by rfl
    resolved := initializerFetchResolved, prepared := by rfl
    complete := initializerFetchComplete
    answerResolved := by simp [initializerFetchComplete, initializerFetchReached]
    clean := by decide }
private def initializerFetch : FetchedSite beforeInitializer afterInitializerFetch :=
  { descriptor := initializerFetchDescriptor, run := initializerFetchRun
    writeData, indeterminate, memoryOracle := by rfl, intent := by rfl
    initialization := by rfl, ledgerEffect := by rfl, authorityEffect := by rfl
    address := by rfl, placed := ⟨codeBase, by rfl⟩, site := initializerDecoded
    noTrailing := by decide }
private def initializerSite :
    SourceFetch.SourceSite source beforeInitializer afterInitializerFetch :=
  { output := initializerOutput, outputAt := by rfl, fetch := initializerFetch
    space := by rfl, observed := by rfl, base := codeBase, baseExact := by rfl
    codeRootOffset := 0, loadedImageBase := codeBase.toNat
    placementExact := by rfl, descriptorStart := by rfl }

private def initializerStep := stepAccess afterInitializerFetch initializerDescriptor
private def afterInitializer : MachineState :=
  match initializerStep with | .ran state => state | .rejected _ => afterInitializerFetch
private def initializerReached := afterInitializerFetch.noteContext thread .thread
private def initializerResolved : initializerReached.memory.ResolvedAccess
    initializerDescriptor.provenance initializerDescriptor.range :=
  (prepareAccess initializerReached.memory initializerDescriptor).toOption.get (by decide)
private def initializerComplete : CompleteCommitted initializerDescriptor :=
  (policy.oracle.answerResolved initializerReached initializerDescriptor initializerResolved).get
    (by decide)
private def initializerRun :
    AccessRun afterInitializerFetch afterInitializer initializerDescriptor :=
  { policy, operation := operation initializerDescriptor, context := thread
    contextKind := .thread, cause, faultAt := noFault
    sequence := .single initializerDescriptor, selected := by rfl
    substeps_exact := by rfl, noFault := by rfl, ran := by rfl
    resolved := initializerResolved, prepared := by rfl, complete := initializerComplete
    answerResolved := by simp [initializerComplete, initializerReached]
    clean := by decide }
private def initializerAccess : MemoryAccess initializerSite.fetch afterInitializer :=
  { descriptor := initializerDescriptor, run := initializerRun, policy := by rfl
    context := by rfl, contextKind := by rfl, cause := by rfl
    fetchContext := by rfl, dataContext := by rfl, space := by rfl, ordering := by rfl
    ledgerEffect := by rfl, authorityEffect := by rfl }
private def initializerNormal :
    StoreNormal source beforeInitializer afterInitializerFetch afterInitializer :=
  { instruction := .local initializerSelection, site := initializerSite, selected := by rfl
    access := initializerAccess, intent := by rfl, initialization := by rfl
    producesInitialized := by rfl, range := by rfl, base := frameBase
    placed := by rfl, rsp := by rfl
    supplied := by
      change initializerSelection.store.writeBytes = initializerSelection.store.writeBytes
      rfl }

private def beforeArgument : State := initializerNormal.result
private theorem initializer_falls_through_to_argument :
    beforeArgument.rip = addressOf codeBase (outputRange argumentOutput).start := by decide

private def argumentFetchStep := stepAccess beforeArgument.machine argumentFetchDescriptor
private def afterArgumentFetch : MachineState :=
  match argumentFetchStep with | .ran state => state | .rejected _ => beforeArgument.machine
private def argumentFetchReached := beforeArgument.machine.noteContext thread .thread
private def argumentFetchResolved : argumentFetchReached.memory.ResolvedAccess
    argumentFetchDescriptor.provenance argumentFetchDescriptor.range :=
  (prepareAccess argumentFetchReached.memory argumentFetchDescriptor).toOption.get (by decide)
private def argumentFetchComplete : CompleteCommitted argumentFetchDescriptor :=
  (policy.oracle.answerResolved argumentFetchReached argumentFetchDescriptor
    argumentFetchResolved).get (by decide)
private def argumentFetchObserved :=
  observedBytes argumentFetchResolved (indeterminate argumentFetchReached argumentFetchDescriptor)
private def argumentDecoded : DecodedSite beforeArgument.rip argumentFetchObserved :=
  (DecodedSite.check beforeArgument.rip argumentFetchObserved).toOption.get (by decide)
private def argumentFetchRun :
    AccessRun beforeArgument.machine afterArgumentFetch argumentFetchDescriptor :=
  { policy, operation := operation argumentFetchDescriptor, context := thread
    contextKind := .thread, cause, faultAt := noFault
    sequence := .single argumentFetchDescriptor, selected := by rfl
    substeps_exact := by rfl, noFault := by rfl, ran := by rfl
    resolved := argumentFetchResolved, prepared := by rfl, complete := argumentFetchComplete
    answerResolved := by simp [argumentFetchComplete, argumentFetchReached]
    clean := by decide }
private def argumentFetch : FetchedSite beforeArgument afterArgumentFetch :=
  { descriptor := argumentFetchDescriptor, run := argumentFetchRun
    writeData, indeterminate, memoryOracle := by rfl, intent := by rfl
    initialization := by rfl, ledgerEffect := by rfl, authorityEffect := by rfl
    address := by
      simpa [argumentFetchDescriptor, fetchDescriptor] using
        congrArg Address.numeric initializer_falls_through_to_argument.symm
    placed := ⟨codeBase, by rfl⟩, site := argumentDecoded, noTrailing := by decide }
private def argumentSite : SourceFetch.SourceSite source beforeArgument afterArgumentFetch :=
  { output := argumentOutput, outputAt := by rfl, fetch := argumentFetch
    space := by rfl, observed := by rfl, base := codeBase, baseExact := by rfl
    codeRootOffset := 0, loadedImageBase := codeBase.toNat
    placementExact := by rfl, descriptorStart := by rfl }

private def argumentStep := stepAccess afterArgumentFetch argumentDescriptor
private def afterArgument : MachineState :=
  match argumentStep with | .ran state => state | .rejected _ => afterArgumentFetch
private def argumentReached := afterArgumentFetch.noteContext thread .thread
private def argumentResolved : argumentReached.memory.ResolvedAccess
    argumentDescriptor.provenance argumentDescriptor.range :=
  (prepareAccess argumentReached.memory argumentDescriptor).toOption.get (by decide)
private def argumentComplete : CompleteCommitted argumentDescriptor :=
  (policy.oracle.answerResolved argumentReached argumentDescriptor argumentResolved).get (by decide)
private def argumentRun : AccessRun afterArgumentFetch afterArgument argumentDescriptor :=
  { policy, operation := operation argumentDescriptor, context := thread
    contextKind := .thread, cause, faultAt := noFault
    sequence := .single argumentDescriptor, selected := by rfl
    substeps_exact := by rfl, noFault := by rfl, ran := by rfl
    resolved := argumentResolved, prepared := by rfl, complete := argumentComplete
    answerResolved := by simp [argumentComplete, argumentReached]
    clean := by decide }
private def argumentAccess : MemoryAccess argumentSite.fetch afterArgument :=
  { descriptor := argumentDescriptor, run := argumentRun, policy := by rfl
    context := by rfl, contextKind := by rfl, cause := by rfl
    fetchContext := by rfl, dataContext := by rfl, space := by rfl, ordering := by rfl
    ledgerEffect := by rfl, authorityEffect := by rfl }
private def argumentNormal : StoreNormal source beforeArgument afterArgumentFetch afterArgument :=
  { instruction := .argument argumentSelection, site := argumentSite, selected := by rfl
    access := argumentAccess, intent := by rfl, initialization := by rfl
    producesInitialized := by rfl, range := by rfl, base := frameBase
    placed := by rfl, rsp := by rfl
    supplied := by
      change argumentPayload = argumentPayload
      rfl }

example : initializerNormal.instruction.payload = le32 0 := by decide
example : argumentNormal.instruction.payload = List.replicate 8 0 := by decide
example : afterArgument.events.length = 4 := by decide
example : beforeArgument.machine = afterInitializer := by rfl

example (i : Nat) (hi : i < 4) :
    afterInitializer.memory.cellAt? frameAlloc (initializerSelection.store.range.start + i) =
      some (0, true) := by
  have payload : initializerNormal.instruction.payload = List.replicate 4 0 := by decide
  have root : initializerNormal.access.descriptor.provenance.root = frameAlloc := by rfl
  have start : initializerNormal.access.descriptor.range.start =
      initializerSelection.store.range.start := by decide
  have width : initializerNormal.access.descriptor.range.size = 4 := by decide
  have covered : initializerNormal.access.descriptor.range.Covers
      (initializerSelection.store.range.start + i) := by
    simp only [ByteRange.covers_def, start, width]
    omega
  have cell := initializerNormal.stored_cell _ covered
  rw [payload, root, start] at cell
  rw [Nat.add_sub_cancel_left, List.getElem?_replicate, if_pos hi] at cell
  exact cell

example (i : Nat) (hi : i < 8) :
    afterArgument.memory.cellAt? frameAlloc (argumentSelection.result.range.start + i) =
      some (0, true) := by
  have payload : argumentNormal.instruction.payload = List.replicate 8 0 := by decide
  have root : argumentNormal.access.descriptor.provenance.root = frameAlloc := by rfl
  have start : argumentNormal.access.descriptor.range.start =
      argumentSelection.result.range.start := by decide
  have width : argumentNormal.access.descriptor.range.size = 8 := by decide
  have covered : argumentNormal.access.descriptor.range.Covers
      (argumentSelection.result.range.start + i) := by
    simp only [ByteRange.covers_def, start, width]
    omega
  have cell := argumentNormal.stored_cell _ covered
  rw [payload, root, start] at cell
  rw [Nat.add_sub_cancel_left, List.getElem?_replicate, if_pos hi] at cell
  exact cell

end Grass.Tests.ISA.X86.ExecutionFramePrefix
