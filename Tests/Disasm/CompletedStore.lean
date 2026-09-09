import Grass.Disasm.FetchedEntry
import Grass.Disasm.CompletedViolation
import Grass.Disasm.Spatial
import Tests.Artifact.PE.Imported
import Tests.Op.FakeIsa

/-! A closed declared model run, not a Windows loader or a proof that C source
is defined. The test uses FakeIsa's explicitly unproved memory-profile package.
Root allocation write authority and the caller's narrower object are distinct. -/
namespace Grass.Tests.Disasm.CompletedStore

open Grass.Core Grass.Artifact.PE Grass.Disasm Grass.Memory Grass.Memory.SpatialAccess
  Grass.Op Grass.Std.Logical Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Tests.FakeIsa
open Tests.Artifact.PE.Imported
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def code : ByteSeq := [0xc7, 0x41, 0x08, 0x2a, 0, 0, 0]
def input : Grass.Std.Logical.ByteArray :=
  Vec.fromList ((externalFixture.set 440 7).toList.take 512 ++ code ++
    externalFixture.toList.drop 519)
def parsed? : Option (CheckedImportedImage input) :=
  match checkImportedImage input with | .done parsed _ => some parsed | _ => none
theorem parsed_ok : parsed?.isSome := by decide
def entry? : Option (Entry.Entry input) :=
  (Entry.selectEntry (parsed?.get parsed_ok) 0x1000).toOption
theorem entry_ok : entry?.isSome := by decide
def entry := entry?.get entry_ok
example : entry.bytes = code := by decide

def codeBacking : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
def dataBacking : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.2.fresh.1
def codeProv : Provenance := { constProv with rootExtent := ⟨0, 7⟩ }
def dataProv : Provenance := { bufferProv with rootExtent := ⟨0, 16⟩ }
def objectProv : Provenance := { dataProv with path :=
  [{ kind := .object, label := ⟨"caller-array-eight-bytes"⟩, extent := ⟨0, 8⟩ }] }
def codeRecord : AllocationRecord :=
  { extent := ⟨0, 7⟩, epoch := epoch₀, space := .cpuVirtual, source := .imageMapping
    owners := [thread₀], permission := .readExecute, live := true, backing := codeBacking
    origin := 0, base := some 0x50001000 }
def dataRecord : AllocationRecord :=
  { extent := ⟨0, 16⟩, epoch := epoch₀, space := .cpuVirtual, source := .virtualAlloc
    owners := [thread₀], permission := .readWrite, live := true, backing := dataBacking
    origin := 0, base := some 0x2000 }
def memory? : Option MemoryState := do
  let memory ← MemoryState.empty.installBacking? codeBacking ⟨7, ByteStore.empty.write 0 code true⟩
  let memory ← memory.installBacking? dataBacking ⟨16, ByteStore.empty.write 0 (List.replicate 16 0) true⟩
  memory.allocateAll? [(constAlloc, codeRecord), (bufferAlloc, dataRecord)]
theorem memory_ok : memory?.isSome := by decide
def before : State :=
  { machine := .initial (memory?.get memory_ok), gpr := fun r => if r = .rcx then 0x2000 else 0
    rip := 0x50001000, rflags := 0 }
def fetchDescriptor := acc codeProv ⟨0, 7⟩ 0x50001000 .execute .readExecute true false
def writeDescriptor := acc dataProv ⟨8, 4⟩ 0x2008 .write .readWrite false true
inductive ProbeOp where | fetch | write
instance : HasOperationFacets ProbeOp where
  facets op :=
    { memoryEffects := some (.single (match op with | .fetch => fetchDescriptor | .write => writeDescriptor))
      faults := some [.pageFault], restartability := some .restartable, ordering := some .plain }
def cause : EventCause := ⟨⟨"declared-c7-probe"⟩⟩
def fetchStep := step policy before.machine (SomeOperation.of ProbeOp.fetch) thread₀ .thread cause
def afterFetch? : Option MachineState := match fetchStep with | .ran s => some s | _ => none
theorem fetch_ran : afterFetch?.isSome := by decide
def afterFetch := afterFetch?.get fetch_ran
def fetchReached := before.machine.noteContext thread₀ .thread
def fetchResolved := (prepareAccess fetchReached.memory fetchDescriptor).toOption.get (by decide)
def fetchComplete := (policy.oracle.answerResolved fetchReached fetchDescriptor fetchResolved).get (by decide)
def observed := observedBytes fetchResolved (indeterminateByte fetchReached fetchDescriptor)
def site := (DecodedSite.check before.rip observed).toOption.get (by decide)
def fetch : FetchedSite before afterFetch :=
  { descriptor := fetchDescriptor
    run :=
      { policy := policy, operation := SomeOperation.of ProbeOp.fetch
        context := thread₀, contextKind := .thread, cause := cause
        faultAt := fun _ => .none, sequence := .single fetchDescriptor
        selected := by rfl, substeps_exact := by rfl, noFault := by rfl, ran := by rfl
        resolved := fetchResolved, prepared := by rfl, complete := fetchComplete
        answerResolved := by simp [fetchComplete, fetchReached], clean := by decide }
    writeData := storedBytes, indeterminate := indeterminateByte, memoryOracle := by rfl
    intent := by rfl, initialization := by rfl, ledgerEffect := by rfl, authorityEffect := by rfl
    address := by rfl, placed := ⟨0x50001000, by rfl⟩, site := site, noTrailing := by decide }
def binding? := (FetchedEntry.check entry 0x50000000 fetch).toOption
theorem binding_ok : binding?.isSome := by decide
def binding := binding?.get binding_ok
example := FetchedEntry.original_event binding

def payload : MachineState → AccessDescriptor → ByteSeq := fun _ _ => [42, 0, 0, 0]
def writePolicy : StepPolicy := { policy with oracle := .ofMemory payload indeterminateByte }
def writeStep := step writePolicy afterFetch (SomeOperation.of ProbeOp.write) thread₀ .thread cause
def afterWrite? : Option MachineState := match writeStep with | .ran s => some s | _ => none
theorem write_ran : afterWrite?.isSome := by decide
def afterWrite := afterWrite?.get write_ran
def writeReached := afterFetch.noteContext thread₀ .thread
def writeResolved := (prepareAccess writeReached.memory writeDescriptor).toOption.get (by decide)
def writeComplete := (writePolicy.oracle.answerResolved writeReached writeDescriptor writeResolved).get (by decide)
def writeRun : AccessRun afterFetch afterWrite writeDescriptor :=
  { policy := writePolicy, operation := SomeOperation.of ProbeOp.write
    context := thread₀, contextKind := .thread, cause := cause
    faultAt := fun _ => .none, sequence := .single writeDescriptor
    selected := by rfl, substeps_exact := by rfl, noFault := by rfl, ran := by rfl
    resolved := writeResolved, prepared := by rfl, complete := writeComplete
    answerResolved := by simp [writeComplete, writeReached], clean := by decide }
def objectResolved := (afterFetch.memory.resolveAccess? objectProv objectProv.extent).toOption.get (by decide)
def object : PlacedObject afterFetch.memory objectProv :=
  { resolved := objectResolved, base := 0x2000, placed := by rfl, noWrap := by decide }
def candidate := (StoreCandidate.check before.rip code fetch.afterState).toOption.get (by decide)
example : objectProv.extent = ⟨0, 8⟩ := by decide
example : candidate.address = 0x2008 := by decide
example : outsideIndex? object (Spatial.footprint candidate) = some 0 := by decide
example : OutsideByte object (Spatial.footprint candidate) 0 :=
  outsideIndex?_sound object (Spatial.footprint candidate) (by decide)
example := writeRun.completed_event

def completion : StoreCompletion before afterFetch afterWrite fetch :=
  { candidate := candidate, candidateChecked := by rfl
    descriptor := writeDescriptor, run := writeRun
    writeData := payload, indeterminate := indeterminateByte, memoryOracle := by rfl
    sameContext := by rfl, sameContextKind := by rfl, sameCause := by rfl
    sameProfile := by rfl, sameRequiredFacets := by rfl, sameAuthorities := by rfl
    sameCompatibility := by rfl, descriptorContext := by rfl
    descriptorAddress := by rfl, space := by rfl, descriptorWidth := by rfl
    intent := by rfl, requiredPermission := by rfl, alignment := by rfl
    ordering := by decide, initialization := by rfl, producesInitialized := by rfl
    observations := by rfl, ledgerEffect := by rfl, authorityEffect := by rfl
    placed := ⟨0x2000, by rfl⟩, written := by decide }
example := completion.memory_written
example : before.machine.memory.byteAt? bufferAlloc 8 = some 0 := by decide
example : afterWrite.memory.byteAt? bufferAlloc 8 = some 42 := by decide

def callerResolved := (before.machine.memory.resolveAccess? objectProv objectProv.extent).toOption.get (by decide)
def callerObject : PlacedObject before.machine.memory objectProv :=
  { resolved := callerResolved, base := 0x2000, placed := by rfl, noWrap := by decide }
def witness? := ((CompletedViolation.check completion callerObject).toOption.bind id)
theorem witness_exists : witness?.isSome := by decide
def witness := witness?.get witness_exists
example : witness.index = 0 := by decide
example := CompletedViolation.original_fetch_and_outside_write binding completion callerObject witness

-- The physically authorized root is larger than the separately declared object.
-- Making that root the declared referent changes the claim; it is not a repair
-- of the original object8 violation.
def rootResolved := (before.machine.memory.resolveAccess? dataProv dataProv.extent).toOption.get (by decide)
def rootObject : PlacedObject before.machine.memory dataProv :=
  { resolved := rootResolved, base := 0x2000, placed := by rfl, noWrap := by decide }
example : ((CompletedViolation.check completion rootObject).toOption.bind id).isNone := by decide

-- An unrelated object's numerical placement cannot be paired with this pointer.
def codeResolved := (before.machine.memory.resolveAccess? codeProv codeProv.extent).toOption.get (by decide)
def codeObject : PlacedObject before.machine.memory codeProv :=
  { resolved := codeResolved, base := 0x50001000, placed := by rfl, noWrap := by decide }
example : (match CompletedViolation.check completion codeObject with
  | .error .pointerDoesNotStartAtObject => true | _ => false) = true := by decide

end Grass.Tests.Disasm.CompletedStore
