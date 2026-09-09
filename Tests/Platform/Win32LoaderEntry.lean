import Grass.Platform.Win32.LoaderEntry
import Tests.Artifact.PE.ImageWriter
import Tests.Assembly.SourceLinkedImage

/-! Initialization fixtures and an actual Grass Hello World source-to-plan
consumer. These validate model construction; they do not execute a Windows
binary or establish physical loader correspondence. -/

namespace Grass.Tests.Win32LoaderEntry

open Grass.Core Grass.Memory Grass.Std.Logical Grass.Artifact
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

private def allocationSupply : FreshSupply AllocTag := .initial
private def storageSupply : FreshSupply StorageTag := .initial
private def epoch : EpochId := (FreshSupply.initial : FreshSupply EpochTag).fresh.1
private def thread : ContextId := (FreshSupply.initial : FreshSupply ContextTag).fresh.1
private def peer : ContextId := (FreshSupply.initial : FreshSupply ContextTag).fresh.2.fresh.1
private def stackId : AllocId := allocationSupply.fresh.1
private def stackStorage : StorageId := storageSupply.fresh.1
private def returnAddress : BitVec 64 := 0x7ff01000

/-- The fixture supplies initialized return bytes and leaves other stack cells absent. -/
private def stackBacking : BackingRecord :=
  { capacity := 256
    bytes := ByteStore.empty.write 168
      (Binary.writeLittleEndian (count := 8) returnAddress).toList true }

private def stackRecord : AllocationRecord :=
  { extent := ⟨0, 256⟩, epoch, space := .cpuVirtual, source := .stack
    owners := [thread], permission := .readWrite, live := true
    backing := stackStorage, origin := 0, base := some 0x100000 }

private def environmentMemoryWith? (backing : BackingRecord) : Option MemoryState := do
  let memory ← MemoryState.empty.installBacking? stackStorage backing
  memory.allocate? stackId stackRecord

private def environmentMemory : MemoryState := (environmentMemoryWith? stackBacking).getD .empty

private def environment : MachineState :=
  { MachineState.initial environmentMemory with
    contexts := FiniteMap.empty.insert thread .thread |>.insert peer .externalAgent }

/-- Advance public supplies; no nominal identity representation is inspected. -/
private def identitiesFrom : Nat → FreshSupply AllocTag → FreshSupply StorageTag → List RegionIdentity
  | 0, _, _ => []
  | count + 1, allocations, storages =>
    { allocation := allocations.fresh.1, storage := storages.fresh.1, epoch } ::
      identitiesFrom count allocations.fresh.2 storages.fresh.2

/-- Shared initialized stack and identity inputs for bounded loader consumers. -/
def inputsFor (plan : PE.ImagePlan) (targets : ImportTargets) : EntryInputs :=
  { environment, thread, independentContext := peer
    identities := identitiesFrom (plan.layout.placed.length + 1)
      allocationSupply.fresh.2 storageSupply.fresh.2
    targets
    stack := { allocation := stackId, offset := 168, frameBytes := 80, returnAddress }
    gpr := fun register => if register = .rsp then 0x1000a8 else 0x1234
    rflags := 0x202 }

/-- Executable checks are validation, not theorem authority. -/
private def check (label : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError ("Windows loader fixture failed: " ++ label))

#eval do
  let some plan := (PE.prepareImage _root_.Tests.Artifact.PE.ImageWriter.description).toOption
    | throw (IO.userError "fixture plan refused")
  let image : ImageInput := ⟨plan, (PE.writeImage plan).toHostBytes, rfl⟩
  let inputs := inputsFor plan (.fromList [.fromList [0x7ff02000]])
  check "valid initialization" (initialize? image inputs).isSome
  check "missing imports" (!(initialize? image { inputs with targets := .empty }).isSome)
  check "extra symbol target" (!(initialize? image { inputs with targets := .fromList [.fromList [1, 2]] }).isSome)
  check "missing identities" (!(initialize? image { inputs with identities := [] }).isSome)
  check "reused allocation" (!(initialize? image { inputs with
    identities := identitiesFrom (plan.layout.placed.length + 1) allocationSupply storageSupply }).isSome)
  check "independent context" (!(initialize? image { inputs with independentContext := thread }).isSome)
  check "direction flag" (!(initialize? image { inputs with rflags := 0x602 }).isSome)
  check "frame below stack" (!(initialize? image { inputs with
    stack := { inputs.stack with frameBytes := 169 } }).isSome)
  check "wrong return bytes" (!(initialize? image { inputs with
    stack := { inputs.stack with returnAddress := returnAddress + 1 } }).isSome)
  let some uninitialized := environmentMemoryWith? { stackBacking with bytes := .empty }
    | throw (IO.userError "uninitialized stack setup refused")
  check "uninitialized return bytes" (!(initialize? image { inputs with
    environment := { inputs.environment with memory := uninitialized } }).isSome)
  let some patches := importPatches? plan inputs.targets
    | throw (IO.userError "import fixture refused")
  let some region := (assignedRegions image inputs patches).head?
    | throw (IO.userError "image fixture empty")
  let violation : AuditViolation :=
    { class_ := .outOfBounds, context := thread, range := ⟨0, 1⟩
      provenance :=
        { space := .cpuVirtual
          root := region.allocId
          epoch := region.epoch
          source := .imageMapping
          rootExtent := ⟨0, region.bytes.length⟩
          path := [] } }
  let history := { inputs.environment with
    violations := inputs.environment.violations.append violation }
  check "historical allocation reference" (!decide (HistoryFresh history [region]))
  check "historical reference initialization refusal"
    (!(initialize? image { inputs with environment := history }).isSome)
  check "uninitialized stack retained" (decide (environmentMemory.cellAt? stackId 0 = none))
  check "physical alias" (!decide (CpuPlacementsDisjoint (stackId, stackRecord)
    (allocationSupply.fresh.2.fresh.1, stackRecord)))
  check "IAT exact little endian plus framing" (decide (patchContents [⟨100, 0x0807060504030201⟩] 99
    (.fromList [42, 0, 0, 0, 0, 0, 0, 0, 0, 43]) =
      Vec.fromList [42, 1, 2, 3, 4, 5, 6, 7, 8, 43]))
/-- Production source linking is reused; no Python/C or handwritten instruction
bytes stand in for the authored Grass program in this integration fixture. -/
def helloPlanFrom? (source : List Char) : Option PE.ImagePlan := do
  let body ← (Grass.Assembly.SourceInput.extractHelloSourceChars source).toOption
  let frame ← Grass.Assembly.SourceFrame.derive? body
  let splice ← Grass.Assembly.SourceSplice.derive? frame 0
  let statics ← Grass.Assembly.StaticSection.layout?
    (Grass.Tests.Assembly.SourceLinkedImage.staticTable Grass.Tests.Assembly.SourceLinkedImage.payload)
    Grass.Tests.Assembly.SourceLinkedImage.staticName 0x40000040
  let requests ← Grass.Assembly.SourceImportRequests.resolve? splice "kernel32.dll"
  let linked ← Grass.Assembly.SourceLinkedImage.build? splice statics
    { codeName := Grass.Tests.Assembly.SourceLinkedImage.codeName
      codeCharacteristics := 0x60000020
      pdataName := Grass.Tests.Assembly.SourceLinkedImage.pdataName
      xdataName := Grass.Tests.Assembly.SourceLinkedImage.xdataName } requests
  pure linked.plan

/-- Model fixture over the checked-in source embedding; the native exporter
supplies freshly read source to `helloPlanFrom?` instead. -/
def helloPlan? : Option PE.ImagePlan := helloPlanFrom? Grass.Tests.Assembly.SourceResolve.authored

/-- Initialize the exact source-linked PE using explicit three-symbol target data. -/
def helloEntry? : Option (Nat × Bool) := do
  let plan ← helloPlan?
  let input : ImageInput := ⟨plan, (PE.writeImage plan).toHostBytes, rfl⟩
  let loaded ← initialize? input (inputsFor plan
    (.fromList [.fromList [0x7ff01000, 0x7ff02000, 0x7ff03000]]))
  pure (loaded.initialState.rip.toNat,
    loaded.initialState.gpr .rax == 0x1234 && loaded.initialState.rflags == 0x202)

#eval check "actual Grass source entry" (helloEntry? == some (0x140001000, true))

end Grass.Tests.Win32LoaderEntry
