import Grass.ISA.AArch64.BootControl

/-! Generic first-boot instruction partitions, not a spike or a CPU program path.
Each run begins at the same fresh snapshot and performs just one execute read. -/
namespace Tests.ISA.AArch64.BootControl

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.AArch64 Grass.ISA.AArch64.BootControl
open Grass.Platform.BareMetal Grass.Platform.BareMetal.BootMemory

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def code : AllocId := (FreshSupply.initial : FreshSupply AllocTag).fresh.1
private def store : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def epoch : EpochId := (FreshSupply.initial : FreshSupply EpochTag).fresh.1
private def core : ContextId := (FreshSupply.initial : FreshSupply ContextTag).fresh.1

-- CBZ X0,+8; SVC #0; NOP (unsupported by this bounded body decoder).
private def bytes : ByteSeq := [0x40, 0, 0, 0xb4, 1, 0, 0, 0xd4, 0x1f, 0x20, 3, 0xd5]
private def backing : BackingRecord := ⟨12, ByteStore.empty.write 0 bytes true⟩
private def allocation : AllocationRecord :=
  { extent := ⟨0, 12⟩, epoch := epoch, space := .cpuPhysical, source := .imageMapping
    owners := [core], permission := .readExecute, live := true, backing := store
    origin := 0, base := some 0x1000 }

private def memory? : Option MemoryState := do
  let memory ← MemoryState.empty.installBacking? store backing
  memory.allocate? code allocation

example : memory?.isSome := by decide
private def before : MachineState := MachineState.initial (memory?.getD .empty)
private def physicalMap : PhysicalMap := ⟨[⟨0x1000, 12⟩], []⟩
private def admission : Admission physicalMap core before :=
  (admit? physicalMap core before).get (by decide)

private def vocabulary : AdmittedVocabulary :=
  { addressSpaces := ⟨[BootFetch.ramSpace]⟩
    faultClasses := ⟨[]⟩, allocationSources := ⟨[.imageMapping]⟩
    provenanceStepKinds := ⟨[]⟩, auditViolationClasses := ⟨AuditViolationClass.emittedByTransition⟩
    obligationKinds := ⟨[]⟩, orderingModes := ⟨[]⟩, orderingScopes := ⟨[]⟩
    contextKinds := ⟨[.thread]⟩, initializationJustifications := ⟨[]⟩
    atomicityJustifications := ⟨[]⟩, faultVisibilityRules := ⟨[]⟩
    grantKinds := ⟨[]⟩, protocols := ⟨[]⟩ }

private def policy : BootFetch.Policy :=
  { operation :=
      { profile := ⟨⟨"aarch64.boot.control.fixture"⟩, 1, vocabulary⟩
        requiredFacets := [.memoryEffects, .faults, .restartability, .ordering]
        oracle := .ofMemory (fun _ _ => []) (fun _ _ _ => 0)
        authorities := []
        violationClassesDeclared := by decide
        vocabularyWellFormed := by decide }
    ramDeclared := rfl, faults := [], cause := ⟨⟨"aarch64-first-fetch"⟩⟩ }

private def cbzEntry : Entry admission code ⟨0, 4⟩ :=
  (entry? admission code ⟨0, 4⟩).get (by decide)
private def svcEntry : Entry admission code ⟨4, 4⟩ :=
  (entry? admission code ⟨4, 4⟩).get (by decide)
private def nopEntry : Entry admission code ⟨8, 4⟩ :=
  (entry? admission code ⟨8, 4⟩).get (by decide)
private def shortEntry : Entry admission code ⟨0, 3⟩ :=
  (entry? admission code ⟨0, 3⟩).get (by decide)
private def unalignedEntry : Entry admission code ⟨1, 4⟩ :=
  (entry? admission code ⟨1, 4⟩).get (by decide)

private def cpu (pc : BitVec 64) (value : BitVec 64) : Cpu := ⟨fun _ => value, pc, 0b1010⟩

-- Real observed CBZ bytes select different successors for arbitrary operand values.
example : (match run .a64LittleEndian policy cbzEntry (cpu 0x1000 0) with
    | .fetched fetch _ (.ok decoded) =>
      match decoded.outcome with
      | .next after => after.pc == 0x1008 && fetch.read.after.events.length == 1
      | _ => false
    | _ => false) = true := by decide

example : (match run .a64LittleEndian policy cbzEntry (cpu 0x1000 1) with
    | .fetched _ _ (.ok decoded) =>
      match decoded.outcome with
      | .next after => after.pc == 0x1004 && after.nzcv == 0b1010
      | _ => false
    | _ => false) = true := by decide

-- SVC produces a request with an actual fetched word, not normal continuation.
example : (match run .a64LittleEndian policy svcEntry (cpu 0x1004 77) with
    | .fetched fetch _ (.ok decoded) =>
      match decoded.outcome with
      | .supervisor immediate => immediate == 0 && decoded.body.source.word == 0xd4000001 &&
          fetch.read.after.events.length == 1
      | _ => false
    | _ => false) = true := by decide

-- Unsupported instruction retains the completed read and its exact endpoint.
example : (match run .a64LittleEndian policy nopEntry (cpu 0x1008 0) with
    | .fetched fetch _ (.error (.unsupported word)) =>
        word == 0xd503201f && fetch.read.after.events.length == 1
    | _ => false) = true := by decide

example : (match run .a64LittleEndian policy cbzEntry (cpu 0x1004 0) with
    | .pcMismatch _ => true | _ => false) = true := by decide
example : (match run .a64LittleEndian policy shortEntry (cpu 0x1000 0) with
    | .fetchFailure .width => true | _ => false) = true := by decide
example : (match run .a64LittleEndian policy unalignedEntry (cpu 0x1001 0) with
    | .fetchFailure .alignment => true | _ => false) = true := by decide

#print axioms Grass.ISA.AArch64.BootControl.Decoded.parsed
#print axioms Grass.ISA.AArch64.BootControl.Decoded.cases
#print axioms Grass.ISA.AArch64.BootControl.fetched_observation
#print axioms Grass.ISA.AArch64.BootControl.run_fetchFailure
#print axioms Grass.ISA.AArch64.BootControl.run_fetched

end Tests.ISA.AArch64.BootControl
