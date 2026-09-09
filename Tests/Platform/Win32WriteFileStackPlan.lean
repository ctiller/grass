import Grass.Platform.Win32.WriteFileStackPlan
import Grass.Platform.Win32.GetStdHandleStackPlan
import Tests.Platform.Win32LoaderEntry
import Tests.Artifact.PE.ImageWriter

/-!
# Constructive WriteFile stack-plan regression

This is a bounded model fixture.  It loads an opaque PE containing one indirect
CALL, executes that CALL through the production factory, and resolves only the
WriteFile buffer, count, and fifth arguments.  Return and home slots are never
written down here; the shared producer must derive them from the actual receipt.
No native Windows execution or export correspondence is claimed.
-/

namespace Grass.Tests.Win32WriteFileStackPlan

open Grass.Core Grass.Memory Grass.Std.Logical Grass.Artifact
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader
open Grass.Platform.Win32.WriteFile

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- At the fixture layout the CALL falls through at RVA 0x1006 and reads the
single IAT slot at RVA 0x2028, hence the checked signed displacement 0x1022. -/
def callDescription : PE.ExecutableImageDescription :=
  { Tests.Artifact.PE.ImageWriter.description with
    entryPoint := { sectionIndex := 0, offset := 0 }
    sections := .fromList [
      { name := Tests.Artifact.PE.ImageWriter.textName
        contents := .fromList [0xff, 0x15, 0x22, 0x10, 0, 0]
        characteristics := 0x60000020 }]
    imports := .fromList [{ Tests.Artifact.PE.ImageWriter.kernel32 with
      symbols := .fromList [{ name := Text.utf8 "WriteFile" }] }] }

def plan := (PE.prepareImage callDescription).toOption.get (by decide)
def image : ImageInput := ⟨plan, (PE.writeImage plan).toHostBytes, rfl⟩

theorem actual_iat_rva : plan.layout.importAddressRva? 0 0 = some 0x2028 := by decide

/-- Initialize semantic bytes and the nullable fifth argument in the existing
fixture stack by following its actual allocation and backing identities. -/
def preparedInputs? : Option EntryInputs := do
  let original := Grass.Tests.Win32LoaderEntry.inputsFor plan
    (.fromList [.fromList [0x7ff02020]])
  let stackRecord ← original.environment.memory.allocations.lookup original.stack.allocation
  let stackBacking ← original.environment.memory.backings.lookup stackRecord.backing
  let stackBase ← stackRecord.base
  let bytes := stackBacking.bytes
    |>.write 0 [11, 22, 33] true
    |>.write 16 [0, 0, 0, 0] true
    |>.write 176 [0, 0, 0, 0] true
    |>.write 200 (List.replicate 8 0) true
  let installed ← MemoryState.empty.installBacking? stackRecord.backing
    { stackBacking with bytes }
  let memory ← installed.allocate? original.stack.allocation stackRecord
  pure { original with
    environment := { original.environment with memory }
    gpr := fun register =>
      if register = .rsp then stackBase + 168
      else if register = .rcx then 0x55
      else if register = .rdx then stackBase
      else if register = .r8 then 3
      else if register = .r9 then stackBase + 16
      else 0x1234 }

def inputs := preparedInputs?.get (by decide)
def loaded := (initialize? image inputs).get (by decide)
def initial := loaded.initialState
def cpu := (Cpu.policy? loaded initial).get (by decide)
def called := (CallFactory.call cpu initial).toOption.get (by decide)
def binding : WriteFile.CallPolicy loaded called.receipt :=
  WriteFile.CallPolicy.ofFactory (by rfl) called

theorem actual_call_target : called.result.rip = 0x7ff02020 := by decide
theorem actual_call_entry_rsp : called.result.gpr .rsp = 0x1000a0 := by decide

/-- Deterministic checked argument resolution used only for buffer, count, and
fifth argument construction. -/
def resolveArgument? (memory : MemoryState) (argument : Argument) :
    Option (Resolved memory argument) := do
  let access ← memory.resolveAccess? argument.provenance argument.range |>.toOption
  match placed : access.allocation.base with
  | none => none
  | some base =>
    if fits : FitsAllocation base access.allocation.extent.stop then
      pure { toResolvedAccess := access, base, placed, noWrap := fits }
    else none

/-- Convert the loader's finite placement invariant into the lookup-shaped
facts required by `Prepared`.  This bridge is shared by both request fixtures. -/
theorem placement_of_valid {memory : MemoryState} (valid : PlacementValid memory) :
    ∀ root allocation, memory.allocations.lookup root = some allocation →
      allocation.live = true → allocation.space = .cpuVirtual →
      ∃ base, allocation.base = some base ∧ FitsAllocation base allocation.extent.stop := by
  intro root allocation found live cpuSpace
  have member : (root, allocation) ∈ memory.allocations.entries :=
    FiniteMap.mem_of_lookup found
  have placed := valid.2.1 (root, allocation) member live cpuSpace
  split at placed
  · contradiction
  · rename_i base placedEq
    exact ⟨base, placedEq, placed⟩

theorem separation_of_valid {memory : MemoryState} (valid : PlacementValid memory) :
    ∀ left right a b leftBase rightBase,
      memory.allocations.lookup left = some a → memory.allocations.lookup right = some b →
      left ≠ right → a.live = true → b.live = true →
      a.space = .cpuVirtual → b.space = .cpuVirtual →
      a.base = some leftBase → b.base = some rightBase →
      (a.extent.shift leftBase.toNat).Disjoint (b.extent.shift rightBase.toNat) := by
  intro left right a b leftBase rightBase foundLeft foundRight different
    liveLeft liveRight cpuLeft cpuRight baseLeft baseRight
  have leftMember : (left, a) ∈ memory.allocations.entries :=
    FiniteMap.mem_of_lookup foundLeft
  have rightMember : (right, b) ∈ memory.allocations.entries :=
    FiniteMap.mem_of_lookup foundRight
  have separated := valid.2.2 (left, a) leftMember (right, b) rightMember
    different liveLeft liveRight cpuLeft cpuRight
  rw [baseLeft, baseRight] at separated
  simp only [ByteRange.Disjoint, ByteRange.shift, ByteRange.stop] at *
  dsimp at *
  omega

def stackRecord := inputs.environment.memory.allocations.lookup inputs.stack.allocation |>.get (by decide)
def stackProvenance := allocationProvenance inputs.stack.allocation stackRecord

def request : Request :=
  { handle := 0x55, requested := 3, bytes := .fromList [11, 22, 33]
    buffer := ⟨stackProvenance, ⟨0, 3⟩⟩
    countSlot := ⟨stackProvenance, ⟨16, 4⟩⟩ }

def bufferResolved := resolveArgument? called.result.machine.memory request.buffer |>.get (by decide)
def countResolved := resolveArgument? called.result.machine.memory request.countSlot |>.get (by decide)
def fifthArgument : Argument := ⟨stackProvenance, ⟨200, 8⟩⟩
def fifthResolved := resolveArgument? called.result.machine.memory fifthArgument |>.get (by decide)

def prepared : Prepared called.result.machine.memory request where
  buffer := bufferResolved
  countSlot := countResolved
  bufferSize := by decide
  bytesSize := by decide
  countSize := by decide
  bufferCPU := by decide
  countCPU := by decide
  separated := by decide
  dedicated := (show PlacementValid called.result.machine.memory by decide).1
  placement := placement_of_valid (show PlacementValid called.result.machine.memory by decide)
  allocationSeparation := separation_of_valid
    (show PlacementValid called.result.machine.memory by decide)
  input := by decide

def entry : Abi.Entry called.result request where
  prepared := prepared
  overlappedSlot := fifthArgument
  overlappedResolved := fifthResolved
  overlappedCPU := by decide
  handle := by decide
  bufferAddress := by decide
  requestedLow := by decide
  countAddress := by decide
  overlappedAddress := by decide
  overlappedNull := by decide

/-- A second actual execution points the count argument into the home area.
The common return/home plan remains derivable, while the WriteFile extension
must reject the semantic overlap. -/
def overlapInputs : EntryInputs :=
  { inputs with gpr := fun register =>
      if register = .r9 then 0x1000b0 else inputs.gpr register }
def overlapLoaded := (initialize? image overlapInputs).get (by decide)
def overlapInitial := overlapLoaded.initialState
def overlapCpu := (Cpu.policy? overlapLoaded overlapInitial).get (by decide)
def overlapCalled := (CallFactory.call overlapCpu overlapInitial).toOption.get (by decide)
def overlapBinding : WriteFile.CallPolicy overlapLoaded overlapCalled.receipt :=
  WriteFile.CallPolicy.ofFactory (by rfl) overlapCalled

def overlapRequest : Request :=
  { request with countSlot := ⟨stackProvenance, ⟨176, 4⟩⟩ }
def overlapBufferResolved :=
  resolveArgument? overlapCalled.result.machine.memory overlapRequest.buffer |>.get (by decide)
def overlapCountResolved :=
  resolveArgument? overlapCalled.result.machine.memory overlapRequest.countSlot |>.get (by decide)
def overlapFifthResolved :=
  resolveArgument? overlapCalled.result.machine.memory fifthArgument |>.get (by decide)

def overlapPrepared : Prepared overlapCalled.result.machine.memory overlapRequest where
  buffer := overlapBufferResolved
  countSlot := overlapCountResolved
  bufferSize := by decide
  bytesSize := by decide
  countSize := by decide
  bufferCPU := by decide
  countCPU := by decide
  separated := by decide
  dedicated := (show PlacementValid overlapCalled.result.machine.memory by decide).1
  placement := placement_of_valid
    (show PlacementValid overlapCalled.result.machine.memory by decide)
  allocationSeparation := separation_of_valid
    (show PlacementValid overlapCalled.result.machine.memory by decide)
  input := by decide

def overlapEntry : Abi.Entry overlapCalled.result overlapRequest where
  prepared := overlapPrepared
  overlappedSlot := fifthArgument
  overlappedResolved := overlapFifthResolved
  overlappedCPU := by decide
  handle := by decide
  bufferAddress := by decide
  requestedLow := by decide
  countAddress := by decide
  overlappedAddress := by decide
  overlappedNull := by decide

/-- The synthetic target is WriteFile.  Sending the same actual CALL binding
through the GetStdHandle plan door below tests only reuse of the generic Win64
return/home producer; it makes no GetStdHandle dispatch or endpoint claim. -/
def commonResult :=
  GetStdHandle.StackPlanFactory.deriveLoaded? binding
def writeFileResult :=
  Abi.StackPlanFactory.deriveLoaded? binding entry

def sharedPlanFields? : Option Bool := do
  let common ← commonResult.toOption
  let write ← writeFileResult.toOption
  pure (write.continuation == common.continuation &&
    write.returnSlot == common.returnSlot &&
    write.returnResolved.base == common.returnResolved.base &&
    write.homeSlot == common.homeSlot &&
    write.homeResolved.base == common.homeResolved.base)

theorem constructive_writeFile_plan_exists : writeFileResult.toOption.isSome := by decide
theorem shared_return_home_fields_are_identical : sharedPlanFields? = some true := by decide

def overlapResult :=
  Abi.StackPlanFactory.deriveLoaded? overlapBinding overlapEntry

def refused_for_home_count_overlap : Bool :=
  match overlapResult with
  | .error .homeCountOverlap => true
  | _ => false

theorem semantic_home_overlap_is_specific : refused_for_home_count_overlap = true := by decide

end Grass.Tests.Win32WriteFileStackPlan
