import Grass.Platform.Win32.WriteFileAbi
import Grass.Platform.Win32.LoaderEntry

/-!
# Checked WriteFile argument preparation

This factory derives a `WriteFile` request and its entry evidence from one
actual callee-entry machine state.  The caller supplies the semantic buffer,
canonical count-slot provenance, input bytes, and fifth-argument provenance;
the factory supplies no source, provider, or native-call assumption.
-/

namespace Grass.Platform.Win32.WriteFile.EntryFactory

open Grass.ABI Grass.Core Grass.Memory Grass.Std.Logical
open Grass.ISA.X86
open Grass.Platform.Win32.Loader

/-- Every refusal is a finite observation failure of the supplied state or
arguments. -/
inductive Failure where
  | bufferResolve (reason : MemoryState.ResolveFailure)
  | countResolve (reason : MemoryState.ResolveFailure)
  | fifthResolve (reason : MemoryState.ResolveFailure)
  | bufferUnplaced
  | countUnplaced
  | fifthUnplaced
  | bufferWrap
  | countWrap
  | fifthWrap
  | placement
  | bufferSize
  | bytesSize
  | countSize
  | bufferCPU
  | countCPU
  | fifthCPU
  | bufferCountOverlap
  | input
  | bufferAddress
  | countAddress
  | fifthAddress
  | fifthNull
deriving Repr

/-- The semantic request is fixed by the actual RCX/R8 values and the supplied
canonical argument provenance and input snapshot. -/
def requestOf (state : Execution.State) (buffer countSlot : Argument) (bytes : Vec Byte) : Request :=
  { handle := state.gpr .rcx
    requested := BitVec.setWidth 32 (state.gpr .r8)
    buffer
    countSlot
    bytes }

@[simp] theorem requestOf_handle (state : Execution.State) (buffer countSlot : Argument)
    (bytes : Vec Byte) : (requestOf state buffer countSlot bytes).handle = state.gpr .rcx := rfl

@[simp] theorem requestOf_requested (state : Execution.State) (buffer countSlot : Argument)
    (bytes : Vec Byte) :
    (requestOf state buffer countSlot bytes).requested = BitVec.setWidth 32 (state.gpr .r8) := rfl

@[simp] theorem requestOf_buffer (state : Execution.State) (buffer countSlot : Argument)
    (bytes : Vec Byte) : (requestOf state buffer countSlot bytes).buffer = buffer := rfl

@[simp] theorem requestOf_countSlot (state : Execution.State) (buffer countSlot : Argument)
    (bytes : Vec Byte) : (requestOf state buffer countSlot bytes).countSlot = countSlot := rfl

@[simp] theorem requestOf_bytes (state : Execution.State) (buffer countSlot : Argument)
    (bytes : Vec Byte) : (requestOf state buffer countSlot bytes).bytes = bytes := rfl

private def resolve? (memory : MemoryState) (argument : Argument)
    (resolveFailure : MemoryState.ResolveFailure → Failure) (unplacedFailure wrapFailure : Failure) :
    Except Failure (Resolved memory argument) := do
  let access ← memory.resolveAccess? argument.provenance argument.range |>.mapError resolveFailure
  match placed : access.allocation.base with
  | none => .error unplacedFailure
  | some base =>
      if fits : FitsAllocation base access.allocation.extent.stop then
        .ok { toResolvedAccess := access, base, placed, noWrap := fits }
      else .error wrapFailure

private theorem placement_of_valid {memory : MemoryState} (valid : PlacementValid memory) :
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

private theorem separation_of_valid {memory : MemoryState} (valid : PlacementValid memory) :
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

/-- Check and construct the complete semantic and Win64 fifth-argument entry
receipt from the actual machine and supplied canonical arguments.  The
buffer/count disjointness here supports `Prepared`; separation of the fifth
slot from semantic ranges is checked by the later stack-plan factory. -/
private def prepareExact? (state : Execution.State) (buffer countSlot : Argument) (bytes : Vec Byte)
    (fifthSlot : Argument) : Except Failure
      { entry : Abi.Entry state (requestOf state buffer countSlot bytes) //
        entry.overlappedSlot = fifthSlot } :=
  let request := requestOf state buffer countSlot bytes
  match resolve? state.machine.memory buffer .bufferResolve .bufferUnplaced .bufferWrap with
  | .error failure => .error failure
  | .ok bufferResolved =>
    match resolve? state.machine.memory countSlot .countResolve .countUnplaced .countWrap with
    | .error failure => .error failure
    | .ok countResolved =>
      match resolve? state.machine.memory fifthSlot .fifthResolve .fifthUnplaced .fifthWrap with
      | .error failure => .error failure
      | .ok fifthResolved =>
        if placement : PlacementValid state.machine.memory then
        if bufferSize : buffer.range.size = request.requested.toNat then
        if bytesSize : bytes.length = request.requested.toNat then
        if countSize : countSlot.range.size = 4 then
        if bufferCPU : buffer.provenance.space = .cpuVirtual then
        if countCPU : countSlot.provenance.space = .cpuVirtual then
        if fifthCPU : fifthSlot.provenance.space = .cpuVirtual then
        if separated : bufferResolved.physical.Disjoint countResolved.physical then
        if input : InputMatches state.machine.memory request then
        if bufferAddress : state.gpr .rdx = addressOf bufferResolved.base buffer.range.start then
        if countAddress : state.gpr .r9 = addressOf countResolved.base countSlot.range.start then
        if fifthAddress : (addressOf fifthResolved.base fifthSlot.range.start).toNat =
            (state.gpr .rsp).toNat + Abi.overlappedSlotOffset then
        if fifthNull : Abi.InitializedNullQword fifthResolved then
          .ok ⟨
            { prepared :=
                { buffer := bufferResolved
                  countSlot := countResolved
                  bufferSize := bufferSize
                  bytesSize := bytesSize
                  countSize := countSize
                  bufferCPU := bufferCPU
                  countCPU := countCPU
                  separated := separated
                  dedicated := placement.1
                  placement := placement_of_valid placement
                  allocationSeparation := separation_of_valid placement
                  input := input }
              overlappedSlot := fifthSlot
              overlappedResolved := fifthResolved
              overlappedCPU := fifthCPU
              handle := rfl
              bufferAddress := bufferAddress
              requestedLow := rfl
              countAddress := countAddress
              overlappedAddress := fifthAddress
              overlappedNull := fifthNull }, rfl⟩
        else .error .fifthNull
        else .error .fifthAddress
        else .error .countAddress
        else .error .bufferAddress
        else .error .input
        else .error .bufferCountOverlap
        else .error .fifthCPU
        else .error .countCPU
        else .error .bufferCPU
        else .error .countSize
        else .error .bytesSize
        else .error .bufferSize
        else .error .placement

/-- Construct the checked entry from the exact request and supplied arguments.
The internal result retains fifth-slot identity at construction time. -/
def prepare? (state : Execution.State) (buffer countSlot : Argument) (bytes : Vec Byte)
    (fifthSlot : Argument) : Except Failure (Abi.Entry state (requestOf state buffer countSlot bytes)) :=
  (prepareExact? state buffer countSlot bytes fifthSlot).map Subtype.val

/-- A successful checked result retains the supplied fifth argument. -/
theorem prepare?_fifthSlot {state : Execution.State} {buffer countSlot : Argument}
    {bytes : Vec Byte} {fifthSlot : Argument} {entry : Abi.Entry state (requestOf state buffer countSlot bytes)}
    (success : prepare? state buffer countSlot bytes fifthSlot = .ok entry) :
    entry.overlappedSlot = fifthSlot := by
  unfold prepare? at success
  cases result : prepareExact? state buffer countSlot bytes fifthSlot with
  | error failure => simp [result, Except.map] at success
  | ok prepared =>
    have same : prepared.val = entry := by simpa [result, Except.map] using success
    rw [← same]
    exact prepared.property

end Grass.Platform.Win32.WriteFile.EntryFactory
