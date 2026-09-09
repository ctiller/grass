import Grass.ISA.X86.Execution.MemoryWrite
import Grass.ISA.X86.Execution.ReadValue32
import Grass.ISA.X86.Execution.MoveNormal

/-!
# Source-free normal x86 memory MOV receipts

This module ties a canonical MOV encoding, a completed instruction fetch, and
one continuous checked memory access together.  It is deliberately source-free:
callers that obtain the instruction from an assembler retain that provenance in
their own adapter.  These are conditional clean normal receipts; they do not
exclude a distinct faulting or rejected execution.
-/

namespace Grass.ISA.X86.Execution.MemoryMoveNormal

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution

/-- The bounded RSP-relative memory MOV forms used by this execution seam. -/
inductive Instruction where
  | store32Imm (displacement immediate : BitVec 32)
  | store64SignedImm32 (displacement immediate : BitVec 32)
  | load32 (displacement : BitVec 32) (destination : Gpr)
deriving DecidableEq, Repr

namespace Instruction

/-- The RSP-relative operand encoded by every form in this bounded family. -/
def operand : Instruction → MemOperand
  | .store32Imm displacement _ => .base .rsp displacement
  | .store64SignedImm32 displacement _ => .base .rsp displacement
  | .load32 displacement _ => .base .rsp displacement

/-- The displacement represented by the actual instruction form. -/
def displacement : Instruction → BitVec 32
  | .store32Imm displacement _ => displacement
  | .store64SignedImm32 displacement _ => displacement
  | .load32 displacement _ => displacement

/-- The data-access width represented by the instruction form. -/
def width : Instruction → Nat
  | .store32Imm _ _ | .load32 _ _ => 4
  | .store64SignedImm32 _ _ => 8

/-- Store payload, absent exactly for the load form. -/
def payload? : Instruction → Option ByteSeq
  | .store32Imm _ immediate => some (le32 immediate)
  | .store64SignedImm32 _ immediate =>
      some (le64 (BitVec.signExtend 64 immediate))
  | .load32 _ _ => none

/-- The canonical encoder selected for this exact instruction form. -/
def encode? : Instruction → Option InsnEncoding
  | .store32Imm displacement immediate => movMem32Imm32 (.base .rsp displacement) immediate
  | .store64SignedImm32 displacement immediate =>
      movMem64Imm32 (.base .rsp displacement) immediate
  | .load32 displacement destination =>
      BasicInstructions.movReg32Mem destination (.base .rsp displacement)

/-- The architectural effective address for the family’s RSP-relative operand. -/
def effectiveAddress (before : State) (instruction : Instruction) : MachineAddress :=
  before.gpr .rsp + BitVec.signExtend 64 instruction.displacement

/-- A canonical encoder production, retained rather than treating an arbitrary
encoding with equal bytes as this MOV form. -/
structure Encoding (instruction : Instruction) where
  encoding : InsnEncoding
  exact : instruction.encode? = some encoding

theorem Encoding.decodes {instruction : Instruction} (encoded : Encoding instruction)
    (rest : ByteSeq) :
    decodeInsn (encoded.encoding.toBytes ++ rest) = .ok (encoded.encoding, rest) := by
  cases instruction with
  | store32Imm displacement immediate =>
      exact movMem32Imm32_decodes encoded.exact rest
  | store64SignedImm32 displacement immediate =>
      exact movMem64Imm32_decodes encoded.exact rest
  | load32 displacement destination =>
      exact BasicInstructions.movReg32Mem_decodes encoded.exact rest

theorem payload_width {instruction : Instruction} {payload : ByteSeq}
    (exact : instruction.payload? = some payload) : payload.length = instruction.width := by
  cases instruction with
  | store32Imm displacement immediate =>
      simp [payload?] at exact
      rw [← exact, length_le32]
      rfl
  | store64SignedImm32 displacement immediate =>
      simp [payload?] at exact
      rw [← exact, length_le64]
      rfl
  | load32 displacement destination => simp [payload?] at exact

end Instruction

/-- A completed fetched immediate-memory MOV and its actual continuous write. -/
structure StoreNormal (instruction : Instruction) (encoded : Instruction.Encoding instruction)
    (before : State) (afterFetch afterData : MachineState) where
  fetch : FetchedSite before afterFetch
  /-- Fetch code is a CPU-virtual instruction access. -/
  fetchSpace : fetch.descriptor.space = .cpuVirtual
  encodingExact : fetch.site.encoding = encoded.encoding
  access : MemoryAccess fetch afterData
  /-- `StoreNormal.unplaced_impossible` excludes a base-less data resolution. -/
  placed : ∃ base, access.run.resolved.allocation.base = some base
  intent : access.descriptor.intent = .write
  initialization : access.descriptor.initialization = .readsNothing
  producesInitialized : access.descriptor.producesInitialized = true
  address : access.descriptor.address = .numeric (Instruction.effectiveAddress before instruction)
  width : access.descriptor.range.size = instruction.width
  payload : ByteSeq
  payloadExact : instruction.payload? = some payload
  supplied : fetch.writeData
    (afterFetch.noteContext access.run.context access.run.contextKind) access.descriptor = payload

namespace StoreNormal

/-- The checked data preparation supplies the actual placed CPU address and
nonwrapping allocation bound for this store. -/
theorem placement {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : StoreNormal instruction encoded before afterFetch afterData) :
    ∃ base, receipt.access.run.resolved.allocation.base = some base ∧
      FitsAllocation base receipt.access.run.resolved.allocation.extent.stop ∧
      receipt.access.descriptor.address = .numeric
        (addressOf base receipt.access.descriptor.range.start) := by
  obtain ⟨base, placed⟩ := receipt.placed
  obtain ⟨fits, address⟩ := prepared_base_fits_and_address receipt.access.run.prepared placed
  exact ⟨base, placed, fits, address⟩

/-- `StoreNormal.unplaced_impossible` rules out a base-less data resolution. -/
theorem unplaced_impossible {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : StoreNormal instruction encoded before afterFetch afterData)
    (unplaced : receipt.access.run.resolved.allocation.base = none) : False := by
  obtain ⟨base, placed⟩ := receipt.placed
  rw [unplaced] at placed
  contradiction

/-- The actual oracle completion wrote precisely the typed immediate payload. -/
theorem written_exact {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : StoreNormal instruction encoded before afterFetch afterData) :
    receipt.access.run.complete.committed.written = some receipt.payload :=
  receipt.access.written_exact receipt.payload receipt.intent
    (by rw [receipt.width]; exact Instruction.payload_width receipt.payloadExact)
    receipt.supplied

/-- The actual data memory is the checked commit of the typed store payload. -/
theorem memory_written {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : StoreNormal instruction encoded before afterFetch afterData) :
    afterData.memory =
      (afterFetch.noteContext receipt.access.run.context receipt.access.run.contextKind).memory.writeResolved
        receipt.access.run.resolved receipt.payload true
        (receipt.access.run.complete.committed.writtenFits _ receipt.written_exact) := by
  have committed := Grass.Memory.commitResolved_of_eq_some
    (afterFetch.noteContext receipt.access.run.context receipt.access.run.contextKind).memory
    receipt.access.descriptor receipt.access.run.resolved receipt.access.run.complete.committed.written
    receipt.access.run.complete.committed.writtenFits receipt.payload receipt.written_exact
  exact receipt.access.memory_committed.trans
    (by simpa only [receipt.producesInitialized] using committed)

/-- Every covered cell in the actual result is the supplied MOV payload and is
initialized. -/
theorem stored_cell {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : StoreNormal instruction encoded before afterFetch afterData) (offset : Nat)
    (covered : receipt.access.descriptor.range.Covers offset) :
    afterData.memory.cellAt? receipt.access.descriptor.provenance.root offset =
      (receipt.payload[offset - receipt.access.descriptor.range.start]?).map (·, true) := by
  rw [receipt.memory_written]
  apply MemoryState.cellAt?_writeResolved_of_covers
  have payloadWidth : receipt.payload.length = receipt.access.descriptor.range.size := by
    rw [receipt.width]
    exact Instruction.payload_width receipt.payloadExact
  simpa [payloadWidth] using covered

/-- The source-free normal architectural result keeps the actual data machine,
advances by the actual fetched encoding, and applies ordinary MOV flags. -/
def result {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : StoreNormal instruction encoded before afterFetch afterData) : State :=
  { before with
    machine := afterData
    rip := receipt.fetch.site.fallthroughRip
    rflags := completedMoveRflags before }

theorem gpr_frame {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : StoreNormal instruction encoded before afterFetch afterData) :
    receipt.result.gpr = before.gpr := rfl

end StoreNormal

/-- A completed fetched `mov r32, [rsp + disp32]` and its actual initialized
continuous read. -/
structure LoadNormal (instruction : Instruction) (encoded : Instruction.Encoding instruction)
    (before : State) (afterFetch afterData : MachineState) where
  displacement : BitVec 32
  destination : Gpr
  instructionExact : instruction = .load32 displacement destination
  fetch : FetchedSite before afterFetch
  fetchSpace : fetch.descriptor.space = .cpuVirtual
  encodingExact : fetch.site.encoding = encoded.encoding
  access : MemoryAccess fetch afterData
  /-- Data-side preparation must use a present allocation base. -/
  placed : ∃ base, access.run.resolved.allocation.base = some base
  intent : access.descriptor.intent = .read
  initialization : access.descriptor.initialization = .allBytesInitialized
  address : access.descriptor.address = .numeric (Instruction.effectiveAddress before instruction)
  width : access.descriptor.range.size = 4

namespace LoadNormal

/-- The checked data preparation supplies the actual placed CPU address and
nonwrapping allocation bound for this load. -/
theorem placement {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : LoadNormal instruction encoded before afterFetch afterData) :
    ∃ base, receipt.access.run.resolved.allocation.base = some base ∧
      FitsAllocation base receipt.access.run.resolved.allocation.extent.stop ∧
      receipt.access.descriptor.address = .numeric
        (addressOf base receipt.access.descriptor.range.start) := by
  obtain ⟨base, placed⟩ := receipt.placed
  obtain ⟨fits, address⟩ := prepared_base_fits_and_address receipt.access.run.prepared placed
  exact ⟨base, placed, fits, address⟩

/-- `LoadNormal.unplaced_impossible` rules out a base-less data resolution. -/
theorem unplaced_impossible {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : LoadNormal instruction encoded before afterFetch afterData)
    (unplaced : receipt.access.run.resolved.allocation.base = none) : False := by
  obtain ⟨base, placed⟩ := receipt.placed
  rw [unplaced] at placed
  contradiction

/-- The actual initialized DWORD read attached to this normal MOV receipt. -/
def read {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : LoadNormal instruction encoded before afterFetch afterData) :
    ReadValue32 receipt.access.run :=
  { writeData := receipt.fetch.writeData
    indeterminate := receipt.fetch.indeterminate
    memoryOracle := receipt.access.memoryOracle
    reads := by rw [receipt.intent]; rfl
    writes := by rw [receipt.intent]; rfl
    width := receipt.width
    initialization := receipt.initialization }

/-- The source-free normal architectural result writes the actual observed
DWORD through x86’s canonical zero-extending write-back. -/
def result {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : LoadNormal instruction encoded before afterFetch afterData) : State :=
  { before.withGpr receipt.destination
      (writeBack .w32 (before.gpr receipt.destination) receipt.read.value) with
    machine := afterData
    rip := receipt.fetch.site.fallthroughRip
    rflags := completedMoveRflags before }

theorem loaded_value {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : LoadNormal instruction encoded before afterFetch afterData) :
    BitVec.setWidth 32 (receipt.result.gpr receipt.destination) = receipt.read.value := by
  simp only [result, State.withGpr, ↓reduceIte]
  exact writeBack.read_back_w32 _ _

theorem clears_high {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : LoadNormal instruction encoded before afterFetch afterData) :
    BitVec.extractLsb' 32 32 (receipt.result.gpr receipt.destination) = 0 := by
  simp only [result, State.withGpr, ↓reduceIte]
  exact writeBack.w32_clears_high _ _

theorem memory_frame {instruction : Instruction} {encoded : Instruction.Encoding instruction}
    {before : State} {afterFetch afterData : MachineState}
    (receipt : LoadNormal instruction encoded before afterFetch afterData) :
    receipt.result.machine.memory = before.machine.memory :=
  (receipt.access.read_state_frame (by rw [receipt.intent]; rfl)).1

end LoadNormal
end Grass.ISA.X86.Execution.MemoryMoveNormal
