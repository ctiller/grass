import Grass.Assembly.SourceFetch
import Grass.Assembly.FrameMemorySource
import Grass.ISA.X86.Execution.MemoryWrite
import Grass.ISA.X86.Execution.ReadValue32
import Grass.Assembly.Store32Addressing
import Grass.Assembly.FrameArgumentAddressing
import Grass.ISA.X86.Execution.MemoryMoveNormal

/-! Source-selected frame memory MOV normal branches. Source resolution supplies
the instruction occurrence, operand, and payload; actual fetched/data runs supply
the observation and backing transition. These conditional receipts do not exclude
faults, rejections, or interruptions and do not establish entry reachability. -/

namespace Grass.Assembly.FrameMemoryExecution
open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open SourceResolve

/-- The two source-derived immediate stores needed by the frame path. -/
inductive StoreInstruction {frame : SourceFrame.Result} {rootOffset : Nat}
    (source : SourceResolve.Result frame rootOffset) where
  | local (selection : StoreSelection source)
  | argument (selection : ArgumentSelection source)

namespace StoreInstruction

/-- The source selection determines a source-free typed x86 MOV. -/
def isa {frame rootOffset} {source : SourceResolve.Result frame rootOffset} :
    StoreInstruction source → MemoryMoveNormal.Instruction
  | .local selection => .store32Imm (BitVec.ofNat 32 selection.store.displacement)
      selection.store.input.value
  | .argument selection => .store64SignedImm32 (BitVec.ofNat 32 selection.result.displacement)
      (BitVec.ofNat 32 selection.result.value)

def output {frame rootOffset} {source : SourceResolve.Result frame rootOffset} :
    StoreInstruction source → SourceResolve.Output source.splice source.symbols source.codeBase
  | .local selection => selection.output
  | .argument selection => selection.output

def payload {frame rootOffset} {source : SourceResolve.Result frame rootOffset} :
    StoreInstruction source → ByteSeq
  | .local selection => selection.store.writeBytes
  | .argument selection => le64 (BitVec.signExtend 64 (BitVec.ofNat 32 selection.result.value))

def encoding {frame rootOffset} {source : SourceResolve.Result frame rootOffset} :
    StoreInstruction source → InsnEncoding
  | .local selection => selection.store.encoding
  | .argument selection => selection.result.encoding

theorem output_encoding {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    (instruction : StoreInstruction source) : instruction.output.encoding = instruction.encoding := by
  cases instruction with
  | «local» selection => exact selection.encodingExact
  | argument selection => exact selection.encodingExact

/-- `encoded` retains the successful production encoder equation from source resolution. -/
def encoded {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    (instruction : StoreInstruction source) : MemoryMoveNormal.Instruction.Encoding instruction.isa where
  encoding := instruction.encoding
  exact := by
    cases instruction with
    | «local» selection =>
        have input := (Store32.localAddress_of_resolve? selection.primitiveExact)
        obtain ⟨_, _, inputExact, _, _, _⟩ := input
        change movMem32Imm32 selection.store.operand selection.store.input.value = _
        rw [inputExact]
        exact Store32.encoding_equation_of_resolve? selection.primitiveExact
    | argument selection => exact selection.result.encodingExact

theorem isa_payload {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    (instruction : StoreInstruction source) : instruction.isa.payload? = some instruction.payload := by
  cases instruction <;> rfl

def range {frame rootOffset} {source : SourceResolve.Result frame rootOffset} :
    StoreInstruction source → ByteRange
  | .local selection => selection.store.range
  | .argument selection => selection.result.range

def rspRootOffset {frame rootOffset} {source : SourceResolve.Result frame rootOffset} :
    StoreInstruction source → Nat
  | .local selection => selection.store.rspRootOffset
  | .argument selection => selection.result.rootOffset

def displacement {frame rootOffset} {source : SourceResolve.Result frame rootOffset} :
    StoreInstruction source → Nat
  | .local selection => selection.store.displacement
  | .argument selection => selection.result.displacement

theorem payload_width {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    (instruction : StoreInstruction source) : instruction.payload.length = instruction.range.size := by
  cases instruction with
  | «local» selection => exact length_le32 _
  | argument selection => exact length_le64 _

theorem range_start {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    (instruction : StoreInstruction source) :
    instruction.range.start = instruction.rspRootOffset + instruction.displacement := by
  cases instruction <;> rfl

theorem isa_width {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    (instruction : StoreInstruction source) : instruction.range.size = instruction.isa.width := by
  cases instruction <;> rfl

theorem isa_displacement {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    (instruction : StoreInstruction source) :
    instruction.isa.displacement = BitVec.ofNat 32 instruction.displacement := by
  cases instruction <;> rfl

theorem signed_displacement {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    (instruction : StoreInstruction source) :
    BitVec.signExtend 64 (BitVec.ofNat 32 instruction.displacement) =
      BitVec.ofNat 64 instruction.displacement := by
  cases instruction with
  | «local» selection => exact Store32.signExtend_displacement_of_resolve? selection.primitiveExact
  | argument selection =>
      change BitVec.signExtend 64 (BitVec.ofNat 32 selection.result.displacement) = _
      unfold BitVec.signExtend
      rw [selection.result.signed_displacement]
      rfl

end StoreInstruction

/-- The actual fetched source store and its continuous initialized data write.
`frameOffset` locates the runtime frame within the actual allocation; source
coordinates determine only the displacement and width. -/
structure StoreNormal {frame : SourceFrame.Result} {rootOffset : Nat}
    (source : SourceResolve.Result frame rootOffset)
    (before : State) (afterFetch afterStore : MachineState) where
  instruction : StoreInstruction source
  site : SourceFetch.SourceSite source before afterFetch
  selected : site.output = instruction.output
  access : MemoryAccess site.fetch afterStore
  intent : access.descriptor.intent = .write
  initialization : access.descriptor.initialization = .readsNothing
  producesInitialized : access.descriptor.producesInitialized = true
  frameOffset : Nat
  range : access.descriptor.range =
    ⟨frameOffset + instruction.displacement, instruction.range.size⟩
  base : MachineAddress
  placed : access.run.resolved.allocation.base = some base
  rsp : before.gpr .rsp = addressOf base frameOffset
  supplied : access.writeData
    (afterFetch.noteContext access.run.context access.run.contextKind) access.descriptor =
      instruction.payload

namespace StoreNormal

/-- `selected_encoding` joins source selection to the actual canonical decode. -/
theorem selected_encoding {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterStore : MachineState}
    (receipt : StoreNormal source before afterFetch afterStore) :
    receipt.site.fetch.site.encoding = receipt.instruction.encoding := by
  rw [receipt.site.encoding_exact, receipt.selected, receipt.instruction.output_encoding]

/-- `address_exact` derives agreement with the actual source-selected operand. -/
theorem address_exact {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterStore : MachineState}
    (receipt : StoreNormal source before afterFetch afterStore) :
    receipt.access.descriptor.address = .numeric (before.gpr .rsp +
      BitVec.signExtend 64 (BitVec.ofNat 32 receipt.instruction.displacement)) :=
  receipt.access.address_of_rsp receipt.base receipt.frameOffset
    receipt.instruction.displacement receipt.placed receipt.rsp
    (by rw [receipt.range])
    receipt.instruction.signed_displacement

/-- `execution` injects the source-selected witnesses into the single x86 normal
memory-MOV interpretation. Assembly defines no competing register transfer. -/
def execution {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterStore : MachineState}
    (receipt : StoreNormal source before afterFetch afterStore) :
    MemoryMoveNormal.StoreNormal receipt.instruction.isa receipt.instruction.encoded
      before afterFetch afterStore :=
  { fetch := receipt.site.fetch
    fetchSpace := receipt.site.space
    encodingExact := receipt.selected_encoding
    access := receipt.access
    placed := ⟨receipt.base, receipt.placed⟩
    intent := receipt.intent
    initialization := receipt.initialization
    producesInitialized := receipt.producesInitialized
    address := by simpa [MemoryMoveNormal.Instruction.effectiveAddress,
      receipt.instruction.isa_displacement] using receipt.address_exact
    width := by rw [receipt.range]; exact receipt.instruction.isa_width
    payload := receipt.instruction.payload
    payloadExact := receipt.instruction.isa_payload
    supplied := receipt.supplied }

/-- `written_exact` derives the source payload from the actual oracle answer. -/
theorem written_exact {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterStore : MachineState}
    (receipt : StoreNormal source before afterFetch afterStore) :
    receipt.access.run.complete.committed.written = some receipt.instruction.payload :=
  receipt.access.written_exact receipt.instruction.payload receipt.intent
    (by rw [receipt.range]; exact receipt.instruction.payload_width) receipt.supplied

/-- `memory_written` derives the initialized backing mutation from the actual
checked transition. It is a consequence of `memory_committed`, not an input. -/
theorem memory_written {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterStore : MachineState}
    (receipt : StoreNormal source before afterFetch afterStore) :
    afterStore.memory =
      (afterFetch.noteContext receipt.access.run.context receipt.access.run.contextKind).memory.writeResolved
        receipt.access.run.resolved receipt.instruction.payload true
        (receipt.access.run.complete.committed.writtenFits _ receipt.written_exact) := by
  have committed := Grass.Memory.commitResolved_of_eq_some
    (afterFetch.noteContext receipt.access.run.context receipt.access.run.contextKind).memory
    receipt.access.descriptor receipt.access.run.resolved receipt.access.run.complete.committed.written
    receipt.access.run.complete.committed.writtenFits receipt.instruction.payload receipt.written_exact
  exact receipt.access.memory_committed.trans
    (by simpa only [receipt.producesInitialized] using committed)

/-- `stored_cell` derives each byte and initialization bit in the actual result. -/
theorem stored_cell {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterStore : MachineState}
    (receipt : StoreNormal source before afterFetch afterStore) (offset : Nat)
    (covered : receipt.access.descriptor.range.Covers offset) :
    afterStore.memory.cellAt? receipt.access.descriptor.provenance.root offset =
      (receipt.instruction.payload[offset - receipt.access.descriptor.range.start]?).map (·, true) := by
  rw [receipt.memory_written]
  apply MemoryState.cellAt?_writeResolved_of_covers
  have width : receipt.instruction.payload.length = receipt.access.descriptor.range.size := by
    rw [receipt.range]; exact receipt.instruction.payload_width
  simpa [width] using covered

/-- The normal result uses the actual store state and ordinary MOV completion. -/
def result {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterStore : MachineState}
    (receipt : StoreNormal source before afterFetch afterStore) : State :=
  receipt.execution.result

theorem gpr_frame {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterStore : MachineState}
    (receipt : StoreNormal source before afterFetch afterStore) : receipt.result.gpr = before.gpr := rfl

end StoreNormal

/-- An actual source-selected DWORD local load with an initialized data read.
`frameOffset` is the runtime allocation-local RSP offset, independent of the
static source root coordinate. -/
structure LoadNormal {frame : SourceFrame.Result} {rootOffset : Nat}
    (source : SourceResolve.Result frame rootOffset)
    (before : State) (afterFetch afterLoad : MachineState) where
  selection : LoadSelection source
  site : SourceFetch.SourceSite source before afterFetch
  selected : site.output = selection.output
  access : MemoryAccess site.fetch afterLoad
  intent : access.descriptor.intent = .read
  initialization : access.descriptor.initialization = .allBytesInitialized
  frameOffset : Nat
  range : access.descriptor.range =
    ⟨frameOffset + selection.result.address.displacement, selection.result.address.width⟩
  base : MachineAddress
  placed : access.run.resolved.allocation.base = some base
  rsp : before.gpr .rsp = addressOf base frameOffset

namespace LoadNormal

/-- `rsp_toNat` derives the nonwrapping runtime frame origin from the actual
prepared load's allocation bounds and placement. -/
theorem rsp_toNat {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) :
    (before.gpr .rsp).toNat = receipt.base.toNat + receipt.frameOffset := by
  have fits := (prepared_base_fits_and_address receipt.access.run.prepared receipt.placed).1
  have within := receipt.access.run.resolved.coordinates.withinView
  have width := receipt.selection.result.load_width
  have frameLt : receipt.frameOffset < receipt.access.run.resolved.allocation.extent.stop := by
    have rangeStop := congrArg ByteRange.stop receipt.range
    change receipt.selection.result.address.width = 4 at width
    simp only [ByteRange.stop] at rangeStop
    simp only [ByteRange.Contains, ByteRange.stop] at within
    change receipt.frameOffset < receipt.access.run.resolved.allocation.extent.start +
      receipt.access.run.resolved.allocation.extent.size
    omega
  rw [receipt.rsp, toNat_addressOf fits frameLt]

def isa {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) : MemoryMoveNormal.Instruction :=
  .load32 (BitVec.ofNat 32 receipt.selection.result.address.displacement)
    receipt.selection.result.destination

def encoded {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) : MemoryMoveNormal.Instruction.Encoding receipt.isa :=
  ⟨receipt.selection.result.encoding, receipt.selection.result.encodingExact⟩

/-- `selected_encoding` joins the source load operand to the actual decode. -/
theorem selected_encoding {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) :
    receipt.site.fetch.site.encoding = receipt.selection.result.encoding := by
  rw [receipt.site.encoding_exact, receipt.selected, receipt.selection.encodingExact]

/-- `read` constructs the value witness from this exact initialized data run. -/
def read {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) : ReadValue32 receipt.access.run :=
  { writeData := receipt.access.writeData
    indeterminate := receipt.access.indeterminate
    memoryOracle := receipt.access.memoryOracle
    reads := by rw [receipt.intent]; rfl
    writes := by rw [receipt.intent]; rfl
    width := by rw [receipt.range]; exact receipt.selection.result.load_width
    initialization := receipt.initialization }

/-- `address_exact` derives agreement with the resolved source load operand. -/
theorem address_exact {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) :
    receipt.access.descriptor.address = .numeric (before.gpr .rsp +
      BitVec.signExtend 64 (BitVec.ofNat 32 receipt.selection.result.address.displacement)) := by
  apply receipt.access.address_of_rsp receipt.base receipt.frameOffset
    receipt.selection.result.address.displacement receipt.placed receipt.rsp
  · rw [receipt.range]
  · unfold BitVec.signExtend
    rw [receipt.selection.result.address.signed_displacement]
    rfl

/-- `execution` supplies the exact source load to the shared x86 interpretation. -/
def execution {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) :
    MemoryMoveNormal.LoadNormal receipt.isa receipt.encoded before afterFetch afterLoad :=
  { displacement := BitVec.ofNat 32 receipt.selection.result.address.displacement
    destination := receipt.selection.result.destination
    instructionExact := rfl
    fetch := receipt.site.fetch
    fetchSpace := receipt.site.space
    encodingExact := receipt.selected_encoding
    access := receipt.access
    placed := ⟨receipt.base, receipt.placed⟩
    intent := receipt.intent
    initialization := receipt.initialization
    address := receipt.address_exact
    width := by rw [receipt.range]; exact receipt.selection.result.load_width }

/-- The DWORD register write uses the exact observed value and canonical
zero-extension rule; the memory machine is the actual read result. -/
def result {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) : State :=
  receipt.execution.result

theorem loaded_value {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) :
    BitVec.setWidth 32 (receipt.result.gpr receipt.selection.result.destination) = receipt.read.value := by
  exact receipt.execution.loaded_value

theorem clears_high {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) :
    BitVec.extractLsb' 32 32 (receipt.result.gpr receipt.selection.result.destination) = 0 := by
  exact receipt.execution.clears_high

theorem memory_frame {frame rootOffset} {source : SourceResolve.Result frame rootOffset}
    {before : State} {afterFetch afterLoad : MachineState}
    (receipt : LoadNormal source before afterFetch afterLoad) :
    receipt.result.machine.memory = before.machine.memory :=
  (receipt.access.read_state_frame (by rw [receipt.intent]; rfl)).1

end LoadNormal
end Grass.Assembly.FrameMemoryExecution
