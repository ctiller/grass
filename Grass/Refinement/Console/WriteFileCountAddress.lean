import Grass.Assembly.FrameMemorySource
import Grass.Assembly.SourceFetch
import Grass.ISA.X86.Execution.BodyComputationFactory
import Grass.ISA.X86.Execution.MemoryMoveFactory
import Grass.Platform.Win32.CpuPolicy
import Grass.Platform.Win32.WriteFileArguments
import Grass.Refinement.Console.WriteFileCountArgument

/-! Source-local LEA identity for the WriteFile count argument. The argument is
computed from the selected CPU stack provenance and the source-resolved local
range. Numeric register equality never supplies provenance or access rights.
Request construction and same-call return ancestry remain endpoint obligations.
-/

namespace Grass.Refinement.Console.WriteFileCountAddress

open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Memory Grass.Platform.Win32 Grass.Platform.Win32.WriteFile

/-- The actual fixed LEA success and its exact resolved source occurrence. -/
structure SourceLea (policy : CpuAccessPolicy) {frame : SourceFrame.Result}
    {rootOffset : Nat} (source : SourceResolve.Result frame rootOffset) (before : State) where
  success : BodyComputationFactory.LeaSuccess policy before
  ran : BodyComputationFactory.lea policy before = .ok success
  item : X86ControlFlow.CodeItem
  resolved : FrameLea.Result
  sourceExact : FrameLea.resolve? frame rootOffset item = some resolved
  site : SourceFetch.SourceSite source before success.fetched.after
  fetchExact : site.fetch = success.fetched.dispatched.fetch
  originExact : site.output.origin = .source (.lea item resolved sourceExact)
  instructionSelected : success.instruction =
    ⟨.rsp, resolved.destination, BitVec.ofNat 32 resolved.address.displacement⟩

/-- This is the argument the fixed endpoint must use when constructing the
request. It carries the selected stack provenance, not one inferred from R9. -/
def SourceLea.argument {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (lea : SourceLea policy source before) : Argument :=
  ⟨policy.stack, lea.resolved.address.range⟩

theorem SourceLea.stack_selected {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {policy : CpuAccessPolicy}
    {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    (lea : SourceLea policy source before) (selected : Cpu.policy? loaded before = some policy) :
    loaded.stackProvenance? = some lea.argument.provenance := by
  obtain ⟨_, stack, _, stackSelected, _, stackExact, _⟩ := Cpu.policy?_inputs selected
  change loaded.stackProvenance? = some policy.stack
  rw [stackExact]
  exact stackSelected

theorem SourceLea.argument_width {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (lea : SourceLea policy source before) : lea.argument.range.size = 4 :=
  lea.resolved.local_width

/-- Re-selecting the fixed Windows policy at the later load retains the same
stack provenance even when its instruction cause and code location differ. -/
theorem SourceLea.load_stack_same {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {policy loadPolicy : CpuAccessPolicy}
    {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before loadBefore : State}
    (lea : SourceLea policy source before) (selected : Cpu.policy? loaded before = some policy)
    (loadSelected : Cpu.policy? loaded loadBefore = some loadPolicy) :
    loadPolicy.stack = lea.argument.provenance := by
  obtain ⟨_, stack, _, stackSelected, _, stackExact, _⟩ := Cpu.policy?_inputs loadSelected
  rw [stackExact]
  exact Option.some.inj (stackSelected.symm.trans (lea.stack_selected selected))

/-- The actual load factory uses this same argument provenance. A standalone
load receipt or a numeric pointer equality cannot discharge this conclusion. -/
theorem SourceLea.load_provenance {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {policy loadPolicy : CpuAccessPolicy}
    {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before loadBefore : State}
    (lea : SourceLea policy source before) (selected : Cpu.policy? loaded before = some policy)
    (loadSelected : Cpu.policy? loaded loadBefore = some loadPolicy)
    {fetched : FetchFactory.Success loadPolicy loadBefore}
    {instruction : MemoryMoveNormal.Instruction}
    {encoded : MemoryMoveNormal.Instruction.Encoding instruction} {afterData : MachineState}
    {receipt : MemoryMoveNormal.LoadNormal instruction encoded loadBefore fetched.after afterData}
    {fetchExact : receipt.fetch = fetched.dispatched.fetch}
    (ran : MemoryMoveFactory.memoryMove loadPolicy loadBefore =
      .ok ⟨fetched, .load encoded receipt fetchExact⟩) :
    receipt.access.descriptor.provenance = lea.argument.provenance :=
  (MemoryMoveFactory.memoryMove_load_stack ran).trans (lea.load_stack_same selected loadSelected)

/-- The destination is the source-local address formed from the actual RSP.
This equality is modular; the spatial theorem below additionally excludes wrap. -/
theorem SourceLea.argument_address {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (lea : SourceLea policy source before) (base : MachineAddress)
    (rsp : before.gpr .rsp = addressOf base lea.resolved.address.rootOffset) :
    lea.success.result.gpr lea.resolved.destination = addressOf base lea.argument.range.start := by
  have computed := lea.success.receipt.destination_exact
  change lea.success.result.gpr lea.success.instruction.destination = _ at computed
  rw [lea.success.fetch_exact] at computed
  rw [lea.instructionSelected] at computed
  simp only [LeaInstruction.effectiveAddress, LeaInstruction.baseValue] at computed
  rw [lea.resolved.signed_displacement, rsp] at computed
  change lea.success.result.gpr lea.resolved.destination =
    (base + BitVec.ofNat 64 lea.resolved.address.rootOffset) +
      BitVec.ofNat 64 lea.resolved.address.displacement at computed
  change lea.success.result.gpr lea.resolved.destination =
    base + BitVec.ofNat 64 (lea.resolved.address.rootOffset + lea.resolved.address.displacement)
  rw [BitVec.ofNat_add]
  exact computed.trans (BitVec.add_assoc _ _ _)

/-- Resolve that exact computed argument in the actual pre-LEA memory. Spatial
evidence supplies placement and nonwrapping, not authorization to access it. -/
theorem SourceLea.argument_address_toNat {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (lea : SourceLea policy source before)
    (spatial : Resolved before.machine.memory lea.argument)
    (rsp : before.gpr .rsp = addressOf spatial.base lea.resolved.address.rootOffset) :
    (lea.success.result.gpr lea.resolved.destination).toNat =
      spatial.base.toNat + lea.argument.range.start := by
  rw [lea.argument_address spatial.base rsp]
  apply toNat_addressOf spatial.noWrap
  have contained := spatial.root_contains
  have width := lea.argument_width
  simp only [ByteRange.contains_def] at contained
  change lea.argument.range.start < spatial.allocation.extent.start + spatial.allocation.extent.size
  omega

/-- Same source frame, root offset and local name yield the very same address
result for LEA and the later DWORD load. No independent offset is accepted. -/
theorem SourceLea.load_address_same {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (lea : SourceLea policy source before) (load : SourceResolve.LoadSelection source)
    (sameSlot : lea.resolved.slot = load.result.slot) :
    lea.resolved.address = load.result.address := by
  have leaSource := FrameLea.resolve?_source lea.sourceExact
  have loadSource := FrameLoad.resolve?_source load.success
  have left := lea.resolved.addressExact
  have right := load.result.addressExact
  rw [leaSource.1, leaSource.2.2, sameSlot] at left
  rw [loadSource.1, loadSource.2.2] at right
  exact Option.some.inj (left.symm.trans right)

theorem SourceLea.load_range_same {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (lea : SourceLea policy source before) (load : SourceResolve.LoadSelection source)
    (sameSlot : lea.resolved.slot = load.result.slot) :
    lea.argument.range = load.result.address.range :=
  congrArg LocalAddress.Result.range (lea.load_address_same load sameSlot)

/-- Recover the exact destination and local name from the source instruction,
so the authored `lea r9, transferred.addr` needs no independent register guess. -/
theorem SourceLea.authored_operand {policy : CpuAccessPolicy} {frame : SourceFrame.Result}
    {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset} {before : State}
    (lea : SourceLea policy source before)
    (authored : lea.item.instruction =
      ⟨.lea, [.register ⟨.r9, .w64⟩, .address "transferred"]⟩) :
    lea.resolved.destination = .r9 ∧ lea.resolved.slot = "transferred" := by
  have instruction := lea.resolved.instructionExact
  rw [(FrameLea.resolve?_source lea.sourceExact).2.1, authored] at instruction
  simp only [X86Source.Instruction.mk.injEq, List.cons.injEq,
    X86Source.Operand.register.injEq, X86Source.Register.mk.injEq,
    X86Source.Operand.address.injEq] at instruction
  exact ⟨instruction.2.1.1.symm, instruction.2.2.1.symm⟩

/-- Executing LEA is one way to establish the canonical incoming argument;
the argument itself depends only on the static local and fixed loaded stack. -/
theorem SourceLea.canonical_argument {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {policy callPolicy : CpuAccessPolicy}
    {frame : SourceFrame.Result} {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset}
    {before callBefore : State} (lea : SourceLea policy source before)
    (leaSelected : Cpu.policy? loaded before = some policy)
    (callSelected : Cpu.policy? loaded callBefore = some callPolicy)
    (selectedLocal : SourceResolve.LoadSelection source)
    (sameSlot : lea.resolved.slot = selectedLocal.result.slot) :
    lea.argument = WriteFileCountArgument.argument callPolicy selectedLocal := by
  have stack := WriteFileCountArgument.stack_same leaSelected callSelected
  have range := lea.load_range_same selectedLocal sameSlot
  change (⟨policy.stack, lea.argument.range⟩ : Argument) = ⟨callPolicy.stack, _⟩
  rw [stack, range]

end Grass.Refinement.Console.WriteFileCountAddress
