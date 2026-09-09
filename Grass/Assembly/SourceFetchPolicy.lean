import Grass.Assembly.LoadedCodeRoot
import Grass.Platform.Win32.CpuPolicy
import Grass.ISA.X86.Execution.FetchFactory
import Grass.Assembly.SourceFetched

/-! Connect the fixed Windows CPU policy to the source-bound loaded code region.
Policy construction derives provenance; it does not establish execution success. -/

namespace Grass.Assembly.SourceFetchPolicy

open Grass.Memory Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

/-- A source address in the executable loaded section admits construction of
the fixed CPU policy, using the actual initialized stack allocation. -/
theorem policy_available {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) (before : State)
    (contains : ContainsCodeAddress
      (SourceLoadedImage.codeRegion binding loaded).region before.rip) :
    (Cpu.policy? loaded before).isSome = true := by
  have code := LoadedCodeRoot.codeRoot?_isSome binding loaded contains
  obtain ⟨record, present, stack, _⟩ := loaded.stackProvenance_present
  unfold Cpu.policy?
  cases selected : loaded.codeRoot? before.rip with
  | none => simp [selected] at code
  | some root => simp [stack]

/-- Every policy produced at this source address names the exact source code
allocation. No independently supplied provenance equality is required. -/
theorem policy_code_root {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {before : State}
    (contains : ContainsCodeAddress
      (SourceLoadedImage.codeRegion binding loaded).region before.rip)
    {policy : CpuAccessPolicy} (selected : Cpu.policy? loaded before = some policy) :
    policy.code.root = (SourceLoadedImage.codeRegion binding loaded).region.allocId := by
  obtain ⟨code, stack, codeAt, _, codeExact, _⟩ := Cpu.policy?_inputs selected
  rw [codeExact]
  exact LoadedCodeRoot.codeRoot?_provenance_root binding loaded contains codeAt

/-- The actual dispatched fetch uses the source allocation selected by the
fixed Windows policy, rather than an independently supplied descriptor root. -/
theorem fetched_code_root {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {before : State}
    (contains : ContainsCodeAddress
      (SourceLoadedImage.codeRegion binding loaded).region before.rip)
    {policy : CpuAccessPolicy} (selected : Cpu.policy? loaded before = some policy)
    (fetched : FetchFactory.Success policy before) :
    fetched.dispatched.fetch.descriptor.provenance.root =
      (SourceLoadedImage.codeRegion binding loaded).region.allocId := by
  have metadata := fetched.observed.dispatch_metadata fetched.dispatched fetched.dispatch_exact
  have descriptor := congrArg (fun d : AccessDescriptor => d.provenance.root)
    fetched.descriptor_exact
  change fetched.observed.descriptor.provenance.root = policy.code.root at descriptor
  rw [metadata.2.2.2.2, descriptor]
  exact policy_code_root binding loaded contains selected

/-- Current code-allocation preservation identifies the factory's actual base
with the loaded source base. Stack writes need not preserve the whole memory. -/
theorem fetched_code_base {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {before : State}
    (contains : ContainsCodeAddress
      (SourceLoadedImage.codeRegion binding loaded).region before.rip)
    {policy : CpuAccessPolicy} (selected : Cpu.policy? loaded before = some policy)
    (fetched : FetchFactory.Success policy before)
    (present : before.machine.memory.allocations.lookup
      (SourceLoadedImage.codeRegion binding loaded).region.allocId =
      some (SourceLoadedImage.codeRegion binding loaded).region.allocationRecord) :
    fetched.plan.base = (SourceLoadedImage.codeRegion binding loaded).region.base := by
  have lookup := fetched.plan.lookup
  rw [policy_code_root binding loaded contains selected, present] at lookup
  have allocation := Option.some.inj lookup
  have placed := fetched.plan.placed
  rw [← allocation] at placed
  exact (Option.some.inj placed).symm

/-- A reached source RIP determines the actual descriptor offset through the
factory's retained address plan. No authored numeric displacement is copied. -/
theorem fetched_source_start {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {before : State}
    (contains : ContainsCodeAddress
      (SourceLoadedImage.codeRegion binding loaded).region before.rip)
    {policy : CpuAccessPolicy} (selected : Cpu.policy? loaded before = some policy)
    (fetched : FetchFactory.Success policy before)
    (present : before.machine.memory.allocations.lookup
      (SourceLoadedImage.codeRegion binding loaded).region.allocId =
      some (SourceLoadedImage.codeRegion binding loaded).region.allocationRecord)
    (index : Nat)
    (rip : before.rip.toNat =
      (SourceLoadedImage.codeRegion binding loaded).region.base.toNat +
        ByteLayout.offset source.splice.finalSizes index) :
    fetched.dispatched.fetch.descriptor.range.start =
      ByteLayout.offset source.splice.finalSizes index := by
  have metadata := fetched.observed.dispatch_metadata fetched.dispatched fetched.dispatch_exact
  have descriptor := congrArg (fun d : AccessDescriptor => d.range.start)
    fetched.descriptor_exact
  change fetched.observed.descriptor.range.start = fetched.plan.offset at descriptor
  rw [metadata.2.2.2.2, descriptor, AddressPlan.offset,
    fetched_code_base binding loaded contains selected fetched present, rip]
  omega

/-- Initialized source bytes determine the actual fetch width through the
factory's decoder. The width is a conclusion, not a caller-supplied equality. -/
theorem fetched_source_width {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) {before : State}
    (contains : ContainsCodeAddress
      (SourceLoadedImage.codeRegion binding loaded).region before.rip)
    {policy : CpuAccessPolicy} (selected : Cpu.policy? loaded before = some policy)
    (fetched : FetchFactory.Success policy before)
    (present : before.machine.memory.allocations.lookup
      (SourceLoadedImage.codeRegion binding loaded).region.allocId =
      some (SourceLoadedImage.codeRegion binding loaded).region.allocationRecord)
    (index : Nat) (bounded : index < source.outputs.length)
    (rip : before.rip.toNat =
      (SourceLoadedImage.codeRegion binding loaded).region.base.toNat +
        ByteLayout.offset source.splice.finalSizes index)
    (lengthBound : 0 < source.outputs[index].encoding.size ∧
      source.outputs[index].encoding.size ≤ 15)
    (fallthroughFits : before.rip.toNat + source.outputs[index].encoding.size < 2 ^ 64)
    (cells : ∀ offset,
      before.machine.memory.cellAt?
        (SourceLoadedImage.codeRegion binding loaded).region.allocId offset =
      loaded.initialState.machine.memory.cellAt?
        (SourceLoadedImage.codeRegion binding loaded).region.allocId offset)
    (outside : ∀ i, i < source.outputs[index].encoding.size →
      ∀ patch ∈ loaded.patches,
        ¬ (patch.rva ≤ source.codeBase + ByteLayout.offset source.splice.finalSizes index + i ∧
          source.codeBase + ByteLayout.offset source.splice.finalSizes index + i < patch.rva + 8)) :
    fetched.dispatched.fetch.descriptor.range.size = source.outputs[index].encoding.size := by
  have metadata := fetched.observed.dispatch_metadata fetched.dispatched fetched.dispatch_exact
  have planOffset : fetched.plan.offset = ByteLayout.offset source.splice.finalSizes index := by
    unfold AddressPlan.offset
    rw [fetched_code_base binding loaded contains selected fetched present, rip]
    omega
  have width := fetched.extent_of_memory_prefix source.outputs[index].encoding
    lengthBound fallthroughFits (by
      intro i bound
      rw [policy_code_root binding loaded contains selected, planOffset]
      unfold MemoryState.byteAt?
      rw [cells]
      have sourceByte := SourceFetched.instruction_byte source index bounded i bound
      have initialized := SourceLoadedImage.selected_code_byte_initialized binding loaded
        sourceByte (by simpa [Nat.add_assoc] using outside i (by simpa using bound))
      rw [initialized]
      rfl) source.outputs[index].encodingDecodes
  rw [metadata.2.2.2.2]
  exact width

end Grass.Assembly.SourceFetchPolicy
