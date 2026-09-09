import Grass.Assembly.SourceBytes
import Grass.Artifact.PE.LayoutBinding

namespace Grass.Assembly.SourceImage
open Grass.Artifact.PE Grass.Std.Logical Grass.ISA.X86

/-- Exact resolved code and its RVA basis in one checked image. Symbol bindings,
loader applicability, section permissions and execution safety remain separate. -/
structure CodeSection {frame rootOffset} (source : SourceResolve.Result frame rootOffset)
    (plan : ImagePlan) (sectionIndex : Nat) where
  placedSection : PlacedSection
  selected : plan.layout.placed.get? sectionIndex = some placedSection
  bytesExact : placedSection.source.contents = source.bytes
  baseExact : placedSection.virtualSpan.start = source.codeBase

/-- Check both final code bytes and the RVA basis against the selected image section. -/
def bindCode? {frame rootOffset} (source : SourceResolve.Result frame rootOffset)
    (plan : ImagePlan) (sectionIndex : Nat) : Option (CodeSection source plan sectionIndex) :=
  match selected : plan.layout.placed.get? sectionIndex with
  | none => none
  | some placedSection =>
    if bytesExact : placedSection.source.contents = source.bytes then
      if baseExact : placedSection.virtualSpan.start = source.codeBase then
        some ⟨placedSection, selected, bytesExact, baseExact⟩
      else none
    else none

/-- Positive instruction sizes keep every instruction start inside the exact code section. -/
theorem CodeSection.instruction_bound {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {plan : ImagePlan} {sectionIndex : Nat}
    (binding : CodeSection source plan sectionIndex) (index : Nat)
    (bounded : index < source.encodings.length) :
    ByteLayout.offset source.splice.finalSizes index < binding.placedSection.source.contents.length := by
  rw [binding.bytesExact, source.bytes_length, ← source.encoding_sizes]
  exact ByteLayout.offset_lt_total _ index (by simpa using bounded)
    (by simpa using source.encodings[index].size_pos)

/-- PE location resolution agrees with the RVA used by source instruction resolution. -/
theorem CodeSection.instruction_rva {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {plan : ImagePlan} {sectionIndex : Nat}
    (binding : CodeSection source plan sectionIndex) (index : Nat)
    (bounded : index < source.encodings.length) :
    resolveSectionLocation? plan.layout.placed
        ⟨sectionIndex, ByteLayout.offset source.splice.finalSizes index⟩ =
      some (source.codeBase + ByteLayout.offset source.splice.finalSizes index) := by
  simp [resolveSectionLocation?, binding.selected,
    binding.instruction_bound index bounded, binding.baseExact]

/-- Decoding the selected section at a computed instruction position recovers the
resolved encoding and exact emitted suffix. -/
theorem CodeSection.decode_at_instruction {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {plan : ImagePlan} {sectionIndex : Nat}
    (binding : CodeSection source plan sectionIndex) (index : Nat)
    (bounded : index < source.outputs.length) :
    decodeInsn (binding.placedSection.source.contents.toList.drop
      (ByteLayout.offset source.splice.finalSizes index)) =
      .ok (source.outputs[index].encoding,
        ByteLayout.emitted (source.encodings.drop (index + 1))) := by
  rw [binding.bytesExact]
  exact source.decode_at_instruction index bounded

/-- Selecting this code section's start as the entry location makes the image
entry RVA equal to the source resolver's code base. -/
theorem CodeSection.entry_rva {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {plan : ImagePlan} {sectionIndex : Nat}
    (binding : CodeSection source plan sectionIndex)
    (entry : plan.layout.requested.entryPoint = ⟨sectionIndex, 0⟩) :
    plan.layout.entryPointRva = source.codeBase := by
  have resolved := plan.layout.entryPointRva_eq
  rw [entry] at resolved
  simp [resolveSectionLocation?, binding.selected] at resolved
  exact resolved.2.symm.trans binding.baseExact

end Grass.Assembly.SourceImage
