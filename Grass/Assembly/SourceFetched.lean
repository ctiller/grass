import Grass.Assembly.SourceBytes
import Grass.Assembly.SourceImage
import Grass.ISA.X86.Execution.FetchedEncoding

/-! Connect a resolved source instruction's exact emitted byte slice to an
actual execute-memory fetch. This is a selection bridge only: it does not show
that execution reaches the instruction address. -/

namespace Grass.Assembly.SourceFetched

open Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Memory

/-- A bounded instruction position selects exactly that resolved encoding's
bytes from the complete source byte stream. -/
theorem instruction_bytes {frame rootOffset}
    (source : SourceResolve.Result frame rootOffset) (index : Nat)
    (bounded : index < source.outputs.length) :
    (source.bytes.toList.drop
      (ByteLayout.offset source.splice.finalSizes index)).take
        source.outputs[index].encoding.size =
      source.outputs[index].encoding.toBytes := by
  rw [source.bytes_at_instruction]
  have encodingBound : index < source.encodings.length := by
    simpa [SourceResolve.Result.encodings] using bounded
  rw [List.drop_eq_getElem_cons encodingBound]
  change (source.encodings[index].toBytes ++
    ByteLayout.emitted (source.encodings.drop (index + 1))).take
      source.outputs[index].encoding.size = _
  simp only [SourceResolve.Result.encodings, List.getElem_map]
  simp

/-- If an actual completed fetch observes the exact bounded source slice, its
decoded instruction is the encoding retained at that source position. -/
theorem encoding_of_source_observation {frame rootOffset}
    (source : SourceResolve.Result frame rootOffset) (index : Nat)
    (bounded : index < source.outputs.length) {before : State} {after : MachineState}
    (fetch : FetchedSite before after)
    (observed : fetch.run.complete.committed.observed = some
      ((source.bytes.toList.drop
        (ByteLayout.offset source.splice.finalSizes index)).take
          source.outputs[index].encoding.size)) :
    fetch.site.encoding = source.outputs[index].encoding := by
  apply fetch.encoding_of_observation source.outputs[index].encoding
    (by simpa using source.outputs[index].encodingDecodes [])
  rwa [instruction_bytes source index bounded] at observed

/-- The same selection law applies to the exact code section bound by
`SourceImage`; section placement still supplies no reachability claim. -/
theorem encoding_of_code_section_observation {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {plan : Grass.Artifact.PE.ImagePlan}
    {sectionIndex : Nat} (binding : SourceImage.CodeSection source plan sectionIndex)
    (index : Nat) (bounded : index < source.outputs.length)
    {before : State} {after : MachineState} (fetch : FetchedSite before after)
    (observed : fetch.run.complete.committed.observed = some
      ((binding.placedSection.source.contents.toList.drop
        (ByteLayout.offset source.splice.finalSizes index)).take
          source.outputs[index].encoding.size)) :
    fetch.site.encoding = source.outputs[index].encoding := by
  apply encoding_of_source_observation source index bounded fetch
  rwa [binding.bytesExact] at observed

end Grass.Assembly.SourceFetched
