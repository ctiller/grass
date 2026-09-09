import Grass.Assembly.SourceLoadedImage
import Grass.Assembly.SourceFetched
import Grass.Op.ReadBytes

/-! Derive a completed instruction observation from the actual loaded source
cells. Range selection and preservation of the reached code cells remain explicit inputs;
the observed bytes themselves are obtained from the checked memory oracle. -/

namespace Grass.Assembly.LoadedFetchObservation

open Grass.Std.Logical Grass.Memory Grass.Op Grass.Artifact
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

/-- An actual fetch of the selected source range reads its encoding from the
installed initialized backing. No independent observation equality is assumed. -/
theorem observed_source {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs) (index : Nat)
    (bounded : index < source.outputs.length) {before : State} {after : MachineState}
    (fetch : FetchedSite before after)
    (memory : ∀ offset, fetch.descriptor.range.Covers offset →
      before.machine.memory.cellAt?
        (SourceLoadedImage.codeRegion binding loaded).region.allocId offset =
      loaded.initialState.machine.memory.cellAt?
        (SourceLoadedImage.codeRegion binding loaded).region.allocId offset)
    (root : fetch.descriptor.provenance.root =
      (SourceLoadedImage.codeRegion binding loaded).region.allocId)
    (start : fetch.descriptor.range.start =
      ByteLayout.offset source.splice.finalSizes index)
    (size : fetch.descriptor.range.size = source.outputs[index].encoding.size)
    (outside : ∀ offset, fetch.descriptor.range.Covers offset →
      ∀ patch ∈ loaded.patches,
        ¬ (patch.rva ≤ source.codeBase + offset ∧
          source.codeBase + offset < patch.rva + 8)) :
    fetch.run.complete.committed.observed = some source.outputs[index].encoding.toBytes := by
  have slice := SourceFetched.instruction_bytes source index bounded
  have cells : ∀ offset, fetch.descriptor.range.Covers offset →
      before.machine.memory.cellAt? fetch.descriptor.provenance.root offset =
        (source.outputs[index].encoding.toBytes[offset - fetch.descriptor.range.start]?).map
          (·, true) := by
    intro offset covered
    have bounds := covered
    simp only [ByteRange.covers_def] at bounds
    have byteBound : offset - fetch.descriptor.range.start <
        source.outputs[index].encoding.toBytes.length := by
      simp only [InsnEncoding.length_toBytes]
      omega
    have sizeBound : offset - fetch.descriptor.range.start < source.outputs[index].encoding.size := by simpa using byteBound
    have atByte := congrArg (fun bytes : List Byte =>
      bytes[offset - fetch.descriptor.range.start]?) slice
    simp only [List.getElem?_take, List.getElem?_drop] at atByte
    have sourceByte : source.bytes.get? offset =
        some source.outputs[index].encoding.toBytes[offset - fetch.descriptor.range.start] := by
      simpa [Vec.get?, ← start, size, byteBound, sizeBound, Nat.add_sub_of_le bounds.1] using atByte
    rw [root, memory offset covered, SourceLoadedImage.selected_code_byte_initialized
      binding loaded sourceByte (outside offset covered)]
    rw [List.getElem?_eq_getElem byteBound]
    rfl

  have observed := observedBytes_eq_of_state_cells fetch.run.resolved
    source.outputs[index].encoding.toBytes (by simpa using size.symm) cells
    (fetch.indeterminate (before.machine.noteContext fetch.run.context fetch.run.contextKind)
      fetch.descriptor)
  have actual := fetch.observed_exact
  have encodingBytes := fetch.site.bytesExact
  rw [fetch.noTrailing, List.append_nil] at encodingBytes
  exact actual.trans (congrArg some (encodingBytes.symm.trans observed))

end Grass.Assembly.LoadedFetchObservation
