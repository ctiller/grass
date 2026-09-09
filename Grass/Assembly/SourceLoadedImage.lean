import Grass.Assembly.SourceImage
import Grass.Platform.Win32.LoaderEntry

/-! Checked composition facts between resolved source code and the preferred-base
loader result. These facts do not establish entry reachability, ASLR coverage,
or physical loader correspondence. -/

namespace Grass.Assembly.SourceLoadedImage

open Grass.Std.Logical Grass.Memory Grass.Artifact
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

/-- Selecting the exact bound code-section start as the image entry gives the
initial natural RIP from the preferred base and source resolver's code base. -/
theorem entry_rip_exact {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} {sectionIndex : Nat}
    (binding : SourceImage.CodeSection source image.plan sectionIndex)
    (loaded : LoadedImage image inputs)
    (entry : image.plan.layout.requested.entryPoint = ⟨sectionIndex, 0⟩) :
    loaded.initialState.rip.toNat =
      (preferredBase image).toNat + source.codeBase := by
  rw [loaded.entryRip_exact, binding.entry_rva entry]

/-- `patchContents_get?_outside` preserves each logical byte outside all IAT slots. -/
theorem patchContents_get?_outside (patches : List ImportPatch) (start : Nat)
    (bytes : Vec Byte) {offset : Nat} {byte : Byte}
    (original : bytes.get? offset = some byte)
    (outside : ∀ patch ∈ patches,
      ¬ (patch.rva ≤ start + offset ∧ start + offset < patch.rva + 8)) :
    (patchContents patches start bytes).get? offset = some byte := by
  have originalList : bytes.toList[offset]? = some byte := by
    simpa [Vec.get?] using original
  simp [patchContents, Vec.get?, originalList,
    patchedByte_outside patches (start + offset) byte outside]

/-- An actual assigned code region exposes each source byte as initialized when
that byte lies outside the exact checked IAT patch slots. `code_byte_initialized`
requires membership in the loaded image's actual assigned regions. -/
theorem code_byte_initialized {frame rootOffset}
    {source : SourceResolve.Result frame rootOffset} {image : ImageInput}
    {inputs : EntryInputs} (loaded : LoadedImage image inputs)
    {region : InitializedRegion}
    (member : region ∈ assignedRegions image inputs loaded.patches)
    (codeBytes : region.bytes =
      patchContents loaded.patches source.codeBase source.bytes)
    {offset : Nat} {byte : Byte} (sourceByte : source.bytes.get? offset = some byte)
    (outside : ∀ patch ∈ loaded.patches,
      ¬ (patch.rva ≤ source.codeBase + offset ∧
        source.codeBase + offset < patch.rva + 8)) :
    loaded.initialState.machine.memory.cellAt? region.allocId offset = some (byte, true) := by
  apply loaded.cellAt? member
  rw [codeBytes]
  exact patchContents_get?_outside loaded.patches source.codeBase source.bytes sourceByte outside

end Grass.Assembly.SourceLoadedImage
