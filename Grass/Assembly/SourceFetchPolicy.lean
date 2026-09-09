import Grass.Assembly.LoadedCodeRoot
import Grass.Platform.Win32.CpuPolicy

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

end Grass.Assembly.SourceFetchPolicy
