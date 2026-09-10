import Grass.Assembly.LoadedStaticArgument
import Tests.Assembly.StaticSection
import Tests.Artifact.PE.ImageWriter
import Tests.Platform.Win32LoaderEntry

/-! A loaded two-object static section supplies a checked suffix argument from
the second object's nonzero offset. -/
namespace Grass.Tests.Assembly.LoadedStaticArgument

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

open Grass.Artifact.PE Grass.Assembly Grass.Assembly.SourceStaticBindings
  Grass.Assembly.LoadedStaticArgument Grass.Memory Grass.Platform.Win32
  Grass.Platform.Win32.Loader Grass.Std.Logical
open Grass.Tests.Assembly.StaticSection

private def textName : SectionName :=
  ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩

private def text : RawSection :=
  { name := textName, contents := Vec.singleton 0xc3, characteristics := 0x60000020 }

/-- This fixture has an executable first section so the existing static table
is section one and occupies assigned loaded-region index two, after headers. -/
private def preparedSuffix? : Option Bool := do
  let statics ← Grass.Assembly.StaticSection.layout? table sectionName 0x40000040
  let plan ← (prepareImage
    { entryPoint := ⟨0, 0⟩
      sections := Vec.fromList [text, statics.rawSection]
      imports := Vec.empty }).toOption
  let image : ImageInput := ⟨plan, (writeImage plan).toHostBytes, rfl⟩
  let inputs := Grass.Tests.Win32LoaderEntry.inputsFor plan .empty
  let loaded ← initialize? image inputs
  let binding ← resolveOne? plan statics 1 "second"
  let prepared ← prepare? binding loaded loaded.memory 1
  let atEnd ← prepare? binding loaded loaded.memory 2
  if fits : 1 ≤ prepared.argument.range.size then
    let mismatched := loaded.memory.writeResolved prepared.resolved.toResolvedAccess [0] true
      (by simpa using fits)
    let uninitialized := loaded.memory.writeResolved prepared.resolved.toResolvedAccess [5] false
      (by simpa using fits)
    pure (prepared.bytes == Vec.fromList [5] &&
      prepared.argument.range.start == 9 &&
      prepared.argument.range.size == 1 &&
      prepared.regionIndex == 2 &&
      prepared.provenance.root == prepared.region.allocId &&
      prepared.address.toNat == (preferredBase image).toNat + binding.span.rva + 1 &&
      atEnd.bytes.length == 0 &&
      atEnd.argument.range.size == 0 &&
      !(prepare? binding loaded loaded.memory 3).isSome &&
      !(prepare? binding loaded inputs.environment.memory 1).isSome &&
      !(prepare? binding loaded mismatched 1).isSome &&
      !(prepare? binding loaded uninitialized 1).isSome)
  else none

example : preparedSuffix? = some true := by decide

/-- An import section is not a static-object source after the loader fills its
IAT. Restoring the source bytes through the selected current region still
leaves `Prepared.loadedPayloadExact` false. -/
private def patchedImportRefused? : Option Bool := do
  let plan ← (prepareImage
    { entryPoint := ⟨0, 0⟩
      sections := Vec.singleton text
      imports := Vec.singleton _root_.Tests.Artifact.PE.ImageWriter.kernel32 }).toOption
  let source ← plan.layout.placed.get? 1
  let staticTable := Grass.Assembly.StaticObjects.checked
    [{ name := "import", alignment := 1, kind := .rodata, bytes := source.source.contents }]
    (by
      constructor
      · change ["import"].Nodup
        decide
      · intro declaration member
        have same : declaration =
            { name := "import", alignment := 1, kind := .rodata,
              bytes := source.source.contents } := by
          simpa using member
        subst declaration
        change Nat.isPowerOfTwo 1
        decide)
  let statics ← Grass.Assembly.StaticSection.layout? staticTable source.source.name
    source.source.characteristics
  let image : ImageInput := ⟨plan, (writeImage plan).toHostBytes, rfl⟩
  let inputs := Grass.Tests.Win32LoaderEntry.inputsFor plan
    (.fromList [.fromList [0x7ff02020]])
  let loaded ← initialize? image inputs
  let binding ← resolveOne? plan statics 1 "import"
  let region ← (assignedRegions image inputs loaded.patches)[2]?
  let provenance := allocationProvenance region.allocId region.allocationRecord
  let resolved ← (loaded.memory.resolveAccess? provenance
    { start := 0, size := source.source.contents.length }).toOption
  let restored := loaded.memory.writeResolved resolved source.source.contents.toList true
    (by
      change source.source.contents.toList.length ≤ source.source.contents.toList.length
      exact Nat.le_refl _)
  pure (!(region.bytes == source.source.contents) &&
    source.source.contents.toList.zipIdx.all (fun entry => decide
      (restored.cellAt? provenance.root entry.2 = some (entry.1, true))) &&
    !(prepare? binding loaded loaded.memory 0).isSome &&
    !(prepare? binding loaded restored 0).isSome)

example : patchedImportRefused? = some true := by decide

end Grass.Tests.Assembly.LoadedStaticArgument
