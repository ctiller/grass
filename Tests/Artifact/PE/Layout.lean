import Grass.Artifact.PE.Layout
import Tests.Artifact.PE.ImageSectionTable

/-! # PE32+ declared-layout fixtures -/

namespace Grass.Tests.Artifact.PE.Layout

open Grass.Artifact.Binary Grass.Artifact.COFF Grass.Artifact.PE
open Grass.Std.Logical

def validTable : ImageSectionTable :=
  Grass.Tests.Artifact.PE.ImageSectionTable.table

example : validTable.headerSpan = ⟨0, 304⟩ := by decide

example : declaredImageSpans validTable = [⟨0, 304⟩, ⟨512, 512⟩] := by
  decide

example : DeclaredImageLayoutValid validTable 1024 := by decide

def overlappingSection : SectionHeader :=
  { Grass.Tests.Artifact.PE.ImageSectionTable.textSection with
    pointerToRawData := 0x100 }

def overlappingTable : ImageSectionTable where
  headers := validTable.headers
  sections := Vec.singleton overlappingSection
  sectionCount := by rfl

example : ¬ DeclaredImageLayoutValid overlappingTable 1024 := by decide

def relocationBearingSection : SectionHeader :=
  { Grass.Tests.Artifact.PE.ImageSectionTable.textSection with
    pointerToRelocations := 0x400
    numberOfRelocations := 1 }

example : ¬ imageSectionPointersCoherent relocationBearingSection := by decide

end Grass.Tests.Artifact.PE.Layout
