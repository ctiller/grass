import Grass.Artifact.COFF.SectionTable
import Tests.Artifact.COFF.Header
import Tests.Artifact.COFF.SectionHeader

/-! # Count-coupled COFF section-table fixtures -/

namespace Grass.Tests.Artifact.COFF.SectionTable

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical
open Grass.Tests.Artifact.COFF.Header
open Grass.Tests.Artifact.COFF.SectionHeader

def singleSectionHeader : Header :=
  { amd64ObjectHeader with numberOfSections := 1 }

def singleSectionTable : SectionTable where
  header := singleSectionHeader
  sections := Vec.singleton textSection
  sectionCount := by rfl

example : readSectionTable (writeSectionTable singleSectionTable) =
    .done singleSectionTable Vec.empty := by
  exact readSectionTable_writeSectionTable singleSectionTable

example : readSectionTable
    (writeSectionTable singleSectionTable ++ Vec.fromList [0xaa]) =
    .done singleSectionTable (Vec.fromList [0xaa]) := by
  exact readSectionTable_writeSectionTable_append singleSectionTable _

example : readSectionTable encodedHeader = .needMore (some 120) := by rfl

example : (writeSectionTable singleSectionTable).length = 60 := by
  exact length_writeSectionTable singleSectionTable

example : Derives sectionTableFormat (writeSectionTable singleSectionTable)
    singleSectionTable Vec.empty := by
  exact writeSectionTable_derives singleSectionTable

end Grass.Tests.Artifact.COFF.SectionTable
