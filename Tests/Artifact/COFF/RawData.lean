import Grass.Artifact.COFF.RawData
import Tests.Artifact.COFF.SectionHeader

/-! # Header-sized COFF raw-section fixtures -/

namespace Grass.Tests.Artifact.COFF.RawData

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical
open Grass.Tests.Artifact.COFF.SectionHeader

def rawSection : SectionHeader := { textSection with sizeOfRawData := 4 }

def payload : SectionRawData rawSection :=
  ⟨Vec.fromList [0x48, 0x31, 0xc0, 0xc3], by rfl⟩

example : writeSectionRawData payload =
    Vec.fromList [0x48, 0x31, 0xc0, 0xc3] := by rfl

example : readSectionRawData rawSection
    (writeSectionRawData payload ++ Vec.fromList [0xaa, 0xbb]) =
    .done payload (Vec.fromList [0xaa, 0xbb]) := by
  exact readSectionRawData_write_append payload _

example : readSectionRawData rawSection (Vec.fromList [0x48]) =
    .needMore (some 3) := by rfl

example : (writeSectionRawData payload).length =
    rawSection.sizeOfRawData.toNat := by
  exact length_writeSectionRawData payload

example : Derives (sectionRawDataFormat rawSection)
    (writeSectionRawData payload) payload Vec.empty := by
  exact writeSectionRawData_derives payload

end Grass.Tests.Artifact.COFF.RawData
