import Grass.Artifact.COFF.Relocation
import Tests.Artifact.COFF.SectionHeader

/-! # COFF relocation record and block fixtures -/

namespace Grass.Tests.Artifact.COFF.Relocation

open Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical
open Grass.Tests.Artifact.COFF.SectionHeader

def rawRelocation : Grass.Artifact.COFF.Relocation where
  virtualAddress := 0x12
  symbolTableIndex := 3
  relocationType := 4

def encodedRelocation : Std.Logical.ByteArray := Vec.fromList [
  0x12, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00]

example : writeRelocation rawRelocation = encodedRelocation := by decide

example : readRelocation encodedRelocation =
    .done rawRelocation Vec.empty := by rfl

example : readRelocation (encodedRelocation ++ Vec.fromList [0xaa]) =
    .done rawRelocation (Vec.fromList [0xaa]) := by rfl

example : readRelocation (Vec.fromList [0x12, 0x00, 0x00]) =
    .needMore (some 7) := by rfl

def twoRelocations : Vec Grass.Artifact.COFF.Relocation :=
  Vec.fromList [rawRelocation, { rawRelocation with virtualAddress := 0x34 }]

example : (writeRelocations twoRelocations).length = 20 := by
  exact length_writeRelocations twoRelocations

example : readRelocations 2
    (writeRelocations twoRelocations ++ Vec.fromList [0xbb]) =
    .done twoRelocations (Vec.fromList [0xbb]) := by
  exact readRelocations_writeRelocations_append twoRelocations _

example : Derives (.repeat 2 relocationFormat)
    (writeRelocations twoRelocations) twoRelocations Vec.empty := by
  exact writeRelocations_derives twoRelocations

def relocationSection : SectionHeader :=
  { textSection with numberOfRelocations := 2 }

def relocationBlock : RelocationBlock relocationSection where
  relocations := twoRelocations
  relocationCount := by rfl

example : readRelocationBlock relocationSection
    (writeRelocationBlock relocationBlock ++ Vec.fromList [0xcc]) =
    .done relocationBlock (Vec.fromList [0xcc]) := by
  exact readRelocationBlock_writeRelocationBlock_append relocationBlock _

example : readRelocationBlock relocationSection encodedRelocation =
    .needMore (some 10) := by rfl

example : Derives (relocationBlockFormat relocationSection)
    (writeRelocationBlock relocationBlock) relocationBlock Vec.empty := by
  exact writeRelocationBlock_derives relocationBlock

end Grass.Tests.Artifact.COFF.Relocation
