import Grass.Artifact.Binary.Gobj.Section

/-! # Typed `.gobj` section fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.Section

open Grass.Artifact.Binary.Gobj Grass.Grammar Grass.Std.Logical

def nameBytes : Std.Logical.ByteArray :=
  Vec.fromList [0x2e, 0x74, 0x65, 0x78, 0x74]

theorem nameBytes_lengthFits : nameBytes.length < 2 ^ 32 := by decide

def name : U32LengthPrefixedBytes := ⟨nameBytes, nameBytes_lengthFits⟩

def contentsBytes : Std.Logical.ByteArray := Vec.fromList [0x90, 0xc3]

theorem contentsBytes_lengthFits : contentsBytes.length < 2 ^ 32 := by decide

def contents : U32LengthPrefixedBytes :=
  ⟨contentsBytes, contentsBytes_lengthFits⟩

def alignment : GobjSectionAlignment := ⟨4, by decide⟩

def permissions : GobjSectionPermissions := ⟨5, by decide⟩

def entry : GobjSection where
  name := name
  alignment := alignment
  permissions := permissions
  contents := contents

def suffix : Std.Logical.ByteArray := Vec.fromList [0xaa, 0xbb]

def profileId : GobjRelocationProfileId where
  owner := name
  name := contents
  version := 7

def relocatableProfile : GobjSectionProfile := .relocatable profileId

example : readGobjSectionProfile
    (writeGobjSectionProfile relocatableProfile ++ suffix) =
      .done relocatableProfile suffix := by
  exact readGobjSectionProfile_write_append relocatableProfile suffix

example : readGobjSectionProfile (Vec.singleton 2) =
    .invalid (.malformed "unknown .gobj section profile tag") := by rfl

example : (writeGobjSection entry).length = 20 := by
  rw [length_writeGobjSection]
  decide

example : readGobjSection (writeGobjSection entry ++ suffix) =
    .done entry suffix := by
  exact readGobjSection_write_append entry suffix

example : readGobjSection (Vec.fromList [0, 0, 0, 0, 32]) =
    .invalid (.malformed
      ".gobj section alignment exponent exceeds 31") := by rfl

example : readGobjSection (Vec.fromList [0, 0, 0, 0, 0, 8]) =
    .invalid (.malformed
      ".gobj section permission reserved bit is set") := by rfl

example : readGobjSection (Vec.fromList [0, 0, 0, 0, 0, 0, 1, 0]) =
    .invalid (.malformed "nonzero .gobj section reserved field") := by rfl

/-- A missing profile tag also accounts for the mandatory contents length. -/
example : readGobjSection
    (Vec.fromList [0, 0, 0, 0, 0, 0, 0, 0]) =
    .needMore (some 5) := by rfl

/-- A partial relocatable profile accounts for its remaining nominal field,
version, and the section contents length. -/
example : readGobjSection
    (Vec.fromList [0, 0, 0, 0, 0, 0, 0, 0, 1, 100, 0, 0, 0]) =
    .needMore (some 112) := by rfl

theorem singleton_countFits : (Vec.singleton entry).length < 2 ^ 32 := by decide

def table : GobjSectionTable := ⟨Vec.singleton entry, singleton_countFits⟩

example : (writeGobjSectionTable table).length = 24 := by
  rw [length_writeGobjSectionTable]
  decide

example : readGobjSectionTable (writeGobjSectionTable table ++ suffix) =
    .done table suffix := by
  exact readGobjSectionTable_write_append table suffix

example : readGobjSectionTable (Vec.fromList [2, 0, 0, 0]) =
    .needMore (some 26) := by rfl

/-- A malformed first entry is irrecoverable even when later entries are wholly
absent; the table count must not mask the bad alignment byte. -/
example : readGobjSectionTable
    (Vec.fromList [2, 0, 0, 0, 0, 0, 0, 0, 32]) =
    .invalid (.malformed
      ".gobj section alignment exponent exceeds 31") := by rfl

/-- The deficit includes the selected name payload and every mandatory field
that follows it in the smallest section entry. -/
example : readGobjSectionTable
    (Vec.fromList [1, 0, 0, 0, 100, 0, 0, 0]) =
    .needMore (some 109) := by rfl

theorem table_lengthFits : (writeGobjSectionTable table).length < 2 ^ 32 := by
  rw [length_writeGobjSectionTable]
  decide

def framedTable : U32LengthPrefixedBytes := table.toFramed table_lengthFits

example : parseGobjSectionTableBody framedTable = .ok table := by
  exact parseGobjSectionTableBody_toFramed table table_lengthFits

def trailingTableBytes : Std.Logical.ByteArray :=
  writeGobjSectionTable table ++ Vec.singleton 0xff

theorem trailingTableBytes_lengthFits : trailingTableBytes.length < 2 ^ 32 := by
  unfold trailingTableBytes
  rw [Vec.length_append, length_writeGobjSectionTable]
  decide

def trailingTableBody : U32LengthPrefixedBytes :=
  ⟨trailingTableBytes, trailingTableBytes_lengthFits⟩

example : parseGobjSectionTableBody trailingTableBody =
    .error .trailingInput := by
  unfold parseGobjSectionTableBody trailingTableBody trailingTableBytes
  rw [readGobjSectionTable_write_append]
  rfl

def truncatedTableBody : U32LengthPrefixedBytes :=
  ⟨Vec.fromList [1, 0, 0, 0], by decide⟩

example : parseGobjSectionTableBody truncatedTableBody =
    .error (.malformed "truncated .gobj section-table body") := by rfl

end Grass.Tests.Artifact.Binary.Gobj.Section
