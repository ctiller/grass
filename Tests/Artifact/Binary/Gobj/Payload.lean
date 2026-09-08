import Grass.Artifact.Binary.Gobj.Payload

/-! # Versioned proof-free `.gobj` payload fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.Payload

open Grass.Artifact.Binary.Gobj Grass.Grammar Grass.Std.Logical

def scopeBytes : Std.Logical.ByteArray :=
  Vec.fromList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

theorem scopeBytes_length : scopeBytes.length = 16 := by decide

def scope : SizedByteArray 16 := ⟨scopeBytes, scopeBytes_length⟩

def emptyBody : U32LengthPrefixedBytes := ⟨Vec.empty, by decide⟩

def sectionBytes : Std.Logical.ByteArray := Vec.fromList [0xaa]

theorem sectionBytes_lengthFits : sectionBytes.length < 2 ^ 32 := by decide

def sections : U32LengthPrefixedBytes :=
  ⟨sectionBytes, sectionBytes_lengthFits⟩

def payload : GobjPayload where
  formatVersion := .v1
  scope := scope
  sections := sections
  symbols := emptyBody
  relocations := emptyBody
  imports := emptyBody
  sourceMap := emptyBody

def suffix : Std.Logical.ByteArray := Vec.fromList [0xfe, 0xed]

example : (writeGobj payload).length = 45 := by
  rw [length_writeGobj]
  decide

example : readGobj (writeGobj payload ++ suffix) = .done payload suffix := by
  exact readGobj_write_append payload suffix

example : readGobj (Vec.fromList [0x42, 0x4f, 0x42, 0x4a]) =
    .invalid (.malformed "invalid .gobj magic") := by rfl

example : readGobj (Vec.fromList [0x47, 0x4f, 0x42, 0x4a, 0x02, 0x00]) =
    .invalid (.unsupported "unsupported .gobj format version") := by rfl

example : readGobj
    (Vec.fromList [0x47, 0x4f, 0x42, 0x4a, 0x01, 0x00, 0x01, 0x00]) =
      .invalid (.malformed "nonzero .gobj reserved field") := by rfl

example : readGobj
    (Vec.fromList [0x47, 0x4f, 0x42, 0x4a, 0x01, 0x00, 0x00, 0x00,
      0x10, 0x11, 0x12]) = .needMore (some 13) := by rfl

end Grass.Tests.Artifact.Binary.Gobj.Payload
