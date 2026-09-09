import Grass.Artifact.Binary.Gobj.Payload

/-! # Versioned proof-free `.gobj` payload fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.Payload

open Grass.Artifact.Binary.Gobj Grass.Grammar Grass.Std.Logical

def scope : StableScopeId := Grass.StableId.mk "alpha.beta" "gamma"

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

example : (writeGobj payload).length = 61 := by
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
      0x02]) = .invalid (.malformed "noncanonical unary natural") := by rfl

example : readGobj
    (Vec.fromList [0x47, 0x4f, 0x42, 0x4a, 0x01, 0x00, 0x00, 0x00]) =
      .needMore (some 22) := by rfl

example : readScopeComponent
    (writeScopeComponent "λ" ++ suffix) = .done "λ" suffix := by
  exact readScopeComponent_write_append "λ" suffix

example : readScopeComponent (Vec.fromList [1, 0, 0xff]) =
    .invalid (.malformed "invalid UTF-8 in .gobj scope") := by rfl

example : readScopeComponent (Vec.fromList [1, 1, 0]) =
    .needMore (some 2) := by rfl

example : readScopeComponent (Vec.fromList [1, 1]) =
    .needMore (some 3) := by rfl

example : readStableScopeId
    (writeStableScopeId (Grass.StableId.mk "" "")) =
      .done (Grass.StableId.mk "" "") Vec.empty := by
  exact readStableScopeId_write (Grass.StableId.mk "" "")

example : Derives stableScopeIdFormat
    (writeStableScopeId scope ++ suffix) scope suffix := by
  exact derives_stableScopeId_iff.mpr rfl

example (input rest : Std.Logical.ByteArray) (value : StableScopeId) :
    readStableScopeId input = .done value rest ↔
      Derives stableScopeIdFormat input value rest := by
  exact readStableScopeId_done_iff input value rest

example : writeStableScopeId (Grass.StableId.mk "a.b" "c") ≠
    writeStableScopeId (Grass.StableId.mk "a" "b.c") := by decide

end Grass.Tests.Artifact.Binary.Gobj.Payload
