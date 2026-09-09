import Grass.Artifact.Binary.Gobj.Framing

/-! # Deterministic `.gobj` framing fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.Framing

open Grass.Artifact.Binary.Gobj Grass.Grammar Grass.Std.Logical

def payloadBytes : Std.Logical.ByteArray := Vec.fromList [0x10, 0x20, 0x30]

theorem payloadBytes_lengthFits : payloadBytes.length < 2 ^ 32 := by decide

def payload : U32LengthPrefixedBytes := ⟨payloadBytes, payloadBytes_lengthFits⟩

def suffix : Std.Logical.ByteArray := Vec.fromList [0xaa, 0xbb]

example : writeU32LengthPrefixedBytes payload =
    Vec.fromList [0x03, 0x00, 0x00, 0x00, 0x10, 0x20, 0x30] := by decide

example : readU32LengthPrefixedBytes
    (writeU32LengthPrefixedBytes payload ++ suffix) =
      .done payload suffix := by
  exact readU32LengthPrefixedBytes_write_append payload suffix

example : Derives u32LengthPrefixedBytesFormat
    (writeU32LengthPrefixedBytes payload ++ suffix) payload suffix := by
  exact derives_u32LengthPrefixedBytes_iff.mpr rfl

example : readU32LengthPrefixedBytes
    (writeU32LengthPrefixedBytes payload ++ suffix) = .done payload suffix ↔
    Derives u32LengthPrefixedBytesFormat
      (writeU32LengthPrefixedBytes payload ++ suffix) payload suffix :=
  readU32LengthPrefixedBytes_done_iff _ _ _

example : readU32LengthPrefixedBytes (Vec.fromList [0x03, 0x00]) =
    .needMore (some 2) := by rfl

example : readU32LengthPrefixedBytes
    (Vec.fromList [0x03, 0x00, 0x00, 0x00, 0x10]) =
      .needMore (some 2) := by rfl

end Grass.Tests.Artifact.Binary.Gobj.Framing
