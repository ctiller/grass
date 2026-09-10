import Grass.Artifact.Binary.LEB128
import Grass.Artifact.Binary.LittleEndian
import Grass.Target.Artifact

/-!
# Wasm names

A Wasm `name` is `vec(byte)` holding a string's UTF-8 bytes: an LEB128
byte-length followed by exactly that many bytes. `Grass.Target.Artifact`
already supplies the `List UInt8 ↔ ByteArray` crossing (`bytesOfList`/
`listOfBytes`) every format in this seam writes against; this file adds the
one further crossing a name needs, `ByteArray ↔ String`, straight from core
(`String.toUTF8`/`String.fromUTF8?`), with no detour through
`Grass.Std.Logical`'s `Vec Byte`/`Text` machinery (which exists for a
different boundary and would add a conversion layer this format does not
otherwise need, exactly as `Grass.Artifact.ELF`'s docstring explains for the
combinator-based `Grass.Grammar` reader it also declines to reuse).
-/

namespace Grass.Artifact.Wasm

open Grass.Artifact.Binary Grass.Target

/-- The reverse of `Grass.Target.listOfBytes_bytesOfList`: packing a byte
array's own list of bytes recovers the array exactly. Only `List UInt8 →
ByteArray → List UInt8` is needed elsewhere in this seam; a name's bytes
need the round trip the other way round, to hand `String.fromUTF8?` a
`ByteArray` built from the `List UInt8` this format reads. -/
theorem bytesOfList_listOfBytes (bytes : ByteArray) :
    bytesOfList (listOfBytes bytes) = bytes := rfl

/-- Decoding a string's own UTF-8 encoding recovers it: `String.fromUTF8?`
takes the validity branch on `s.isValidUTF8` (the proof `String` already
carries as a field), and `String.fromUTF8` applied to a string's own
byte array and validity proof is the string back, by the structure's own
eta. -/
theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.toUTF8_eq_toByteArray, String.fromUTF8?, dif_pos s.isValidUTF8,
    String.fromUTF8]

/-- A Wasm `name`: the UTF-8 byte length (LEB128), then those bytes. -/
def encodeName (s : String) : List UInt8 :=
  natToLEB128 (listOfBytes s.toUTF8).length ++ listOfBytes s.toUTF8

/-- Recover a name from the head of the list: an LEB128 length, that many
bytes, decoded as UTF-8 (`none` if they are not valid UTF-8 — this format
never emits invalid UTF-8, so this can only reject non-canonical bytes). -/
def decodeName (bytes : List UInt8) : Option (String × List UInt8) :=
  match readLEB128 bytes with
  | none => none
  | some (len, bytes) =>
      match takeBytes len bytes with
      | none => none
      | some (nameBytes, rest) =>
          match String.fromUTF8? (bytesOfList nameBytes) with
          | none => none
          | some s => some (s, rest)

/-- The name round trip: decoding a name's own canonical bytes recovers it
and the exact byte suffix. -/
theorem decodeName_encodeName (s : String) (rest : List UInt8) :
    decodeName (encodeName s ++ rest) = some (s, rest) := by
  unfold encodeName decodeName
  simp only [List.append_assoc, readLEB128_natToLEB128_append,
    takeBytes_append_of_eq rfl, bytesOfList_listOfBytes, fromUTF8?_toUTF8]

end Grass.Artifact.Wasm
