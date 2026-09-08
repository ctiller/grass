import Grass.Artifact.Binary.Gobj.Scope

/-!
# Versioned proof-free `.gobj` payload envelope

`GobjPayload` is the deterministic first-order serialization boundary described
by `docs/VERIFIED_OBJECTS.md`. Table bodies remain uninterpreted framed bytes in
this layer; typed section, symbol, relocation, import, and source-map codecs are
layered above without changing the envelope.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Format versions accepted by the current `.gobj` envelope reader. -/
inductive GobjFormatVersion where
  | v1
deriving DecidableEq, Repr

/-- The first-order, proof-free fields carried by one `.gobj` file. -/
structure GobjPayload where
  formatVersion : GobjFormatVersion
  scope : StableScopeId
  sections : U32LengthPrefixedBytes
  symbols : U32LengthPrefixedBytes
  relocations : U32LengthPrefixedBytes
  imports : U32LengthPrefixedBytes
  sourceMap : U32LengthPrefixedBytes
deriving DecidableEq, Repr

/-- Four-byte ASCII `.gobj` discriminator (`GOBJ`). -/
def gobjMagic : SizedByteArray 4 :=
  ⟨Vec.fromList [0x47, 0x4f, 0x42, 0x4a], by decide⟩

/-- Numeric encoding of the sole currently supported format version. -/
def GobjFormatVersion.toBits : GobjFormatVersion → BitVec 16
  | .v1 => 1

/-- Decode a supported format version or classify it as unsupported data. -/
def readGobjFormatVersion (bits : BitVec 16) :
    Except ParseError GobjFormatVersion :=
  if bits = 1 then .ok .v1
  else .error (.unsupported "unsupported .gobj format version")

/-- The version decoder inverts the canonical version encoding. -/
@[simp] theorem readGobjFormatVersion_toBits (version : GobjFormatVersion) :
    readGobjFormatVersion version.toBits = .ok version := by
  cases version
  rfl

/-- Serialize the canonical envelope and its five independently framed bodies. -/
def writeGobj (payload : GobjPayload) : Std.Logical.ByteArray :=
  writeExact gobjMagic ++
  writeLittleEndian (count := 2) payload.formatVersion.toBits ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeStableScopeId payload.scope ++
  writeU32LengthPrefixedBytes payload.sections ++
  writeU32LengthPrefixedBytes payload.symbols ++
  writeU32LengthPrefixedBytes payload.relocations ++
  writeU32LengthPrefixedBytes payload.imports ++
  writeU32LengthPrefixedBytes payload.sourceMap

/-- Read and validate the complete fixed envelope while preserving any suffix. -/
def readGobj (input : Std.Logical.ByteArray) : ParseResult GobjPayload :=
  match takeExactSized 4 input with
  | .done magic afterMagic =>
    if _magicOk : magic = gobjMagic then
      match takeLittleEndian 2 afterMagic with
      | .done versionBits afterVersion =>
        match readGobjFormatVersion versionBits with
        | .ok version =>
          match takeLittleEndian 2 afterVersion with
          | .done reserved afterReserved =>
            if _reservedOk : reserved = 0 then
              match readStableScopeId afterReserved with
              | .done scope afterScope =>
                match readU32LengthPrefixedBytes afterScope with
                | .done sections afterSections =>
                  match readU32LengthPrefixedBytes afterSections with
                  | .done symbols afterSymbols =>
                    match readU32LengthPrefixedBytes afterSymbols with
                    | .done relocations afterRelocations =>
                      match readU32LengthPrefixedBytes afterRelocations with
                      | .done imports afterImports =>
                        match readU32LengthPrefixedBytes afterImports with
                        | .done sourceMap suffix =>
                          .done {
                            formatVersion := version
                            scope := scope
                            sections := sections
                            symbols := symbols
                            relocations := relocations
                            imports := imports
                            sourceMap := sourceMap } suffix
                        | .needMore hint => .needMore hint
                        | .invalid error => .invalid error
                      | .needMore hint => .needMore hint
                      | .invalid error => .invalid error
                    | .needMore hint => .needMore hint
                    | .invalid error => .invalid error
                  | .needMore hint => .needMore hint
                  | .invalid error => .invalid error
                | .needMore hint => .needMore hint
                | .invalid error => .invalid error
              | .needMore hint => requireAfter 20 (.needMore hint)
              | .invalid error => .invalid error
            else
              .invalid (.malformed "nonzero .gobj reserved field")
          | .needMore hint => .needMore hint
          | .invalid error => .invalid error
        | .error error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    else
      .invalid (.malformed "invalid .gobj magic")
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- `length_writeGobj` gives the exact envelope and framed-body byte width. -/
@[simp] theorem length_writeGobj (payload : GobjPayload) :
    (writeGobj payload).length =
      28 + (writeStableScopeId payload.scope).length +
        payload.sections.bytes.length + payload.symbols.bytes.length +
        payload.relocations.bytes.length + payload.imports.bytes.length +
        payload.sourceMap.bytes.length := by
  simp [writeGobj]
  omega

/-- `readGobj_write_append` parses a canonical payload exactly and preserves
every following suffix. -/
@[simp] theorem readGobj_write_append (payload : GobjPayload)
    (suffix : Std.Logical.ByteArray) :
    readGobj (writeGobj payload ++ suffix) = .done payload suffix := by
  unfold readGobj writeGobj
  simp only [Vec.append_assoc]
  rw [takeExactSized_writeExact_append]
  simp only [dite_true]
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only [readGobjFormatVersion_toBits]
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only [dite_true]
  rw [readStableScopeId_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]

/-- `readGobj_write` is the complete-input payload round trip. -/
@[simp] theorem readGobj_write (payload : GobjPayload) :
    readGobj (writeGobj payload) = .done payload Vec.empty := by
  simpa using readGobj_write_append payload Vec.empty

/-- Parse a complete `.gobj` buffer, rejecting both truncation and trailing data. -/
def parseGobj (input : Std.Logical.ByteArray) : Except ParseError GobjPayload :=
  match readGobj input with
  | .done payload rest =>
    if rest = Vec.empty then .ok payload else .error .trailingInput
  | .needMore _ => .error (.malformed "truncated .gobj payload")
  | .invalid error => .error error

/-- `parseGobj_write` is the normative complete-input `.gobj` corpus law. -/
@[simp] theorem parseGobj_write (payload : GobjPayload) :
    parseGobj (writeGobj payload) = .ok payload := by
  unfold parseGobj
  rw [readGobj_write]
  rfl

end Grass.Artifact.Binary.Gobj
