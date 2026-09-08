import Grass.Artifact.PE.OptionalHeader

/-!
# Canonical PE32+ image headers

This module composes the `PE\0\0` signature, shared COFF file header, and
canonical PE32+ optional header. The resulting value carries the exact
`sizeOfOptionalHeader = 240` coupling required by the serialized components.
-/

namespace Grass.Artifact.PE

open Grass.Grammar Grass.Std.Logical

/-- A PE image-header prefix paired with its exactly declared optional header. -/
structure ImageHeaders where
  headerPrefix : HeaderPrefix
  optionalHeader : OptionalHeader
  optionalHeaderSize : headerPrefix.fileHeader.sizeOfOptionalHeader.toNat = 240
deriving DecidableEq, Repr

/-- Grammar product before the optional-header size invariant is promoted. -/
abbrev ImageHeadersProduct := HeaderPrefix × OptionalHeader

/-- Product refined by the COFF header's exact optional-header byte count. -/
abbrev CheckedImageHeaders :=
  {headers : ImageHeadersProduct //
    headers.1.fileHeader.sizeOfOptionalHeader.toNat = 240}

/-- Restore named image headers from their checked grammar product. -/
def ImageHeaders.ofChecked (headers : CheckedImageHeaders) : ImageHeaders :=
  ⟨headers.1.1, headers.1.2, headers.2⟩

/-- Forget field labels while retaining the exact size proof. -/
def ImageHeaders.toChecked (headers : ImageHeaders) : CheckedImageHeaders :=
  ⟨(headers.headerPrefix, headers.optionalHeader), headers.optionalHeaderSize⟩

/-- Named image headers and checked grammar products are totally isomorphic. -/
def imageHeadersIsomorphism :
    Isomorphism CheckedImageHeaders ImageHeaders where
  forward := ImageHeaders.ofChecked
  backward := ImageHeaders.toChecked
  backward_forward := by
    intro headers
    rcases headers with ⟨⟨headerPrefix, optionalHeader⟩, size⟩
    rfl
  forward_backward := by
    intro headers
    rcases headers with ⟨headerPrefix, optionalHeader, size⟩
    rfl

/-- Unrefined grammar for the 24-byte prefix and 240-byte optional header. -/
def rawImageHeadersFormat : Format ImageHeadersProduct :=
  .seq headerPrefixFormat fun _ => optionalHeaderFormat

/-- Promote the optional-header byte-count invariant into the grammar value. -/
def checkedImageHeadersFormat : Format CheckedImageHeaders :=
  rawImageHeadersFormat.refineValue fun headers =>
    headers.1.fileHeader.sizeOfOptionalHeader.toNat = 240

/-- Typed grammar of the complete canonical PE32+ image headers. -/
def imageHeadersFormat : Format ImageHeaders :=
  checkedImageHeadersFormat.iso imageHeadersIsomorphism

/-- Parse all 264 bytes and reject an inconsistent optional-header size. -/
def readImageHeaders (input : Std.Logical.ByteArray) :
    ParseResult ImageHeaders :=
  if 264 ≤ input.length then
    match readHeaderPrefix input with
    | .done headerPrefix afterPrefix =>
      match readOptionalHeader afterPrefix with
      | .done optionalHeader rest =>
        if size : headerPrefix.fileHeader.sizeOfOptionalHeader.toNat = 240 then
          .done ⟨headerPrefix, optionalHeader, size⟩ rest
        else
          .invalid (.malformed "PE32+ optional-header size mismatch")
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  else
    .needMore (some (264 - input.length))

/-- A truncated image-header block reports its exact whole-block deficit. -/
theorem readImageHeaders_short {input : Std.Logical.ByteArray}
    (short : input.length < 264) :
    readImageHeaders input = .needMore (some (264 - input.length)) := by
  simp [readImageHeaders, Nat.not_le.mpr short]

/-- Serialize the signature, COFF file header, and PE32+ optional header. -/
def writeImageHeaders (headers : ImageHeaders) : Std.Logical.ByteArray :=
  writeHeaderPrefix headers.headerPrefix ++
  writeOptionalHeader headers.optionalHeader

/-- Canonical PE32+ image headers occupy exactly 264 bytes. -/
@[simp] theorem length_writeImageHeaders (headers : ImageHeaders) :
    (writeImageHeaders headers).length = 264 := by
  simp [writeImageHeaders]

/-- `readImageHeaders_write_append` states that canonical image headers
round-trip while preserving an arbitrary suffix. -/
@[simp] theorem readImageHeaders_write_append
    (headers : ImageHeaders) (rest : Std.Logical.ByteArray) :
    readImageHeaders (writeImageHeaders headers ++ rest) =
      .done headers rest := by
  rcases headers with ⟨headerPrefix, optionalHeader, size⟩
  simp only [readImageHeaders, Vec.length_append, length_writeImageHeaders]
  have enough : 264 ≤ 264 + rest.length := by omega
  simp only [enough, ite_true, writeImageHeaders, Vec.append_assoc,
    readHeaderPrefix_writeHeaderPrefix_append,
    readOptionalHeader_write_append, size, ↓reduceDIte]

/-- Whole-input canonical image-header round trip. -/
@[simp] theorem readImageHeaders_write (headers : ImageHeaders) :
    readImageHeaders (writeImageHeaders headers) =
      .done headers Vec.empty := by
  simpa using readImageHeaders_write_append headers Vec.empty

/-- Every canonical image-header serialization derives from its grammar. -/
theorem writeImageHeaders_derives (headers : ImageHeaders) :
    Derives imageHeadersFormat (writeImageHeaders headers)
      headers Vec.empty := by
  rcases headers with ⟨headerPrefix, optionalHeader, size⟩
  unfold imageHeadersFormat
  refine @Derives.iso CheckedImageHeaders ImageHeaders
    checkedImageHeadersFormat imageHeadersIsomorphism _ Vec.empty
    ⟨(headerPrefix, optionalHeader), size⟩ ?_
  unfold checkedImageHeadersFormat
  apply Derives.lift
  unfold rawImageHeadersFormat writeImageHeaders
  exact Derives.seqAppend (writeHeaderPrefix_derives headerPrefix)
    (writeOptionalHeader_derives optionalHeader)

end Grass.Artifact.PE
