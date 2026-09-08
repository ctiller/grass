import Grass.Artifact.COFF.Header

/-!
# PE image header prefix

Portable Executable images identify the image header with the four-byte
`PE\0\0` signature and then reuse the 20-byte COFF file-header record. This
module models that format boundary only; machine identifiers, optional-header
contents, section layout, and loader legality belong to later layers.
-/

namespace Grass.Artifact.PE

open Grass.Artifact.Binary Grass.Artifact.COFF Grass.Grammar Grass.Std.Logical

/-- The fixed four-byte signature beginning every PE image header. -/
def signatureBytes : Std.Logical.ByteArray :=
  Vec.fromList [0x50, 0x45, 0x00, 0x00]

/-- The PE signature has its format-mandated width. -/
@[simp] theorem length_signatureBytes : signatureBytes.length = 4 := rfl

/-- Exact-width PE signature value used by the generic fixed-byte grammar. -/
def signatureSized : SizedByteArray 4 :=
  ⟨signatureBytes, length_signatureBytes⟩

/-- The typed language containing exactly the `PE\0\0` signature. -/
def signatureFormat : Format Unit :=
  (fixedBytesFormat 4).lift fun _ => signatureSized

/-- Parse and validate the PE signature. Truncation retains the exact deficit;
a complete non-signature prefix is irrecoverably malformed. -/
def readSignature (input : Std.Logical.ByteArray) : ParseResult Unit :=
  match takeExact 4 input with
  | .done candidate rest =>
      if candidate = signatureBytes then .done () rest
      else .invalid (.malformed "PE signature mismatch")
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Emit the unique PE signature. -/
def writeSignature (_ : Unit) : Std.Logical.ByteArray := signatureBytes

/-- Every truncated signature reports the exact missing-byte count. -/
theorem readSignature_short {input : Std.Logical.ByteArray}
    (short : input.length < 4) :
    readSignature input = .needMore (some (4 - input.length)) := by
  rw [readSignature, takeExact_short short]

/-- `readSignature_writeSignature_append` states that the canonical signature
parser consumes exactly four bytes and preserves an arbitrary suffix. -/
@[simp] theorem readSignature_writeSignature_append (rest : Std.Logical.ByteArray) :
    readSignature (writeSignature () ++ rest) = .done () rest := by
  rw [readSignature]
  unfold writeSignature
  rw [takeExact_append length_signatureBytes rest]
  simp

/-- The canonical signature writer realizes `signatureFormat`. -/
theorem writeSignature_derives :
    Derives signatureFormat (writeSignature ()) () Vec.empty := by
  apply Derives.lift
  exact (derives_fixedBytes_iff).2 (by
    simpa [signatureSized, writeSignature] using
      anyBytes_derives signatureBytes Vec.empty)

/-- Named PE prefix following the signature. Its file-header field is the
shared 20-byte COFF binary record, without importing any instruction facts. -/
structure HeaderPrefix where
  fileHeader : COFF.Header
deriving DecidableEq, Repr

/-- Product representation consumed directly by the sequencing grammar. -/
abbrev HeaderPrefixFields := Unit × COFF.Header

/-- Restore a named PE prefix from its grammar product. -/
def HeaderPrefix.ofFields (fields : HeaderPrefixFields) : HeaderPrefix :=
  ⟨fields.2⟩

/-- Forget field names while retaining the unique signature witness. -/
def HeaderPrefix.toFields (headerPrefix : HeaderPrefix) : HeaderPrefixFields :=
  ((), headerPrefix.fileHeader)

/-- Named PE prefixes and signature/header products are a total isomorphism. -/
def headerPrefixFieldsIsomorphism :
    Isomorphism HeaderPrefixFields HeaderPrefix where
  forward := HeaderPrefix.ofFields
  backward := HeaderPrefix.toFields
  backward_forward := by
    intro fields
    rcases fields with ⟨signatureWitness, header⟩
    cases signatureWitness
    rfl
  forward_backward := by
    intro headerPrefix
    rcases headerPrefix with ⟨header⟩
    rfl

/-- Typed grammar for `PE\0\0` followed by the 20-byte file header. -/
def headerPrefixFormat : Format HeaderPrefix :=
  (Format.seq signatureFormat fun _ => COFF.headerFormat).iso
    headerPrefixFieldsIsomorphism

/-- Parse a PE signature and its following file header, preserving every byte
after the 24-byte prefix. -/
def readHeaderPrefix (input : Std.Logical.ByteArray) : ParseResult HeaderPrefix :=
  match readSignature input with
  | .done _ afterSignature =>
      match COFF.readHeader afterSignature with
      | .done fileHeader rest => .done ⟨fileHeader⟩ rest
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Serialize the signature and shared file-header record of a PE image. -/
def writeHeaderPrefix (headerPrefix : HeaderPrefix) : Std.Logical.ByteArray :=
  writeSignature () ++ COFF.writeHeader headerPrefix.fileHeader

/-- A serialized PE header prefix is exactly 24 bytes. -/
@[simp] theorem length_writeHeaderPrefix (headerPrefix : HeaderPrefix) :
    (writeHeaderPrefix headerPrefix).length = 24 := by
  simp [writeHeaderPrefix, writeSignature]

/-- `readHeaderPrefix_writeHeaderPrefix_append` states that reading a canonical
PE header consumes exactly its prefix and preserves an arbitrary suffix. -/
@[simp] theorem readHeaderPrefix_writeHeaderPrefix_append
    (headerPrefix : HeaderPrefix) (rest : Std.Logical.ByteArray) :
    readHeaderPrefix (writeHeaderPrefix headerPrefix ++ rest) =
      .done headerPrefix rest := by
  rcases headerPrefix with ⟨fileHeader⟩
  simp [readHeaderPrefix, writeHeaderPrefix, Vec.append_assoc]

/-- Whole-prefix reader/writer round trip. -/
@[simp] theorem readHeaderPrefix_writeHeaderPrefix
    (headerPrefix : HeaderPrefix) :
    readHeaderPrefix (writeHeaderPrefix headerPrefix) =
      .done headerPrefix Vec.empty := by
  simpa using readHeaderPrefix_writeHeaderPrefix_append headerPrefix Vec.empty

/-- Every canonical PE header-prefix serialization derives from
`headerPrefixFormat`. -/
theorem writeHeaderPrefix_derives (headerPrefix : HeaderPrefix) :
    Derives headerPrefixFormat (writeHeaderPrefix headerPrefix)
      headerPrefix Vec.empty := by
  rcases headerPrefix with ⟨fileHeader⟩
  unfold headerPrefixFormat
  refine @Derives.iso HeaderPrefixFields HeaderPrefix
    (Format.seq signatureFormat fun _ => COFF.headerFormat)
    headerPrefixFieldsIsomorphism
    (writeHeaderPrefix ⟨fileHeader⟩) Vec.empty ((), fileHeader) ?_
  unfold writeHeaderPrefix
  exact Derives.seqAppend writeSignature_derives
    (COFF.writeHeader_derives fileHeader)

end Grass.Artifact.PE
