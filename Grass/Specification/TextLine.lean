import Grass.Std.Logical.Text

/-!
# Logical text lines and their rendering

`TextLine` records exactly the text requested by a portable specification.  It
does not choose an encoding or a line ending.  Those choices are values in
`LineRendering`, so LF, CRLF, and any later target convention remain explicit
projection data.
The encoding laws and `LineRendering.bytes_eq_append` prove exact rendering of
the selected text. Conformance of the selected terminator to a platform's
newline convention is a separate obligation of that target plan.
-/

namespace Grass.Specification

open Grass.Std.Logical

/-- A logical line containing exactly its authored text. -/
structure TextLine where
  /-- The text, without an implicitly added line ending. -/
  text : String
  deriving DecidableEq, Repr

/-- String literals and other `String` values may be used as logical lines. -/
instance : Coe String TextLine := ⟨TextLine.mk⟩

/--
An encoding together with the laws required to move between text and bytes.

`encode_decode` applies only when decoding succeeds; invalid byte sequences do
not acquire an arbitrary textual meaning.
-/
structure TextEncoding where
  /-- Encode logical text as bytes. -/
  encode : String → Vec Byte
  /-- Decode bytes, rejecting sequences outside this encoding. -/
  decode : Vec Byte → Option String
  /-- Encoding empty text emits no bytes. -/
  encode_empty : encode "" = Vec.empty
  /-- `TextEncoding.encode_append` is the required text-concatenation law. -/
  encode_append : ∀ a b, encode (a ++ b) = encode a ++ encode b
  /-- Every encoded string decodes to that same string. -/
  decode_encode : ∀ text, decode (encode text) = some text
  /-- Every successful decoding re-encodes to the original bytes. -/
  encode_decode : ∀ bytes text, decode bytes = some text → encode text = bytes

namespace TextEncoding

/-- The law-bearing UTF-8 encoding supplied by the logical text foundation. -/
def utf8 : TextEncoding where
  encode := Text.utf8
  decode := Text.decode?
  encode_empty := Text.utf8_empty
  encode_append := Text.utf8_append
  decode_encode := Text.decode?_utf8
  encode_decode := by
    intro bytes text decoded
    unfold Text.decode? at decoded
    split at decoded
    · next valid =>
      simp only [Option.some.injEq] at decoded
      subst text
      exact Text.utf8_decode bytes valid
    · contradiction

/--
`TextEncoding.encode_injective` derives injectivity from the decoding law.

This strong claim is enforced by `decode_encode`: applying the same decoder to
equal encodings recovers the two original strings.
-/
theorem encode_injective (encoding : TextEncoding) : Function.Injective encoding.encode := by
  intro a b equal
  have decoded : encoding.decode (encoding.encode a) =
      encoding.decode (encoding.encode b) := congrArg encoding.decode equal
  simpa [encoding.decode_encode] using decoded

end TextEncoding

/-- Explicit rendering choices; this value does not certify platform conformance. -/
structure LineRendering where
  /-- The selected text encoding. -/
  encoding : TextEncoding
  /-- The exact terminator text selected by the caller or target projection. -/
  newline : String

namespace LineRendering

/-- Render a line followed by the selected target newline. -/
def bytes (rendering : LineRendering) (line : TextLine) : Vec Byte :=
  rendering.encoding.encode (line.text ++ rendering.newline)

/-- Rendering is the concatenation of the separately encoded text and newline. -/
theorem bytes_eq_append (rendering : LineRendering) (line : TextLine) :
    rendering.bytes line =
      rendering.encoding.encode line.text ++ rendering.encoding.encode rendering.newline :=
  rendering.encoding.encode_append _ _

/--
With a fixed rendering, equal rendered lines have equal authored text.

This strong claim is enforced by `TextEncoding.encode_injective`, followed by
right cancellation of the fixed `newline` from the decoded concatenations.
-/
theorem bytes_injective (rendering : LineRendering) : Function.Injective rendering.bytes := by
  intro a b equal
  have joined : a.text ++ rendering.newline = b.text ++ rendering.newline :=
    rendering.encoding.encode_injective equal
  cases a with
  | mk aText =>
    cases b with
    | mk bText =>
      congr
      exact (String.append_left_inj rendering.newline).mp joined

/-- UTF-8 rendering is exactly the existing canonical UTF-8 conversion. -/
@[simp] theorem utf8_bytes_exact (newline : String) (line : TextLine) :
    ({ encoding := TextEncoding.utf8, newline := newline } : LineRendering).bytes line =
      Text.utf8 (line.text ++ newline) := rfl

end LineRendering

/-- The LF line ending, available for explicit selection by a rendering. -/
def lf : String := "\n"

/-- The CRLF line ending, available for explicit selection by a rendering. -/
def crlf : String := "\r\n"

end Grass.Specification
