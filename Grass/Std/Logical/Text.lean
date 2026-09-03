import Grass.Std.Logical.HostBytes

/-!
# Text as bytes

`docs/STDLIB.md` §6 puts "encoding-indexed `String`/text views" in this library
and states one property precisely:

> UTF-8 conversion of a literal used as a logical constant reduces during kernel
> elaboration to the canonical `Vec Byte`, so consumers reason directly about its
> bytes and derive its length. Runtime or nonliteral conversion uses the ordinary
> law-bearing encoding API and does not borrow this definitional shortcut.

That is two demands. The second is an encoding function with laws, which is
`Text.utf8` below. The first is a *reduction* property — a claim about what the
kernel can compute, not about what can be proved — so the only honest way to
establish it is to make the kernel do it. `Tests/Std/Text.lean` does, by
`rfl`, including a multi-byte case.

## This delegates, and what that does and does not buy

`Text.utf8` is `Vec.ofHostBytes ∘ String.toUTF8`. It does not re-implement UTF-8,
and it is important to be exact about how little that costs and how little it
delivers, because an earlier draft of this module was wrong about both.

In this toolchain `String` is a structure over its own bytes:

```lean
structure String where ofByteArray ::
  toByteArray : ByteArray
  isValidUTF8 : ByteArray.IsValidUTF8 toByteArray
```

`String.toUTF8` is the projection and `String.fromUTF8` is the constructor. So
encoding and decoding are not algorithms this module could have got wrong; they
are taking a structure apart and putting it back together.

**What the laws below therefore do and do not say.** `Text.length_utf8` and
`Text.utf8_injective` are consequences of that structure, not of any encoder
being correct: `String.utf8ByteSize` is *defined* as `toByteArray.size`, so the
length law is close to definitional, and injectivity is structure injectivity.
A caller of `Text.utf8` on a non-literal string can derive its length, that
distinct texts stay distinct, and — via `Text.isValidUTF8_utf8` — that the bytes
are valid UTF-8, because `String` carries that as a field. These laws do not reach
the claim that any particular character maps to any particular bytes. That is what
`Tests/Std/Text.lean` exhibits by reduction, and `docs/FOUNDATION.md` §3 is
explicit that a fixture is evidence and never a theorem.

**The trust boundary, stated exactly.** `String.toByteArray` carries
`@[extern "lean_string_to_utf8"]`, and `Vec.toHostBytes`/`Vec.ofHostBytes` route
through `Array.mk` and `Array.toList`, which carry `@[extern "lean_array_mk"]`
and `@[extern "lean_array_to_list"]`. So at least three externs sit between these
theorems and running bytes. Kernel reduction and every theorem here use the Lean
models; the externs are what run. The axiom audit does not see any of
this, because an `@[extern]` is not an axiom, so a green audit run is not
evidence about this boundary. `docs/FOUNDATION.md` §3
asks for such a correspondence to be "recorded in the TCB ledger"; this repository
has no ledger file yet, and this module comment is a placeholder for one rather
than a substitute.

## What is absent

Encoding-indexed text *views* — `docs/STDLIB.md` §6's phrase. A `Text enc` type
indexed by its encoding should be designed against a consumer with a second
encoding, and UTF-8 is the only encoding any spike uses.

Nothing else. An earlier draft also listed decoding as absent, on the stated
grounds that core supplies no round-trip theorem and that supplying one "means
proving UTF-8 correctness against a specification, which is a project rather than
a function". That was false, and adversarial review caught it: because `String`
is the structure above, both round-trip directions are a few lines each and are
`Text.decode_utf8` and `Text.utf8_decode` below. The reason given for the absence
was not the reason for it.
-/

namespace Grass.Std.Logical

namespace Text

/--
The UTF-8 encoding of `s`, as the canonical byte sequence.

Delegates to Lean's `String.toUTF8` and crosses with `Vec.ofHostBytes`; see
`Text.toHostBytes_utf8` for the connection and the module comment for why this
delegates rather than re-implements.
-/
def utf8 (s : String) : Vec Byte := Vec.ofHostBytes s.toUTF8

/--
The crossing back is exactly Lean's encoding, so nothing is lost by routing
through `Vec Byte`.

Deliberately **not** `@[simp]`. A consumer review found that as a simp lemma it
fires inside `Vec.ofHostBytes (Vec.toHostBytes (Text.utf8 s))` before the general
`Vec.ofHostBytes_toHostBytes` can, rewriting away the redex that law needs and
leaving a goal that looks like it should have closed. A lemma that destroys a
more general lemma's left-hand side does not belong in the default set, and this
one is wanted at specific sites rather than everywhere.
-/
theorem toHostBytes_utf8 (s : String) : (utf8 s).toHostBytes = s.toUTF8 :=
  Vec.toHostBytes_ofHostBytes s.toUTF8

/-- The encoded length is the string's UTF-8 byte size, which is the "derive its
length" half of `docs/STDLIB.md` §6. -/
@[simp] theorem length_utf8 (s : String) : (utf8 s).length = s.utf8ByteSize := by
  rw [utf8, Vec.length_ofHostBytes, String.toUTF8_eq_toByteArray, String.size_toByteArray]

@[simp] theorem utf8_empty : utf8 "" = Vec.empty := by
  apply Vec.ext_of_get?
  intro i
  simp [utf8, Vec.ofHostBytes, Vec.get?, Vec.empty]

/--
The bytes of an encoded string are valid UTF-8.

Free, because `String` carries validity as a field, and worth exposing because it
is the only genuinely UTF-8-specific fact this module can offer. Without it a
consumer holding `Text.utf8 s` would have to reach into core to learn that its
bytes are well-formed.
-/
@[simp] theorem isValidUTF8_utf8 (s : String) :
    (utf8 s).toHostBytes.IsValidUTF8 := by
  rw [toHostBytes_utf8, String.toUTF8_eq_toByteArray]
  exact s.isValidUTF8

/--
Decode valid UTF-8 bytes back to text.

The validity argument is not ceremony: `docs/STDLIB.md` §6 makes text encoding
explicit at binary boundaries, and bytes arriving from one are not valid UTF-8
until something says so. `Text.isValidUTF8_utf8` discharges it for bytes this
module produced; bytes from elsewhere owe a proof.
-/
def decode (bytes : Vec Byte) (valid : bytes.toHostBytes.IsValidUTF8) : String :=
  String.fromUTF8 bytes.toHostBytes valid

/-- Decoding inverts encoding. -/
@[simp] theorem decode_utf8 (s : String) : decode (utf8 s) (isValidUTF8_utf8 s) = s := by
  simp only [decode, String.fromUTF8, toHostBytes_utf8, String.toUTF8_eq_toByteArray]

/-- And encoding inverts decoding, so no bytes are lost or invented in either
direction. -/
@[simp] theorem utf8_decode (bytes : Vec Byte) (valid : bytes.toHostBytes.IsValidUTF8) :
    utf8 (decode bytes valid) = bytes := by
  simp only [utf8, decode, String.toUTF8_eq_toByteArray, String.fromUTF8]
  exact Vec.ofHostBytes_toHostBytes bytes

/--
Encoding distributes over concatenation.

An earlier fixture asserted that the general law was "false for strings that
share a code point across the boundary" and pinned only a concrete instance.
That reason was wrong: every `String` is individually valid UTF-8 — it carries
the proof as a field — so no code point can straddle an append, and the law
holds unconditionally. Adversarial review found it. It is the law
`Spikes/4_Web_Server` needs to compose a header block with a body.
-/
@[simp] theorem utf8_append (a b : String) : utf8 (a ++ b) = utf8 a ++ utf8 b := by
  show Vec.ofHostBytes (a ++ b).toUTF8 = _
  rw [String.toUTF8, String.toByteArray_append, Vec.ofHostBytes_append]
  rfl

/-- Encoding is injective: two strings with the same bytes are the same string.
This is the property that lets a specification compare encoded payloads without
losing the distinction between the texts that produced them. -/
theorem utf8_injective {a b : String} (h : utf8 a = utf8 b) : a = b := by
  have hb : a.toUTF8 = b.toUTF8 := by
    rw [← toHostBytes_utf8 a, ← toHostBytes_utf8 b, h]
  have : a.toByteArray = b.toByteArray := by
    simpa using hb
  exact String.toByteArray_inj.mp this

end Text

end Grass.Std.Logical
