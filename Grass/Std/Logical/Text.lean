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

## This delegates, and that is a trust-ledger entry rather than a shortcut

`Text.utf8` is `Vec.ofHostBytes ∘ String.toUTF8`. It does not re-implement UTF-8.

Writing a second encoder would mean either proving it agrees with Lean's — which
needs a specification neither this library nor `docs/STDLIB.md` supplies — or
having two encoders in the trusted base where the corpus wants one. Delegating
puts the question where `docs/FOUNDATION.md` §3 wants it: as a named dependency
rather than as a private reimplementation.

The trust boundary is worth stating exactly, because it is not where it first
appears. `String.toUTF8` carries `@[extern "lean_string_to_utf8"]` over a Lean
model, `String.toByteArray`. Kernel reduction and every theorem here use the
model; the extern is what runs. So `Text.length_utf8` is a theorem about the
model, and the claim that a compiled program's bytes match it rests on the extern
agreeing with its model — a standard Lean trust assumption, already inside the
boundary `docs/FOUNDATION.md` §3 draws around the toolchain, and not one this
module widens.

## What is absent

Decoding. `String.fromUTF8` exists in core and takes a validity proof, but core
supplies no round-trip theorem relating it to `String.toUTF8`, so a
`Vec Byte → String` here could not carry the law that would make it worth
having. Supplying that law means proving UTF-8 correctness against a
specification, which is a project rather than a function, and no consumer has
asked: `docs/GZIP.md` and `docs/HTTP2_CONSTRAINTS.md` decode bytes as protocol
data rather than as text. It is an open item in
`docs/STDLIB_IMPLEMENTATION_PLAN.md` rather than a silent gap.

Encoding-indexed text *views* — `docs/STDLIB.md` §6's phrase — are likewise
absent. A `Text enc` type indexed by its encoding is a design that should be
written against a consumer with a second encoding, and UTF-8 is the only one any
spike uses.
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

/-- The crossing back is exactly Lean's encoding, so nothing is lost by routing
through `Vec Byte`. -/
@[simp] theorem toHostBytes_utf8 (s : String) : (utf8 s).toHostBytes = s.toUTF8 :=
  Vec.toHostBytes_ofHostBytes s.toUTF8

/-- The encoded length is the string's UTF-8 byte size, which is the "derive its
length" half of `docs/STDLIB.md` §6. -/
@[simp] theorem length_utf8 (s : String) : (utf8 s).length = s.utf8ByteSize := by
  rw [utf8, Vec.length_ofHostBytes, String.toUTF8_eq_toByteArray, String.size_toByteArray]

@[simp] theorem utf8_empty : utf8 "" = Vec.empty := by
  apply Vec.ext_of_get?
  intro i
  simp [utf8, Vec.ofHostBytes, Vec.get?, Vec.empty]

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
