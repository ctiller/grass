import Grass.Std.Logical.Text

/-!
# A UTF-8 literal reduces to its bytes

`docs/STDLIB.md` §6 makes a claim that no theorem can discharge:

> UTF-8 conversion of a literal used as a logical constant reduces during kernel
> elaboration to the canonical `Vec Byte`, so consumers reason directly about its
> bytes and derive its length.

"Reduces during kernel elaboration" is a statement about what the kernel can
compute. A theorem proved by `simp` would establish that the equation holds, not
that it holds *by reduction*, which is the property a consumer relies on when it
writes `decide` or pattern-matches on a payload's bytes. So every example in the
first two sections is closed by `rfl` on purpose, and would be worthless closed
any other way.

`Spikes/4_Web_Server/Spec.lean` is the consumer this matters to: it states a
response-body equation against an encoded literal, and that equation is only
checkable if the literal's bytes are computable.
-/

namespace Grass.Tests.Std.Text

open Grass.Std.Logical

/-! ## ASCII literals reduce to their bytes and their length -/

example : (Text.utf8 "Hi").toList = [0x48, 0x69] := rfl
example : (Text.utf8 "Hi").length = 2 := rfl
example : (Text.utf8 "").length = 0 := rfl

/-- `Spikes/1_Hello_World/Spec.lean`'s message, whose exact bytes are the
observable the whole spike is specified against. -/
example : (Text.utf8 "Hello, World!").length = 13 := rfl

/-- Indexing reduces too, so a consumer can name a byte rather than the whole. -/
example : (Text.utf8 "Hi").get? 1 = some 0x69 := rfl

/-! ## Multi-byte literals reduce as well

This is the case that separates real reduction from an ASCII fast path. `é` is
two bytes and `€` is three, so a length derived from the character count would be
wrong here and the corpus's "derive its length" would be unsound.
-/

example : (Text.utf8 "é").toList = [0xC3, 0xA9] := rfl
example : (Text.utf8 "é").length = 2 := rfl
example : (Text.utf8 "€").toList = [0xE2, 0x82, 0xAC] := rfl
example : (Text.utf8 "€").length = 3 := rfl

/-- One character, four bytes: the astral plane still reduces. -/
example : (Text.utf8 "𝄞").length = 4 := rfl

/-- And a mixed string, so the length is not accidentally a character count. -/
example : (Text.utf8 "a€b").length = 5 := rfl

/-! ## The literal shortcut does not leak into the general API

`docs/STDLIB.md` §6's second sentence is the constraint: "Runtime or nonliteral
conversion uses the ordinary law-bearing encoding API and does not borrow this
definitional shortcut." Nothing in `Grass/Std/Logical/Text.lean` special-cases a
literal — `Text.utf8` is one function — so a non-literal argument gets the same
function and the same laws, and simply does not reduce, because there is nothing
to reduce.
-/

/-- The general law applies to a variable string, where no reduction is possible. -/
example (s : String) : (Text.utf8 s).length = s.utf8ByteSize := Text.length_utf8 s

/-- And the crossing back is Lean's own encoding, for any string. -/
example (s : String) : (Text.utf8 s).toHostBytes = s.toUTF8 := Text.toHostBytes_utf8 s

/-- Distinct texts stay distinguishable after encoding, which is what lets a
specification compare payloads without collapsing them. -/
example : Text.utf8 "a" ≠ Text.utf8 "b" := by
  intro h
  exact absurd (Text.utf8_injective h) (by decide)

/-! ## Bytes reach the host encoding unchanged

The point of routing text through `Vec Byte` rather than Lean's `ByteArray` is
that the sequence laws apply to it. The point of `Vec.toHostBytes` is that
nothing is lost on the way back out to whatever writes it.
-/

example : (Text.utf8 "Hi").toHostBytes.data.toList = [0x48, 0x69] := rfl

/-! Encoding distributes over concatenation, in general.

An earlier version of this fixture pinned only the concrete instance below and
justified the omission by asserting that the general law is "false for strings
that share a code point across the boundary". That was wrong, and adversarial
review proved the general law. No code point can straddle an append: every
`String` carries a proof that its own bytes are valid UTF-8, so there is no
partial sequence at either end to join with. The law is `Text.utf8_append`.
-/

example (a b : String) : Text.utf8 (a ++ b) = Text.utf8 a ++ Text.utf8 b :=
  Text.utf8_append a b

/-- The concrete instance, kept because it reduces. -/
example : Text.utf8 "Hi" ++ Text.utf8 "!" = Text.utf8 "Hi!" := rfl

/-- And a multi-byte join, which is the case the false claim was about. -/
example : Text.utf8 "€" ++ Text.utf8 "a" = Text.utf8 "€a" := rfl

/-! ## Decoding

Also absent until adversarial review showed the stated blocker was false. -/

example (s : String) : Text.decode (Text.utf8 s) (Text.isValidUTF8_utf8 s) = s :=
  Text.decode_utf8 s

example : Text.decode (Text.utf8 "Hi!") (Text.isValidUTF8_utf8 "Hi!") = "Hi!" := by
  simp

/-- The bytes of an encoded string are valid UTF-8 — the one genuinely
UTF-8-specific fact this module can offer, and free because `String` carries it
as a field. -/
example (s : String) : (Text.utf8 s).toHostBytes.IsValidUTF8 := Text.isValidUTF8_utf8 s

end Grass.Tests.Std.Text
