import Grass.Std.Logical.Vec

/-!
# The sanctioned crossing to Lean's host `ByteArray`

`docs/STDLIB.md` §1 says two things that only make sense together. Grass "must not
introduce a second unrelated byte-container primitive", and:

> Adapters to Lean's host `ByteArray`, OS buffers, or foreign vectors require
> connection theorems preserving order, length, and byte values.

`Grass/Std/Logical/Vec.lean` implements the first half, and
`Tests/Std/VecVocabulary.lean` pins it: a host `_root_.ByteArray` is rejected
where a Grass `ByteArray` is required. That rejection is only half a design. A
seam with no sanctioned crossing is not a boundary, it is a dead end, and the
first author who needs to hand bytes to the operating system will cross it
somewhere — with `Array.map` and no theorem, in a module that does not own the
question.

This module is the crossing. §1 asks for three properties and each has a name
here: length by `Vec.size_toHostBytes` and `Vec.length_ofHostBytes`, order and
byte values by `Vec.getElem?_toHostBytes` and `Vec.get?_ofHostBytes` stated at
every index, and losslessness by `Vec.ofHostBytes_toHostBytes` and
`Vec.toHostBytes_ofHostBytes`.

## Why this is `Std.Logical` and not `Std.Owned`

Nothing here is a resource. `_root_.ByteArray` is a pure Lean value —
`structure ByteArray where mk :: data : Array UInt8` — so converting to and from
it is a total function between two logical sequences, with no allocator, no
provenance, and no loan. `docs/MODULES.md` puts `Std.Owned` above the memory and
obligation layers precisely so that pure conversions like this one do not have
to wait for them.

An *OS buffer* is a different matter and is not here. Handing a pointer and a
length to `WriteFile` involves provenance and a pinned loan, which
`docs/STDLIB.md` §5 assigns to `OwnedVec`'s `PinLoan`. This module stops at the
Lean value.

## Why `Byte` and `UInt8` round-trip exactly

`Byte` is `BitVec 8` by `docs/STDLIB.md` §1, and Lean's `UInt8` is
`structure UInt8 where ofBitVec :: toBitVec : BitVec 8`. The two are the same
eight bits behind different constructors, so `Byte.toUInt8` and `Byte.ofUInt8`
are mutually inverse by `rfl` rather than by a numeric argument about ranges.
That is worth stating because the obvious alternative encoding — through `Nat`
with `UInt8.ofNat` — would not be, since `UInt8.ofNat` reduces modulo 256 and
its inverse law needs a bound.
-/

namespace Grass.Std.Logical

/-! ## Bytes -/

namespace Byte

/-- Grass's byte as Lean's. -/
def toUInt8 (b : Byte) : UInt8 := UInt8.ofBitVec b

/-- Lean's byte as Grass's. -/
def ofUInt8 (u : UInt8) : Byte := u.toBitVec

@[simp] theorem ofUInt8_toUInt8 (b : Byte) : ofUInt8 (toUInt8 b) = b := rfl

@[simp] theorem toUInt8_ofUInt8 (u : UInt8) : toUInt8 (ofUInt8 u) = u := rfl

theorem toUInt8_injective {a b : Byte} (h : toUInt8 a = toUInt8 b) : a = b := by
  have := congrArg ofUInt8 h
  simpa using this

end Byte

/-! ## Byte arrays

Two naming decisions, both forced rather than chosen.

The crossing is named for its direction rather than overloaded on `coe`, because
`docs/STDLIB.md` §1 wants it visible at the use site. A coercion would make it
invisible, which is the property the rejection in `Tests/Std/VecVocabulary.lean`
exists to prevent.

It lives in the `Vec` namespace, not a `ByteArray` one, and carries `Bytes` in
its name to say what it converts. The reason is mechanical: `ByteArray` is an
`abbrev` for `Vec Byte`, so dot notation on a byte array resolves in the `Vec`
namespace and a `ByteArray.toHost` would be unreachable as `bytes.toHost` wherever
the elaborator had already unfolded the abbreviation. A first draft of this module
did exactly that and `Tests/Std/HostBytes.lean` caught it: the call worked on a
value whose declared type was written `ByteArray` and failed on the same value
reached through a type ascription. An operation that resolves depending on how
its argument's type was spelled is worse than one with a longer name.
-/

namespace Vec

/-- Grass's byte array as Lean's, in the same order. -/
def toHostBytes (bytes : Vec Byte) : _root_.ByteArray :=
  ⟨(bytes.toList.map Byte.toUInt8).toArray⟩

/-- Lean's byte array as Grass's, in the same order. -/
def ofHostBytes (host : _root_.ByteArray) : Vec Byte :=
  Vec.fromList (host.data.toList.map Byte.ofUInt8)

/-! ### Length is preserved -/

@[simp] theorem size_toHostBytes (bytes : Vec Byte) : (toHostBytes bytes).size = bytes.length := by
  show ((bytes.toList.map Byte.toUInt8).toArray).size = bytes.length
  simp [Vec.length]

@[simp] theorem length_ofHostBytes (host : _root_.ByteArray) :
    (ofHostBytes host).length = host.size := by
  show (host.data.toList.map Byte.ofUInt8).length = host.data.size
  simp

/-! ### Order and byte values are preserved

Stated at every index rather than as a statement about the whole, because "same
order" is exactly the claim that index `i` on one side is index `i` on the other.
-/

@[simp] theorem getElem?_toHostBytes (bytes : Vec Byte) (i : Nat) :
    (toHostBytes bytes).data[i]? = (bytes.get? i).map Byte.toUInt8 := by
  simp [toHostBytes, get?]

@[simp] theorem get?_ofHostBytes (host : _root_.ByteArray) (i : Nat) :
    (ofHostBytes host).get? i = host.data[i]?.map Byte.ofUInt8 := by
  simp [ofHostBytes, get?]

/-! ### The crossing is lossless in both directions -/

@[simp] theorem ofHostBytes_toHostBytes (bytes : Vec Byte) :
    ofHostBytes (toHostBytes bytes) = bytes := by
  apply Vec.ext_of_get?
  intro i
  simp [Option.map_map, Function.comp_def]

@[simp] theorem toHostBytes_ofHostBytes (host : _root_.ByteArray) :
    toHostBytes (ofHostBytes host) = host := by
  obtain ⟨data⟩ := host
  apply congrArg _root_.ByteArray.mk
  apply Array.ext'
  simp [ofHostBytes, List.map_map, Function.comp_def]

/--
The crossing is additive in both directions.

Missing until adversarial review proved it. Without it the crossing is a
bijection and nothing more, and a consumer joining two byte runs — a response
header block and a body, a frame and its payload — has to cross once at the end
instead of composing.
-/
@[simp] theorem ofHostBytes_append (x y : _root_.ByteArray) :
    ofHostBytes (x ++ y) = ofHostBytes x ++ ofHostBytes y := by
  apply toList_injective
  show (x ++ y).data.toList.map Byte.ofUInt8 = _
  show _ = (x.data.toList.map Byte.ofUInt8) ++ (y.data.toList.map Byte.ofUInt8)
  rw [← List.map_append, _root_.ByteArray.data_append, Array.toList_append]

/--
The other direction, without which the previous law is a regression.

`Vec.ofHostBytes_append` was added as `@[simp]` and fires innermost-first, so
`(ofHostBytes x ++ ofHostBytes y).toHostBytes = x ++ y` — a goal that `simp`
closed before it existed — was left stranded with nothing to finish the rewrite.
Adversarial review caught it. Adding a law can break a proof, and a one-sided
`@[simp]` homomorphism is the ordinary way.
-/
@[simp] theorem toHostBytes_append (a b : Vec Byte) :
    toHostBytes (a ++ b) = toHostBytes a ++ toHostBytes b := by
  apply congrArg _root_.ByteArray.mk
  apply Array.ext'
  simp [toHostBytes]

/-- `Vec.toHostBytes` loses nothing, so two Grass byte arrays that cross to the
same host value were equal. -/
theorem toHostBytes_injective {a b : Vec Byte}
    (h : toHostBytes a = toHostBytes b) : a = b := by
  have := congrArg ofHostBytes h
  simpa using this

end Vec

end Grass.Std.Logical
