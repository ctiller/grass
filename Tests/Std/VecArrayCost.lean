import Grass.Std.Logical.VecArray
import Grass.Std.Logical.Vec

/-!
# What the Array-backed representation keeps, and what it costs

`Grass/Std/Logical/VecArray.lean` is a costing experiment, not a proposal to
merge. It answers the question adversarial review left open: the shipped `Vec` is
a structure over `List` and is quadratic to build; `agent/c-stdlib/vec-as-array-probe`
made `Vec` an `abbrev` for `Array` but left every body list-shaped, so it is a
rename and no faster. Neither had been compared against the option of a distinct
structure whose *field* is an `Array`.

This fixture pins the half that is about types. The half that is about speed is
in the commit message and `docs/STDLIB_IMPLEMENTATION_PLAN.md` §3.2, because a
timing is evidence and `Tests.lean` is explicit that a fixture is not a theorem.

## The type distinction survives, and is strictly stronger than the abbreviation's

`docs/STDLIB.md` §1 forbids a second unrelated byte-container primitive. The
shipped `Vec` enforces that by being a distinct type; so does `abbrev Vec :=
Array`, for `List Byte` and for the host `ByteArray`. What the abbreviation gives
up, and this representation keeps, is the third case: under `abbrev Vec :=
Array`, a bare `Array Byte` *is* a Grass byte array, so any array of bytes from
anywhere satisfies the type. All three rejections are pinned below.
-/

namespace Grass.Tests.Std.ArrayCost

open Grass.Std.Logical

def hi : AByteArray := AVec.fromList [0x48, 0x69, 0x21]

example : hi.length = 3 := by decide

example : hi.get? 1 = some 0x69 := by decide

/-! ## Three rejections, not two -/

/--
error: Type mismatch
  [72, 105]
has type
  List Byte
but is expected to have type
  AByteArray
-/
#guard_msgs in
example : AByteArray := ([0x48, 0x69] : List Byte)

/--
error: Type mismatch
  ∅
has type
  _root_.ByteArray
but is expected to have type
  AByteArray
-/
#guard_msgs in
example : AByteArray := (∅ : _root_.ByteArray)

/-! The third rejection, which `abbrev Vec := Array` would not give. Under the
abbreviation an `Array Byte` and a Grass `ByteArray` are the same type, so
nothing stops bytes from an arbitrary array being treated as the reviewed
container. Here they are distinct and the crossing has to be written. -/

/--
error: Type mismatch
  #[72, 105]
has type
  Array Byte
but is expected to have type
  AByteArray
-/
#guard_msgs in
example : AByteArray := (#[0x48, 0x69] : Array Byte)

/-- And the crossing is one constructor, so keeping the distinction is not
expensive at a use site. -/
example : AByteArray := AVec.ofArray (#[0x48, 0x69] : Array Byte)

/-! ## The laws port, and where they stop being free

Seventeen laws were ported from the shipped `Vec`. The routes, which are the
costing result:

- **Ten proved by a native `Array` lemma**, one line each: the `length`/`get?`
  laws for `empty`, `push`, `set`, `append`, and `map`. `Array` has
  `size_push`, `size_setIfInBounds`, `getElem?_push`, `getElem?_setIfInBounds_ne`,
  `size_append`, `size_map`, `getElem?_map` and they apply directly.
- **Four needed dropping to `Array.toList`**: extensionality, `length_take`,
  `length_drop`, and `append_splitAt`. This is not incidental — `Array` has no
  `size_take`, no `size_drop`, and no `take_append_drop`, so the entire
  prefix/suffix algebra that `docs/SPIKE_PROOF_BURDEN.md` names three times has
  to be rebuilt over lists whichever representation is chosen.
- **One was awkward**: `get?_push_lt`. `Array.getElem?_push_lt` concludes
  `= some xs[i]` rather than `= xs[i]?`, so it does not match a `get?`-shaped
  law; the `if`-form plus a disequality is what works.
- Two round trips were free.

So the porting cost is real but bounded, and it is concentrated in exactly the
place where `Array`'s own API is thin.
-/

example (v : AVec Nat) (a : Nat) : (v.push a).length = v.length + 1 :=
  AVec.length_push v a

example (v : AVec Nat) (n : Nat) : v.take n ++ v.drop n = v :=
  AVec.append_splitAt v n

/-- The two representations agree on what they compute, which is the minimum for
a migration to be a migration rather than a rewrite of meaning. -/
example :
    (AVec.fromList [1, 2, 3] : AVec Nat).toList = (Vec.fromList [1, 2, 3] : Vec Nat).toList :=
  rfl

end Grass.Tests.Std.ArrayCost
