import Grass.Std.Logical.HostBytes

/-!
# Crossing to Lean's byte array, and back

`Tests/Std/VecVocabulary.lean` pins that a host `_root_.ByteArray` is rejected
where a Grass `ByteArray` is required. This fixture is the other half of that
design: the crossing exists, it is explicit, and it loses nothing.

`docs/STDLIB.md` §1 asks a connection theorem to preserve order, length, and byte
values. Those are proved in `Grass/Std/Logical/HostBytes.lean`; what a fixture
adds is that they hold of an actual value rather than only of a quantified one,
and that the crossing still has to be written down at the use site.
-/

namespace Grass.Tests.Std.Host

open Grass.Std.Logical

/-! ## A concrete value survives the round trip

Every `ByteArray` below is qualified. This module is the first in the repository
to mention both byte arrays at once, and it is where `docs/STDLIB.md` §1's name
collision with Lean's prelude stops being hypothetical: a bare `ByteArray` here
is an ambiguity error naming both candidates. The naming question is open with
g-design; this fixture is now its concrete instance rather than an argument
about one.
-/

def hi : Grass.Std.Logical.ByteArray := Vec.fromList [0x48, 0x69, 0x21]

/-! Both call shapes are exercised deliberately. A first draft of
`Grass/Std/Logical/HostBytes.lean` put the crossing in a `ByteArray` namespace,
where it was reachable as `hi.toHost` here — because `hi`'s declared type is
written `ByteArray` — and unreachable through the type ascription in the last
section of this file, because `ByteArray` is an `abbrev` and dot notation lands
in `Vec`. Keeping both shapes pins that the operation resolves the same way
regardless of how its argument's type was spelled. -/

example : hi.toHostBytes.size = 3 := rfl
example : hi.toHostBytes.data.toList = [0x48, 0x69, 0x21] := rfl
example : Vec.ofHostBytes hi.toHostBytes = hi := Vec.ofHostBytes_toHostBytes hi

/-- Starting from the host side instead. -/
def hostHi : _root_.ByteArray := ⟨#[0x48, 0x69, 0x21]⟩

example : (Vec.ofHostBytes hostHi).length = 3 := rfl
example : (Vec.ofHostBytes hostHi).toHostBytes = hostHi := Vec.toHostBytes_ofHostBytes hostHi

/-- Order is preserved index by index, not merely in bulk. -/
example : (Vec.ofHostBytes hostHi).get? 1 = some 0x69 := rfl

/-! ## The crossing is still explicit

`Grass/Std/Logical/HostBytes.lean` deliberately supplies named functions rather
than a `Coe`, so the conversion appears at the use site. The rejection that
`Tests/Std/VecVocabulary.lean` pins is therefore unchanged by this module's
existence — which is the point, since a seam that a new import quietly dissolves
was never a seam.
-/

/--
error: Type mismatch
  hostHi
has type
  _root_.ByteArray
but is expected to have type
  Std.Logical.ByteArray
-/
#guard_msgs in
example : Grass.Std.Logical.ByteArray := hostHi

/-- And the conversion is what makes it typecheck. -/
example : Grass.Std.Logical.ByteArray := Vec.ofHostBytes hostHi

/-! ## Byte values are preserved, including the ones that would break a `Nat` route

`Byte` is `BitVec 8` and `UInt8` wraps `BitVec 8`, so the conversion is a
constructor swap and the round trip is `rfl`. The module comment notes that a
route through `Nat` and `UInt8.ofNat` would need a bound instead. `0xFF` is the
value that would expose a missing one.
-/

example : Byte.ofUInt8 (Byte.toUInt8 0xFF) = 0xFF := rfl
example : Byte.toUInt8 (Byte.ofUInt8 0xFF) = 0xFF := rfl
example :
    (Vec.fromList [0x00, 0x7F, 0x80, 0xFF] : Grass.Std.Logical.ByteArray).toHostBytes.data.toList
      = [0x00, 0x7F, 0x80, 0xFF] := rfl

end Grass.Tests.Std.Host
