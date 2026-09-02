import Grass.Std.Logical.Vec

/-!
# The `Vec` vocabulary expresses what `docs/STDLIB.md` §1 and §3 ask of it

`Tests.lean` states what a fixture is for: not to prove a theorem, but to have
the elaborator check that the vocabulary can express the cases it claims to.
Three claims in `Grass/Std/Logical/Vec.lean` are worth checking that way rather
than reading.

The first is the one `docs/STDLIB.md` §1 actually cares about — "Grass must not
introduce a second unrelated byte-container primitive". The module comment argues
that a one-field structure, rather than an `abbrev` over `List`, is what gives
that rule teeth. The `#guard_msgs` example below is that argument submitted to
the elaborator: if `Vec` were an abbreviation it would compile, and the rule
would be a naming convention. It also pins the name collision §1 creates with
Lean's host `ByteArray`, which is why every mention here is qualified.

The second is that extensionality concludes propositional equality here, unlike
`FiniteMap.Equiv`. `built_two_ways` uses it in the shape a consumer would.

The third is that the framing law is usable in the shape the memory layer
applies it: an update is visible at its own index and nowhere else.
-/

namespace Grass.Tests.Std

open Grass.Std.Logical

/-! ## A list of bytes is not a byte array

Every `ByteArray` below is written out in full. Bare `ByteArray` does not
elaborate inside `open Grass.Std.Logical`, because Lean's own `_root_.ByteArray`
is also in scope; that collision is recorded in `Grass/Std/Logical/Vec.lean` and
is an open naming question for the owner of `docs/STDLIB.md`.
-/

/--
error: Type mismatch
  [72, 105]
has type
  List Byte
but is expected to have type
  Std.Logical.ByteArray
-/
#guard_msgs in
example : Grass.Std.Logical.ByteArray := ([0x48, 0x69] : List Byte)

/-- The conversion is available; it is just not silent. -/
example : Grass.Std.Logical.ByteArray := Vec.fromList ([0x48, 0x69] : List Byte)

/-- And it round-trips, so nothing is lost by making it explicit. -/
theorem bytes_round_trip (l : List Byte) : (Vec.fromList l).toList = l := rfl

/-! Lean's host `ByteArray` stays reachable and stays separate. `docs/STDLIB.md` §1
asks for a connection theorem preserving order, length, and byte values rather
than an identification, and `Grass.Std.Owned` owns that adapter. What this
fixture records is only that no such theorem is being assumed by accident: a host
value is not silently a Grass one. -/

/--
error: Type mismatch
  ∅
has type
  _root_.ByteArray
but is expected to have type
  Std.Logical.ByteArray
-/
#guard_msgs in
example : Grass.Std.Logical.ByteArray := (∅ : _root_.ByteArray)

/-- A byte array reports the length of the bytes it holds. -/
example : (Vec.fromList ([0x48, 0x69, 0x21] : List Byte)).length = 3 := rfl

/-! ## Extensionality concludes equality -/

/--
The same three-element sequence reached two ways.

`docs/STDLIB.md` §5 asks for "extensionality by length and indexed values". This
is that law used the way a consumer would use it: two constructions that share no
step are equal because they agree at every index. Note the conclusion is `=`, not
a `Vec.Equiv`, which is the difference from `FiniteMap` the module comment
records.
-/
theorem built_two_ways :
    ((Vec.empty.push (1 : Nat)).push 2).push 3 = Vec.fromList [1, 2, 3] :=
  Vec.ext_of_get? (fun i => by
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | _ + 3 => rfl)

/-- `replicate` and a fold agree, again by index rather than by construction. -/
example : Vec.replicate 3 (0 : Nat) = Vec.fromList [0, 0, 0] := rfl

/-! ## Framing an update

`docs/MEMORY_MODEL.md` §3 reduces almost every memory proof to "this update did
not touch the index I am reading". `Grass/Std/Logical/FiniteMap.lean` supplies
that shape for keys; these are the sequence versions.
-/

variable {α : Type}

/-- An update is invisible at any other index. -/
theorem update_frames (v : Vec α) (i j : Nat) (h : j ≠ i) (a : α) :
    (v.set i a).get? j = v.get? j :=
  Vec.get?_set_ne v h a

/-- An in-range update is visible at its own index, and the length does not move. -/
theorem update_is_visible_and_keeps_length (v : Vec α) (i : Nat) (h : i < v.length) (a : α) :
    (v.set i a).get? i = some a ∧ (v.set i a).length = v.length :=
  ⟨Vec.get?_set_self v h a, Vec.length_set v i a⟩

/-- An out-of-range update changes nothing at all, rather than growing the
sequence or faulting. -/
theorem out_of_range_update_is_a_no_op (v : Vec α) {i : Nat} (h : v.length ≤ i) (a : α) :
    v.set i a = v :=
  Vec.ext_of_get? (fun j => by
    rw [Vec.get?_set]
    split
    · next hj =>
      subst hj
      rw [Vec.get?_eq_none v h]
      simp [Nat.not_lt_of_ge h]
    · rfl)

/-! ## Splitting loses nothing -/

/-- `docs/STDLIB.md` §5's order preservation for `append`, in the form a parser or
a chunked byte channel needs: cutting anywhere and rejoining is the identity. -/
theorem cut_and_rejoin (v : Vec α) (n : Nat) : v.take n ++ v.drop n = v :=
  Vec.append_splitAt v n

/-- The two halves account for the whole length. -/
theorem halves_account_for_the_length (v : Vec α) (n : Nat) :
    (v.take n).length + (v.drop n).length = v.length := by
  simp only [Vec.length_take, Vec.length_drop]
  omega

/-! ## Map preserves position -/

/-- A mapped sequence holds the mapped element at the same index. This is the
statement `docs/STDLIB.md` §5 calls order preservation for `map`. -/
theorem map_keeps_position {β : Type} (f : α → β) (v : Vec α) (i : Nat) :
    (v.map f).get? i = (v.get? i).map f :=
  Vec.get?_map f v i

/-- Fusion, in the shape a two-pass pipeline would rely on. -/
theorem two_passes_are_one {β γ : Type} (f : α → β) (g : β → γ) (v : Vec α) :
    (v.map f).map g = v.map (fun a => g (f a)) :=
  Vec.map_map g f v

end Grass.Tests.Std
