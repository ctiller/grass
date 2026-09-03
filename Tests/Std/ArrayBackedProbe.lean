import Grass.Std.Logical.Vec

/-!
# What the `Vec := Array` representation buys, measured

This file exists only on `agent/c-stdlib/vec-as-array-probe` and is not proposed
for merge. It records what changes when `Vec` is Lean's `Array` rather than a
private one-field structure over `List`, so that
`docs/STDLIB_IMPLEMENTATION_PLAN.md` §3.2's open question is decided against
measurements instead of against two plausible-sounding arguments.

The parts that cannot be shown in a file are in the branch itself: swapping the
representation changed `Grass/Std/Logical/Vec.lean` by 25 insertions and 27
deletions, a net reduction, and changed nothing else. `Tests/Std/VecVocabulary.lean`,
`Tests/Std/SpikeSurface.lean`, and `Tests/Std/PartialWrite.lean` compile
completely unchanged, including both `#guard_msgs` rejection cases, so the
byte-container seam `docs/STDLIB.md` §1 demands survives the swap intact.

What this file adds is the half that could not be checked before: the spike
literal syntax of §3.5.
-/

namespace Grass.Tests.Std.ArrayBacked

open Grass.Std.Logical

/-! ## Array-literal syntax now works, with no notation of our own

`docs/STDLIB_IMPLEMENTATION_PLAN.md` §3.5 measured three mechanisms for making
`#[...]` build a `Vec` and rejected all three: `macro_rules` shadows Lean's array
literal repository-wide, `CoeTail` cannot reach `#[]` or `v ++ #[9]`, and an
expected-type elaborator never fires and would need `import Lean` at the base of
the dependency chain.

Under this representation the question dissolves. No notation is declared here.
-/

/-- `Spikes/5_Spinning_Cube/Layout.lean:10`, verbatim in shape. -/
def deviceExtensionNames : Vec String := #["VK_KHR_swapchain"]

/-- The empty literal, which `CoeTail` could not reach. -/
def noInstructions : Vec Nat := #[]

/-- A literal as an operand of `++`, which `CoeTail` could not reach either. -/
def appended (v : Vec Nat) : Vec Nat := v ++ #[9]

/-- The `Spikes/5_Spinning_Cube/Macros.lean` shape: a match whose branches are
literals, concatenated with expansion results. -/
def expandResult (result : Option Nat) (prefix_ : Vec Nat) : Vec Nat :=
  prefix_ ++ #[7] ++ (match result with | none => #[] | some k => #[k])

example : (appended (Vec.fromList [1])).toList = [1, 9] := rfl
example : (expandResult none (Vec.fromList [1])).toList = [1, 7] := rfl
example : (expandResult (some 5) (Vec.fromList [1])).toList = [1, 7, 5] := rfl
example : noInstructions.length = 0 := rfl

/-! ## Lean's array literal is unaffected

The `macro_rules` mechanism broke exactly this. Here `Array` literals still mean
`Array`, because nothing was overloaded.
-/

def stillAnArray : Array Nat := #[1, 2, 3]

def inferredAsArray := #[1, 2, 3]

example : stillAnArray.size = 3 := rfl
example : inferredAsArray.size = 3 := rfl

/-! ## The byte seam still holds, and byte literals become writable

`docs/STDLIB.md` §1 requires Grass's byte container and Lean's host `ByteArray`
to stay distinct types related by a connection theorem. `Vec Byte` is
`Array (BitVec 8)` under this representation while `_root_.ByteArray` is a
structure over `Array UInt8`, so they stay distinct; `Tests/Std/VecVocabulary.lean`
carries that rejection and the `List Byte` one, and both compile unchanged here.

Two things are worth adding at this representation. One is a gain: a byte-array
literal elaborates directly, which `Spikes/4_Web_Server/Macros.lean` writes
repeatedly and which no mechanism in §3.5 could deliver. The other is the check
that the gain did not cost anything, since numeric literals are polymorphic and
"it compiles" is not by itself evidence the element type is right: a `Vec Nat` is
still refused where a byte array is required.
-/

/-- A byte-array literal now elaborates directly, which
`Spikes/4_Web_Server/Macros.lean` writes repeatedly. Numeric literals are
polymorphic, so these are `BitVec 8` values rather than `Nat`s that leaked in. -/
example : Grass.Std.Logical.ByteArray := #[0x48, 0x69, 0x21]

/--
error: Type mismatch
  v
has type
  Vec Nat
but is expected to have type
  Std.Logical.ByteArray
-/
#guard_msgs in
example (v : Vec Nat) : Grass.Std.Logical.ByteArray := v

/-! ## What is still owed

`Array` does not carry `size_take`, `size_drop`, or `take_append_drop`, so the
prefix/suffix algebra that `docs/SPIKE_PROOF_BURDEN.md` names three times is
still this library's to write under either representation. That is the single
most-demanded item in the corpus, and it is unaffected by the choice — which is
worth knowing, because it means the choice is about the cheap half of the module
rather than the expensive half.

`Array` also spells length `size` rather than `length`, which
`docs/STDLIB.md` §3 names. This branch keeps `Vec.length` as its own definition
for that reason; a port that dropped it would be renaming a term the normative
document fixes.
-/

/-- The prefix laws still come from this library, not from core. -/
example (v : Vec Nat) (n : Nat) : v.take n ++ v.drop n = v := Vec.append_splitAt v n

/-- And `length` is still ours, because §3 names `length` and `Array` says `size`. -/
example (v : Vec Nat) : v.length = v.size := rfl

end Grass.Tests.Std.ArrayBacked
