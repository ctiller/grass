import Grass.Artifact.Binary.Realization
import Grass.Grammar.Whole

/-! # Whole-input parser fixtures -/

namespace Grass.Tests.Grammar.Whole

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

def byte (value : Nat) : Byte := BitVec.ofNat 8 value

example : requireWhole takeByte Vec.empty = .needMore (some 1) := rfl

example : requireWhole takeByte (Vec.singleton (byte 7)) =
    .done (byte 7) Vec.empty := by
  change requireWhole takeByte (writeByte (byte 7)) = .done (byte 7) Vec.empty
  simp [requireWhole]

example : requireWhole takeByte
    (Vec.singleton (byte 7) ++ Vec.singleton (byte 8)) =
    .invalid .trailingInput := by
  change requireWhole takeByte (writeByte (byte 7) ++ Vec.singleton (byte 8)) =
    .invalid .trailingInput
  simp [requireWhole]
  intro impossible
  have lengths := congrArg Vec.length impossible
  simp at lengths

example : ParserRealizes anyByteSemantics.whole (requireWhole takeByte) :=
  takeByte_realizes.whole

end Grass.Tests.Grammar.Whole
