import Grass.Grammar.Core

/-!
# Generic grammar base fixtures

These examples pin empty, split, suffix, and truncation behavior. They challenge
the executable implementation; the theorems in `Grass.Grammar.Core` remain the
correctness evidence.
-/

namespace Grass.Tests.Grammar

open Grass.Std.Logical Grass.Grammar

def sample : Std.Logical.ByteArray := Vec.fromList [0x10, 0x20, 0x30]

example : takeByte Vec.empty = .needMore (some 1) := rfl

example : takeByte sample = .done 0x10 (Vec.fromList [0x20, 0x30]) := rfl

example : takeExact 0 sample = .done Vec.empty sample := by simp

example : takeExact 2 sample =
    .done (Vec.fromList [0x10, 0x20]) (Vec.fromList [0x30]) := rfl

example : takeExact 4 sample = .needMore (some 1) := rfl

example (byte : Byte) (suffix : Std.Logical.ByteArray) :
    takeByte (writeByte byte ++ suffix) = .done byte suffix := by simp

example (head suffix : Std.Logical.ByteArray) (h : head.length = 2) :
    takeExact 2 (head ++ suffix) = .done head suffix := by simp [h]

end Grass.Tests.Grammar
