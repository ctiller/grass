import Grass.Artifact.Binary.Realization

/-! # Primitive binary reader/writer fixtures -/

namespace Grass.Tests.Artifact.Binary

open Grass.Std.Logical Grass.Grammar Grass.Artifact.Binary

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

example (value : Byte) :
    takeByte (writeByte value) = .done value Vec.empty :=
  parse_write takeByte_realizes writeByte_realizes value

example (value : Byte) (suffix : Std.Logical.ByteArray) :
    Derives anyByteFormat (writeByte value ++ suffix) value suffix :=
  writeByte_realizes.derivesWithSuffix value suffix

example (input : Std.Logical.ByteArray) (short : input.length < 8) :
    takeExact 8 input = .needMore (some (8 - input.length)) :=
  (takeExact_realizes 8).needMoreExact input (some (8 - input.length)) |>.2
    ⟨short, rfl⟩

end Grass.Tests.Artifact.Binary
