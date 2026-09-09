import Grass.Grammar.Binary

/-! # Derived binary-format fixtures -/

namespace Grass.Tests.Grammar

open Grass.Std.Logical Grass.Grammar

example (first second : Byte) (suffix : Std.Logical.ByteArray) :
    Derives (fixedBytesFormat 2)
      ((Vec.singleton first ++ Vec.singleton second) ++ suffix)
      ⟨Vec.singleton first ++ Vec.singleton second, by simp⟩ suffix := by
  exact Derives.lift (by
    simpa using anyBytes_derives
      (Vec.singleton first ++ Vec.singleton second) suffix)

example (input : Std.Logical.ByteArray) (short : input.length < 4) :
    (fixedBytesSemantics 4).repairableIncompletePrefix input
      (some (4 - input.length)) :=
  ⟨short, rfl⟩

end Grass.Tests.Grammar
