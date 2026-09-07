import Grass.Grammar.Realization

/-! # Parser/writer realization fixtures -/

namespace Grass.Tests.Grammar

open Grass.Std.Logical Grass.Grammar

example (value : Byte) (rest : Std.Logical.ByteArray) :
    anyByteSemantics.selectedDerivation
      (Vec.singleton value ++ rest) value rest := rfl

example : anyByteSemantics.repairableIncompletePrefix Vec.empty (some 1) :=
  ⟨rfl, rfl⟩

example (error : ParseError) :
    ¬ anyByteSemantics.irrecoverablyInvalidPrefix Vec.empty error := by
  simp [anyByteSemantics]

end Grass.Tests.Grammar
