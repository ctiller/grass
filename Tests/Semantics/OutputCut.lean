import Grass.Semantics.OutputCut
import Grass.Std.Logical.Text

/-! Byte cuts deliberately include undecodable character and newline prefixes. -/
namespace Grass.Tests.Semantics.OutputCut

open Std.Logical Grass.Semantics

private def payload : Vec Byte := Text.utf8 "é\r\n"
private def characterInterior : OutputCut payload := ⟨1, by decide⟩
private def newlineInterior : OutputCut payload := ⟨3, by decide⟩

/-- The first byte alone is retained, even though it is not complete UTF-8. -/
example : characterInterior.emitted.toList = [0xC3] := rfl

/-- CR without the LF is a distinct permitted represented cut. -/
example : newlineInterior.emitted.toList = [0xC3, 0xA9, 0x0D] := rfl

/-- Arbitrary subdivision preserves all bytes across these interior cuts. -/
example : characterInterior.between newlineInterior ++
    newlineInterior.between (OutputCut.full payload) =
    characterInterior.between (OutputCut.full payload) :=
  OutputCut.between_compose _ _ _ (by decide) (by decide)

end Grass.Tests.Semantics.OutputCut
