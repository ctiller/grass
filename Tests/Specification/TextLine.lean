import Grass.Specification.TextLine

namespace Grass.Tests.Specification.TextLine

open Grass.Std.Logical
open Grass.Specification

/-- The intended authored literal surface elaborates without extra syntax. -/
def message : TextLine := "Sample"

example : message.text = "Sample" := rfl

example :
    ({ encoding := TextEncoding.utf8, newline := crlf } : LineRendering).bytes message =
      Text.utf8 "Sample\r\n" := rfl

/-- Line-ending policy is selected explicitly for the same logical message. -/
example :
    ({ encoding := TextEncoding.utf8, newline := lf } : LineRendering).bytes message =
      Text.utf8 "Sample\n" := rfl

example :
    ({ encoding := TextEncoding.utf8, newline := lf } : LineRendering).bytes message ≠
      ({ encoding := TextEncoding.utf8, newline := crlf } : LineRendering).bytes message := by
  decide

example :
    (({ encoding := TextEncoding.utf8, newline := crlf } : LineRendering).bytes message).toList =
      [0x53, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x0d, 0x0a] := rfl

end Grass.Tests.Specification.TextLine
