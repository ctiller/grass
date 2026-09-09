import Grass.Specification.TextLine

namespace Grass.Tests.Specification.TextLine

open Grass.Std.Logical
open Grass.Specification

/-- The intended authored literal surface elaborates without extra syntax. -/
def message : TextLine := "Hello, World!"

example : message.text = "Hello, World!" := rfl

example :
    ({ encoding := TextEncoding.utf8, newline := crlf } : LineRendering).bytes message =
      Text.utf8 "Hello, World!\r\n" := rfl

/-- Line-ending policy is selected explicitly for the same logical message. -/
example :
    ({ encoding := TextEncoding.utf8, newline := lf } : LineRendering).bytes message =
      Text.utf8 "Hello, World!\n" := rfl

example :
    ({ encoding := TextEncoding.utf8, newline := lf } : LineRendering).bytes message ≠
      ({ encoding := TextEncoding.utf8, newline := crlf } : LineRendering).bytes message := by
  decide

example :
    (({ encoding := TextEncoding.utf8, newline := crlf } : LineRendering).bytes message).toList =
      [0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x57, 0x6f, 0x72, 0x6c,
        0x64, 0x21, 0x0d, 0x0a] := rfl

end Grass.Tests.Specification.TextLine
