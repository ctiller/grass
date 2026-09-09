import Grass.Assembly.SourceImportRequests
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.SourceImportRequests
open Grass.Assembly.SourceImportRequests

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def actual : Option (List String × List String × List Grass.Std.Logical.ByteArray ×
    Grass.Std.Logical.ByteArray) := do
  let body ← (Grass.Assembly.SourceInput.extractHelloSourceChars authored).toOption
  let frame ← Grass.Assembly.SourceFrame.derive? body
  let splice ← Grass.Assembly.SourceSplice.derive? frame 0
  let result ← resolve? splice "selected-library.dll"
  pure (result.sourceNames, result.entries.map Entry.sourceName,
    result.entries.map (fun entry => entry.nativeSymbol.name), result.library.name)

example : actual = some
    (["__imp_GetStdHandle", "__imp_WriteFile", "__imp_ExitProcess"],
     ["__imp_GetStdHandle", "__imp_WriteFile", "__imp_ExitProcess"],
     [Grass.Std.Logical.Text.utf8 "GetStdHandle",
      Grass.Std.Logical.Text.utf8 "WriteFile",
      Grass.Std.Logical.Text.utf8 "ExitProcess"],
     Grass.Std.Logical.Text.utf8 "selected-library.dll") := by decide +kernel

example : (resolveName? "__imp_WriteFile").map
    (fun entry => (entry.sourceName, entry.api, entry.nativeSymbol.name)) =
    some ("__imp_WriteFile", .writeFile,
      Grass.Std.Logical.Text.utf8 "WriteFile") := by decide +kernel

example : resolveName? "__imp_Unknown" = none := by decide +kernel

end Grass.Tests.Assembly.SourceImportRequests
