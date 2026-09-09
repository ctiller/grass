import Grass.Platform.Win32.Signatures

namespace Grass.Tests.Platform.Win32Signatures
open Grass.Platform.Win32.Signatures

example : argumentIndex? .writeFile "overlapped" = some 4 := by decide
example : argumentIndex? .writeFile "missing" = none := by decide
example : argumentIndex? .exitProcess "overlapped" = none := by decide
example : resolveName? "WriteFile" = some .writeFile := by decide
example : resolveImport? "__imp_WriteFile" = some .writeFile := by decide
example : resolveImport? "WriteFile" = none := by decide

end Grass.Tests.Platform.Win32Signatures
