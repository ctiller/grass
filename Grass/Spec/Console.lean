import Grass.Console.WriteLineContract
import Grass.Console.Resources
import Grass.Specification.TextLine

/-!
# Specification-authoring facade: console

A thin re-export module. `Console.writeLineContract`, `ConsoleResourceModel`,
`ConsoleWriteResources` and `ConsoleWriteOutcomePolicy` are already declared
directly in namespace `Grass` (or `Grass.Console`, matched unqualified by a
spike's `Console.` prefix), so importing their defining modules is enough to
make them resolve. `TextLine` is declared in the sibling namespace
`Grass.Specification` and is aliased into `Grass` here so it resolves
unqualified too.
-/

namespace Grass

export Specification (TextLine)

end Grass
