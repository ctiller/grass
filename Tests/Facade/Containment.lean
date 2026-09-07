import Lean

/-!
# Reading a facade's dependency cone

`docs/MODULES.md` requires every facade to carry a fixture demonstrating "both
halves of the boundary: the intended spike vocabulary resolves through the
concise import, and representative implementation-only declarations do not".

The second half is the awkward one. A test cannot observe a failed `import`, and
a test that merely *uses* the vocabulary shows only the first half -- which is
the half that fails loudly anyway, the moment an author writes the import.

The environment of a module is exactly its transitive import closure, so a
module importing only the facade can be asked directly which names it can see.
That is what `checkCone` does. Absence here is absence from the cone, not
absence from the repository: every name in a `absent` list below is a real
declaration that another module can import perfectly well.

One caveat, stated because it bounds what these fixtures prove: the fixture
module also imports `Lean`, so `Lean.*` is in scope. Every name checked is under
`Grass`, and no `Grass` module is reachable from `Lean`, so the two closures do
not overlap.
-/

namespace Grass.Tests.Facade

open Lean Elab Command

/-- Fail unless every name in `present` is in the current environment and every
name in `absent` is not.

Both directions are errors rather than warnings, because `warningAsError` makes
that distinction invisible and a facade fixture that could pass while leaking
would be worse than no fixture. -/
def checkCone (facade : String) (present absent : List Name) :
    CommandElabM Unit := do
  let env ← getEnv
  let missing := present.filter (!env.contains ·)
  let leaked := absent.filter (env.contains ·)
  unless missing.isEmpty do
    throwError
      "{facade}: the facade does not export {missing}. Either the shard that \
       declares each name left the cone, or the name changed; a facade that \
       stops exporting its own vocabulary is a breaking change for every \
       author downstream."
  unless leaked.isEmpty do
    throwError
      "{facade}: {leaked} reached the cone. docs/MODULES.md holds facades to a \
       measured dependency cone and forbids Impl, Cert, a whole-program \
       aggregate, or a concrete program from entering it for convenience. \
       Adding an import to a facade widens what every downstream author \
       compiles against, so this is a reviewed change rather than a fix."

end Grass.Tests.Facade
