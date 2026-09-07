import Lean

/-!
# Reading a facade's dependency cone

`docs/MODULES.md` requires every facade to carry a fixture demonstrating "both
halves of the boundary: the intended spike vocabulary resolves through the
concise import, and representative implementation-only declarations do not".

The second half is the awkward one. A test cannot observe a failed `import`, and
a test that merely *uses* the vocabulary shows only the first half -- the half
that fails loudly anyway, the moment an author writes the import.

The environment of a module is exactly its transitive import closure, so a
module importing only the facade can be asked directly what it can see.

## Why the cone is checked by name, not by sampling

The first version of this file checked a *list of declarations that must be
absent*. Two cold reviewers defeated that within one session, in two different
ways, and both defeats share a root: a negative list only ever says something
about the names on it.

* Rename or delete any absent name -- exactly what happens while a cone is being
  restructured, which is when the check matters most -- and the entry is
  vacuously satisfied. All four entries were replaced with plausible near-misses
  (`Grass.Memory.MemoryEvnt`, `Grass.ABI.Win64.UnwindInfoStruct`) and the
  fixture still passed.
* Widen the cone by something the list does not mention and nothing fires.
  Adding `Grass.Memory.Access`, `Grass.Obligation.Core` and
  `Grass.Semantics.Execution` to the ISA facade took its closure from 14 modules
  to 27 -- the memory, obligation and semantics layers all entered -- and the
  fixture passed.

So `checkCone` pins the closure itself: the exact set of `Grass` modules the
facade reaches. That is finite, exhaustive, and cannot go quietly vacuous,
because every module in the cone must be named and nothing else may appear. A
widening fails whether or not anyone anticipated the module that caused it.

The declaration list is kept as well, but its job is now the *first* half only:
a facade that stops exporting its own vocabulary is a breaking change for
everyone downstream, and that is worth its own error message.

One caveat that bounds what these fixtures prove: the fixture module also
imports `Lean`, so `Lean.*` is in scope. Only modules under `Grass` are compared,
and no `Grass` module is reachable from `Lean`, so the two closures do not
overlap.
-/

namespace Grass.Tests.Facade

open Lean Elab Command

/-- The `Grass` modules a fixture's own environment can reach. -/
def grassCone (env : Environment) : Array Name :=
  env.header.moduleNames.filter (fun m => (`Grass).isPrefixOf m)

/-- Fail unless the facade's cone is exactly `cone` and it exports `present`.

Both directions are errors rather than warnings: `warningAsError` makes that
distinction invisible, and a facade fixture that could pass while leaking would
be worse than no fixture. -/
def checkCone (facade : String) (cone present : List Name) :
    CommandElabM Unit := do
  let env ← getEnv
  let actual := (grassCone env).toList.map (·.toString) |>.mergeSort (· ≤ ·)
  let expected := cone.map (·.toString) |>.mergeSort (· ≤ ·)
  let entered := actual.filter (!expected.contains ·)
  let left := expected.filter (!actual.contains ·)
  unless entered.isEmpty do
    throwError
      "{facade}: {entered} entered the dependency cone. docs/MODULES.md holds \
       facades to a measured cone and forbids Impl, Cert, a whole-program \
       aggregate, or a concrete program from entering it for convenience. \
       Widening a facade widens what every downstream author compiles \
       against, so this is a reviewed change rather than a fix: if the new \
       edge is intended, add it here and say why in the facade's own header."
  unless left.isEmpty do
    throwError
      "{facade}: {left} is named here but is no longer in the cone. Drop it \
       if the edge was meant to go, so that this list keeps describing the \
       facade rather than describing its history."
  let missing := present.filter (!env.contains ·)
  unless missing.isEmpty do
    throwError
      "{facade}: the facade does not export {missing}. Either the shard that \
       declares each name left the cone, or the name changed; a facade that \
       stops exporting its own vocabulary is a breaking change for every \
       author downstream."

end Grass.Tests.Facade
