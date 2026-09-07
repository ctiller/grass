import Grass.Verify.VerifiedProgram

/-!
# Verified emission facade

`Grass.Emit` is the bounded author-facing entry point named by
`docs/MODULES.md`. It imports exactly `Grass.Verify.VerifiedProgram`, exposing
the checked `VerifiedProgram` gate, `emitProgram`, and their result theorems.

Importing a Lean module exposes its transitive closure, so this facade does not
claim namespace hiding. Its boundary is the single declared import above and
the compile-time non-reachability guards in `Tests/Artifact/EmitFacade.lean`.
Raw instruction encoders, memory implementations, artifact writers, linkers,
and unchecked construction remain outside this dependency cone.

This module deliberately declares nothing. Adding a second import or a new
emission function is a facade-boundary change requiring review.
-/
