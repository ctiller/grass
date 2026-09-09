import Grass.Std.Logical.Vec

/-!
# The array-literal mechanism `docs/STDLIB_IMPLEMENTATION_PLAN.md` §3.5 ruled out

§3.5 measured three ways to let a consumer write `#[1, 2, 3]` for a `Vec` and
concluded that none is shippable. Its first row rejects `macro_rules` because the
rule is global once imported, so `Array` literals would stop elaborating in every
module that transitively imports this library — through `Memory`, most of the
repository.

**That row is correct, and confirmed here.** Removing `scoped` from the
declaration below breaks the `Array` checks in the sibling namespace, and breaks
`Tests/Std/VecLiteralImporter.lean` with it.

What §3.5 did not measure is the *scoped* form, and that changes the conclusion:
a rule that activates only where it is opened has none of the reach the objection
is about. This fixture is that measurement, so the claim is rerunnable rather
than argued.

**Nothing here is exported.** The notation is declared in this test module's own
namespace. `Grass/Std/Logical/` gains no notation, no new module, and no
`import Lean` — `macro_rules` is core syntax, which also answers §3.5's objection
to putting Lean's metaprogramming frontend at the base of the dependency chain.
Whether the library *should* ship this is a separate question §3.5 says is not
wholly its own, since the authored surface is governed by
`docs/SPIKE_AUTHORING.md` and "the spikes should write `Vec.fromList [...]`" is
an equally available answer. What this file settles is only the mechanism.
-/

namespace Grass.Tests.Std.VecLiteral

open Grass.Std.Logical

/-- The candidate, scoped so it activates only where it is opened. -/
scoped macro_rules | `(#[$elems,*]) => `(Vec.fromList [$elems,*])

end Grass.Tests.Std.VecLiteral

namespace Grass.Tests.Std.VecLiteralUse

open Grass.Std.Logical

/-! ## Outside the opt-in, `Array` is untouched

This is the whole objection §3.5 raises, and it does not apply to the scoped
form.

These checks live in a *sibling namespace* rather than beside the rule, and that
placement is load-bearing rather than tidiness. `scoped` is active inside its own
namespace, so an `Array` literal written next to the `macro_rules` line does not
elaborate. An earlier draft put them there and claimed same-file placement was
the stronger check; the build refused it. What the scoping confines is *other*
namespaces, which is what the objection is actually about.
-/

def plainArray : Array Nat := #[1, 2, 3]

example : plainArray.size = 3 := rfl

/-- Unascribed, so nothing steers elaboration: still an `Array`. -/
def inferred := #[1, 2, 3]

example : inferred = (#[1, 2, 3] : Array Nat) := rfl

/-! ## Opening the parent namespace does not activate it either

A consumer writes `open Grass.Std.Logical` to reach `Vec`. That must not change
what a literal means, or the opt-in would not be one. It does not: `Vec` is in
scope throughout this namespace and the two declarations above are `Array`s.
Opting in is a second, explicit `open`.
-/

section OptedIn

open Grass.Tests.Std.VecLiteral

/-! §3.5 lists the three shapes the spike sources use: an ascribed literal, `#[]`
returned where a `Vec` is expected, and `#[...]` as an operand of `++`. Its
`CoeTail` row fails the second and third. All three work here. -/

def ascribed : Vec Nat := #[1, 2, 3]

/-- The empty literal, where the element type is a metavariable — the case the
coercion could not reach. -/
def emptyLit : Vec Nat := #[]

/-- As an operand of `++`, which the coercion could not reach either, because it
does not see into `HAppend`. -/
def appended : Vec Nat := ascribed ++ #[9]

example : ascribed.length = 3 := rfl
example : emptyLit.length = 0 := rfl
example : appended.length = 4 := rfl
example : ascribed.toList = [1, 2, 3] := rfl
example : appended.toList = [1, 2, 3, 9] := rfl

end OptedIn

/-! ## The cost, which makes this a decision rather than a fix

Inside a scope that has opted in, an `Array` literal can no longer be written:
`#[1, 2, 3]` means a `Vec` there, so `(#[1, 2, 3] : Array Nat)` is a type error.
That is confined to modules that ask for it rather than repository-wide, but a
module needing both containers cannot have literal syntax for both, and would
write `Array.mk [1, 2, 3]` or not opt in.

This cost cannot be pinned by an example, because an example demonstrating it
would be a compile error. It was measured by writing
`def stillAnArray : Array Nat := #[1, 2, 3]` inside the section above and
observing the type mismatch — the same way the sibling-namespace requirement
above was found. It is described rather than checked, which is a real limit of
this fixture rather than an oversight.
-/

end Grass.Tests.Std.VecLiteralUse
