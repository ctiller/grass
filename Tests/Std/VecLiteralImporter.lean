import Tests.Std.VecLiteral

/-!
# The half of the measurement that needs a second module

`Tests/Std/VecLiteral.lean` shows a `scoped macro_rules` giving `Vec` the three
array-literal shapes the spike sources use. What it cannot show, from inside
itself, is the property that makes the mechanism shippable at all: that a module
which merely *imports* it keeps working `Array` literals.

That distinction is not pedantic. §3.5's objection is specifically about modules
that *transitively import* the library — "through `Memory`, most of the
repository" — and a fixture that only checks its own file has not tested that
claim, whatever it shows. This module tests it: it imports the rule's module and
does nothing but write `Array` literals.

Delete `scoped` from `Tests/Std/VecLiteral.lean` and both files fail — that
module at its own sibling-namespace checks, and this one because its dependency
no longer builds. Confirmed by running exactly that.

One caution for whoever edits this next, because it cost three wrong
measurements. `Tests/Std/VecLiteral.lean` mentions the string
`scoped macro_rules` in its prose before it reaches the declaration, so a
first-occurrence replacement edits a comment and the falsification silently
proves nothing. Anchor on the full declaration.
-/

namespace Grass.Tests.Std.VecLiteralImporter

/-- The declaration §3.5 names as the casualty of a global rule. -/
def c : Array Nat := #[1, 2, 3]

example : c.size = 3 := rfl

/-- And the one it says "silently becomes a `Vec`" — still an `Array` here. -/
def xs := #[1, 2, 3]

example : xs = (#[1, 2, 3] : Array Nat) := rfl

example : xs.toList = [1, 2, 3] := rfl

end Grass.Tests.Std.VecLiteralImporter
