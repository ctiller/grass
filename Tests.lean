/-!
# Fixture root

The Lake root of the `Tests` library. Like `Grass.lean` it imports nothing, and
for the same reason: the `Tests.+` glob in `lakefile.toml` builds every fixture
without an umbrella importing them.

Fixtures are evidence, not proof. `docs/FOUNDATION.md` §3 is explicit that "Tests
challenge trust; they never establish a theorem." What these files do establish is
narrower and still worth having: that the vocabulary can *express* the cases it
claims to, checked by the elaborator rather than by assertion.
-/
