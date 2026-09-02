/-!
# Grass library root

This module is the Lake root of the `Grass` library. It deliberately imports
nothing.

`docs/OLEAN_SHARDING.md` forbids a leaf importing a whole-program umbrella and
forbids an aggregate that imports every leaf directly, so this root must not
grow into an import list. The library is built by the `Grass.+` glob in
`lakefile.toml`, which reaches every submodule without an umbrella import.

Consumers import the narrowest module that owns the fact they need. The module
tree and its normative dependency direction are in `docs/MODULES.md`.
-/
