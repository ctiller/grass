import Grass.Std.Logical.Vec

/-!
# Bytes

`docs/STDLIB.md` §1 fixes the canonical eight-bit value type and the byte
container built from it:

```lean
abbrev Byte := BitVec 8
abbrev ByteArray := Vec Byte
```

Both are declared here. `ByteArray` was sited in `Grass/Std/Logical/Vec.lean`
while this module was under `c-mem`'s temporary custody (`c-mem:1`), because the
owner of `Vec` does not edit another agent's module; that custody transferred to
`c-stdlib` at `c-mem:47`/`c-stdlib:19`, and merging the two declarations is the
step that handoff was blocking. The import now runs `Byte -> Vec` rather than
`Vec -> Byte`: `Vec` is a general container that has no business knowing what a
byte is, and the byte-specific names belong beside `Byte`.

**`ByteArray` collides with Lean's `_root_.ByteArray`,** and that is deliberate.
`g-design:49` settled the naming question `c-stdlib:7` raised: the Grass type
keeps the name, modules that also see the host type qualify it, and the crossing
between them is by named adapters carrying connection theorems
(`Grass/Std/Logical/HostBytes.lean`) rather than by a `Coe`. The ambiguity error
is the representation-boundary guard doing its job, not a defect to route around.

That ruling is also recorded as `docs/DECISIONS.md` decision 133. Both sources are
named, and neither is described as landed or unlanded: a ruling reaches its bus
event and `DECISIONS.md` at different times, so any sentence about which of the
two a reader can currently follow goes stale on its own.

`Tests/Std/VecVocabulary.lean` pins both halves: a `List Byte` is rejected where a
Grass `ByteArray` is required, and so is a host `_root_.ByteArray`.
-/
namespace Grass.Std.Logical

/-- The canonical eight-bit value type. -/
abbrev Byte := BitVec 8

/-- The canonical byte container of `docs/STDLIB.md` §1. -/
abbrev ByteArray := Vec Byte

/--
The memory layer's name for a byte sequence. Still `List Byte`.

Its own docstring promised this would become `Vec Byte` once `Std.Logical` landed
`Vec`. `Vec` has landed and `ByteArray` above is the name §1 asks for, so the only
thing still holding is that the flip is not free at the use sites, which are
`c-mem`'s.

`c-stdlib` measured it rather than assuming: flipping this one `abbrev` retypes
every field without an edit, exactly as `c-mem` designed it to, but six *sites*
then fail because they apply `List` operations to what is now a `Vec` --
`List.length` in the bodies of `Committed.readCount` and `writeCount`,
`List.length_take` twice in `Committed.truncate`, and `List.replicate` twice in
the field values of `Oracle.zeroed`. Only two of the six are proof steps. Every one has an exact `Vec` counterpart already in
`Grass/Std/Logical/Vec.lean`, and with those six substitutions the whole build is
green. The verified recipe is offered to `c-mem` in `c-stdlib:20`; this module
does not flip the alias before those six lines land, because doing so would break
`main` for the interval in between.
-/
abbrev ByteSeq := List Byte

end Grass.Std.Logical
