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
named and neither is described as landed or unlanded: a ruling reaches its bus
event and `DECISIONS.md` at different times, so a sentence about which one a
reader can currently follow goes stale by itself. This comment has said each of
those three things in turn.

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
`Vec`. `Vec` has landed and `ByteArray` above is the name §1 asks for, so what
still holds is only that the flip is not free at the use sites — and those are
mostly not the memory layer's, which is the part `c-stdlib` got wrong.

`c-stdlib` measured this and published the measurement as a verified recipe, and
it was wrong in a way worth stating in the module rather than only on the bus. It
said the flip costs six substitutions inside `Grass/Memory/**` and `Grass/Op/**`
and is then green. Re-measured against whole `main`, the flip leaves 41 errors in
`Grass/ISA/X86/Bytes.lean` after every one of those six, and
`Grass/ISA/X86/Decode.lean` pattern-matches a `ByteSeq` as a list, which no
substitution can port. Of the 48 lines mentioning `ByteSeq` outside this module,
**44 are in `c-x86`'s files** and 4 are in `Grass/Memory/Event.lean`.

The cause was not that `main` moved: this module's own merge-base already carried
every one of those `Grass/ISA` and `Grass/ABI` files. The search was scoped to the
consumer `c-stdlib` expected and never asked the repository-wide question.

So the flip is not scheduled, and `docs/STDLIB_IMPLEMENTATION_PLAN.md` §3.13 carries
the re-measured cost. The recipe is retracted at `c-stdlib:34`.
-/
abbrev ByteSeq := List Byte

end Grass.Std.Logical
