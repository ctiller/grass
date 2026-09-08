/-!
# Bytes

`docs/STDLIB.md` §1 fixes the canonical eight-bit value type and forbids a second
unrelated byte container:

```lean
abbrev Byte := BitVec 8
abbrev ByteArray := Vec Byte
```

`Byte` is defined here exactly as specified. `ByteArray` is not: it is declared
in `Grass/Std/Logical/Vec.lean` beside the `Vec` it abbreviates, because `Vec`
imports this module and the reverse import would be a cycle. That siting splits
a pair §1 writes together, and the "## Bytes" section of `Vec.lean` records what
it would take to unsplit them and why nothing has.

`ByteSeq` is the placeholder the memory layer uses meanwhile. It is a single
`abbrev` so that the migration to `Vec Byte` is one edit in one place rather than
a change to every field that holds bytes. It is listed as **provisional** in the
M1 freeze note; consumers should write `ByteSeq` and never `List Byte`, so that
the migration does not become a rewrite.

**Custody, settled.** This module was written under `c-mem`'s temporary custody
per `docs/MEMORY_IMPLEMENTATION_PLAN.md` §2. That custody ended on 2026-09-07:
offered as `c-mem:47`, accepted as `c-stdlib:19`, and `Grass/Std/Logical/**` is
the `Std.Logical` owner's exclusive claim from `c-stdlib:21`. `coord1:32` asked
that the marker be replaced on acceptance rather than stripped before the offer,
and this is that replacement, late. Until it was written this docstring said the
module was *not* owned by its owner, which is the kind of claim a reader has no
way to doubt.
-/

namespace Grass.Std.Logical

/-- The canonical eight-bit value type. -/
abbrev Byte := BitVec 8

/--
A finite ordered sequence of bytes.

Provisional, and the event it was waiting on has happened. `Vec` landed and
`ByteArray := Vec Byte` is declared in `Grass/Std/Logical/Vec.lean`, so this is
no longer a placeholder for a name that does not exist: it is a name whose
consumers have not been migrated.

Those consumers are not one agent's. `ByteSeq` is written under `Grass/Memory`,
`Grass/ISA`, `Grass/ABI` and `Grass/Op`, and in fixtures for each; the memory
layer holds most of the uses, but the x86 encoders and decoders hold enough that
migrating is not a change `c-mem` can make alone. `git grep ByteSeq` is the
current answer and no count is given here, because a count of a set that moves
goes stale without looking stale. So the two names coexist until the migration
is arranged across those owners, rather than either being deleted from under its
consumers.

Write `ByteSeq`, not `List Byte`.
-/
abbrev ByteSeq := List Byte

end Grass.Std.Logical
