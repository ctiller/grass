/-!
# Bytes

`docs/STDLIB.md` §1 fixes the canonical eight-bit value type and forbids a second
unrelated byte container:

```lean
abbrev Byte := BitVec 8
abbrev ByteArray := Vec Byte
```

`Byte` is defined here exactly as specified. `Vec` is not: it is the flagship
`Std.Logical` type, its design is the `Std.Logical` owner's, and inventing one
under custody would be the over-reach `docs/MEMORY_IMPLEMENTATION_PLAN.md` §2
warns against.

`ByteSeq` is the placeholder the memory layer uses meanwhile. It is a single
`abbrev` so that the migration to `Vec Byte` is one edit in one place rather than
a change to every field that holds bytes. It is listed as **provisional** in the
M1 freeze note; consumers should write `ByteSeq` and never `List Byte`, so that
the migration does not become a rewrite.

**Custody note.** `Grass.Std.Logical` is not owned by the memory agent. This
module is temporary custody under `docs/MEMORY_IMPLEMENTATION_PLAN.md` §2.
-/

namespace Grass.Std.Logical

/-- The canonical eight-bit value type. -/
abbrev Byte := BitVec 8

/--
A finite ordered sequence of bytes.

Provisional. This becomes `ByteArray := Vec Byte` when `Std.Logical` lands `Vec`,
per `docs/STDLIB.md` §1. Write `ByteSeq`, not `List Byte`.
-/
abbrev ByteSeq := List Byte

end Grass.Std.Logical
