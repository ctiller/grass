import Grass.ISA.X86.Addressing
import Grass.ISA.X86.Bytes
import Grass.ISA.X86.Citation
import Grass.ISA.X86.Decode
import Grass.ISA.X86.DualCitation
import Grass.ISA.X86.Encoding
import Grass.ISA.X86.Ledger
import Grass.ISA.X86.Performance
import Grass.ISA.X86.Profile
import Grass.ISA.X86.Register
import Grass.ISA.X86.Sources

/-!
# The x86 machine-authority facade

`docs/MODULES.md` defines this as "the lower machine-authority facade over the
x86 encoding, decoding, instruction semantics, and validation-metadata shards",
consumed directly by machine-model authors and by `Grass.Assembly.X86`, so that
"ordinary assembly authors should not have to assemble its shards one by one".

This module declares nothing. It is the import list and this note, which is what
makes it a facade rather than a second implementation hierarchy: there is no
name here that could drift from the shard that owns it.

## Scope

`Grass.Assembly.X86` is a different surface and is not owned here.
`docs/MODULES.md` assigns it to the construction/lowering workstream and has it
consume this facade as a dependency; the construction vocabulary a spike author
writes -- `asm_source`, `withStack`, block annotations, calls -- is
architecture-independent and lives in `Construct` and `CFG`. Naming the x86
table owner as the owner of that surface was the confusion `c-x86:7` raised and
`g-design:71` settled.

## The cone

Eleven shards, and outside `Grass.ISA.X86` exactly two leaves: `Grass.Core.Name`
and `Grass.Std.Logical.Byte`. Nothing else enters, and `docs/MODULES.md` forbids
`Impl`, `Cert`, a whole-program aggregate, and a concrete program from entering
for convenience.

That is a claim about a dependency cone rather than about a proof, so it is
checked the way a cone can be: `Tests/Facade/ISAX86.lean` reads the environment
of a module importing only this one, requires the authoring vocabulary to be
present, and requires representative declarations from the certificate, memory
and Win64 unwind layers to be absent. Both halves are the fixture
`docs/MODULES.md` asks facades to carry.

## What a reader should not conclude

Membership in this cone is not a statement that a shard is validated. The
citation, dual-citation, ledger and source shards are *validation metadata*:
they record which external authority is claimed for which encoding rule and
which of those claims is still unconfirmed. `Grass.ISA.X86.openReleaseBlockers`
is not empty, and `Tests/ISA/X86/LedgerAudit.lean` reports the count on every
build.
-/
