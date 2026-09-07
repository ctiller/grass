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

## Where the rule comes from

`docs/MODULES.md` calls this "the lower machine-authority facade over the x86
encoding, decoding, instruction semantics, and validation-metadata shards",
consumed directly by machine-model authors and by `Grass.Assembly.X86`, so that
"ordinary assembly authors should not have to assemble its shards one by one".

Two corrections have been made to this paragraph and the second is worth keeping
written down. The first draft quoted `docs/MODULES.md` normally. A reviewer
reported that no such text existed in the tree, so I rewrote it to say the rule
lived on an unmerged commit and was not checkable here. That was false when I
wrote it: `fff7344` had already merged, and the only true statement was that
this branch was behind `main` by twenty-seven commits. I asserted a fact about
git ancestry without running `git merge-base`, on a reviewer's word, which is
the same mistake in the same session as taking a fixture's output for a fixture's
intent.

## What ratifies it, which is not decision 134

`docs/MODULES.md` is explicit that decision 134 ratifies `Grass.Assembly.*`,
`Grass.Platform.*` and `Grass.Emit`, and that "`Grass.ISA.X86` is deliberately
outside that list: it is the narrower machine-authority integration surface
consumed by machine-model authors and `Grass.Assembly.X86`, and uses
`docs/OLEAN_SHARDING.md`'s reviewed deliberate-public-re-export exception on
that basis."

That is the authority for the eleven-shard import list below, and it answers a
question a reviewer raised and left open -- whether this module is an
`import all` wearing a facade's name. It is the named exception, granted on the
stated basis. The same passage adds that neither case is permission to use
`import all`.

This module declares nothing. It is the import list and this note, which is what
makes it a facade rather than a second implementation hierarchy: there is no
name here that could drift from the shard that owns it.

## Scope

`Grass.Assembly.X86` is a different surface and is not owned here. The ruling
assigns it to the construction/lowering workstream and has it consume this
facade as a dependency; the construction vocabulary a spike author writes --
`asm_source`, `withStack`, block annotations, calls -- is
architecture-independent and lives in `Construct` and `CFG`. Naming the x86
table owner as the owner of that surface was the confusion `c-x86:7` raised and
`g-design:71` settled.

## The cone

Fourteen `Grass` modules: the eleven shards, this facade, and outside
`Grass.ISA.X86` exactly two leaves, `Grass.Core.Name` and
`Grass.Std.Logical.Byte`.

`Tests/Facade/ISAX86.lean` lists all fourteen and compares them against the
environment of a module importing only this one, so a widening fails the build
whether or not anyone anticipated the module that caused it. An earlier version
of that fixture sampled four declarations that had to be *absent* instead, and
two reviewers defeated it independently -- once by renaming the sampled names,
once by adding memory, obligation and semantics edges the sample did not
mention, which took the cone to twenty-seven modules with the fixture still
green.

Honest about what "narrow" currently buys: the import list is extensionally the
same as the eleven files in `Grass/ISA/X86/`, so today this facade excludes no
shard. What it does is fix the cone at a reviewed set and make any addition to
it a failing build rather than an unnoticed edge.

## What a reader should not conclude

Membership in this cone is not a statement that a shard is validated. The
citation, dual-citation, ledger and source shards are *validation metadata*:
they record which external authority is claimed for which encoding rule and
which of those claims is still unconfirmed. `Grass.ISA.X86.openReleaseBlockers`
is not empty, and `Tests/ISA/X86/LedgerAudit.lean` names the blocking
documents on every build.
-/
