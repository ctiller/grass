# Spike completion plan

Status: c-spike's working plan for turning the five drafted spikes into
elaborated, verified, emitted programs. It schedules and prices work owned by
other agents; it does not authorize it. Every item here becomes a bus issue or
dependency against the owning agent, and the owning agent's own implementation
plan is authoritative for how the item is done.

The drafts in `Spikes/` are the product of a long design iteration, and this
plan's first question is "what has to exist underneath so that what the author
already types is what the author keeps typing" rather than "what should the
author type".

That is a starting point, not a closure. An earlier revision of this paragraph
said the drafts were fixed and that re-opening them was the failure mode this
plan exists to prevent; `g-design:183` is right that this contradicts the
project rule that specifications and authoring interfaces move when
implementation exposes inadequacy or poor proof economics. What the sentence was
actually defending is worth keeping and is narrower: the author surface must not
be churned to suit whatever the libraries find convenient to supply. So the
gate is a reviewed finding, not a closed door. An adequacy or proof-economy
finding opens the drafts; a library's preference does not.

## 1. The governing constraint

`docs/SPIKE_AUTHORING.md` divides every identifier a spike names into authored
definition, authored proof, library instance, generated structural fact, or
versioned authority model. The authoring surface stays small exactly to the
extent that the last three categories are carried by libraries and elaboration
rather than by files under `Spikes/`.

Two consequences drive the ordering below.

Every name that a library fails to supply does not disappear. It reappears as
authored ceremony in the spike directory, and the proof-economy claim in
`docs/SPIKE_PROOF_BURDEN.md` fails quietly rather than loudly. Work is therefore
ordered by how much authored surface it prevents, not by how close it is to the
metal.

And `Spikes/` is in no `lakefile.toml` target, so no build gate notices when a
library change falsifies a drafted import. That is a gap in the build, not a
missing instrument: the fix is to put the corpus in the build once it can
compile, which is what section 5 argues and P1 schedules.

## 2. What the drafts demand, measured

Method: every capitalized or dotted identifier referenced by the twenty
`.lean` files under `Spikes/`, minus the names the spike defines itself, checked
against every declaration and structure field on `main`,
`agent/g-foundation/execution-dedup`, `agent/c-process/process-layer`,
`agent/c-stdlib/std-logical` and `agent/g-design/normative-design`.

| Spike | Unresolved names | Dominant group |
|---|---|---|
| 1 Hello World | 23 | platform, ABI and projection |
| 2 Sort | 68 | specification front end and assembly DSL |
| 3 Gzip | 54 | platform, ABI and the zlib package |
| 4 Web server | 356 | assembly DSL, HTTP/2 package, block contracts |
| 5 Spinning cube | 331 | Vulkan and SPIR-V authority constants |

| Group | Names | Owner today |
|---|---|---|
| Platform constants and API authority facts | 185 | nobody |
| Assembly and CFG construction vocabulary | 118 | g-construct |
| `Grass.Std` domain packages | 124 | c-stdlib, sequenced |
| Platform, ABI, layout and projection | 46 | nobody |
| Specification front end (`Grass.Spec.*`) | 41 | contested, see section 3 |
| Application obligations and scraper noise | 318 | c-spike, already priced in `SPIKE_PROOF_BURDEN.md` |

The owner column is as of the merge of this revision and moves; the bus
registry is authoritative. Two of the four groups changed owner after the
measurement: `g-construct:1` took construction and lowering and exports
`BlockContract`, which is itself one of the 118 names, and `c-stdlib:26`
sequenced the domain packages in response to `c-spike:6`.

Two limits on these figures, stated so they are not over-read. They are lower
bounds: a dotted name counts as resolvable when its head type exists, so
`SpecProcess.ofRelational` was scored resolvable on the strength of
`SpecProcess` alone, and it does not exist. And the last row mixes genuine
authored obligations, which are supposed to be there, with false positives from
binders and namespace fragments. The first four rows are the ones that matter,
and they are unowned or unaware.

## 3. The divergence, and how it was settled

This was the plan's blocking item: the drafts and the libraries disagreed about
`SpecProcess`, about `MeetsAllSpecificationTheorems`, and about the module names
an author types. It was raised as `c-spike:4` and settled by `g-design:50`,
adopting **decision 134**, and the ruling went to the drafts rather than to the
implementations. Recorded here because the plan's whole ordering rested on it.

**`SpecProcess` keeps the drafted shape.** The public `SpecProcess` is the
resource-indexed captured `SpecificationSuite` root of `docs/SEMANTICS.md`, as
`Spikes/1_Hello_World/Spec.lean` writes it. The unindexed record on the
foundation branch is not an alternate public type. `capture`, `ofRelational`,
`withLiveness` and the other suite modifiers are therefore **library
obligations**, not drafting errors -- they must be built, and the spikes that
name them are correct to.

**`MeetsAllSpecificationTheorems` has an owner.** `Grass.Semantics.SpecProcess`
owns it, as universal satisfaction of the precious independently keyed
`spec.suite.theorems` family.

**The drafted imports are ratified.** The concise spike imports are narrow
signature-only authoring facades, and a facade module must not import `Impl`,
`Cert`, or aggregates. `c-process:64` then delivered the first one:
`Grass.Process` exists as exactly that -- four imports, a closure of 25 modules,
neither the Lake root nor an aggregate of `Grass/Process/**`, with
`Tests/Process/FacadeFixtures.lean` authoring against that single import line
and guarding that seven further modules' vocabulary does *not* resolve through
it. Widening a facade is now a visible change that breaks a guard rather than a
quiet one.

That is the outcome this plan wanted and did not assume: the authoring surface
was held fixed and the libraries took the work. Two consequences for what
follows. The 41 specification-front-end names in section 2 are confirmed library
obligations rather than candidates for renegotiation, which is what P3 now
schedules. And the facade pattern is the mechanism by which section 4's
economy is defended, so "which facade does this name enter through" becomes a
real design question per module rather than a packaging afterthought.

### 3.0 The machine and platform import names, settled

`c-spike:19` asked c-x86 where the drafted machine and platform imports land.
`c-x86:6` answered by splitting the question, escalated the normative half as
`c-x86:7`, and `g-design:71` then ruled on it. All four names now have a settled
spelling and a named owner.

`Grass.Platform.Win10.X64` becomes `Grass.Platform.Win32`, and c-x86 will
deliver `Grass/Platform/Win32.lean` as a signature-only authoring facade on the
`c-process:64` pattern, with a fixture guarding against quiet widening. The
reasoning is one c-spike raised as a secondary point and c-x86 made the deciding
one: `Win10` names an OS version and `X64` an architecture, while the module is
about neither -- it is the Win32 API family, and the architecture is already
named by `ABI/Win64`.

`Grass.Assembly.X86` is *not* that layer. c-x86 read
`Spikes/1_Hello_World/Program.lean` rather than reasoning from the name:
`asm_source`, `static_objects`, `MachineSource`, `withStack`, `withCallFrame`
and the `@placement`/`@invariant`/`@terminal` annotations are construction and
lowering vocabulary, which `docs/MODULES.md` puts in `Construct/` and `CFG/` --
coord1:43's second proposed owner. `Grass.Emit` is likewise `Unsafe/`, which
MODULES.md scopes to raw construction, import, stepping and emission. c-x86 owns
`ISA/X86`, which MODULES.md scopes to encoding, decoding and validation
metadata: the tables underneath that vocabulary, not the vocabulary. A single
`Grass.Assembly.X86` facade over c-x86's leaves would export `InsnEncoding`,
`MemOperand`, `Gpr` and `UnwindOp`, none of which Spike 1 types, so it would
have looked like a fix without being one.

The consequence for this plan is sharper than section 6's P2 first recorded.
Spike 1 needs three of the target-side owners, not one, and all three are
registered: c-x86, whose half is committed and partly built; `g-construct`,
which took construction and lowering at `g-construct:1` and is the recipient
of the `Grass.Assembly.X86` obligation `g-design:71` assigns it. The third, the
artifact owner that `g-design:71` assigns `Grass.Emit`, is g-build, whose latest
published scope `g-build:16` claims `Grass/Emit.lean` exclusively along with
`Grass/Artifact/PE/**`, `Grass/Artifact/COFF/**`, `Grass/Build/Manifest/**` and
`Grass/Grammar/**`.

One risk under this layer is worth recording because it is a release blocker
rather than a scheduling one, and it is not c-spike's to solve. c-x86's ledger
audit reports 158 modelled declarations of which 6 carry a citation and 98 are
owed, and 9 of 18 anchors unconfirmed, with `[amd64-apm-40332-4.09]` named as
the release-blocker set: `docs/VALIDATION.md` section 1 makes a dead location
under a `referenceOnly` policy block release. `c-x86:2` states the cause -- the
AMD half of decision 15's dual-cited Intel/AMD intersection is currently
unobtainable, so every rule in the common profile rests on one vendor. Spike 1
emits x86-64 through this layer, so the spike corpus inherits that blocker
whatever else is ready.

What exists for Spike 1 on c-x86's side today, per `c-x86:6`: the prologue is
modelled and externally verified -- `spike1Prologue`, `spike1Layout`, and
`spike1UnwindInfo_toBytes` proving the exact `.xdata` bytes byte-identical to
Microsoft's assembler for the same prologue; `STD_OUTPUT_HANDLE` and
`INVALID_HANDLE_VALUE` exist as `StdHandleId.value` and
`GetStdHandleResult.invalidHandleValue`; the `GetStdHandle` and `WriteFile`
contracts exist; and the `[rip + symbol]` form Spike 1 needs is
`MemOperand.ripRelative`, checked against `ndisasm`. Named as missing rather
than left to be discovered: no encoder yet for `push`, `sub`, `test`, `cmp`,
`jz`/`je`/`ja`/`jmp`, or call-through-memory-import.

`g-design:71` settled which normative document moves, and it moved MODULES.md
rather than the author surface. The normative module map now declares
`Grass.Assembly.X86` as the first-class assembly-author facade over narrow
`Construct`, `CFG` and `Grass.ISA.X86` signatures, owned by the future
construction and lowering workstream rather than by the x86 table owner.
`Grass.ISA.X86` is the machine-authority facade owned by c-x86.
`Grass.Platform.Win32` replaces the spike spelling `Grass.Platform.Win10.X64`,
with Windows 10 and x64 remaining explicit profile selections rather than being
conflated with the Win32 API family in the path. `Grass.Emit` remains the safe
facade exposing `VerifiedProgram` and a checked `emitProgram`, with raw erasure,
admission, linking and byte writing staying in `Unsafe` and `Artifact`; the
facade may not expose unverified source to executable bytes. Every one of these
is signature-only, and each requires both positive vocabulary and negative
implementation-leakage fixtures.

So three of the four drafted names stand unchanged and only the platform
spelling moved. `g-design:71` directed c-spike to update and resynchronize only
the Platform import, which this branch does: four authored sources and their
four byte-exact `SPIKE_n.md` mirror blocks, in one pass, verified by
`check-spike-sources.ps1` and negative-tested by desynchronizing one side alone.
`Spikes/5_Spinning_Cube/Process.lean` still imports
`Grass.Platform.Win10.Vulkan13`, deliberately: it raises the same shape of
question, `g-design:71` did not rule on it, Vulkan is not the Win32 API family,
and the graphics platform owner is not registered. Renaming it by analogy would
be inventing a ruling.

### 3.0.1 The facade roots, and who names them

`docs/MODULES.md` now declares all four facades in the tree with their owners:
`Assembly/X86.lean` as the first-class x86 assembly authoring facade owned by
the construction and lowering workstream, `ISA/X86.lean` as the lower
machine-authority facade owned by c-x86 and deliberately outside the
author-facing set, `Platform/Win32.lean` as the Win32 API family facade, and
`Emit.lean` as the safe verified-emission facade. All four are signature-only
with measured dependency cones, and each requires fixtures demonstrating both
what resolves and what does not.

`c-spike:36` reported that every one of those roots sat outside the directory
glob of the owner assigned to deliver it, since a glob does not reach a sibling
file. `coord1:78` ruled explicit listing: an assigned facade root is not
implicitly in the assignee's scope, and the owner names the root file in its own
`scope.set` beside the glob. The reasoning is worth keeping because it
generalizes past this case -- an implicit rule creates ownership no tool can
see, and scope-conflict detection and every third-party check operate on the
published globs, so a facade root covered only by convention is a claim
agent-bus cannot verify or report a collision on.

That ruling also corrected c-spike's evidence. It re-derived the four instances
against each owner's latest published scope rather than the ones the report
cited, and found c-x86 had already fixed its half unprompted at `c-x86:12`. The
report named `c-x86:1`, which was accurate when read and stale when acted on.

All four roots are now owned, checked against every agent's latest `scope.set`
rather than against any owner's description of it: `ISA/X86.lean` and
`Platform/Win32.lean` by `c-x86:12`, `Assembly/X86.lean` by `g-construct:49`,
and `Emit.lean` by `g-build:10`, which `g-build:14` records as constrained to
the checked `VerifiedProgram`/`emitProgram` surface `g-design:71` describes.
`Emit.lean` mattered most of the four and came last: it is the only module all
five spikes import, so it is where the corpus terminates, and by the time it was
claimed a second consumer was waiting on the same seam in `g-construct:65`.

The method is the part worth keeping. c-spike found the same defect four times
and filed it once, as a routing question to the coordinator, rather than as
three separate corrections at three owners. One ruling then fixed all four, and
the two owners who had not yet published scope absorbed it without a second
prompt. Filing per-instance would have cost three exchanges and produced three
chances to cite a stale scope, which is exactly the error `coord1:78` had to
correct in the single report that was filed.

### 3.1 Two spike-side import decisions still open

`c-process:64` answered `c-spike:7` and handed back two choices which are
c-spike's, not c-process's. Both are recorded here rather than in a commit
because neither can be finalized yet, and the reason is worth keeping.

`Spikes/5_Spinning_Cube/Process.lean` line 2 imports `Grass.Process.Blend`,
which names nothing and never has; the module is `Grass.Process.Weave.Blend`.
`Spikes/4_Web_Server/Cancellation.lean` line 1 imports
`Grass.Process.Cancellation`, which has no umbrella module either -- the leaves
are `.Identity`, `.Policy` and `.Compose`. For each, the spike may import the
leaf or leaves directly, or c-process may publish a facade.

The governing principle, from section 4: prefer the direct leaf import, and
treat a facade as earned only when one coherent authored concern genuinely needs
several leaves. One extra import line in one spike is cheaper than putting a
whole subsystem's vocabulary into every author's closure, and `Grass.Process`'s
own fixtures show what widening costs.

Neither can be settled by that principle alone yet, because the names the spikes
actually use are not in the modules the repointing would name.
`Spikes/5_Spinning_Cube/Process.lean` uses `BlendedProcessGraph`,
`ClosedBlend` and `ProcessRealization.blend`, and none of the three is in
`Grass/Process/Weave/Blend.lean`, which holds `VocabularyEmbedding`,
`DisjointWeave` and `routing_is_forced`. That module reached main with
`c-process:71` at 28a24f6, and each half of this claim was re-checked against
main rather than carried forward: the three names it holds are there, and the
three the spike wants are in no file under `Grass/` at all.
`Spikes/4_Web_Server/Cancellation.lean` uses `CancellationPolicy`, which is in
`Cancellation/Policy.lean`, but also `CancellationSummary` and
`CancellationPolicyRealizes`, which are in none of the three leaves. Check that
second pair by declaration and not by `grep -l`: `CancellationSummary` does
appear in `Cancellation/Compose.lean`, but only at line 37 inside prose
comparing that module to PROCESS.md §3, and a name found only in a docstring is
not a declaration. `boundaryProjection` sets the same trap in
`Grass/Process/Network/Plan.lean`, where the only match is the module note
quoting the pre-128 shape of a structure that no longer has the field. Repointing
an import at a module that will not contain the name is not a fix; it moves the
error rather than removing it. The open question to c-process is therefore
placement -- where these five names will live -- and the import lines follow
from the answer.

## 4. Surface economy: the ninety-five block contracts

Across the five drafts, 95 referenced names end in `Entry` or `Exit`:
`CompareEntry`, `FlushOutputExit`, `Http2.X86.Contract.dispatchEntry`, and so
on. `docs/SPIKE_PROOF_BURDEN.md` sections 3 and 5 classify them as
generated-structural defaults -- typed operands, derived effects and clobbers,
declared exit meanings -- which the elaborator derives from block annotations
and which an author may strengthen but never has to write.

If the assembly and CFG layer does not derive them, those 95 names become
authored files in `Spikes/4_Web_Server/` and `Spikes/5_Spinning_Cube/`, and the
proof-economy claim those spikes exist to test has already failed before the
first proof is attempted. Derivation of block contracts from annotations is
therefore an acceptance condition on the assembly layer, not a later
optimization, and it belongs in the first ticket that assigns that layer rather
than being discovered during Spike 4.

As of `g-construct:12` this is no longer only c-spike's argument. The owner of
the layer accepted it as a consumer contract: the 95 names remain
generated-structural, `BlockContract` is an internal checked value rather than
an authored spike declaration, and source discovery must derive the exit family
and the effect and clobber facts from annotations and instruction facets. The
same event accepts the facade split -- g-construct owning the signature-only
`Grass.Assembly.X86` facade plus raw `Unsafe` emission, admission and stepping,
with the artifact owner, now g-build, holding the safe `Grass.Emit` facade -- and names
Spike 1 as its first end-to-end acceptance target. The risk in this section is
therefore now a commitment that can be checked against a deliverable rather than
a concern a consumer is carrying alone.

The same reasoning covers the other generated classes
`docs/SPIKE_AUTHORING.md` lists as normally omitted: source closures and import
manifests, label-to-cancellation dictionaries, ABI/frame/relocation records, and
the generated internal network of the standard sequential adapter. Each is a
category of file that appears under `Spikes/` if the library declines it.

## 5. Measuring the surface

Three questions have to be answered mechanically rather than by somebody
reading the corpus, and none of them needs a new tool.

**Does every name resolve?** That is `lake build`, as soon as `Spikes/` is in a
Lake target. An unresolved name is a compile error at the exact line that
referenced it. A separate report which says the same thing afterwards, in JSON,
is worse than the compiler: later, and one more thing to keep true.

**Is the surface still small?** That is the file and line count under
`Spikes/`. The failure mode section 4 describes is a block contract migrating
from generated-structural to authored, and when that happens it appears as a
new declaration in a file under `Spikes/` -- in the diff, in review, in the
count. It does not hide.

**Do the two views still match?** That is `check-spike-sources.ps1`, which
exists and passes. Checked rather than assumed: all 123 fenced blocks across
the five documents carry an immediate classification, block identities are
unique, and all 20 authored blocks match their files byte for byte after
newline normalization.

An earlier revision of this section said the script needs PowerShell 7, that
this machine has only 5.1, and that the result had therefore been established
by reimplementing the three tests rather than by running the script. The first
clause was untested and is wrong; it is retracted at `c-spike:46` and amended
at `c-spike:47`. Windows PowerShell 5.1 Desktop runs `check-spike-sources.ps1`
directly and it exits 0, as do `check-doc-links.ps1` and g-foundation's
`audit-trust.ps1`. c-spike runs its own gates and does not depend on a reviewer
for them.

The reimplementation was still worth having, for the reason that outlives the
error: it was negative-tested, and the script was not. Changing one byte of
`Spikes/1_Hello_World/Spec.lean` reports the mismatch; deleting one
classification comment from `docs/SPIKE_2.md` reports the unclassified block.
A gate that has only ever been seen to pass is not yet known to be able to
fail. So the drift this plan guards against is drift from a known-good state,
measured by an instrument that has been shown to move.

**What can the corpus falsify?** Counted rather than assumed, because a library
owner asking "will the spikes catch it if I get this wrong" deserves a number.
Across the five spikes there are 3 success terminals and 15 non-success ones --
3 in Spike 1, 6 in Spike 2, 6 in Spike 3, and none in Spikes 4 and 5, which are
process-shaped and carry no `@terminal` labels at all. Of the 15, six are the
partial-write case, `writeFailed` and `noProgress`, exactly one of each in all
three assembly spikes; three are `stdoutUnavailable`, where nothing was ever
offered, which is the cheap negative for any rule that demands a destination
for an uncommitted suffix.

The gap is the part worth publishing. **Not one of the 15 is `.cancelled`** --
zero across all five spikes. Any obligation that splits failure from
cancellation is exercised six times on one branch and never on the other, so a
wrong cancellation rule passes the whole corpus. That is filed at `c-spike:50`
against the first library change it actually bears on, c-process's repair of
`closed_streams_committed_everything`, and it will recur for every later one:
by `c-stdlib:29`'s bar a repair has to be shown both satisfiable and still
refusing what it exists to refuse, and today the corpus can only do the first
for cancellation. Closing it means an authored cancellation consumer, which is
c-spike's to write once a library owner names the vocabulary -- not something
to invent ahead of one.

The inventory in section 2 is sizing evidence, not an instrument. It answered
"how much work is there and who owns it" once, well enough to order this plan.
It does not need an owner, a schema version, or a report envelope, and
promoting it to one would be this document inventing work for the same reason
the plan exists to prevent elsewhere.

`docs/IMPLEMENTATION_RATCHET.md` specifies seven `grass spike` subcommands.
Two of them measure something the compiler genuinely cannot: `mutate`, which
checks that weakening a named invariant actually breaks the check it is
supposed to break, and `locality`, which measures the rebuild cone of a change.
Those are the proof-economy claims, they belong at implementation acceptance
per that document's own section 7, and they are not prerequisites for any
library. This plan does not schedule them. The rest of that command surface is
an evidence-projection format for review, and it should be built when somebody
is actually blocked for want of it.

## 6. Ordered plan

P0 was the only sequencing constraint on everything else and it is settled, so
P2, P3 and P4 are now unblocked and independent of one another; they should run
in parallel across their owning agents, and the spike order inside P4 is what
serializes. P1 follows P2 by necessity rather than by choice, since a spike
cannot enter a build target before it can compile. The critical path is
therefore P2 -- not because it lacks owners, since all three of its workstreams
are registered (`c-x86:1`, `g-construct:1`, `g-build:1`), but because every
spike waits on a target-side authoring surface none of them has written yet.
The routing gap that remains is in P3, where the resource and console contract
families still have no owner.

### P0 — Reconcile the surface — DONE

Settled by `g-design:50` as decision 134, section 3 above. The drafts stood and
the libraries took the work. What it produced is not an empty phase but a
transfer: `capture`, `ofRelational`, `withLiveness`, the other suite modifiers,
and `MeetsAllSpecificationTheorems` are now named library obligations against
`Grass.Semantics.SpecProcess`, and they belong to P3 rather than to a
reconciliation nobody owes any more. The two residual import questions in
section 3.1 are c-spike's and are open.

### P1 — Put the corpus in the build

Owner: c-spike.

`Spikes/` is in no `lakefile.toml` target, so nothing notices when a library
change falsifies a drafted import. Add each spike to the default target as soon
as it can compile -- which for every spike means after P0 and P2 -- and keep the
mirror check running in CI until then. That is the whole of this phase.

`check-spike-sources.ps1` is portable as of this branch. It called
`[IO.Path]::GetRelativePath`, which exists only on .NET Core and .NET 5+, so it
ran in CI -- `corpus.yml` invokes it with `shell: pwsh` -- and died on its first
file for anyone without PowerShell 7. A gate whose purpose is to be run before
you push is the wrong thing to have working only after you push. Verified under
Windows PowerShell 5.1 and negative-tested: a changed source byte and a deleted
classification comment each fail it.

Exit: `lake build` fails when a spike references a name the libraries no longer
provide.

### P2 — The target side (blocking every spike)

Owner: routed by `coord1:43` into three workstreams, all of which have
registered. The bus registry is authoritative for who owns what; what follows
records the split and the obligations, not a running census.

`c-x86` took machine and platform authority -- `Grass/ISA/X86`,
`Grass/ABI/Win64`, `Grass/Platform/Win32` -- at `c-x86:1`, and already has an
encoder, a decoder and a byte-level round-trip theorem. `g-construct` took
construction and lowering at `g-construct:1` -- `Grass/CFG/**`,
`Grass/Construct/**`, `Grass/Unsafe/**` -- with the explicit purpose of
implementing the normative authored assembly surface, and is the current
recipient of the `Grass.Assembly.X86` author-surface obligation. The artifact
and build layer is g-build's, and `Grass.Emit` is its obligation rather than
`g-construct`'s: `g-design:71` is explicit that raw erasure, admission, linking
and byte writing stay in `Unsafe` and `Artifact` while the checked `Grass.Emit`
facade belongs to the artifact owner.

An earlier revision of this section said that owner remained unregistered, 224
lines after section 3.0.1 of this same document recorded `Grass/Emit.lean` as
owned by `g-build:10`. Both sentences were c-spike's. The contradiction survived
because the resolution was appended as a new section instead of replacing the
claim it falsified -- twenty lines above the correct statement, this document
records that one of c-spike's own reports "named `c-x86:1`, which was accurate
when read and stale when acted on". `g-design:183` found the stale half. The
method that prevents a repeat is the one that ruling prescribes: delete the
prose a finding falsifies rather than appending a correction beside it, and
re-read the whole document after a ruling lands rather than only the section
being edited.

Assigned delivery and published scope are not the same thing, and one gap
between them is worth recording because it will block a delivery rather than a
plan. `g-design:71` assigns `Grass.ISA.X86` and `Grass.Platform.Win32` to c-x86,
but `c-x86:1`'s globs are `Grass/ISA/X86/**` and `Grass/Platform/Win32/**`,
which match paths *underneath* those directories and not the root facade files
`Grass/ISA/X86.lean` and `Grass/Platform/Win32.lean` themselves. Both facade
roots therefore fall outside c-x86's published exclusive scope. c-x86 needs to
extend that scope, or receive an explicit handoff, before writing either file.
This is scope bookkeeping, not an ownership dispute: the assignment is settled
and only the glob does not reach it. Raised with c-x86 rather than left here.

The split itself, decided by the user and recorded in `coord1:43`, is by layer
rather than one owner: machine and platform authority (`ISA/X86`, `ABI/Win64`,
`Platform/Win32`), the construction and lowering language (`CFG`, `Construct`,
`Unsafe`) consuming the first, and artifact and build (`Grammar`, `Artifact/*`,
`Build/*`). Registration of these workstreams had been held until the agent-bus
contention work landed, since a bus then taking minutes per publish would not
have survived fifteen concurrent pushers. That work has landed and all three
registered on the strength of it, the artifact and build owner at `g-build:1`.
Two things coord1 flagged rather than decided: `Effect` and `Weave` are not
target-side at all and may belong with g-foundation -- `Grass/Weave/**` has
since become g-foundation's under `g-foundation:69` while `Effect` remains
unrouted -- and `Programs/` is unassigned on purpose,
since `HelloWin64` and its siblings are the productionized form of exactly the
end-to-end demonstrations c-spike owns -- whether that makes them c-spike's is a
question for the user.

This remains the single largest block in the plan and the only reason no spike
can emit a file.

`Grass.Assembly.X86` -- `asm_source`, `AsmSource`, `MachineOperand`,
`AddressOperand`, `VerifiedFragment`, `FragmentConstructorClosure`,
`StaticObjectTable` with its `static_objects` macro, `BlockContract`,
`MacroTable`, and the `@placement`, `@invariant`, `@terminal`, `@audit`,
`@violation_edge`, `@containment_tail` annotations.
`Grass.Platform.Win32` -- `PlatformPlan`, the Win64 ABI, `FrameLayout.derive`,
`StructLayout.derive`, `withStack`, `withCallFrame`, the import table.
`Grass.Emit` -- the PE writer, and the checked `emitProgram` over
`VerifiedProgram`.
Plus `TargetProjection` / `TargetOutcomeProjection` and the
`verify_assembly … deriving_standard_process_from … with …` tactic.

`StaticObjectTable` and the `static_objects` macro were listed under
`Grass.Emit` here and that was wrong. `c-x86:6` grouped `static_objects` with
the construction and lowering vocabulary when it read
`Spikes/1_Hello_World/Program.lean`, and `docs/ASSEMBLY_CONSTRUCTION.md` settles
it: `StaticObjectTable` is a field of `AuthoredSourceInputs`, the dependent
inputs to `asm_source`, beside `FragmentConstructorClosure` and
`LayoutSelection`. They are construction vocabulary and belong with
`Grass.Assembly.X86`. c-spike raised this to g-build in `c-spike:35` as a
boundary it could not resolve; the evidence was in a normative document it had
not read, and the answer did not need g-build at all.

Acceptance conditions, not optional extras: block contracts are derived from
annotations, not authored (section 4); and source closure, cancellation maps and
relocation manifests are derived and inspectable, not authored.

Exit: `Spikes/1_Hello_World/Program.lean` elaborates and emits a PE.

### P3 — The specification front end

Owner: `Grass.Semantics.SpecProcess` and the facade modules are g-foundation's
by its existing `Grass/Semantics/**` claim; the resource and console contract
families have no owner yet and are the part of this phase still to route.

Decision 134 converted these from contested to owed. Its `DECISIONS.md` text
reached main with `g-design:77`; before that it existed only as the bus ruling
`g-design:50`, so looking it up by number on main failed -- which is what
`c-x86:10` hit and `c-spike:24` corrected. `capture`, `ofRelational`,
`withLiveness` and the other suite modifiers, plus
`MeetsAllSpecificationTheorems`, are library obligations against
`Grass.Semantics.SpecProcess` with the drafted signatures fixed, which is the
cheapest possible starting position: the interface is already written down and
already reviewed.

The 41 names behind `Grass.Spec.Resource`, `Grass.Spec.Console`,
`Grass.Spec.Grammar` and `Grass.Spec.Graphics`: the resource models
(`ConsoleResourceModel.singleLine`, `ConsoleBufferResourceModel.untilMemoryExhaustion`,
`StreamingResourceModel`), the console contract family
(`Console.writeLineContract` and its correctness, `ConsoleWriteOutcomePolicy`,
`TextLine`, `Console.byteLineStreamFormat`, the suite constructors), and
`Format` with `Format.parserRequirement`.

No dependency on P2. Shared by all five spikes, so it is the cheapest work per
spike unblocked.

### P4 — The domain packages

Owner: c-stdlib.

In spike order, because each is a prerequisite for exactly one spike:
`Grass.Std.Sort.Stable` (spike 2), `Grass.Std.Zlib.Fixed32K` (spike 3),
`Grass.Std.Process.Network` and `Grass.Std.Process.Supervision` with
`Grass.Std.Protocol.Http2` and its `.X86` realization (spike 4), and
`Grass.Std.Process.Graphics` with `Grass.Std.Graphics.Cube` (spike 5).

These are the `authority-model` and banked-theorem entries in
`docs/SPIKE_PROOF_BURDEN.md`. They are where the smarts belong: every theorem
that lands here is a theorem the spike author does not write, and the burden
ledger already names the exact ones each spike expects.

`c-stdlib:26` acted on the advance notice in `c-spike:6` and sequenced all five
as section 5.1 of `docs/STDLIB_IMPLEMENTATION_PLAN.md`: all five are band 3,
none is scheduled, and the burden ledger's cost-escalation rule is adopted as
binding. That last part matters more than the scheduling. Section 7 of the
burden ledger says that if these obligations expand by orders of magnitude,
Grass records the cost and changes the reusable interface rather than hiding the
work in `Grass.Std`; an owner adopting that as binding before starting is the
difference between a proof-economy claim that can fail loudly and one that
quietly absorbs whatever it costs.

### P5 — The spikes, in their drafted order

1 Hello World, then 2 Sort, then 3 Gzip, then 4 Web server, then 5 Spinning
cube. The order is the drafts' own and is preserved: each spike is the smallest
program that adds one new class of obligation.

Spikes 4 and 5 additionally carry a named blocking dependency as of
`g-design:67`, which is worth recording because it is not visible from the spike
sources. Ruling (3) preserves the facet-carrying `ProcessTopology` of decision
122 as normative but defers implementing it out of c-process's M4 candidate into
a later milestone, and states that until it lands the current
`ProcessPlan`/topology implementation is provisional: it cannot claim to
discharge cancellation or supervision requirements, and cannot be consumed as a
complete `ProcessPlan` by `VerifiedProgram`. Both spikes instantiate
`ProcessPlan` -- `Spikes/4_Web_Server/Process.lean:229` and
`Spikes/5_Spinning_Cube/Process.lean:200` -- and both close through it, via
`ProcessPlanRealizes` and, in Spike 4, `using explicit_process`. So neither can
reach a verified program until that deferred milestone lands, whatever else is
ready. Nothing in the authored sources changes: the drafted names and shapes
stand, and this is a scheduling fact rather than a resynchronization.

Two scheduled decision points rather than smooth progress. Spike 2 is the first
program whose portable model cannot plausibly carry one step per machine
instruction, so it is where the refinement granularity of
`Grass/Certificate.lean` is decided in practice. Spike 4 is where the
generated-structural boundary of section 4 is tested at scale; if block
contracts are authored by then, the plan has already failed and the interface
must be revised rather than the spike padded.

## 7. What c-spike does and does not do

c-spike owns `Spikes/`, `docs/SPIKE_1..5.md` and this plan, keeps the drafts
coherent, and files and tracks the tickets this plan generates. The annotated
documents are settled as c-spike's under user authority, and the paired sources
come with them: `docs/SPIKE_AUTHORING.md` binds each `authored file=` block to
its file in `Spikes/N_Name/` byte for byte, so the document and its source are
one artifact with one owner and cannot be split between two. That includes the
author-surface resynchronization duty -- keeping the drafts in step with
rulings such as `coord1:4` -- which g-design has been discharging in c-spike's
absence and which now returns here. One sequencing consequence rather than an
ownership one: `agent/g-design/normative-design` carries unmerged edits to
`Spikes/4_Web_Server/Process.lean`, `Spikes/5_Spinning_Cube/Process.lean`,
`docs/SPIKE_4.md` and `docs/SPIKE_5.md` -- at c09c82a as this is written, having
moved from 136b20a, and still changing all four against its merge-base with
main. So c-spike takes custody of those four after that branch lands rather than
racing it. That sequencing now binds a second obligation: `g-design:96`'s
resynchronization of Spikes 4 and 5, which `c-process:71` triggered by landing
the author-facing shape, targets exactly these four files. It waits on this
branch as well as on the two placement answers `c-spike:41` asks c-process for,
and this is the constraint that decides which, not a preference.

Both of those answers arrived. `c-process:86` settles the first two: a product
plan writes `NoObligations`, which c-process is exporting from `Grass.Process`
as a reducible definitional `Unit` rather than leaving authors to reach into
`Tests` for the fixture-local copy; and `cancellation` and `supervision` have no
attachment point at all, so Spike 4 keeps `ServerCancellationLaw` and
`ServerSupervisionLaw` as free-standing propositions *about* `serverProcessPlan`
rather than fields *of* it. That preserves both claims exactly and migrates into
a facet unchanged when the deferred facet-carrying topology lands. It is the
answer c-spike could not have guessed: no field exists to move them to, and
inventing one, or dropping them, would have been the weakening `c-stdlib:29`
warns about.

A third input has since joined them, and it is the reason this paragraph is not
simply a list of two. `g-design:138` rules that `ProcessSpec.Step` is indexed by
the fixed request of the process instance, which makes `terminalNoStep`
request-local: `Terminal request state result -> not Step request state event
after issued emitted`. The live field on main still carries the universal
`(forall request, p.Terminal request state result)` that ruling removes. Both
spikes assign the field by name -- `terminalNoStep := MemoryServerState.terminalNoStep`
at `Spikes/4_Web_Server/Process.lean:263` and `:= cube_terminal_has_no_step` at
`Spikes/5_Spinning_Cube/Process.lean:156` -- so the assignment lines do not
change, but the proposition those two proofs must discharge does. `ProcessCorrect`
still has ten fields and the corpus still names exactly those ten; what is no
longer safe to say is that the tenth needs no work. c-process owns the
Process-side migration and the ruling directs it to coordinate the spike source
update with c-spike, so this is tracked here rather than acted on.

Worth recording about the ruling itself, because it is the constraint this plan
exists to defend: it says combinators and standard constructors should thread
the request implicitly, and that ordinary authors must not duplicate it in
`State` or pay new proof fields. The defect was fixed without charging the
authoring surface for it.

c-spike files and tracks the tickets this plan generates; it does not implement
the libraries. Where a phase above is unowned, the deliverable is a routing
decision from the coordinator, not c-spike quietly taking the work: an agent
that both authored the demonstration and the thing being demonstrated cannot
report that the demonstration failed. That sentence had lost its subject and its
paragraph break somewhere in an earlier merge, leaving an `It` attached to the
preceding ruling; restored here because a document that cannot be read
accurately cannot be checked accurately.

How this document's own changes reach main is now ruled rather than
conventional, and both halves are recorded because c-spike got the second one
wrong. `g-design:144` makes cross-model reviewer independence the default
eligibility rule, with the `c-`/`g-`/`e-` prefixes as the explicit fleet
convention until the registry carries `model_family`. That ratifies the
e-reviewer/g-reviewer rotation this plan has used, and it means `c-reviewer` is
not eligible for c-spike's work at all. Queue depth is advisory rather than an
algorithm, and reviewer unavailability is handled by decline, reassignment or
succession.

The half c-spike had wrong: when a nomination sat unacknowledged, c-spike told
g-design that every remedy was the reviewer's to exercise and that its own only
lever was withdrawal. `g-design:154` corrected that. `docs/AGENT_BUS_SCHEMA.md`
authorizes any author named in the original request to emit `review.reassigned`
directly, so no decline and no coordinator action are required. Withdrawal is
the wrong instrument for a different reason than availability: findings die with
a withdrawn nomination, while a reassignment inherits them.

The mechanical part is worth stating because it is where this goes wrong
quietly. The reassigned request must equal the replaced one except for
`reviewer`, and `inherited_findings` must carry every still-open finding exactly
once. An empty list is correct only when it has been checked to be empty --
`g-construct:114` wedged the bus reducer with an empty one that should not have
been -- so c-spike scans every agent stream for references to the replaced
nomination before claiming there is nothing to inherit.

The one exception this plan admits is refactoring inside `Spikes/` when a phase
is agreed to be unworkable as drafted. That is a change to a reviewed design
surface, so it requires the ruling first and the edit second.
