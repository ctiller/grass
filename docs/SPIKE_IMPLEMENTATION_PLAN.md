# Spike completion plan

Status: c-spike's working plan for turning the five drafted spikes into
elaborated, verified, emitted programs. It schedules and prices work owned by
other agents; it does not authorize it. Every item here becomes a bus issue or
dependency against the owning agent, and the owning agent's own implementation
plan is authoritative for how the item is done.

The drafts in `Spikes/` are the product of a long design iteration and are
treated here as fixed. The question this document answers is not "what should
the author type" -- that is settled, and re-opening it is the failure mode this
plan exists to prevent. It is "what has to exist underneath so that what the
author already types is what the author keeps typing".

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
| Assembly and CFG construction vocabulary | 118 | nobody |
| `Grass.Std` domain packages | 124 | c-stdlib (unaware of the demand) |
| Platform, ABI, layout and projection | 46 | nobody |
| Specification front end (`Grass.Spec.*`) | 41 | contested, see section 3 |
| Application obligations and scraper noise | 318 | c-spike, already priced in `SPIKE_PROOF_BURDEN.md` |

Two limits on these figures, stated so they are not over-read. They are lower
bounds: a dotted name counts as resolvable when its head type exists, so
`SpecProcess.ofRelational` was scored resolvable on the strength of
`SpecProcess` alone, and it does not exist. And the last row mixes genuine
authored obligations, which are supposed to be there, with false positives from
binders and namespace fragments. The first four rows are the ones that matter,
and they are unowned or unaware.

## 3. The blocking divergence: the drafts and the libraries disagree

This is the highest-leverage item in the plan and it is nearly free to fix
relative to everything else. Library work started before it is resolved is
built against a surface that will not typecheck.

**`SpecProcess` has two incompatible shapes.** `Spikes/1_Hello_World/Spec.lean`
writes `SpecProcess resources`, indexed by the selected resource model, and
builds it with `SpecProcess.ofRelational` and
`.withLiveness (.terminatesUnder [.environmentResponsive])`.
`Spikes/2_Sort/Spec.lean` additionally uses `SpecProcess.capture`.
`Grass/Semantics/SpecProcess.lean` on `agent/g-foundation/execution-dedup`
declares an unindexed structure with fields `Input`, `AuditEvent`,
`Observation`, `admits`, `observationProjection`, `accepts` and `requirements`,
and none of `ofRelational`, `withLiveness` or `capture` exists anywhere. Either
the resource-indexed constructor layer is built on top of the foundation
structure, or the drafts change. This is one decision and it should be made
once, before three agents build against two readings of it.

**`MeetsAllSpecificationTheorems` exists nowhere.** All five drafts state their
correctness theorem in terms of it. It is the acceptance predicate for a
specification suite and it has no owner.

**The drafted module names are not the built module paths.** The drafts import
`Grass.Spec.Console`, `Grass.Spec.Resource`, `Grass.Spec.Grammar`,
`Grass.Spec.Graphics`, `Grass.Process`, `Grass.Process.Cancellation`,
`Grass.Process.Blend` and `Grass.Emit`. `docs/MODULES.md` names
`Specification/`, `Process/…` and no `Emit`; `agent/c-process/process-layer`
builds `Grass/Process/Spec.lean`, `Grass/Process/Cancellation/Identity.lean` and
`Grass/Specification/Boundary.lean`, and has no `Grass/Process.lean`, no
`Blend`, and nothing under `Grass/Spec/`. An import line is authoring surface --
it is literally what the author types -- so this is a surface decision, not a
packaging detail, and `docs/OLEAN_SHARDING.md`'s prohibition on a leaf importing
a whole-program umbrella constrains the answer.

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
newline normalization. The script needs PowerShell 7 and this machine has only
5.1, so that was established by reimplementing its three tests and
negative-testing the reimplementation -- changing one byte of
`Spikes/1_Hello_World/Spec.lean` reports the mismatch, deleting one
classification comment from `docs/SPIKE_2.md` reports the unclassified block.
So the drift this plan guards against is drift from a known-good state.

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

P0 is the only sequencing constraint on everything else. P2, P3 and P4 have no
dependencies on each other and should run in parallel across their owning
agents; the spike order inside P4 is what serializes. P1 follows P2 by
necessity rather than by choice, since a spike cannot enter a build target
before it can compile.

### P0 — Reconcile the surface (blocking)

Owner: g-design ruling, implemented by g-foundation and c-process.

Resolve section 3: the `SpecProcess` shape, the owner and statement of
`MeetsAllSpecificationTheorems`, and the public module names the author types.

Exit: every `import` line in `Spikes/*/*.lean` names a module `docs/MODULES.md`
says will exist, and every specification-side type in Spikes 1 and 2 resolves to
a decided owner.

### P1 — Put the corpus in the build

Owner: c-spike.

`Spikes/` is in no `lakefile.toml` target, so nothing notices when a library
change falsifies a drafted import. Add each spike to the default target as soon
as it can compile -- which for every spike means after P0 and P2 -- and keep the
mirror check running in CI until then. That is the whole of this phase.

`check-spike-sources.ps1` needs PowerShell 7 for `GetRelativePath`, which not
every machine has; making it portable is worth more than any new command.

Exit: `lake build` fails when a spike references a name the libraries no longer
provide.

### P2 — The target side (blocking every spike)

Owner: unassigned. This is the single largest block in the plan and the only
reason no spike can emit a file.

`Grass.Assembly.X86` -- `asm_source`, `AsmSource`, `MachineOperand`,
`AddressOperand`, `VerifiedFragment`, `FragmentConstructorClosure`, `BlockContract`,
`MacroTable`, and the `@placement`, `@invariant`, `@terminal`, `@audit`,
`@violation_edge`, `@containment_tail` annotations.
`Grass.Platform.Win10.X64` -- `PlatformPlan`, the Win64 ABI, `FrameLayout.derive`,
`StructLayout.derive`, `withStack`, `withCallFrame`, the import table.
`Grass.Emit` -- `StaticObjectTable`, the `static_objects` macro, the PE writer.
Plus `TargetProjection` / `TargetOutcomeProjection` and the
`verify_assembly … deriving_standard_process_from … with …` tactic.

Acceptance conditions, not optional extras: block contracts are derived from
annotations, not authored (section 4); and source closure, cancellation maps and
relocation manifests are derived and inspectable, not authored.

Exit: `Spikes/1_Hello_World/Program.lean` elaborates and emits a PE.

### P3 — The specification front end

Owner: follows from the P0 ruling.

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

### P5 — The spikes, in their drafted order

1 Hello World, then 2 Sort, then 3 Gzip, then 4 Web server, then 5 Spinning
cube. The order is the drafts' own and is preserved: each spike is the smallest
program that adds one new class of obligation.

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
`docs/SPIKE_4.md` and `docs/SPIKE_5.md` at 136b20a, so c-spike takes custody of
those four after that branch lands rather than racing it. It does not
implement the libraries. Where a phase above is unowned, the deliverable is a
routing decision from the coordinator, not c-spike quietly taking the work: an
agent that both authored the demonstration and the thing being demonstrated
cannot report that the demonstration failed.

The one exception this plan admits is refactoring inside `Spikes/` when a phase
is agreed to be unworkable as drafted. That is a change to a reviewed design
surface, so it requires the ruling first and the edit second.
