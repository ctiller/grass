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

And a surface nothing measures is a surface that drifts. `Spikes/` is in no
`lakefile.toml` target, so today no build gate notices when a library change
falsifies a drafted import. That is why the measuring instrument is scheduled
before most of the libraries rather than after them.

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

## 5. The measuring instrument

`docs/IMPLEMENTATION_RATCHET.md` specifies `grass spike mirror` and
`grass spike authority-report`. The second resolves every identifier a spike
references, classifies it into the six categories, and fails on `unresolved`.

That command is the quantitative form of this entire document. Until it exists,
progress against this plan is prose, and section 2's table has to be
regenerated by a scraper with known false positives. After it exists, every
phase below reports as a falling `unresolved` count per spike, and a library
change that breaks the drafted surface fails a build instead of surviving until
somebody reads the corpus.

It is scheduled early for that reason, and because it is small next to the
target-side work it measures. `check-spike-sources.ps1` is the existing partial
form; the ratchet requires the eventual command to emit a classified manifest
rather than print a pass line.

## 6. Ordered plan

Phases P0 and P1 are sequencing constraints on everything else. P2, P3 and P4
have no dependencies on each other and should run in parallel across their
owning agents; the spike order inside P4 is what serializes.

### P0 — Reconcile the surface (blocking)

Owner: g-design ruling, implemented by g-foundation and c-process.

Resolve section 3: the `SpecProcess` shape, the owner and statement of
`MeetsAllSpecificationTheorems`, and the public module names the author types.

Exit: every `import` line in `Spikes/*/*.lean` names a module `docs/MODULES.md`
says will exist, and every specification-side type in Spikes 1 and 2 resolves to
a decided owner.

### P1 — Make the surface measurable

Owner: needs a `Tools/` owner beyond agent-bus; c-spike consumes it.

`grass spike mirror` and `grass spike authority-report` per
`docs/IMPLEMENTATION_RATCHET.md` section 1. Add `Spikes/` to a Lake target, or
have the mirror command stand in for one, so drift is a build failure.

Exit: `grass spike authority-report --spike 1` classifies every identifier and
publishes an `unresolved` count that is thereafter a ratchet.

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
coherent, and files and tracks the tickets this plan generates. It does not
implement the libraries. Where a phase above is unowned, the deliverable is a
routing decision from the coordinator, not c-spike quietly taking the work: an
agent that both authored the demonstration and the thing being demonstrated
cannot report that the demonstration failed.

The one exception this plan admits is refactoring inside `Spikes/` when a phase
is agreed to be unworkable as drafted. That is a change to a reviewed design
surface, so it requires the ruling first and the edit second.
