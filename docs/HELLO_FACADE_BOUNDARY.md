# Unchanged Hello facade and sole-root boundary

Status: reviewed architecture direction, 2026-09-09. Signatures below are
required author-facing shapes or proposed internal boundaries, not declarations
claimed to exist. Process reviewed the signature snapshot; architecture and
spikes accepted the terminal direction below. Process owns the semantic
implementation; source/artifact integration remains with spikes.
This document applies decisions 134, 136 and 137 under the
authority of [SEMANTICS.md](SEMANTICS.md),
[VERIFIED_PROGRAM.md](VERIFIED_PROGRAM.md) and [MODULES.md](MODULES.md).

## Maintained inputs

Keep the authored [Hello specification](../Spikes/1_Hello_World/Spec.lean) and
[program](../Spikes/1_Hello_World/Program.lean) unchanged. Facades must expose
their vocabulary through the already ratified narrow imports. They must not
make a different specification or assembly listing elaborate under the same
surface names.

| Surface | Owner and required identity |
|---|---|
| `Grass.Spec.Resource` | Process supplies the existing resource model vocabulary and console capability; one resource dictionary and value, no duplicate resource type |
| `Grass.Spec.Console` | Process supplies actual resource-indexed contract/root constructors and independent author theorem semantics |
| Root-level `TargetProjection spec target` | Lowering coordinates with process/Windows: exact selected root, target and lawful rendering/outcome projection |
| `PlatformPlan spec.driverBoundary.requirements` | Windows owns provider dictionaries; plan retains exact root/target/projection selection despite the narrower requirement-set index |
| `Grass.Assembly.X86`, `MachineSource plan`, source wrappers | Spikes owns source-bearing frontend and exact frame/splice/resolve identity; lowering owns adjacent execution correspondence |
| `Grass.Emit`, `VerifiedProgram spec` | Spikes integrates the sole certificate/emission path with process's migrated root and lowering's connected witnesses |
| Unqualified authored `ByteArray` | A narrow facade may expose `Grass.ByteArray` as the existing logical byte vector, not another representation; packed host conversion stays explicit |

Facades remain bounded public signature surfaces. Do not solve missing names by
importing all implementation/certificate bodies or shadowing incompatible types
inside the spike namespace.

## Spec and author theorem signatures

The unchanged source requires these shapes, with the selected resource model
instance retained in dependent indices:

* `Console.writeLineContract resources line policy : BehaviorContract resources`;
* `SpecProcess.ofRelational contract : SpecProcess resources`;
* `spec.withLiveness (.terminatesUnder [.environmentResponsive])`;
* `MeetsAllSpecificationTheorems spec : Prop`; and
* `Console.writeLineContractCorrect resources line policy` proving the authored
  specification theorem package for that exact captured specification.

The last theorem is an actual proof obligation. Existing isolated boundary
timing results do not discharge it by a change of name. No axiom, hidden extra
premise or implementation-only replacement for the authored theorem is allowed.
Constructors can be developed first, but that does not make the unchanged
specification compile while its proof remains missing.

`BehaviorContract resources` must package its outcome type because the authored
return type supplies no separate `Outcome` parameter. Process proposes a small
selected language/syntax/snapshot package with computed interpretation and
denotation; the concrete type declaration still needs review. The requirements
are exact captured syntax/resource semantics and a derived complete behavior
carrier, not independently replaceable `system` or `accepts` fields. Do not
expand this into a separate specification framework project.

The sole `SpecProcess resources` captures that contract and ordered authored
demand fragments. Demand keys, statements and dependency facets are derived
from the captured suite. Adding a theorem fragment preserves unrestricted
behavior and prior fragment identities. Author proofs remain separate from
lowering certificates; author liveness does not become a compiler checklist.

## Target and plan signatures

The authored `TargetOutcomeProjection.successOrFailure` must be constructible
without `[DecidableEq Outcome]`: `HelloOutcome` has no such derived instance.
Store declarative success and status-code data. Its semantic interpretation may
use equality relations or noncomputable specification functions; executable
emission consumes the explicit selected codes and proved branch equations.
Do not change the authored enum merely to reuse the current helper.

Root-level `TargetProjection spec .win10X64` consumes the console projection
through an exact spec/target-indexed wrapper. It is not an alias for the existing
`Console.TargetProjection request Status`, whose indices have a different job.
The Win10 constructor selects the same contract's outcome/policy and lawful
UTF-8/CRLF rendering. Generic `projection.encodeLine` does not alone prove that
the emitted payload is the authored `message`; retain the payload/static/source
equality through composition.

The nominal plan's requirement-set index cannot recover specification identity:
two different specifications can require the same platform operations. Store
the actual root, target and projection with the exact boundary equation, and
make `MachineSource plan`, verification and emission consume that selection.
Keep platform requirements distinct from independently keyed author demands.
Do not select another root or provider dictionary through ambient search.

## Terminal frontier decision

The owned Hello requirement includes terminal status, and the standard
`environmentResponsive` meaning includes eventual terminal observation. A raw
`WriteFile` return or `Returned.logicalComplete` classifies a possible logical
outcome; neither proves actual caller execution or process exit.

For the status-bearing console contract, authoritative complete behavior
distinguishes three phases: component
writing, reporting its selected result, and committed observation. Only the
observed phase is whole-program terminal. Reporting is part of the unconditional
base denotation, never a phase inserted by `withLiveness`.

The reporting selection retains the exact reached history, published cut and
diagnostic cause with its allowed-result proof. Its public outcome is computed
from the same captured policy, not stored as an independently replaceable value.
Even if two causes select the same public outcome, their prior choices remain.
Reporting permits permanent nonresponse at that fixed selection; an allowed
committed-observation reply advances to observed and exposes that outcome.
Its occurrence denotes this selection, not the earlier `WriteFile` call.

Do not map reporting back to a pending write cut: that would reopen output
after failure/no-progress and merge selected success/failure at full output.
Do not publish bytes again. No Windows `ExitProcess` operation or numeric target
status belongs in the precious observation request. A unit observation reply
is sufficient abstractly because the selected outcome is already fixed; the
concrete provider must still prove it represents committed observation.

The bounded reusable implementation may wrap an `OutcomeComponent` with total
terminal-result extraction and terminal-no-step laws. Component terminal
histories embed as reporting prefixes; existing component waits and infinite
histories retain their kind. New reporting waits and observed completions extend
that carrier. Do not claim old component `Complete` is definitionally unchanged
as whole-program `Complete`. Preserve resources and obligations at reporting
until their actual terminal-disposition law applies.

This is not a new mandatory external-status protocol for every Grass contract.
The selected domain meaning determines whether terminal observation is promised;
Hello already promises it. The reusable wrapper must not add an unrequested
observable event or universal progress prerequisite to unrelated specifications.

During migration, `Console.TargetProjection.system/Complete`,
`CapturedProjection.project_system/project_complete` and
`WriteFileHistory.Aligned.upper` must be updated together or expose an explicitly
named component view indexed by the same root. Their current component equality
laws cannot silently become whole-program equality laws. `Returned.logicalFinish`
preserves its exact selection event/history and embeds into reporting; existing
write nonresponse evidence remains writing-phase evidence. Reporting gets its
own occurrence and coverage, never custody of the already returned write call.

Windows supplies the concrete terminal-protocol laws and explicit profile
assumptions. Lowering connects actual caller/terminal execution to the selected
logical outcome without publishing bytes twice. Process supplies the coherent
standard responsive-strategy meaning and author theorem. Permanent waiting,
all allowed results and relevant divergence remain represented in unrestricted
semantics; a favorable return or selected predicate does not prove adequacy.

Windows reports that current implementation contains only `ExitRequest`, the
0/1 status constants and their numerical inequality, plus the call signature.
There is no implemented law-bearing terminal provider. The required
`TerminalProtocolLaws` in `PLATFORM_ABI.md` remain obligations: actual terminal
observation of the exact program/occurrence, preservation/reflection,
demanded-outcome distinguishability, exhaustive conforming/violation/fault
classification and outcome-indexed disposition. Reflection cannot prefilter
reachable events using their normalized status or declared-path conclusion.
Numerical status inequality, a physical handle-closure fact or ordinary
`CallProtocol.return?` cannot substitute for those laws.

This settles the semantic direction. Actual wrapper declarations, component
correspondence, reporting wait/reply coverage, coherent adequate standard
strategies and the universal author theorem remain proof gates. Responsiveness
settles both write and reporting frontiers without pruning allowed results;
console termination additionally uses its finite rank and observation phase.
It is not defined by assuming the desired termination conclusion.

## Migration and proof gates

Replace the old unindexed `SpecProcess` and migrate console capture consumers
to the actual root. `CapturedSpecification` may not remain an independent
stored authoritative root. Transitional views must be derived from the sole
root and confer no alternate certificate/emission path.

Process owns root/contract/suite/liveness modules and the capture reindexing.
Lowering migrates exact history/projection/provider consumers. Spikes integrates
`Certificate`, `Coverage`, `VerifiedProgram` and their audit/test dependencies
in the same accepted boundary, or makes the obsolete public gate unavailable.
Do not adapt the new root back through finite `accepts` and a freely selected
`ProgramBehavior` merely to preserve old code.

The completed certificate needs choice-bearing histories, terminal/infinite/
permanent-wait coverage and justified internal stuttering. The existing
one-concrete-step/one-upper-step refinement cannot stand in for zero-publication
folding or divergence-sensitive correspondence. Actual source identity,
applicable safety, provider/loader adequacy and terminal observation remain
connected obligations; data constructors and successful parsing do not close
them. No x86, PE or grammar redesign follows from this signature coordination.
