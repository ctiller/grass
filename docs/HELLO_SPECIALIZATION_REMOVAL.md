# Hello specialization census and removal plan

Status: census and approved removal work, 2026-09-09. The user approved this
direction: "ruthlessly delete any cheats and rework without bullshit".
Program-specific expansion remains stopped; deletion and general rework are
authorized. No completed removal is claimed by this census. The original
five-spike goal remains open.

The rule now applies to every spike: no spike-specific code is permitted in
`Grass/` or `Tests/`. Remove a discovered recipe, then report the removal and
missing general capability to its owner. Ordinary small test inputs for general
contracts remain useful; a renamed program schedule does not qualify.

## Removal checkpoint

On main through `9c7d1ca9`, the program-name source parser, authored assembly
fixtures, dedicated addressing fixture, production ABI frame/unwind fixtures,
and structural Hello exporter/runner have been removed. General source capture
and its assembly consumers passed 176 focused build jobs. The remaining unwind
corpus contains 51 generic cases, all byte-identical to `ml64`; its row count and
digest were updated after regenerating and reviewing the actual corpus.

Certificate integration through `48a101bc` additionally removes the fixed
loop/guard recognizers and dependent lowering recipes, the aggregate source
witness, and the scripted partial-source execution gate. Its general frontend
and source checks passed 190 jobs, followed by 63 jobs for remaining assembly
fixture changes. The legacy public certificate interface is still incomplete;
these checks are not a full certificate build or a verified spike.

Further confirmed removals are in progress: the seven-file Hello memory schedule
and dependent API test fixtures, the two-symbol instruction-specific Win32
constant lowerer, and the stand-in spike API surface test. These findings extend
the frozen census below. No completed cleanup or completed spike is claimed.

The implementation has accumulated a second, hand-maintained description of
Hello beneath its authored source. This includes source recognizers, fixed
register/guard proofs, a scripted execution harness, and fixture-based emission.
Calling these pieces test glue or parameterizing their payload does not make
them acceptable compiler infrastructure. The earlier assertion that the
unchanged authored files demonstrated acceptable proof burden was inadequate.

## Boundary and scope

The precious input is `Spikes/1_Hello_World/Spec.lean` and `Program.lean`, including
the existing `@invariant write_all_loop(payload)` annotation. Their text is not
to gain companion proofs, an execution script, environment recipes, or a larger
list of author obligations. Moving the code below into a spike certificate
directory would preserve the problem and is not the removal plan.

A compiler necessarily produces program-specific instructions and proof terms.
Those may be disposable outputs derived from the authored input. They must not
be hand-maintained library recipes selected by recognizing this program. Work
requiring intelligence, such as discovering a lowering invariant or proving a
generated verification condition, belongs behind the general verification
interface and must produce kernel-checked evidence against that condition.

This census covers main, certificate integration, and the active frontend,
lowering, Windows, and process supplier trees, including Windows' uncommitted
source. Exact heads, working status, and paths are in
[snapshots.json](audits/hello-specialization/snapshots.json). Historical dormant
branches and the old gasm/wsc repositories are spare parts, not live suppliers;
they are not certified clean by this census. Any later import needs the same
review. Ignored generated frontend experiments are listed separately below.

The accompanying [file inventory](audits/hello-specialization/files.tsv),
[declaration index](audits/hello-specialization/declarations.tsv), and
[text matches](audits/hello-specialization/text-matches.tsv) make the inspected
surface navigable. They distinguish identical files from branch variants using
normalized-text SHA-256. This is a lexical index, not a Lean elaborator census
or a claim that every indexed declaration is defective. The semantic findings
below include files with **zero** Hello-name matches.

## Confirmed program knowledge to remove

Paths below are repository-relative; branch presence and declaration lines are
in the accompanying indexes. `certificate` means it also exists in one or more
active supplier trees, not necessarily main.

| ID | Files and declarations | Duplicated program knowledge | Required disposition |
|---|---|---|---|
| H01 | `Grass/Assembly/SourceInput.lean`: `findAssembly`, `helloSourceCount`, `extractHelloSourceChars`, `extractHelloSource` | Literal `def helloSource` selects the accepted declaration. | Remove special-name extraction. Normal syntax elaboration must pass the actual declaration/body and bindings to a general checked source constructor. |
| H02 | `Grass/Frontend/Source.lean`: `SourceIngress.hello`, `MachineSource.ofHello?`, `ofHello?_inputs`; `Grass/Frontend/AssemblySyntax.lean`: `assemblyBody`, `helloAssemblyDefinition`, `elabHelloAssemblyDefinition`, capture expansion | Mandatory Hello ingress; command grammar fixes one UInt32 local and wrapper shape; body ends at the first closing brace. | Replace with compositional assembly/wrapper syntax, exact source binding, and a name-independent constructor. Delete the special constructor and parser, not merely their names. Preserve `Frontend.Construction` only where it is general structural evidence. |
| H03 | `Grass/ABI/Win64/Convention.lean`: `spike1SavedRegisters`, `spike1FrameLayout`, `spike1CallAllocationBytes`, all `spike1_*` laws | Hand-supplied r12/r13/r14, arity/local geometry, 40/48/72-byte facts and saved offsets. | Delete the production fixture declarations. Derive frame inputs from typed locals, actual saved registers and called signatures using the existing general layout calculation. |
| H04 | `Grass/ABI/Win64/Unwind.lean`: `spike1Prologue*`; `UnwindBytes.lean`: `spike1Layout*`, `spike1UnwindInfo*` | Repeated specific prologue, instruction end offsets 2/4/6/10, exact unwind bytes. | Delete production fixture definitions and dependent numeric proofs. Derive unwind data from actual encoded prologue and retain general encoding/round-trip laws. |
| H05 | `Grass/Platform/Win32/Console.lean`: `successStatus`, `failureStatus`, `statuses_distinct` | Hello's 0/1 outcome policy represented as Win32 semantics. | Delete these unused policy definitions and audit enrollments. Use the outcome projection already supplied in Program.lean. |
| H06 | `Grass/Assembly/WriteAllLoopSource.lean`: instruction constants, `headAnnotations`, `Candidate.Valid`, `Selection`, `select?` | `write_head`, `payload`, r12/r13/r14/rax, exact add/sub/jump adjacency and annotation tokens. | Delete the recognizer. Resolve the actual CFG, operands and annotation terms without knowing this loop's labels, allocation or instruction recipe. |
| H07 | `Grass/Assembly/WriteAllGuardSource.lean`: instruction constants, `Candidate.Valid`, `PrefixCandidate.Valid`, `select?`, `selectAll?` | `transferred`, EAX/R14d, exact exit labels, five-step guard recipe and relative instruction indices. | Delete the recognizer. Branch semantics and generated verification conditions must determine the effect of the actual instructions. |
| H08 | `Grass/Assembly/SourceWitness.lean`: `Result.loop`, `loopExact`, `guards`, `guardsExact`, `produce?` | A supposedly general source witness requires both special recognizers to succeed. | Remove mandatory loop/guard recipe fields and their producer calls. Structural source evidence must not require that a program be Hello-shaped. |
| H09 | `Grass/Refinement/Console/WriteAllX86.lean`: `CursorRegisters`, `UpdateRun`, `SourceUpdate`, update/retry and fixed guard laws | One fixed physical placement and ADD/SUB/JMP implementation of the loop. | Delete sequence/placement schemas; use general ISA register and frame laws to discharge source-derived conditions. |
| H10 | `Grass/Refinement/Console/WriteAllFactory.lean`: `update*`; `WriteAllHead.lean`: `AuthoredUpdate*`; `WriteAllBody.lean`: `load_operand`, `load_destination`, `FactoryLoad`, `Run`, `cursor_after_load_checks`, reentry/return composition | Manually composes the fixed load/guards/update suffix into a proof of this loop. | Delete bespoke compositions and their consumers. Salvage independently general load/frame facts only where a general consumer uses them. |
| H11 | `Grass/Refinement/Console/WriteAllGuards.lean`: `SourceChecks`, `SourceGuard`, `SourceGuards`, target laws; `WriteFileLoad.lean`: `CountChecks` and fixed test/cmp composition | Repeats the exact EAX/R14d test/compare/branch schedule. | Delete sequence carriers; retain general initialized DWORD read and ISA branch laws. |
| H12 | `Grass/Refinement/Console/WriteFileCountEntry.lean`: `prepareCountCall?`, `_slot`, `returned_body`; `WriteFileCountAddress.lean`: `SourceLea.authored_operand`; `WriteFileResume.lean`: cursor/guard/body composition | Refuses every local except `transferred`; prescribes `lea r9, transferred`; binds r12/r13/r14 and the fixed post-return body. | Remove name and instruction-shape requirements. Check the actual incoming call state, count-pointer binding, width and authority. A valid incoming pointer must not require a LEA. |
| H13 | `Grass/Refinement/Console/WriteFileStaticEntry.lean`: `prepare?`, `returned_body`; related count/static adapters | Static preparation is generic in isolation but transitively requires the bad count gate and fixed body. | Remove those dependencies and the body alias. Preserve only ordinary static-memory/ABI checks with actual source bindings. |
| H14 | `Tests/Frontend/WriteFilePrefix.lean.in`: `system`, `advanceTo`, `completeExit`, `finishExit`, `Result`, `inspected`, `run` | A second Hello executor: GetStdHandle then WriteFile or ExitProcess, exact import/name searches, first-load heuristic, `payload`, status 1, fixed empty graphs, noEffects/noReturnInterpretation, representative flags and finite fuel. | Delete this execution template and its obligatory proof path. A general executor/VC generator follows reached instructions and dispatched contracts; it does not know the expected next API. |
| H15 | `Tests/Frontend/check.sh` | Cuts at `def helloVerified`, strips `Grass.Emit`, injects exact namespace/source assertions into the execution template, mutates one literal `mov transferred, 0`. | Replace with full-source compilation and verified emission through the public interface. Delete partial-source construction as the completion gate. |
| H16 | `Tests/Platform/Win32HelloCall.lean`: `ActualSetup`, `ActualPreCall`, `ActualHandoff`, `ActualResult`, `actualSetup?`, `handoffFrom?`, `actualHandoffFor?`, `actualPrefix?` | Rebuilds source/image, manually runs prologue and initializers to presumed first GetStdHandle, uses dedicated carriers. | Delete the Hello setup/carrier chain. General checked instruction and API-entry producers must operate on actual source-linked loaded states. |
| H17 | `Tests/Platform/Win32LoaderEntry.lean`: `helloPlanFrom?`, `helloPlan?`, and `inputsFor` as infrastructure | Fixed test payload/section construction, three import addresses, stack offset 168/frame 80/RSP 0x1000a8 and selected registers enter the program proof. | Delete Hello image factories and test-input dependence. Loader verification quantifies over admitted environments; ordinary unit-test sample inputs cannot supply that universal evidence. |
| H18 | `Tests/Platform/Win32GetStdHandleReturn.lean`: `environmentFor`, `evaluatedFor`, `regressionFor`; `Win32GetStdHandleRawReturn.lean`: regression producers | Selected stdout values and fabricated return observations coupled to Hello carriers are reused by the frontend. | Remove those infrastructure imports. Keep API rejection/acceptance tests only as data to general API checks, independently of Hello execution. |
| H19 | `Tests/Console/WriteFileCountEntry.lean`: `sourceFor`, `selectLoad?`, `withoutLea`, `incoming`, `other_local_refuses`; count-address/static-entry tests | First load stands for the count binding; fixture endorses rejection of a renamed local; copied source/symbol/register setup. | Delete the selection heuristic and name-refusal expectation. Resolve actual operands/dataflow; generic regression inputs must accept equivalent renamed locals. |
| H20 | `Tests/Platform/Win32WriteFileProviderModel.lean`: `selectedAction`, `realization`, `result`, `interpretation`; `Win32WriteFileProviderOperation.lean`: count/read/write/operation/policy/action | A hand-chosen one-full-write model with raw BOOL 2 and count equal to requested bytes, proposed as Hello's positive continuation. | Do not integrate as a program supplier. Use general provider semantics covering permitted outcomes; derive/check actual operation and return evidence without selecting a favorable model to match the desired execution. |
| H21 | `Tests/Platform/Win32WriteFileCausalSchedule.lean`: rank/order/activeGraph/model/realization functions; unpublished `Win32WriteFileCallSchedule`, `Win32WriteFileFullReceipt`, `Win32WriteFileProviderCompletion` | Hand-assembled finite event schedule, exact endpoint tuple and two-access/full-count recipe. Parameterization does not establish same-run provenance or native applicability. | Remove hand-authored program schedule packaging. Compute structural event membership/order from actual operations and call cuts; prove general preservation once. Keep any useful graph lemma only independently of this recipe. |
| H22 | `Grass/Platform/Win32/RawAgencyProfile.lean`: `helloExternalChoice`, `RawStep.pending_external`, `cpu_not_external` (process supplier) | Agency classification explicitly installed for a Hello-selected profile. | Do not integrate this profile. Derive agency from general process/provider ownership contracts and actual transitions; a profile rename is insufficient. Reuse valid inversion lemmas at that boundary. |
| H23 | `Tools/EmitGrassHello.lean`; `Tools/DisasmHello.lean`; associated lake target | Reads source and reconstructs a structural image through fixtures or an explicitly supplied replacement payload instead of consuming `helloVerified` bytes. | Delete special exporters. The generic artifact command consumes verified emission; disassembly accepts those bytes. A structural test image is not the program's verified output. |
| H24 | `probes/windows/run-grass-hello.sh`, `capture-grass-hello.ps1`; `Tools/disasm/check.py`; Hello rows in `Tools/x86-native/run.py` and corpus producers | Program-specific emit/run pipeline and repeated payload/source/operand expectations. | Replace executable logic with general artifact runners and generated/ordinary test data. Preserve useful native ISA/disassembly tests without maintaining another Hello implementation. |

The existing annotation already names the standard write-all invariant. That
permits a reusable semantic theorem about partial writes; it does not permit a
library recognizer to prescribe r13/r14 or five adjacent instructions. The
general verifier must bind the annotation to its actual lexical operands and
check the actual CFG against it.

## Additional fixture and dependency census

These are included, not exempted because they live in Tests. Remove duplicate
program definitions/recipes and keep only ordinary data-driven assertions
against general APIs or the fully authored spike.

| Family | Files / declarations | Disposition |
|---|---|---|
| Frame/unwind/ISA fixtures | `Tests/ABI/Win64/FrameLayout.lean`, `UnwindCorpus.lean`; `Tests/ISA/X86/Spike1Addressing.lean`; `Tests/Memory/Spike1Reference.lean`, `Spike1Policy.lean`, `Spike1Block.lean` | Delete parallel Hello frame/program models and production `spike1*` dependencies; retain independent ABI/ISA/memory examples as ordinary test data. |
| Assembly ingress/layout fixtures | All indexed `Tests/Assembly/*` users of `extractHelloSource*`, `SourceResolve.authored`, `SourceLinkedImage.payload/staticTable`, and literal `def helloSource` wrappers | Migrate to the general grammar and checked constructor. One integration input may reference the precious program; dozens of partial source rewrites and copied image recipes must not be infrastructure. |
| Loop proof fixtures | `Tests/Console/WriteAll{X86,Factory,Head,Guards,Body}.lean`, `WriteFile{Load,Resume,CountAddress,CountEntry,StaticEntry}.lean` | Delete assertions over retired program-shaped carriers; test general instruction/CFG/invariant binding and the complete public endpoint. |
| API service fixtures | `Tests/Platform/Win32WriteFile.lean`, `Win32WriteFileService.lean`, `Win32RawStep.lean`, `Win32RawServicePrefix.lean`, `Win32RawServiceContinuation.lean` and provider tests above | The 3-byte sample, quiet receipts, noEffects and two-step histories can exercise general contracts but cannot be imported to define an authored program's semantics or execution. Remove pipeline dependencies and bespoke scenario producers. |
| Frontend fixtures | `Tests/Frontend/Source.lean`, `Target.lean`, template and shell gate | Retain general syntax/target tests; replace Hello-specific setup and partial compilation with the actual public interface. |
| Ignored experiments | Frontend `.lake/FrontendHello.lean`, `FrontendWriteFilePrefix.lean`, `FrontendWriteFileEntry.lean`, `FrontendPrefixTypeCheck.lean`, `FrontendPrefixDefinitionCheck.lean`, `FrontendExitHelperCheck.lean`, `FrontendCompleteExitCheck.lean`, `FrontendAudit.lean`, `FrontendTrust.lean` | Disposable local experiments, not checked-in authority. Delete obsolete generated copies during cleanup; never promote them as implementations. |
| Generic semantics counterexamples | `Tests/Semantics/{ServiceWaiting,Environment,BoundaryTiming,BehaviorUniverses,History,ExecutionSteps,OutputCut}.lean`; `Tests/Refinement/{ExternalNonresponse,ImplementationConformance,UnclassifiedDeadlock,FiniteHistoryRelation,FinitePathMap,ForwardInclusion,Coverage,Realization}.lean` | Toy states/streams are independent contract tests, not Hello execution. Retain them. The WriteWaiting-dependent part of `Tests/Semantics/Waiting.lean` follows review of its library model. |
| Console denotation fixtures | `Tests/Console/{Behavior,Accounting,Timing,LineBehavior,ObservedBehavior,ObservedFrontier,ObservedEmbedding,ObservedEmbeddingSteps,Contract,Captured,CapturedDemands,TargetProjection,Resources}.lean` | Review alongside explicitly selected library semantics, not as source-to-machine verification. Reporting stages must model the selected general contract, never substitute for executed caller behavior. |
| Enrollments and prose | `Tools/AxiomAudit.lean`, `Tools/check-source-input.sh`, ledger entries, `lakefile.toml`, endpoint/proof-burden docs and native validation reports | Update mechanically with deletions; remove completion claims based on partial gates. Do not preserve a retired declaration to satisfy an audit count. |

## Bounded capabilities and domain laws: explicit adjudication

The census also found boundaries that need a generalization/remit check, rather
than indiscriminate deletion of every Win32 or console theorem.

| Surface | Finding and required treatment |
|---|---|
| `Signatures.Api`, `ApiRequest`, `CallRuntime`, `ApiDispatch`, `RawStepSignature`, `RawState`, `RawStep` | Closed three-API vocabulary, WriteFile-specific causal nodes and service representation. It does not require Hello's API order. Retain the current bounded capability union during this cleanup; extensibility is architectural work, not grounds to call these semantics a duplicate program. When expansion requires composition, use general contract instances rather than a handwritten sum/dispatcher/proof stack for each new program. |
| `ConsoleEnvironment`, `WriteFileConsolePublication` | One static process/caller/provider/stdout route with explicit exclusions. Those restrictions must come from the selected platform/resource contract, not be silently assumed for all programs. Route and ownership evidence must be consumed explicitly. Do not replace native applicability obligations with a favorable fixture. |
| `Frontend.Target`, `PlatformPlan.layout`, `Frontend.win10Layout` | Current supported surface is one Win10/UTF8/CRLF/synchronous-stdout target. Program.lean explicitly selects those facilities, so the constructors themselves are not duplicate Hello policy. Backend layout and API populations must be selected through plan data rather than an unconditional one-target implementation masquerading as a general compiler. |
| `Console.Behavior`, `LineBehavior`, `Captured*`, `Resources`, `Timing`, `TargetProjection`; `Std.Console.WriteAll`, `Std.Console.Process` | Payload/policy-parametric line and partial-write semantics can be legitimate reusable library behavior explicitly selected by the authored spec/annotation. Retain those meanings; delete any mandatory physical Hello recipe or staging duplicate. Do not label UTF8/CRLF or `successOrFailure` a leak merely because Hello explicitly selects them. They must not be the universal `VerifiedProgram` contract. |
| `Console.ObservedBehavior`, `ObservedEmbedding`, `ObservedEmbeddingSteps`, `ObservedFrontier`, `ContractCorrect`, `Contract` | Reporting/observation stages and no-infinite proofs are hand-built library semantics. The authored spec selects `writeLineContract`; preserving that denotation matters. Audit any implementation-side reliance on these stages against actual source execution. Do not silently add caller actions, erase nonresponse, or mistake a proof about the model for a lowering proof. `Resources`' empty selected axes must likewise remain a justified library-resource interpretation, not a universal resource restriction. |
| `Refinement.Console.WriteFile{History,Projection,Policy,ConsoleHistory,Nonresponse,EventualNonresponse,Observed,Finalize}` and `WriteWaiting*` | Some laws quantify over arbitrary payloads, cuts, histories and actual returns. Retain genuine semantic laws as reusable lemmas; remove any dependency on fixed register/label/body selectors. A conditional logical continuation is not an executed caller continuation. |
| General API/ABI leaves, `CheckedCallEntry.prepare?`, actual service-history folds, matched-return transport, synchronization and finite/infinite path laws | These can remain when their statements concern arbitrary actual input states/calls/operations and preserve their provenance. API register locations and DWORD width are contract facts, unlike Hello's r13/r14 placement and `transferred` spelling. Their consumers must be general, not the deleted execution template. |
| ISA/memory/text modules mentioning Hello only in comments | No semantic deletion on a keyword match. Rewrite comments that imply a program-specific remit; preserve correct general definitions. Limited instruction support must be explicit and reject unsupported instructions, not recognize a particular program. |

## Removal sequence

1. **Freeze and establish the deletion list.** Keep supplier branches as spare
   parts. Do not cherry-pick their Hello fixtures, recognizers or profiles.
   Retire the earlier plan that considered fewer lines in the scripted CALL
   blocks sufficient. This document and its inventories are the starting list.

2. **Remove independent leaks.** Delete H03-H05
   production fixtures/status policy and migrate their ordinary unit tests off
   library-owned program data. Remove fixture-based exporters from the claimed
   completion path. This is deletion work, not creation of a new facade.

3. **Make source construction genuinely general.** Frontend/lowering replace
   H01-H02 and H06-H08 with normal syntax capture, typed local/annotation
   bindings, CFG construction and source-derived layout. Structural producers
   return existing evidence about the actual input. No loop recipe is a
   precondition of constructing a MachineSource. The precious source remains
   unchanged; variations are separate test inputs.

4. **Compose execution from contracts.** Architecture defines the smallest
   shared operation boundary with process/Windows/lowering; implementers
   reuse the bounded platform population until an actual extension requires
   changing it. Generic traversal derives the
   reached instruction, import dispatch, arguments and actual event suffix.
   Structural receipts and graphs are computed from actual steps; each API
   instance supplies its semantics. External outcomes are universally covered
   in the proof, rather than chosen by a fixture to reach a desired endpoint.
   Delete H14/H16-H21 as infrastructure when those consumers migrate.

5. **Generate conditions, synthesize proofs, check them.** Lowering/frontend
   delete H09-H13. Generic instruction/CFG and contract rules generate the
   conditions for safety, spec conformance and internal deadlock freedom.
   Source annotation binding and semantic library lemmas support proof
   synthesis. Intelligence may propose proofs; Lean checks the exact generated
   obligations. Neither a hand-maintained Hello proof companion nor a renamed
   parameterized copy of its instruction schedule is an acceptable replacement.
   Author liveness/fairness theorem suites remain outside VerifiedProgram.

6. **Close the real endpoint and delete temporary gates.** Rewrite the stale
   public certificate integration against the general suppliers; compile the
   entire original Spec.lean and Program.lean, including `helloVerified` and
   `bytes`. Emit those verified bytes and run/disassemble that artifact. Delete
   H15/H23-H24 and obsolete template experiments, rather than retaining a
   parallel structural export path to make tests green.

7. **Re-census and publish the actual deletion evidence.** Regenerate import,
   declaration and trust coverage after removals. Report deleted recipes,
   surviving general laws and generated proof artifacts separately. Update
   GitHub in coherent reviewed slices. Spike 1 is complete only at the full
   endpoint; this cleanup does not count as completing any of spikes 1-5.

## Tests that distinguish removal from concealment

- Compile the original source in full without editing or stripping it, and
  without importing Tests as a construction/semantic dependency.
- Rename declaration, labels, locals and static symbols consistently; vary
  payload, register allocation and branch layout through the same interface.
  Supporting library code must not change. Layout/offset proofs remain derived.
- Supply a valid incoming count pointer without LEA and accept it; reject an
  invalid pointer regardless of a familiar instruction pattern or local name.
- Cover every admitted Hello path, including partial writes, failure after
  publication, zero progress, unavailable stdout, environmental nonresponse,
  and exact terminal status/audit observations. Selected 24/14/16-edge paths
  are regressions, not universal verification.
- Preserve safety, actual source-to-byte correspondence, actual event history
  and mandatory internal deadlock freedom. Retain the ordinary trust audit;
  no sorry/native_decide/unchecked execution result supplies proof authority.
- A semantically equivalent instruction arrangement must be checked through
  the general rules. An invalid arrangement must fail on its actual obligation,
  not merely because it no longer resembles Hello.
- No mandatory file may encode Hello's source spelling, instruction schedule,
  static payload or register allocation outside the authored input. Generated
  proof/code outputs must carry their input/obligation provenance and be
  disposable. Moving or renaming a recipe does not satisfy this criterion.

The remaining risk is substantive: the general execution/verification path is
not finished. We cannot honestly promise that deleting the specializations
alone makes Hello compile. The work must build that path and remove the second
program description, rather than hiding the missing path behind more adapters.
