# Spike 1 console boundary review

Status: architecture review proposal, 2026-09-09. This records the current
interfaces and integration obligations; it does not ratify a new verification
contract or certify completion of Hello World. Decisions 134, 136 and 137 and
the narrowly owning documents retain authority.

## Responsibility

The `spikes` task owns sequence, priorities, dispatch, integration and acceptance.
Architecture resolves cross-stack contracts and semantic ownership in support
of that sequence and coordinates bounded migrations. Specialists own their
domain implementations and models; variant spike authors tail validated
baselines. Architecture's primary outputs are documents and coordination
messages. No separate roadmap or coordination framework is introduced.

Cross-specialist design discussion, ownership questions, repeated intermediate
coordination and unresolved interface debates route through architecture.
Spikes receives consolidated actionable conclusions, review-ready commits with
evidence, concrete integration blockers and decisions changing acceptance or
priorities. Architecture is not an approval gate for sound bounded work.

| Boundary | Owner | Required consumer connection |
|---|---|---|
| Captured console denotation, resources, author theorem semantics and root migration | process | Exact captured request, resource model dictionary/value/snapshot and appended demand fragments |
| Target projection, caller/driver and source CFG refinement | lowering | Actual reached caller history and selected provider occurrence; exact global output cut |
| Win32 applicability, provider dispatch/publication, nonresponse and matched return | windows | Actual same-call provider evidence and explicit selected-profile realization assumptions |
| Memory resolution, initialization, custody, loan effects and conflict checking | memory-model | Actual accepted memory transitions and captured access identities |
| Instruction semantics and canonical encoding/decoding | x86 | Selected instruction/source, machine state and all allowed flags/results |
| Final chain and artifact integration | spikes, supported by the above owners | Exact authored source through loaded execution and captured specification |

ELF serialization and Linux syscall semantics remain Linux-owned when that
slice activates. Exact placement, loading, admitted initial states and execution
composition still need explicit connections beyond format serialization laws.

## Evidence inspected

The console capture is process checkpoint `3dbfa17f` (integrated by spikes as
`ffcdc64e`), following history/wait and console denotation checkpoints. The
lowering drafts inspected are on `codex/lowering-console-projection`:
`Grass/Console/TargetProjection.lean`, `CapturedProjection.lean`, and
`Grass/Refinement/Console/WriteFileProjection.lean` and `WriteWaitingGap.lean`.
Lowering subsequently released these as checkpoint `f6908249`, with process
review and supplier-reported gates passing. Windows' corrected nonresponse draft was
`.lake/WriteFileNonresponse.lean`, also unpublished. Draft findings must be
rechecked against the final supplier diff before integration.

The existing `Grass/Platform/Win32/WriteFile.lean`,
`Grass/Semantics/SpecProcess.lean`, `Grass/Certificate.lean` and
`Grass/Verify/VerifiedProgram.lean` were inspected directly. The corrected Windows
draft independently passed `lake env lean .lake/WriteFileNonresponse.lean`
with no diagnostics. Other suppliers report focused and full builds separately;
those results do not establish provider adequacy.

## Interface conclusions

1. **Keep capture exact.** `CapturedSpecification` is explicitly staging, not a
   second certificate root. `CapturedTargetProjection spec Status` retains the
   exact capture index; its `target` is indexed by `spec.context.request`.
   `project_complete` and `project_withLiveness` preserve the complete carrier
   definitionally. Appending an authored liveness demand fragment does not filter executions or
   create an optional compiler certificate. Resource semantics remain the
   stored snapshot with its original dictionary and value indices.

2. **Replace the reply-only driver boundary without weakening the contract.**
   `WriteWaitingGap.no_full_output_wait` proves that the existing `WriteProcess`
   cannot wait with the full nonempty payload already published;
   `full_output_wait` constructs the upper behavior it misses. This is a
   concrete coverage defect. Publication must be represented while the actual
   call remains pending; neither an invented reissue nor early termination
   repairs it.

3. **Use the one occurrence-indexed provider seam.** `Prefix` retains
   `PendingAt`, `Prepared`, clean audit and bounded acceptance. `CommittedStep`
   requires actual `Action.Runs`, selected dispatch/publication evidence,
   publication arithmetic, confinement and causal evidence. `History` fixes
   realization, initial state, call and pending record, starting at an actual
   handoff with zero acceptance. `History.published_eq_output` connects the
   accumulated publications to that request's exact prefix. A free-standing
   `Prefix` is not reachability evidence.

4. **Project at call-start plus acceptance.** `WriteFileProjection.cut` uses
   `start.offset + frontier.accepted` with
   `record.request.bytes = start.remaining`. `history_prefix_exact` accounts
   for earlier output plus this exact call's published bytes. `positive_step`
   supplies an actual upper transition; `zero_step` proves only local equality
   and empty output. The enclosing caller still has to establish that `start`
   and the provider handoff arise from the same reached execution.

5. **Separate infinite actions from absence of response.** The inspected
   `InfiniteContinuation history` fixes the original occurrence and realization
   and stores actual `CommittedStep` edges. Its `historyAt` is now derived by
   extending the supplied history, rather than independently chosen at each
   point. `FixedCut.output_empty` correctly consumes the additional fixed-count
   premise. Neither result proves that all physical continuations have that
   shape or that the external call never responds.

   The first inspected `StalledNonresponse` required an infinite committed-step
   stream, excluding finitely many actual provider actions followed by permanent
   absence of external response. Windows and process agreed to correct it:
   endpoint-rooted `StalledNonresponse predicate history` contains only evidence
   at the exact fixed realization, call, record, reached state and accepted cut.
   It requires no invented steps. Earlier finite activity can be represented by
   a later derived `historyAt`; the infinite-action case remains separate.
   Permanent silence describes the selected execution, not impossibility of
   an allowed reply transition. The latter would contradict reply completeness.

   The corrected draft replaces the phantom realization parameter with
   an explicit argument to the selected relation:
   `Realization -> CallId -> Pending Request -> State Request -> Nat -> Prop`.
   This is evidence plumbing, not a theorem linking it to a physical profile.
   A supplied predicate, including a trivial one, cannot discharge provider
   adequacy. Its interpretation must be fixed by the selected realization/profile
   and connected at the consumer boundary. The corrected declaration was read
   and independently compiled; production promotion still needs the final
   supplier checks. Earlier progress may be any finite `History`, not only a
   restriction obtained from an infinite continuation.

6. **Keep return separate from acceptance and loan bookkeeping.** Full
   acceptance can still be pending. A future matched-return theorem must bind
   the actual return, exact call/record, raw BOOL and count-slot contents,
   accepted output, `CallProtocol.return?` effects and caller continuation.
   Provider effects, matched return and subsequent caller actions must compose
   in the same causal model. Loan reclamation alone proves neither physical
   return nor ordering.

7. **Do not promote local semantics to a machine certificate.** x86
   `RegisterSemantics` supplies operand-local transfers; `RegisterDecode`
   connects supported canonical encodings and decoder suffixes. Fetch, RIP,
   execution admission, faults/interruption and provider transitions need
   their own connections. Undefined flags remain allowed choices. Generic
   memory fault-prefix bounds do not imply ISA atomic all-or-nothing writes.
   External causal evidence does not bypass the conservative generic step
   checker.

## Remaining proof obligations

| Obligation | Lead owner | Completion evidence needed |
|---|---|---|
| Reached caller-to-handoff relation | lowering with windows | Exact request suffix, prior global output and actual handoff in one execution |
| Provider behavior coverage | windows with lowering | All admitted cuts, response outcomes and nonresponse cases under the selected profile; explicit adequacy premises |
| Infinite provider-action projection | lowering with process/windows | Bounded-monotone acceptance stabilization, rooted suffix extraction and justified treatment of internal divergence/stuttering; endpoint nonresponse is separate |
| Matched return | windows with memory-model/lowering | Actual response, count/BOOL/output, custody effects and coherent causal return-to-caller connection |
| Source CFG and machine connection | lowering with x86/spikes | Exact authored instructions, call arguments, local invariants, faults and caller stuttering |
| Terminal observation and responsive strategy | process with windows/lowering | Actual status observation; standard authored `environmentResponsive` meaning and its bridge, without redefining the premise |
| Captured root and certificate migration | process with architecture/spikes | Exact captured denotation, full terminal/infinite/waiting correspondence and choice coverage across adjacent tiers |
| Artifact closure | spikes with format/ISA suppliers | Exact bytes, placement/loading and admitted initial executions connected to that machine behavior |

Arbitrary `Outcome -> Status` selection is projection data until it preserves
the distinctions demanded by the authored contract and is connected to actual
terminal observation. The staging demand `terminatesUnderBoundaryResponse`
does not yet establish the authored `environmentResponsive` theorem.

The old `SpecProcess` exposes finite `accepts`; `ProgramBehavior` supplies an
independently selected system. `VerifiedProgram.coverage` covers represented
histories of that selected system, not yet the authoritative captured
denotation. Existing completion adequacy omits the new permanent-wait carrier;
old prefixes also erase finite choices. Retaining those adapters as the final
bridge would leave the root defect intact. Migration must preserve the new
choice-bearing histories and permanent waits, including full-output waits,
and account for divergence when abstracting internal steps.

`VerifiedProgram` means applicable safety plus specification correspondence.
Author liveness, fairness and no-drop proofs remain separate. A theorem-only
edit must not create a new lowering obligation; a behavioral edit can invalidate
correspondence and affected author proofs. This is application of existing
decisions, not a new universal termination requirement.

## Review disposition

The finite capture/projection/provider interfaces are suitable inputs for
continued local work under their stated limits. Full driver coverage, physical
provider adequacy, matched return and root migration remain open. The external
nonresponse interface correction above is agreed with windows and process and
the corrected scratch declaration passed direct review and compilation. This
review does not block unrelated sound local proofs or claim
spike acceptance; spikes retains integration and acceptance authority.

Independent document review by a Sol agent found no remaining substantive
interface or ownership defect after the endpoint correction. Its terminology,
checkpoint-status and infinite-action scope clarifications are incorporated.
Document validation: `check-doc-links.sh` passed for all 56 Markdown files and
the staged diff passed `git diff --cached --check`. These are document checks,
not end-to-end implementation verification.
