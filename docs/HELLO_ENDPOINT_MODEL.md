# Fixed Win10 console endpoint connection

Architecture decision proposed to spikes, 2026-09-09. This addresses the next
Hello certificate boundary after common CALL/ReturnHome/CP-entry construction.
Names below are proposed roles unless explicitly identified as existing code.
No DSL or new native execution campaign is required for this step.

**Review status:** process review identified a blocking environment-quantifier
issue below. The fixed-initial-environment signatures are provisional and must
not be implemented as an accepted complete-correspondence solution until that
issue is resolved. Shared entry/settlement/resume machinery is unaffected.

## Placement and trust

Keep GetStdHandle and ExitProcess allowed behavior in Windows semantic modules
beside Console.lean. Put their connection to raw entry, same-call settlement and
ProviderResume in endpoint adapter modules. The fixed Win10 profile assembles
those relations with the existing WriteFile semantics. Its environment data
includes process identity, standard-handle table/epoch, output route identity
and terminal observations. Those are explicit admissible environment inputs,
not caller-selected replacement execution or observation relations.

FOUNDATION section 3 permits recorded parameterized external/model correspondence.
Use it: define the model and observation relations concretely, then expose the
claim that native CPU/loader/API behavior refines that model as a named profile
assumption recorded in the TCB ledger. Do not require a proof of Windows internals,
add an axiom to Lean, or turn the assumption into an arbitrary BehaviorModel.
The same fixed model governs every admitted execution of the artifact, not just
the successful trace captured by a test.

## GetStdHandle: request, raw result and route

Existing Console.GetStdHandleResult/UsableHandle classify sentinel bit patterns.
They do not establish that a non-sentinel value denotes stdout or is writable.
The native function does not validate the stored standard-handle value; see
[GetStdHandle](https://learn.microsoft.com/en-us/windows/console/getstdhandle).

The fixed model needs these exact connections:

1. Retain the original evaluated CALL, selected logical binding, issued CallId,
   whole pending record and actual selector decoded from that reached state.
2. Define allowed GetStd results from that request and the environment's actual
   standard-handle table at the selected observation point: failure/invalid,
   absent/null, or the recorded handle value. Classify raw bits independently of
   usability. Do not require every non-sentinel value to denote a valid stream.
   State and cite the admitted failure/pending cases; nonempty response evidence
   alone does not prove external completeness.
3. A returned raw RAX is the result for that same occurrence, with complete
   loan settlement and shared checked resume. Preserve occurrence identity
   through the actual history; matching numeric request/handle values is not
   enough. Resume supplies frame/slot mechanics, not the provider result law.
4. If the environment resolves the returned table entry to the selected stdout
   route, retain that binding with process/epoch and descriptor lifetime. Carry
   it through the actual register/data flow to each WriteFile request. If no
   such usable route exists, retain failure behavior rather than fabricate one.
5. Instantiate existing WriteFile.Realization.executesFor/publishes from the
   fixed environment/provider semantics. Publication is tied to the same
   request handle, occurrence and route, with existing accepted-prefix laws.
   A request cannot publish to the modeled stdout merely because its handle is
   nonzero or its payload happens to equal the desired output.

For the first synchronous profile, either admissibility guarantees handle-table
and route lifetime stability during the relevant call sequence, or the model
retains actual updates and rechecks bindings. Record the chosen restriction;
do not obtain stability from absence of modeled guest calls alone. Preserve
WriteFile's permitted failures, short writes and zero progress. A valid route
does not guarantee any write succeeds.

The result adapter shares GetStdHandle/WriteFile return mechanics: exact pending
record, full batch settlement, original runtime frame, current return-slot read,
preserved registers, computed resume and caller-control restoration. Keep only
the result/payload and route meaning API-specific. Do not use ProviderResume's
data-only Link as evidence of the original CALL occurrence.

### Settlement reuse: existing laws, distinct endpoint evidence

Current CallProtocol already supplies `return?_matches_occurrence`,
`return?_effects`, `return?_removes_pending`, `return?_loans_removed` and
`return?_replay_rejected`. GetStdHandle must use these directly from its actual
return equation; it must not copy their proofs into a second settlement library.
Existing WriteFile.MatchedReturn.effects/consumed show the intended thin adapter.
Keep its publication-prefix conclusion WriteFile-specific.

If a checked endpoint return builder is needed, it executes CallProtocol.return?
on the actual reached protocol state, call and whole pending record's IDs, then
retains the exact returned record and next state. It derives the common effects
once using the existing laws. Its success does not provide a result interpretation
or prove where the original CALL occurred. Those come from the original entry,
actual history, fixed endpoint relation and runtime-preservation evidence.

Likewise, CallResumeBinding's shared PolicyBinding.ofCallEntry and
Link.ofReachedPlan provide the initial resume inputs for both APIs. They are
already thin projections from actual entry and runtime insertion. Reuse their
result through actual provider history; do not recompute a plausible frame at
return time or infer historical identity from a matching lookup alone.

Keep the ordering of result production, loan settlement, current return-slot
access and caller-control restoration explicit in the raw endpoint relation.
The permission state used by each access must be the actual stage state. A
generic convenience wrapper must not move the slot read across settlement or
discard a refusal merely to satisfy its desired result type.

## ExitProcess: invocation is not terminal observation

The actual ExitProcess entry retains the selected request's low DWORD status and
same CallId. It acquires no returning frame. Define a fixed terminal relation
between that process/occurrence and the observed completed process exit, with
observed status equal to the request status and accumulated output preserved.
Preserving output is itself a fixed profile obligation: any teardown/provider
output must either be represented in the observation relation or excluded by an
explicit justified environment restriction. It cannot disappear because it was
not emitted by the guest WriteFile loop.
Decode the demanded zero/one statuses through the target projection; prove their
distinction using the existing status encoding. No caller continuation follows
the terminal edge.

Allow the pending/nonterminating behavior admitted by the profile. ExitProcess
can deadlock during DLL teardown; nonreturning is not a responsiveness theorem.
See [ExitProcess](https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-exitprocess).
A progress theorem must consume an explicit recorded termination/responsiveness
assumption for the selected environment, while unconditional correspondence
retains the pending behavior. Do not filter it away using the desired outcome or
treat a trap/UD2 after an unexpected return as successful termination.

## Selected minimal implementation interface

### Open quantifier decision

The standalone [EnvironmentChoice experiment](../Tests/Architecture/EnvironmentChoice.lean)
kernel-checks a minimal negative and positive pattern: covering all outcomes by
a union of fixed plans does not cover both outcomes at one fixed prefix;
committing on both sides with exact matching reporting states does. It proves
one-step matching and outcome coverage for every related toy state. It imports
no Grass semantics and is not a BehaviorCorrespondence or Hello proof.

Process review narrows the proposed deferred-choice experiment to two necessary
residual cases. After choosing a valid route at cut zero, the upper writing
frontier still permits stdoutUnavailable. After a final successful return at
the full cut, that upper writing frontier still permits writeFailed. Actual
commitments must align with justified reporting transitions or retain the entire
residual choice set. Relabeling WriteFile failure as stdoutUnavailable needs an
actual semantic interpretation, not a proof convenience. If these cases cannot
be realized, root must decide an explicit authored-frontier or contract change;
larger unions and hidden history cannot fix the mismatch.

BehaviorCorrespondence.completeBack requires every upper completion from the
same related lower prefix. A lower initial state with fixed absent stdout cannot
realize the successful full-output completion admitted by the captured console
denotation. initialForth relates each lower initial history; taking a union over
different fixed environments does not repair this per-prefix obligation. The
same issue applies to WaitTranslation.responseCoverage/WaitMatch.replyBack at a
specific occurrence. Native-to-model correspondence does not by itself prove
model-to-authored back coverage.

Direct inspection of HistoryRelation strengthens this check: extendBack already
requires every upper finite extension from each related pair, and extendForth
must relate every lower extension. Deferring only the initial choice is not a
proof. Audit the post-GetStd and post-provider-choice prefixes too. The upper
ObservedBehavior.writing phase still permits all replies at its cut; reporting
fixes a Selection and can only observe it. A relation may advance to reporting
only when that selection and the observation history are justified, not as a
way to discard inconvenient alternatives. Include WaitMatch's actual reply-headed
extension coverage, not only equality of protocol response sets.

Root/process must choose and prove the correct quantification: leave model
environment choices unresolved until the matched interaction and retain the
selected bindings thereafter, or justify environment conditions in the actual
upper interpretation. The first is under review, not yet established sufficient
for subsequent write/exit choices. Do not weaken CompleteMatch, remove failure
branches or substitute successful traces to resolve this. The signatures below
record the pre-review proposal, not a ratified answer to this blocker.

Exit additionally needs terminal disposition of the same pending occurrence and
all live loans/linear obligations. Observed code/output alone proves no such
safety. Any provider/DLL raw divergence classified as an observation wait must
pass the upstream agency/coverage normalization retaining raw execution evidence;
strict CompleteMatch itself retains infinite-to-infinite and waiting-to-waiting.
Responsiveness assumptions must address the exact authored boundary.

A non-sentinel unusable handle follows the actual non-sentinel branch and
attempted WriteFile failure path. It must not be reclassified as a GetStdHandle
null/invalid result merely because no usable route resolves.

Spikes approved the model/correspondence boundary and selected stable standard
handle table plus route lifetime for the first synchronous profile. Stability
and teardown-output disposition are explicit admissibility conditions, not
inferences from the program text. The following is the implementation handoff;
type names are proposed, and signatures describe the required indices.

Windows owns ConsoleEnvironment and the fixed relations in a module beside
Console.lean. Use ordinary data for process identity, environment epoch, the
three standard-table bit values, and a finite handle-to-route/resource table.
Include the selected stdout route and its synchronous mode/rights/lifetime data.
A missing route represents an unresolved/unusable handle; do not force a route
for every non-sentinel value. Admissibility binds any resolved standard-output
entry to the selected stdout route and keeps those identities stable. Reuse an
existing resource identity type if available; do not duplicate memory grants.

For the existing supported-selector slice, the minimal result relation is:

```text
GetStdAllowed env selector rawResult :=
  exists device, selector = StdHandleId.value device and
    (rawResult = INVALID_HANDLE_VALUE or rawResult = env.standardValue device)
```

The table retains raw values, including zero or stale/non-sentinel values.
Admitting failure independently is a conservative over-approximation. This
definition is for the three documented selectors; the fixed Hello entry proves
the output selector. Do not silently claim coverage of arbitrary DWORD selectors.
The relation classifies permitted raw results; a separate checked table lookup
`routeOf? env handle` supplies route evidence. Successful lookup alone supplies
neither write success nor provider execution. Both relations are definitions
over fixed environment data, not arbitrary predicate fields of the environment.

Windows endpoint code constructs `GetStdReturned env entered before after result`
from the original entry occurrence, actual reached history, exact CP return
equation, GetStdAllowed for that entry's selector, actual result RAX, and checked
resume on the correct stage state. Index it by the entire entry and states,
not just selector/handle numbers. The generic return builder supplies settlement
effects; the fixed Windows relation supplies result meaning. Lowering consumes
its RAX equation and route lookup through the authored TEST/CMP/data-flow path.

Represent observed exit as data retaining process, completion marker and status.
The fixed `ExitTerminal env entered observation` requires that exact process,
the original ExitProcess occurrence, completed termination and equality to its
recorded request status. The observation history or adapter witness connects
the occurrence; the host observation need not physically contain a CallId.
Keep `ExitPending` separately in complete behavior. No return constructor is
introduced, and neither relation implies the responsiveness assumption needed
by author progress.

Root owns fixed-profile composition: select one environment and the fixed
relations above, instantiate WriteFile realization with the same route table,
and expose named external/model correspondence plus stability/output-scope
assumptions in the profile's recorded trust interface. The certificate cannot
choose these relations independently. Process owns checking finite/complete
observation and pending/progress composition; lowering owns actual path and
loop correspondence. Windows owns result/terminal adapters after CP factoring.

This division requires no new target-neutral runtime record, arbitrary provider
callback or attribute syntax. It makes common entry/settlement/resume machinery
available to both returning APIs while leaving only their actual result and
effect meaning to the endpoint author.

## Direct whole-Hello closure sequence

1. Finish common CP-entry adoption and actual evaluated-CALL constructors.
2. Define fixed console environment, GetStd allowed-result/route relation and
   Exit terminal/pending relation, with explicit profile correspondence entries.
3. Construct the GetStd same-occurrence result/settlement/resume adapter. Prove
   the authored sentinel branches and carry actual RAX through to WriteFile's
   handle; connect successful publication to the retained stdout route.
4. Compose existing actual WriteFile service history, matched return and body
   reentry. Keep loop invariants and short-write cursor/progress obligations in
   lowering, reusing generic continuation and frame laws.
5. Connect every success/failure exit path to its actual ExitProcess request and
   the fixed terminal/pending relation. Assemble finite and complete behavior
   correspondence for the fixed profile, then the existing public certificate
   and emitter chain. Discharge progress only under its stated assumptions.

Review rejects a GetStd result from another occurrence, a non-sentinel handle
without a route treated as stdout, a changed/closed route reused silently, a
WriteFile publication attached to another handle, partial loan settlement,
Exit entry counted as termination, or a terminal code detached from its request.
These are implementation acceptance checks, not claims of existing tests.
