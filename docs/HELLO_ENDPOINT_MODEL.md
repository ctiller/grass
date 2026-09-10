# Fixed Win10 console endpoint connection

Architecture decision proposed to spikes, 2026-09-09. This addresses the next
Hello certificate boundary after common CALL/ReturnHome/CP-entry construction.
Names below are proposed roles unless explicitly identified as existing code.
No DSL or new native execution campaign is required for this step.

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
