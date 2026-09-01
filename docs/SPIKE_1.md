# Spike 1: annotated proof from portable Hello World to Win32 PE

Status: design artifact for review; intentionally not compilable yet.

Authoring view: agents maintain exactly `Spec.lean` and `Program.lean`. The
exact snapshot is at the end of this document. All other intermediate records
shown below are generated expansions, library interface sketches, or proof
sketches unless explicitly labeled authored source.

Product decision: this spike is the architecture-validation artifact for the
named `SynchronousStdoutOnly` execution profile, not Grass's production-general
Windows console implementation. It may be shipped only with that applicability
constraint in artifact metadata. A later default console plan must adapt between
synchronous and overlapped inherited handles through the same asynchronous byte-
flow specification; it does not change this portable Hello specification.

This is the program and proof we want Grass's eventual libraries to support.
The pseudo-Lean is precise enough to argue about proof burden before library
interfaces harden. Comments explain why a demand exists, who should discharge
it, and which weaker substitutes are unacceptable; normative force comes from
the owning documents listed in [README.md](README.md).

The resource-parameterized portable specification function is the precious
semantic artifact in this spike. The logical `message` and specification
definition state program meaning; `resources` selects this build's reviewed
assurance profile. The selected target
projection and platform
plan and generated or authored program are reviewed
construction inputs, but replaceable implementations: changing either
invalidates the dependent certificates and emitted artifact, which are then
regenerated and rechecked. Compiler-generated CFG/register-allocation results,
proof terms, inferred contracts, encodings, and PE layouts are derived witnesses,
while literal register choices belong to authored `helloSource`. None are independent
author-facing pipeline artifacts. The specification is rejected if it names an
implementation identity or detail not required to state observable behavior,
safety, progress, or terminal resource policy. Conversely, minimality may not
erase a behavior the author actually demands.

The portable program requests the logical text line `Hello, World!`. The Win10
projection represents it as the 15 UTF-8 bytes `Hello, World!\r\n`. Successful completion
maps to exit `0`. Every failure maps to exit `1`, while the audit
trace retains unavailable, failed-write, and zero-progress classifications.
Conservatively, a failing external call may report failure after any prefix,
including after all requested bytes became observable. Zero progress is reached
only while bytes remain, so that outcome follows a proper prefix.

The specification is portable. The realization is Win32 x64 on the Windows 10
API baseline. The artifact is an ASLR-enabled PE32+ image.

## 1. The proof we want to read

```lean
namespace Grass.Spike1

/-!
`TextLine` is logical text without a target newline or encoding. The behavior
contract therefore says what text is wanted without committing the portable
specification to UTF-8, CRLF, a pointer, allocator, or Windows representation.
The faithful target projection derives the canonical `Vec Byte` and its length;
neither is an independently maintained semantic declaration.
-/
/-!
The portable contract distinguishes success and failure without assigning an
OS number. Adding a reachable failure constructor makes the behavior contract
fail to elaborate until it is classified. The Win10 target projection below
maps success to zero and every failure to one. Detailed provider causes remain
distinct in the mandatory audit trace.
Callers can still remap or enrich a typed error row. No wildcard/default handler
is accepted at a verified external boundary.

Grass may provide an explicitly named `CliSpec.writeStdoutResponsive` convenience
builder for the common portable outcome/liveness contract. Merely writing an
effect does not silently choose failure observability or liveness: those are
precious semantic choices, even when a transparent named builder supplies them.

`HelloOutcome` carries only portable product data. Prefix facts are laws of
`Console.writeStdout`, not proof fields application code must pattern match.
Provider diagnostics remain in the complete audit trace.
-/
inductive HelloOutcome
  | success
  | failure

/-!
The portable specification is parameterized by `resources`. Numeric terminal
status and text representation belong to the separately proved target
projection: Win32, Linux, WASI, semihosting, and hypervisor/test devices can give
them different physical realizations. A target with no observable status
channel can still project the abstract outcome only if its profile supplies an
adequate observation. The portable pair does not
mention handles, Win32, x86, PE, calls, or write fragmentation.
Safety, ABI, obligation, and progress demands remain independent mandatory
fields; the functional projection cannot hide them.

The author explicitly chooses conditional liveness intent. A full pipe may leave
a safe execution pending forever. `environmentResponsive` has a fixed portable
meaning: under a coherent abstract branching strategy, every reachable frontier
settles on every compatible maximal continuation, and each terminal-status
frontier produces its declared observation. It grants no success result. The
platform realization may name concrete sufficient assumptions only by proving
they imply that predicate; the author does not duplicate the frontier inventory.
-/
def message : TextLine := "Hello, World!"

def resources : ConsoleResourceModel :=
  ConsoleResourceModel.singleLine

def helloContract {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : BehaviorContract resources :=
  Console.writeLineContract resources message HelloOutcome

def helloSpec {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.ofRelational (helloContract resources)
    |>.withLiveness (.terminatesUnder [.environmentResponsive])

theorem helloSpecCorrect {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : MeetsAllSpecificationTheorems (helloSpec resources) :=
  Console.writeLineContractCorrect resources message HelloOutcome

def spec : SpecProcess resources := helloSpec resources

def policy : TargetOutcomeProjection HelloOutcome UInt32 :=
  .successOrFailure
    (success := HelloOutcome.success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ConsoleText
    (newline := .crlf)
    (encoding := .utf8)
    (outcome := policy)

/-!
Spike 1 uses the unique standard sequential realizer registered by
`Console.writeStdout`. Its extensional console-write relation may fragment the write arbitrarily, exposes every
dependent provider result, and terminates through an abstract status demand. It
contains no process population, channel, handle, chunk-size, or platform loop.
The library theorem proves it realizes the precious byte/status trace contract.

A generated `SequentialAdapter` elaborates it as root/byte-egress/terminal child
processes in the universal process algebra. The egress child accepts the message
once and turns every positive partial provider write into an exact committed
prefix while retaining only the unwritten suffix. That adapter and
its channel escrows are not application declarations and are absent from the
author surface. A novel relation can still be selected explicitly with `using
sequential_process proof`; standard Hello needs no names for either witness.
-/

/-!
Provider selection is program data, not ambient instance search. These exact
dictionaries are retained from elaboration through emission. A second console
provider with the same friendly name cannot be selected during lowering.
-/
def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64SynchronousStdoutOnly projection

/-!
`win10X64SynchronousStdoutOnly` is an audited named value whose inspectable expansion
is exactly `win10X64` plus `win32SynchronousStdout` and `win32ExitProcess` under
their nominal keys. It is not ambient typeclass search; changing either provider
requires constructing or selecting a different plan value.

Provider selection bubbles up its context requirements; the author does not
retype them. Inspection of `plan.contextRequirements` visibly includes
`StdoutSupportsNullOverlappedWrite`, because Windows may supply an inherited
handle opened for overlapped I/O. This provider is inapplicable without that
runtime-context witness. A future provider may implement the full overlapped
protocol. Merely checking handle non-nullness cannot prove synchronous mode.
The plan and emitted artifact are therefore published as
`SynchronousStdoutOnly`; they do not claim general inherited-handle or redirected
async-pipe suitability. A production-general console plan must add an adaptive
runtime/provider protocol without changing the precious write specification.

The requirement is neither silently discharged nor left open. It becomes an
explicit `AdmissibleExecutionContext` parameter of the public execution theorem.
Admissibility is defined without reference to `Loads` or execution and has an
independent inhabitant. Loading is not filtered after the fact to manufacture
the premise; the context is part of the initial environment supplied to the
loader and machine model.

The plan's selected provider modules construct the Win32 terminal protocol laws for exactly
`policy.statusRange`: preservation, reflection, distinguishability, and
pending/terminal resource fidelity. This is where status values zero and one are
proved representable and distinct through `ExitProcess`; it is not inferred by
calling an arbitrary physical termination action a normalization. Constructing
`plan` checks these fields automatically; provider test suites and generated
diagnostics inspect them, but application source contains no probe lemmas.
-/
/-!
The original six acts are a useful ordering, not a mandatory storage pipeline.
The direct relational program is this spike's replaceable plan source.
Provider realization produces a platform-level driver contract. From there Grass supports two peers: generated CFG
lowering, or an authored assembly CFG that directly refines that contract.

Spike 1 takes the authored route. `helloSource` carries the instructions,
labels, register allocation, and proof annotations shown in section 5. The
separate verifier checks those annotations against the synthesized process driver contract;
loans and loop invariants remain checked machine proof state.
This is the genuinely program-specific machine proof we expect to review. The
standard verifier solves per-instruction semantics, ordinary ABI edges, and
arithmetic; named cases remain if those facts do not follow.
-/
/-!
This is the reviewed certificate assembly point. `verify_assembly` first
elaborates an inspectable canonical sequential process plan/driver, exact platform contract, and
`AssemblyImplements contract` witness, then composes the portable specification,
provider contract, assembly refinement, ghost erasure, instruction
encoding/decoding, PE linking, loading, and end-to-end theorem. It reports the
failed named boundary and leaves its actual goal; it is not an opaque oracle.
Authors may name either intermediate witness while debugging or sharing a
contract, but a one-component program need not maintain those definitions.
Generated code uses `verify_program plan with source` against the same internally
elaborated platform contract.
-/
def helloVerified : VerifiedProgram spec := by
  verify_assembly plan with helloSource

/-!
Internally the result contains dependent adjacency certificates: the selected
provider contract realizes this exact specification; the synthesized
`AssemblyImplements` witness refines that exact contract; erasure is of that exact ghost-bearing assembly; the linked PE
contains that exact raw program; and `emitProgram` writes that exact PE. These
witnesses are inspectable in diagnostics but are not six user-maintained sigma
definitions. The field expansion remains the list in section 7.
-/

/-!
`emitProgram` is total only at this gate. Fallible raw encoding and linking live
below it. The bytes here are definitionally or theorem-connected to
`helloVerified.linkedArtifact`; the emitter cannot choose a lookalike artifact.
-/
def bytes : ByteArray := emitProgram helloVerified

end Grass.Spike1
```

The generated documentation prints the full theorem type of
`helloVerified.sound`; application authors do not write a wrapper which merely
specializes that projection. The author-facing proof contains no intermediate
sigma plumbing. Internally,
dependent witnesses make every adjacency inspectable; the implementation may
elaborate them transiently rather than store public pipeline datatypes.

## 2. Portable specification and effects

The selected functional observation is:

```lean
inductive ProviderWriteCause
  | unavailable
  | failed (committed : ByteArray)
  | noProgress (committed : ByteArray)

structure HelloObservation (wanted : ByteArray) where
  stdout : ByteArray
  outcome : HelloOutcome
  status : UInt32

def HelloObservation.Accepts
    (wanted : ByteArray) (o : HelloObservation wanted) : Prop :=
  o.status = policy.status o.outcome ∧
  match o.outcome with
  | .success => o.stdout = wanted
  | .failure => o.stdout.IsPrefixOf wanted
```

`CliWritePolicy.successOrFailure` is library data pairing the standard closed
binary `HelloOutcome` with a total status function; it does not hide a default
branch. The complete audit trace separately retains `ProviderWriteCause` and
the exact provider result occurrence. A total projection maps unavailable,
failed-write, and zero-progress to `.failure`; those diagnostics are not public
product behavior. `noProgress` remains a prompt implementation failure for a
successful zero-byte response without acquiring an arbitrary public status or
outcome constructor.

The Win32 realization proves `ExitProcess` exposes `status`. Linux can normalize
its wait status for the used range; semihosting or a hypervisor/test device can
transport and normalize the same number. A bare-metal realization changes the
physical terminal protocol, not `HelloObservation`.

`stdout` is a raw ordered byte stream. The specification does not claim Unicode
glyph rendering or a particular Windows console code page. The chosen message
is ASCII-compatible UTF-8, but that convenient fact does not redefine the
effect; a future text-console abstraction would require its own encoding law.

The optional high-level-program route uses the portable failure and an ordinary
`Except` result:

```lean
class Console (key : ConsoleKey) where
  writeAll : (bytes : ByteArray) -> Program (Except WriteFailure Unit)
  law      : WriteAllLaw writeAll

class Terminal (key : TerminalKey) (Outcome : Type) where
  terminate : Outcome -> Program α
  law       : TerminalLaw terminate
```

`WriteAllLaw` is indexed by the requested argument and relates each result to
ordered output events. `.ok ()` commits exactly the requested bytes; `.failed`
commits a prefix; `.noProgress` commits a proper prefix. These are law proofs,
not fields carried through application pattern matches. The relation admits
pending behavior and neither promises atomic output nor assumes progress.

For composition, libraries propagate typed failures automatically and weave
their error rows by named injections. A verified program boundary must provide a
total handler for the resulting closed row. This gives local brevity without an
ambient catch-all, exception swallowing, or loss of failure observations.

The specification's liveness intent remains independent of functional
observation. The console/terminal specifications synthesize possible frontier
kinds. Win32 realization supplies a concrete branching strategy, couples its
complete generated-history set to the abstract strategy, and proves universal
responsiveness across all reachable frontier kinds and compatible maximal
continuations. Both strategies prove root compatibility, prefix closure,
nonempty continuation sets, complete coverage of every allowed result value,
and existence of maximal executions, so the universal theorem cannot range over
an empty or favorable-result-only tree. The unrestricted execution profile,
separately, contains real infinite pending branches for unconditional safety.
That inhabitance proof
is separate from per-call response adequacy and from unconditional safe-pending
safety. Conditional termination ranges over every compatible conforming
execution; it is not an existence claim for one favorable run. Thus an
indefinitely pending call is a permitted safe infinite
execution, but not a terminated one. Once a call returns, the implementation
must reach exit or the next frontier in finite internal time.

## 3. Win32 realization and its proof burden

The nominal provider `Win32.Console.Synchronous.v1` first exposes logical Win32
effects in Act 3:

```lean
GetStdHandleRequest(STD_OUTPUT_HANDLE)

WriteFileEffectRequest where
  handle     : BorrowedHandle .synchronous
  buffer     : ByteArray
  count      : UInt32
  countFits  : buffer.length = count.toNat
  overlapped : None

ExitProcessRequest where
  exitCode : UInt32
```

This request names Win32 behavior and its dependent result, but it is not yet an
ABI call and does not pretend that a pure array is a pointer. Act 4 realizes it
as a physical boundary:

```lean
WriteFileCall where
  handle     : BorrowedHandle .synchronous
  buffer     : ReadLoan Byte
  count      : UInt32
  countFits  : buffer.length = count.toNat
  overlapped : NullPointer
```

Its fields are private. `WriteFileEffectRequest.ofChunk` consumes
`buffer.length ≤ UInt32.max.toNat`, derives `count`, and constructs `countFits`;
custom requirements cannot manufacture mismatched buffer/count pairs. Responses
are indexed by this exact request.

`GetStdHandle` may produce a usable borrowed standard handle, `NULL`, or
`INVALID_HANDLE_VALUE`. The borrowed process handle creates no `CloseHandle`
obligation. The selected plan additionally requires the initial standard handle
to support synchronous null-overlapped writes. Windows handle non-nullness does
not imply that property; without the explicit context witness this provider is
inapplicable. A later provider can support inherited overlapped handles by
modeling their full completion protocol.

A synchronous `WriteFile` may remain pending, fail after a modeled prefix has
become externally observable, or succeed with any count from zero through the
requested count. Its dependent response separately records the Boolean return,
output DWORD, output event, and memory post-state; equalities used by the
realizer come only from the cited API law. Successful zero means `noProgress`.

The provider library's pure scheduling/refinement algorithm is:

```lean
def win32WriteAll (requested : ByteArray) :
    Win32 (Except WriteFailure Unit) := do
  let h ← getStdHandle STD_OUTPUT_HANDLE
  if h = null || h = invalidHandleValue then
    return .error .unavailable

  let rec loop
      (committed remaining : ByteArray)
      (partition : committed ++ remaining = requested) := do
    if remaining.isEmpty then
      return .ok ()
    -- `Console.writeAll` accepts arbitrary logical lengths. Each physical call
    -- is bounded by DWORD without narrowing or wrapping the original length.
    let chunk := remaining.take UInt32.max.toNat
    match ← writeFileEffect h chunk with
    | .failed externalPrefix _providerError =>
        return .error (.failed (committed ++ externalPrefix))
    | .success 0 _ =>
        return .error (.noProgress committed)
    | .success (n + 1) within =>
        loop (committed ++ remaining.take (n + 1))
             (remaining.drop (n + 1))
             (by library)
  termination_by remaining.length
  decreasing_by omega

  loop #[] requested (by simp)
```

The provider library proves these separately named facts:

```lean
theorem loop_partition ... : committed' ++ remaining' = requested
theorem loop_output_prefix ... : observed.IsPrefixOf requested
theorem positive_write_decreases ... : remaining'.length < remaining.length
theorem loop_internal_termination ... : TerminatesBetweenAPICalls loop
theorem win32WriteAll_refines : Realizes win32WriteAll Console.writeAll
theorem chunkSchedule_refines : PureChunkScheduleRefinesWriteAll
```

They quantify over all permitted synchronous handle values, arbitrary logical
request lengths, failures, counts, committed prefixes, and pending points. The
provider chunks any finite logical array into nonempty `UInt32`-bounded effect
requests; this spike's small message needs no separately named bound theorem.
The pure theorem makes no addressability claim. Act 4 separately requires a
`ReadableBytes requested` representation and derives each call's `ReadLoan`.
For this spike that representation is synthesized from the assembly's reference
to logical `message`; runtime buffers would supply their own representation and
lifetime evidence. A raw count greater than the current chunk is outside the
provider's `Allowed` relation. The physical program nevertheless checks it
before pointer arithmetic because this particular assembly author selected a
containment trap. The fundamental theorem classifies the response itself as the
first environment violation and makes no claim after that boundary. A second
verified implementation may omit the check; it has the same theorem for every
conforming execution and a deliberately weaker post-violation containment
policy.

The check is typeable only because the Win32 profile distinguishes
`.excessWriteCount` from arbitrary provider failure and supplies a
`ViolationReturnEnvelope`. It proves an ordinary ABI return, an initialized
in-bounds `bytesWritten` slot, `WriteFile`'s exact nonzero TRUE result, a nonzero
slot value strictly greater than the exact request, returned call loans, and
intact frame authority; only `bytesWritten ≤ requested` failed. It entails every
literal path condition through `test eax`; failure branch; slot load; zero test;
`cmp`; and `ja`. The comparison and trap tail consume
exactly that affine envelope for this pending call ID, pre/post world, boundary
step, and read/write loan IDs. It cannot be replayed at another loop iteration.
A memory overwrite, bad stack return, or control violation
has no continuation contract and receives only the maximal pre-violation prefix.

The direct assembly proof does not simulate the provider's `win32WriteAll`
program term. That term and its loop theorems are a reusable realization proof
for generated clients. `helloSource` instead satisfies the same extensional
platform event contract directly: permitted `WriteFile` histories project to
the requested byte-prefix law and terminal outcome.

`ExitProcess` has no conforming normal return. It may be pending or reach the
terminal process state bearing the requested code. The platform profile names
process-owned obligations adopted there. External obligations are not adopted;
this program has none.

## 4. Typed CFG and memory shape

The apparent write loop directly realizes the relational console program.
`write_head` is typed by the specialization:

```lean
Console.WriteStdoutInvariant message policy helloVerified.driver
```

`DirectWriteInvariant` is not a second semantics. It is the zero-boilerplate
specialization of `ProcessLoopInvariant` for the canonical
`SequentialAdapter` plan; diagnostics can expand it to the root/API-child
network and escrow ledger.

The call edge creates one API occurrence; pending retains that occurrence and
its loans; a conforming return supplies one dependent result; the back edge
re-establishes the committed/remaining relation; and an exit block realizes the
terminal demand. Thus the loop interior proof is ordinary relational I/O plus
physical representation inside that degenerate network without changing this
authored contract. The literal instructions remain the evidence for each transition.

An assembly operand such as `[rip + message]` elaborates the logical constant
into one private read-only `StaticObject`, its `RepresentsStatic` theorem, and a
`ReadableBytes` view. These generated values remain inspectable in diagnostics;
the author does not restate them. The static object, not logical `message`, owns
the symbolic address and image provenance. Erasure retains that symbol and
`pe_link` derives `.rdata` from it, preventing an unconnected second copy.
The standard machine-boundary theorem consumes the generated readable view to turn each
logical `WriteFileEffectRequest` slice into a `WriteFileCall` with a fresh,
properly scoped read loan. This is where physical applicability and memory
safety enter; they are not smuggled into the pure chunk scheduler.

The loader/ABI profile supplies only the entry facts used here:
`RSP % 16 = 8`, enough writable stack below `RSP`, valid thread/process context,
and the initial obligation ledger. It does not borrow an ordinary caller's
return-address premise. A dedicated loader theorem connects every loaded entry
state to this contract.

The authored assembly chooses nonvolatile registers for loop state. Its prologue
pushes `r12`, `r13`, and `r14`, then reserves 48 bytes. This produces 16-byte
call-site alignment and the following verifier-derived interpretation. In the
first-class assembly route the author controls literal prologue instructions and
offsets; the frame verifier checks their geometry and derives unwind operations.
Generated-code and macro routes may instead request symbolic slots.

| Offset | Size | Meaning |
|---:|---:|---|
| `+0` | 32 | Win64 caller shadow space |
| `+32` | 8 | fifth argument: null `OVERLAPPED*` |
| `+40` | 4 | initialized `DWORD bytesWritten` |
| `+44` | 4 | padding, never read |
| `+48` | 8 | saved `r14` |
| `+56` | 8 | saved `r13` |
| `+64` | 8 | saved `r12` |

Stack provenance is tied to the loaded entry frame. Every slot is shaped
and initialized before read. There is no normal return: terminal `ExitProcess`
uses the profile's explicit disposition for the process stack allocation.

The generated full control/event graph is derived from `helloSource`; it is not
a maintained second source. Source labels are shown directly, while call
frontiers and continuations receive generated scoped names:

```text
entry
  GetStdHandle -> pending | environmentViolation | entry.afterGetStdHandle
  entry.afterGetStdHandle -> write_head | exit_unavailable

write_head
  -> exit_success | WriteFile
WriteFile
  -> pending
  -> conformingReturn(write_head.afterWriteFile)
  -> environmentViolation [fundamental execution ends]
  -> returnedViolation(.excessWriteCount, affine envelope,
                       containment.afterWriteFile)
write_head.afterWriteFile
  -> exit_write_failed | exit_no_progress | write_head
containment.afterWriteFile
  -> containment.returnTrue [test eax]
  -> containment.countLoaded [mov eax, [bytesWritten]]
  -> containment.countNonzero [test eax]
  -> containment.countCompared [cmp eax, requested]
  -> provider_violation [ja; same physical PCs, separate containment theorem]

exit_success | exit_unavailable | exit_write_failed | exit_no_progress -> exit
exit
  ExitProcess -> pending | terminal | environmentViolation
  returnedViolation(.terminalUnexpectedReturn, affine envelope,
                    exit.unexpectedReturn)
  exit.unexpectedReturn -> fault(ud2) [separate containment theorem]
provider_violation -> fault(ud2)
```

Fault and interruption exits declared by each instruction/API facet are also
retained in the generated `ExitContracts`, even when they do not add a named
source label. A smaller diagram may be generated as a conforming semantic
projection, but this complete graph is authoritative for erasure and artifact
inclusion. The fundamental graph has no post-violation continuation.
`returnedViolation` is a physical containment overlay beginning at the same
return PC with an affine narrow envelope; generic memory, ABI, and control
violations have no overlay edge. A generated graph regression compares source
labels, branch topology, and every normal/pending/terminal/fault/violation exit
to `helloSource`.

A basic block is the primary local proof unit:

```lean
TypedBlock profile (entry : StateContract) (exits : ExitContracts)
```

Symbolic verification starts from `entry` and proves locally that every terminal
instruction establishes one named normal, call, fault, pending, or terminal
exit. A direct jump carries a proof that its source exit entails the target
block's entry. A call proves the callee entry at the call site and imports its
normal/fault/pending exits into the continuation. A loop back edge is an ordinary
checked jump to the invariant-bearing entry plus a separate measure decrease or
frontier proof. Contracts include registers, flags, memory shape, loans, ghost
state, and obligations. Whole-CFG closure then checks labels, all incoming edges,
and indirect-target sets; it does not re-prove block interiors.

The application selects registers and identifies the consumed slice inline; a
CFG library combinator owns the routine partition and bounds facts. The source
header in section 5 elaborates to this inspectable generated contract:

```lean
WriteAllLoopInvariant
    (object := ``message)
    (handle := r12)
    (pointer := r13)
    (remaining := r14d)
```

`WriteAllLoopInvariant` composes `SliceConsumer` with the direct relational
write state, the exact API occurrence, and the provider result law. It
existentially tracks `committed ++ remaining = message`, proves
the accumulated console observation is exactly `committed`, derives pointer
offset/readability and partition preservation, and connects the pending request
to precisely the remaining slice. Its positive-count transition updates the
API occurrence, pointer, remaining register, observation projection,
and canonical length decrease together. The author selects the logical object
and register mapping; no duplicate measure annotation or event-plumbing lemma is
required. A custom ranking or protocol remains an explicit goal.

The cached block theorem is generalized before storage:

```lean
writeAllBlock_correct
  (bytes : ByteArray) (object : StaticObject bytes)
  (representation : RepresentsStatic object bytes) :
  ImplementsBlock (WriteAllBoundary bytes object) writeAllBlock
```

`message` supplies only the thin `StaticObject`/representation instantiation.
Changing same-length content therefore changes static data and that
instantiation, not the parametric loop certificate or its semantic boundary
hash.

The frame solver carries `r12` only after combining register preservation with
the provider capability-stability theorem described below. The verifier also
conjoins the standard Win64 stack, saved-register, call-frontier, and obligation
invariants derived from the prologue and selected API contracts.

At `WriteFile`, the call contract receives a shared read loan for precisely the
remaining constant slice and a unique write loan for `bytesWritten`. The fifth
argument occupies `rsp+32`. All volatile registers are forgotten on return.
The response closes both call loans before local memory is reused.

The following is the inspectable state generated by the standard ABI call rule,
not a `helloSource` declaration. An indefinitely pending call has a
different frontier contract. It does not
extend the local invariant with contradictory ownership: lending the unique
`bytesWritten` slot changes the phase-indexed frame authority.

```lean
structure PendingWriteInvariant where
  data           : SliceConsumerState ``message r13 r14d
  residualFrame  : FrameAuthority (.lent bytesWrittenSlot writeLoanId) rsp
  readLoan       : LiveLoan readLoanId environment remainingMessageSlice
  writeLoan      : LiveLoan writeLoanId environment bytesWrittenSlot
  callCompletion : Obligation callId environment
```

A conforming response consumes `PendingWriteInvariant` and restores the loop
invariant with its dependent post-state. An infinite pending execution retains
these loans and obligation rather than pretending they were closed.
The reusable call-boundary theorem proves disjointness of `residualFrame` and
the lent slot and reconstructs `FrameAuthority.local` only after consuming the
same loan identities.

The same generic rule instantiates a reachable `ExitProcess` pending frontier:

```lean
structure PendingExitInvariant where
  control        : ControlAuthority environment exitCallId
  processRoot    : ProcessRootAuthority (.pendingExit exitCallId)
  ledger         : LiveLedgerBeforeTerminalDisposition
  stagedAdoption : MayAdoptAtTerminal processOwnedObligations
  completion     : Obligation exitCallId environment
```

Continued pending preserves this state. The terminal transition consumes it and
applies the result-indexed terminal disposition exactly once. Staging is not
adoption: non-process/external obligations must already be discharged, and no
resource is considered abandoned while the call remains pending. A physical
normal return is an environment violation, not a third conforming continuation.

The only cyclic SCC is the write back edge. It exists only on permitted positive
completion and strictly decreases `remaining`. Pending occurs at the call
frontier, not as an internal self-loop.

The assembly author controls the literal call slots and saved-register sequence.
The verifier proves alignment, non-overlap, initialization, shadow space, call
loans, pending states, return reconstruction, clobbers, and unwind derivation
from those instructions and selected contracts. It exposes a goal when any such
fact fails, but does not ask the author to restate its internal loan bookkeeping.
The author still supplies novel partition/state relations, the loop measure,
terminal outcome binding, and any nonstandard obligation policy.

## 5. Ghost operations, raw x86, and erasure

The last verified CFG contains existentially packaged instructions and ghost
operations such as `openFrame`, `initSlot`, `borrowReadSlice`, `closeCallLoan`,
`assertWritePartition`, `decrease remaining`, and `terminalDisposition`.

The listing below is the review rendering of the first-class `helloSource`
selected in section 1, not a backend-only diagnostic. The `asm_source`
surface accepts arbitrary authored instruction sequences and nested CFGs. An
author may mix generated and custom implementations at requirement or block
boundaries, or replace the entire machine realization. Each insertion is typed
by the surrounding entry/exit contract and must close all applicable semantic,
memory, ABI, fault, interrupt, progress, and obligation goals. Proven macros can
package common sequences without making them semantically atomic.

`verify_asm` should prove most assembly against low-level contracts
automatically. It symbolically composes instruction relations into weakest
preconditions/strongest postconditions, applies proved API summaries, and uses
kernel-checked arithmetic, bitvector, and memory solvers. It quantifies over
every state satisfying the entry contract. Straight-line code should normally
need no intermediate assertions; loops need an invariant plus a measure or
frontier law; genuinely novel code may expose additional local lemmas.

The tactic is a checked certificate consumer and deterministic goal dispatcher,
not an invariant-discovery oracle. Its report identifies which fragment-family
theorems were instantiated, which CFG contracts were composed, and every
residual goal. It cannot invent a loop invariant, algorithmic correspondence,
failure policy, memory representation, or missing provider case and then hide
that choice behind success.

Low-level contracts are extensional specifications. If two assembly CFGs both
prove equivalence to the same deterministic contract, their equivalence follows
by composition. For relational or nondeterministic contracts, the library
derives the appropriately directed mutual refinement when both directions are
proved. This is the normal optimization/replacement route, without a bespoke
instruction-by-instruction bisimulation.

Custom assembly is therefore on the verified route. `Grass.Unsafe.emitRaw` is a
separate fuzzing/experimentation route and cannot be used to construct
`VerifiedProgram`.

Assembly may also appear earlier in authored code behind an explicit nominal ISA
capability. Doing so narrows the program's implementation requirements but need
not contaminate its functional specification: a portable root `SpecProcess` can be
refined by an intentionally x86-specific program. Weaving rejects incompatible
ISA/provider demands rather than silently choosing one.

Local proof reuse is first class. The author writes one `asm_source` command with named
blocks; its elaborator resolves labels and mechanically assembles certificates
indexed only by their own code and boundary contracts. The following is the
inspectable expansion, not a hand-written `SubCFG.plug` list:

```lean
entryImpl     : ImplementsBlock commonX86Win64 entryContract entryExits entryBody
writeHeadImpl : ImplementsBlock commonX86Win64 writeHeadContract writeHeadExits writeHeadBody
exitImpls     : ImplementsSubCFG commonX86Win64 exitInterface exitBodies

def helloCertificate : ImplementsSubCFG commonX86Win64 helloInterface helloGraph :=
  SubCFG.plug [entryImpl, writeHeadImpl, exitImpls]
```

`SubCFG.plug` proves label uniqueness, edge compatibility, and disjoint internal
ownership. `ImplementsBlock.conseq` transports a certificate only when each new
entry entails the old entry and each old exit entails its corresponding new
exit, separately for normal, call, pending, fault, interruption, and terminal
exits. Resource reuse uses a separate `frame` theorem requiring disjoint
ownership, noninterference, and preserved obligations. Progress measures and
frontier laws do not transport without their own refinement proof. Adding an
unrelated block or woven component therefore does not change `writeHeadImpl`'s
type or re-run its proof. The internally generated `AssemblyImplements` witness
in section 1 is the checked finite map of these local certificates, not a
monolithic proof.

Terminal blocks are explicitly bound to portable outcomes by inline source
annotations; intent is not guessed from an exit-code literal. The Win32
terminal-provider rule checks locally that `ECX` equals `policy.status outcome`,
the `ExitProcess` call satisfies its ABI, and outcome-indexed obligation
disposition holds. The status map, semantic tag, and instruction are three
different claims—not redundant copies—and disagreement produces a local goal.
A bare-metal provider gives the same tagged outcome a different physical
terminal contract.

The following is the single authored `asm_source`, not a rendering assembled from
separate block-proof definitions. Labels split basic blocks automatically;
`@invariant`, `@measure`, and `@terminal` are proof-bearing source annotations.
The registers and instructions remain literal choices; routine ABI storage uses
the named frame layout so the exemplar does not normalize displacement
arithmetic. The expanded review view still contains the exact numeric offsets:

```text
def helloSource :=
withStack (transferred : UInt32 := 0)
withCallFrame WriteFile asm_source for plan {

entry:
    push r12
    push r13
    push r14
    mov  ecx, STD_OUTPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   exit_unavailable
    cmp  rax, INVALID_HANDLE_VALUE
    je   exit_unavailable
    mov  r12, rax                         ; borrowed stdout handle
    lea  r13, [rip + message]
    mov  r14d, sizeof(message)            ; derived from the logical constant

write_head: @placement [handle := r12, cursor := r13, remaining := r14d]
            @invariant write_all_loop(message)
    test r14d, r14d
    je   exit_success
    arg WriteFile.overlapped, 0
    mov  transferred, 0
    mov  rcx, r12
    mov  rdx, r13
    mov  r8d, r14d
    lea  r9, transferred.addr
    call qword ptr [rip + __imp_WriteFile]
    test eax, eax
    jz   exit_write_failed
    mov  eax, transferred
    test eax, eax
    jz   exit_no_progress
    cmp  eax, r14d
    ja   provider_violation @violation_edge(.excessWriteCount)
    add  r13, rax
    sub  r14d, eax
    jmp  write_head

exit_success: @terminal(.success)
    xor  ecx, ecx
    jmp  exit
exit_unavailable: @terminal(.stdoutUnavailable)
    mov  ecx, 1
    jmp  exit
exit_write_failed: @terminal(.writeFailed)
    mov  ecx, 1
    jmp  exit
exit_no_progress: @terminal(.noProgress)
    mov  ecx, 1
    jmp  exit
exit:
    call qword ptr [rip + __imp_ExitProcess]
    ud2 @containment_tail(.terminalUnexpectedReturn)
provider_violation:
    ud2 @containment_tail(.excessWriteCount)
}
```

Containment is single-source: annotations type the literal authored edge and
tail but never generate or delete instructions. To assume the provider contract,
the author deliberately removes the comparison, branch, and corresponding trap;
editing metadata alone cannot change machine code. `exit_with $policy` is a
standard library idea only when invoked with an explicit outcome and a displayed
deterministic expansion; this spike uses literal status loads and jumps so every
emitted instruction is present.

`verify_assembly` verifies this source. `WriteAllLoopInvariant` composes the generic slice
consumer with the provider event projection: accumulated stdout is exactly the
committed prefix, the pending call requests the remaining slice, and a positive
count synthesizes both the residual state and canonical length decrease. A
custom ranking function or invariant remains an explicit authored goal. Erasure
removes contracts and ghost operations while retaining exactly these instruction
choices and connected symbol/import metadata.

Call nodes name the Win64
API contract; verification checks argument registers/stack slots at the call and
forgets the declared volatile clobbers on every return edge. Nonvolatile
`r12`/`r13`/`r14` survive by the callee contract. The stdout capability itself
is framed by `WriteFile`'s provider-specific footprint/stability theorem, which
preserves provider identity, validity/lifetime, non-close/non-transfer behavior,
disjoint resources, and obligations on every used exit. Register preservation
alone does not frame a handle.

Both `ud2` sites are unreachable in a conforming execution. An excessive write
count is not ordinary exit-policy failure `1`: it is the first provider violation and
branches only to the author-selected containment trap after full assurance has
ended. The verifier does not demand that branch; the no-check assembly variant
proves the same conforming low-level contract. Likewise, if `ExitProcess`
returns physically, assurance ended before the return and this implementation's
trap prevents fall-through into data.

The literal `@violation_edge(.excessWriteCount)` and
`@containment_tail(.excessWriteCount)` pair consumes the `WriteFile`
value-domain envelope above. `@containment_tail(.terminalUnexpectedReturn)`
consumes a terminal-provider envelope proving an otherwise intact ABI return.
Neither annotation claims a typed tail after arbitrary memory, ABI, or control
corruption.

The first common-x86 profile need contain only this listing's instructions.
Each instruction supplies applicability, complete steps, registers/flags,
memory events, faults, encoding/decoding, Intel and AMD anchors, and probes.

The important erasure direction is:

```lean
theorem hello_erasure :
  ErasurePreservesSemantics
    helloVerified.ghostProgram helloVerified.rawProgram :=
  helloVerified.erasureCorrectness
```

This owned relation covers coupled initial states and external choices, finite
and infinite behavior, divergence, terminal states, audit events, faults, and
observations. A derived `hello_erasure_violation_prefix` corollary matches only
the maximal prefix before a general environment violation; it is not a weaker
parallel erasure contract. Ghost steps cannot repair a physically invalid raw
sequence.

## 6. The emitted PE32+ image

`pe_link raw` derives rather than duplicates:

- AMD64 PE32+, Windows console subsystem, and the `entry` RVA;
- `.text` with final `R-X` permission;
- `.rdata` derived from the static elaboration of exactly logical `message`,
  final `R--`;
- `.idata` importing exact `KERNEL32.dll` name identities for `GetStdHandle`,
  `WriteFile`, and `ExitProcess`, each tied to the identical nominal provider
  operation/Win64 ABI used at its call site; the loader receives temporary IAT
  write authority and final IAT permission is `R--`;
- `.pdata` and `.xdata` for the one non-leaf function;
- no exports, TLS callbacks, writable program globals, or extra entry roots;
- `NX_COMPAT`, `DYNAMIC_BASE`, `HIGH_ENTROPY_VA`, and
  `LARGE_ADDRESS_AWARE`; `RELOCS_STRIPPED` is clear; plus standard alignments
  and canonical padding.

All program references are RIP-relative and all image metadata uses RVAs. This
image therefore has no base-dependent fixups. The PE profile must prove that its
canonical empty relocation-directory representation remains load-base invariant
and is valid with `DYNAMIC_BASE`; it cannot simply disable ASLR.

The unwind description is generated from the proved prologue, not typed as PE
bytes by the assembly author. Its **prologue-effect review form (execution
order, not serialized `UNWIND_CODE` order)** contains:

```text
UWOP_PUSH_NONVOL r12
UWOP_PUSH_NONVOL r13
UWOP_PUSH_NONVOL r14
UWOP_ALLOC_SMALL 48
```

The frame/unwind library computes code offsets, opcode information, prologue
size, slot count/padding, descending-code-offset serialized order, `.pdata`
range, and exact `.xdata` bytes from the encoded
instructions and proves that the record reverses their state changes. Changing
the prologue forces derived metadata to change without duplicating literals.

Serialization and connection remain distinct:

```lean
theorem pe_write_parse :
  PE.parse (PE.write helloVerified.linkedArtifact) =
    .ok helloVerified.linkedArtifact

theorem pe_parse_canonical bytes parsed :
  PE.parse bytes = .ok parsed -> PE.write parsed = PE.canonicalize bytes

theorem emission_exact :
  emitProgram helloVerified = PE.write helloVerified.linkedArtifact

theorem hello_artifact_connection :
    ArtifactRepresents
      helloVerified.rawProgram helloVerified.linkedArtifact :=
  helloVerified.artifactCorrectness

theorem loaded_execution_connected
    (context : AdmissibleExecutionContext helloVerified.realization)
    (base : AdmissibleLoadBase helloVerified.linkedArtifact)
    (imports : AdmissibleImportEnvironment
      helloVerified.realization helloVerified.linkedArtifact)
    (machine : MachineState)
    (load : WindowsLoader.Loads helloVerified.realization
      (emitProgram helloVerified) context base imports machine) :
    ∃ rawInitial,
      RawInitialState helloVerified.rawProgram rawInitial ∧
      LoadedRawInitialStatesRelated load rawInitial ∧
      ∀ choices trace,
        LoadedExecution machine choices trace ->
        ∃ rawChoices rawTrace,
          LoadedRawChoicesRelated load rawInitial choices rawChoices ∧
          RawExecution helloVerified.rawProgram rawInitial rawChoices rawTrace ∧
          LoadedRawTracesRelated trace rawTrace

theorem loaded_initial_valid
    (context : AdmissibleExecutionContext helloVerified.realization)
    (base : AdmissibleLoadBase helloVerified.linkedArtifact)
    (imports : AdmissibleImportEnvironment
      helloVerified.realization helloVerified.linkedArtifact)
    (machine : MachineState)
    (load : WindowsLoader.Loads helloVerified.realization
      (emitProgram helloVerified) context base imports machine) :
    ValidInitialState helloVerified.realization context
      helloVerified.linkedArtifact machine ∧
    SatisfiesEntryContract helloVerified.rawProgram.entry machine

theorem image_loadable
    (context : AdmissibleExecutionContext helloVerified.realization)
    (base : AdmissibleLoadBase helloVerified.linkedArtifact)
    (imports : AdmissibleImportEnvironment
      helloVerified.realization helloVerified.linkedArtifact) :
    ∃ machine,
      WindowsLoader.Loads helloVerified.realization
        (emitProgram helloVerified) context base imports machine ∧
      ValidInitialState helloVerified.realization context
        helloVerified.linkedArtifact machine ∧
      SatisfiesEntryContract helloVerified.rawProgram.entry machine

theorem emitted_excess_count_containment
    (context : AdmissibleExecutionContext helloVerified.realization)
    (base : AdmissibleLoadBase helloVerified.linkedArtifact)
    (imports : AdmissibleImportEnvironment
      helloVerified.realization helloVerified.linkedArtifact)
    (machine : MachineState)
    (load : WindowsLoader.Loads helloVerified.realization
      (emitProgram helloVerified) context base imports machine)
    (step : ReachableFirstViolation machine .excessWriteCount) :
    ∃ envelope tailState fault,
      ExactViolationEnvelopeFor step envelope ∧
      LoadedTailEntryRelated helloVerified.linkedArtifact
        provider_violation envelope tailState ∧
      ExecutesLiteralContainmentTail tailState fault ∧
      fault.instruction = .ud2 :=
  helloVerified.artifactContainment.excessWriteCount load step
```

The connection consumes the exact written bytes and covers parsing, mapping,
IAT resolution, temporary loader writes, final permissions, unwind metadata,
entry-state construction, and decoding. `SatisfiesEntryContract` supplies the
exact stack/context contract consumed by `entry`; it is not inferred from the
ordinary function-call ABI. Load-base and import domains have independent
inhabitants; the admissible context domain is independently inhabited too. Every
loader result is a valid initial state for the exact supplied context.
`hello_artifact_connection` is the owned semantic relation composed by
`endToEnd`; the expanded theorem preserves the exact loaded/raw initial-state
relation and namespaced external choices. An aggregate unindexed behavior-set
inclusion is only a derived corollary and cannot replace it.
`LoadedRawChoicesRelated` preserves and reflects response values, scheduler
choices, interrupts/faults, allocation/layout choices, import resolutions, and
consistency-witness namespaces for these exact initial states. If an
implementation derives `rawChoices` canonically, its function returns this
dependent subtype rather than an unproved choice stream.

`PE.parse` separately proves conformance for all accepted bytes: it validates
lengths, arithmetic, ranges, overlaps, directories, alignments, and references.
Writer round-trip is not parser correctness.

## 7. What `VerifiedProgram.close` must actually compose

The compact call in section 1 must expose these independent fields under
expansion and in diagnostics:

1. portable specification well-formedness and its functional, outcome/status,
   safety, progress, and liveness policy (generated routes additionally carry
   portable source satisfaction);
2. the exact direct relational program, its non-vacuous refinement to the
   precious specification, and the extensional driver boundary consumed by the
   assembly proof;
3. exact provider identity and coherent platform selection;
4. Win32 API/driver refinement for every permitted dependent result history;
5. typed-CFG edges, ABI, stack, memory shape, and SCC progress;
6. closure of every reachable requirement and required operation facet;
7. safety of every finite prefix of every conforming finite or infinite run;
8. exact loan and obligation creation, transfer, closure, and terminal disposal;
9. raw-to-ghost inclusion after erasure;
10. semantic encoder/decoder equivalence for every reachable instruction;
11. PE well-formedness, writer/reader laws, and exact raw-artifact connection;
12. nonempty response and initial-state domains; separately named independent
    inhabitants for admissible execution context, load base, and imports; plus
    loadability for every admissible triple;
13. a coherent inhabited concrete provider/scheduler strategy for each demanded
    conditional-liveness premise, an explicit abstract-strategy projection, and
    a refinement coupling their complete compatible-history sets with universal
    responsiveness and strategy adequacy of the exact projection;
14. terminal-status preservation, reflection, distinguishability, and resource
    fidelity over the demanded subset; and
15. selected containment coverage and its separate emitted-byte theorem; and
16. the composed loaded-bytes theorem.

For Spike 1 the result specializes to:

```lean
theorem spike1_emitted_sound
    (context : AdmissibleExecutionContext helloVerified.realization)
    (base : AdmissibleLoadBase helloVerified.linkedArtifact)
    (imports : AdmissibleImportEnvironment
      helloVerified.realization helloVerified.linkedArtifact) :
  (∃ machine,
      Loads helloVerified.realization (emitProgram helloVerified)
        context base imports machine) ∧
  ∀ machine,
    (load : Loads helloVerified.realization (emitProgram helloVerified)
      context base imports machine) ->
    ValidInitialState helloVerified.realization context
      helloVerified.linkedArtifact machine ∧
    SatisfiesEntryContract helloVerified.rawProgram.entry machine ∧
    ∀ trace,
      (exec : ModeledExecution machine trace) ->
      AssuranceResult helloVerified context base imports machine load trace exec
```

A conforming result contains a matching portable execution, coinductive
trace/observation refinement, universal prefix safety, applicable progress,
ABI correctness, and matching obligation behavior. A finite specified terminal
result additionally contains an accepted `HelloObservation`; an infinite pending
trace does not fabricate one. Universal conditional liveness rules such a trace
out only when its responsive-strategy premise holds. An environment-violation
result identifies the first bad event and proves only the matched safe prefix
immediately before it. A separately named containment theorem may additionally
consume a narrow `ViolationReturnEnvelope`; that is not payload smuggled into
the fundamental result.

No theorem field may contain `sorry`, `admit`, `sorryAx`, project/dependency
axioms, unsafe declarations, or `native_decide`. `bv_decide` is acceptable only
for universal finite bitvector claims. Execution and probes never fill proofs.

## 8. Where proof automation should stop

Libraries should routinely solve pure `Vec` partitions and prefixes, positive
length decrease, standard Win64 frame arithmetic and clobbers, typed stack-slot
access, direct branches, instruction-contract composition, RIP-relative layout,
derived imports/unwind ranges, and format-component composition.

They must leave a visible goal for any missing external result case, dependent
output state, committed failure prefix, provider identity, loop invariant,
memory loan, strict back-edge decrease, fault/interrupt behavior, terminal
obligation disposition, exact-byte connection, or non-vacuity witness.

Proof economy must come from small orthogonal theorems, not a single opaque
`Correct` proposition.

The spike does not name lemmas that merely restate reducible facts such as the
literal bytes or length of `message`. Consumers normalize or derive those facts
where needed, so changing the message does not create a parallel theorem API.

## 9. Change propagation is part of proof economy

The transparent declarations `message`, `policy`, and `spec` jointly constitute
the one precious semantic source for this program. `plan` and `helloSource` are
reviewed but replaceable construction
inputs: the spec does not determine them, and changing either is an intentional
implementation change. Certificates, generated CFG nodes, loans, symbols,
layouts, encodings, and proof terms are reproducible dependent witnesses. Their
dependencies must be fine-grained enough that an edit rebuilds only its semantic
cone, and their identities must not leak upward into the specification or
unrelated certificates.

| Change | Must be reconsidered or rebuilt | Must remain reusable |
| --- | --- | --- |
| same-length message content | static bytes/content identity, affected artifact bytes and exact connection | source instructions, parametric slice/loop/block certificates and ABI/provider laws |
| message length or representation | static object shape, slice instantiation, derived length immediate, affected layout/encodings/artifact | outcome/liveness policy, provider laws, generic write-loop theorem |
| status remap with unchanged outcomes | terminal bindings, demanded-status laws, authored literal immediates if used, affected bytes, outer `VerifiedProgram spec` composition | console byte-prefix law, write loop, memory/ABI proofs before terminal choice |
| collapse/reclassify audit causes without control change | audit-to-product projection and terminal binding if affected | precious binary outcome, physical write loop, provider effect law, memory/ABI certificates |
| control change such as retry versus terminate | affected direct relational transition, progress law, CFG exits/back edges, downstream composition | provider result domain and unrelated blocks |
| add/remove/change an API result constructor | direct/effect exhaustiveness, provider refinement, affected CFG exits and downstream composition | unrelated pure data/ISA/provider laws whose interfaces remain unchanged |
| liveness policy | abstract premise, adequate concrete strategy bridge, SCC/frontier composition, outer `VerifiedProgram spec` composition | functional byte theorem, unconditional prefix safety, encodings and layout |
| synthesized sequential plan replaced by an explicit plan with the same driver boundary | plan refinement and driver composition | precious spec and source blocks whose boundary contracts are unchanged |
| selected provider/plan | affected effect refinement, context requirements, calls/imports, ABI and terminal protocol, downstream artifact | precious spec and provider-independent logical laws |
| one assembly block or optimization | that block certificate, incident edges, erasure/encoding/layout and downstream byte connection | spec, provider realization, untouched local block certificates |
| ABI/instruction model correction | certificates using the changed rule and their downstream connection | unrelated specifications, providers, and blocks proved through unaffected interfaces |

Every precious `spec` index change re-elaborates and rechecks the outer
`VerifiedProgram spec` composition. Internally unaffected certificates may be
reused by unchanged content/boundary identity. An authored status immediate is a
deliberate tuned-source edit; generated encoding/layout/PE bytes are regenerated,
not described as author edits.

Each row owns a machine-readable `LocalityContract` mutation fixture with
required actions and a negative required-reuse set. The dependency system emits
an `InvalidationPlan` before rebuilding and validates it against the separate
`BuildExecutionReport` plus periodic clean differential reconstruction.
Generated declarations use content/dependency indices rather than whole-program
identity wherever sound. Local block certificates depend on boundary contracts,
not on a monolithic CFG value; artifact stages depend on exact prior outputs, so
they are expected to rebuild cheaply. If changing the message forces the author
to edit a length theorem, or changing one block reopens every block proof, the
Spike 1 interfaces have failed even when the final theorem still compiles.

A golden author-surface fixture contains exactly `message`, `policy`, `spec`,
`plan`, the displayed `helloSource`, and the one `verify_assembly` closure. The
unique standard sequential realizer is selected, normalized, and recorded by
the library; it is not an application declaration. The fixture supplies no application
lemmas for generic slice/event relations, ABI frames, loans, handle stability,
unwind, status mapping, or arithmetic. CI maintains a short allowlist of truly
custom residual goals; new ceremony or an unrelated per-block recheck is a
regression. Explicitly adopted generated source counts as reviewed input, while
non-adopted regenerable output remains a derived witness.

Specification evolution can intentionally change the contract and expose real
new goals: adding an observed failure, weakening liveness, or changing bytes is
not papered over by compatibility coercions. Proof economy means those goals are
local, intelligible, and mostly discharged by reusable laws—not that semantic
changes appear free.

## 10. Adversarial review and later acceptance

Before implementation, reviewers should try to use this shape to emit the wrong
message; prove one friendly API run; omit short, failed, zero, or pending writes;
read an uninitialized count; overrun after a bad count; call with a bad stack;
lose an obligation; reach `ud2` conformingly; switch providers; lie in unwind
metadata; emit bytes unrelated to `raw`; or prove correctness over an empty
loader/response domain. Any success is an interface failure.

After the libraries exist, Spike 1 additionally requires transitive axiom
audits; writer/parser tests; instruction model and decoder fuzzing; API boundary
probes; PE import, ASLR, permission, entry, and unwind inspection; and execution
of the exact artifact on reviewed Intel and AMD Windows hosts. These challenge
the explicit CPU/API/loader correspondence ledger and never replace proof.

## 11. Required sources

Before semantics are implemented, declaration-level citation records must pin
document revision and section for every used Intel and AMD instruction; the
Microsoft x64 ABI, stack, parameters, and unwind format; PE32+ headers, imports,
RVA/ASLR rules, sections, and loader behavior; `GetStdHandle`, `WriteFile`, and
`ExitProcess` including dependent memory and blocking behavior; and Windows
process entry/termination assumptions. [REFERENCES.md](REFERENCES.md) contains
discovery roots, not yet sufficient instruction-level anchors.

If a vendor source does not promise a convenient fact, the model admits the
broader behavior or the plan names and cites a stronger precondition. A probe
cannot silently strengthen the proof contract.


## Exact authored source snapshot

This section is the author-maintained Lean surface defined by
[SPIKE_AUTHORING.md](SPIKE_AUTHORING.md). Earlier code blocks in this document
are generated expansions, library interface sketches, or proof sketches unless
they are explicitly labeled authored source. Reviewers must compare this
snapshot with `Spikes/1_Hello_World/` exactly.

### `Program.lean`

```lean
import Grass.Emit
import Grass.Artifact.PE32Plus
import Grass.Assembly.X86
import Grass.Platform.Win10.X64
import Grass.Process.Sequential
import Spikes.«1_Hello_World».Spec

namespace Grass.Spikes.HelloWorld

def stdoutProtocol : AbstractSpecificationProcessNetwork resources :=
  Console.linearStdoutProtocol resources message HelloOutcome

def stdoutPresentation : ProcessPresentation spec where
  network := stdoutProtocol
  denotationExact := Console.linearStdoutProtocolDenotesWriteLineContract
  requirementsExact := Console.linearStdoutProtocolRequirementsExact

def processRealization : ProcessRealization spec :=
  ProcessRealization.standard
    (Grass.Std.Realizers.lookupExact stdoutPresentation)

def policy : TargetOutcomeProjection HelloOutcome UInt32 :=
  .successOrFailure
    (success := HelloOutcome.success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ConsoleText
    (newline := .crlf)
    (encoding := .utf8)
    (outcome := policy)

def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64SynchronousStdoutOnly projection

def helloSource : MachineSource plan :=
  withStack (transferred : UInt32 := 0)
  withCallFrame WriteFile asm_source {
entry:
  push r12
  push r13
  push r14
  mov ecx, STD_OUTPUT_HANDLE
  call qword ptr [rip + __imp_GetStdHandle]
  test rax, rax
  jz exit_unavailable
  cmp rax, INVALID_HANDLE_VALUE
  je exit_unavailable
  mov r12, rax
  lea r13, [rip + message]
  mov r14d, sizeof(message)

write_head: @placement [handle := r12, cursor := r13, remaining := r14d]
            @invariant write_all_loop(message)
  test r14d, r14d
  je exit_success
  arg WriteFile.overlapped, 0
  mov transferred, 0
  mov rcx, r12
  mov rdx, r13
  mov r8d, r14d
  lea r9, transferred.addr
  call qword ptr [rip + __imp_WriteFile]
  test eax, eax
  jz exit_write_failed
  mov eax, transferred
  test eax, eax
  jz exit_no_progress
  cmp eax, r14d
  ja provider_violation @violation_edge(.excessWriteCount)
  add r13, rax
  sub r14d, eax
  jmp write_head

exit_success: @terminal(.success)
  xor ecx, ecx
  jmp exit

exit_unavailable: @terminal(.stdoutUnavailable)
  mov ecx, 1
  jmp exit

exit_write_failed: @terminal(.writeFailed)
  mov ecx, 1
  jmp exit

exit_no_progress: @terminal(.noProgress)
  mov ecx, 1
  jmp exit

exit:
  call qword ptr [rip + __imp_ExitProcess]
  ud2 @containment_tail(.terminalUnexpectedReturn)

provider_violation:
  ud2 @containment_tail(.excessWriteCount)
}

theorem sourceImplementsDriver :
    AssemblyImplements processRealization plan helloSource := by
  verify_asm

def helloVerified : VerifiedProgram spec := by
  verify_assembly plan with helloSource

def bytes : ByteArray := emitProgram helloVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  helloVerified.sound

def artifact : PE32Plus := helloVerified.linkedArtifact

theorem writerRoundTrip : PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem textDecodesExactly :
    LoadedTextDecodesTo artifact helloVerified.rawProgram :=
  helloVerified.artifactCorrectness.loadedTextDecodes

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

end Grass.Spikes.HelloWorld
```

### `Spec.lean`

```lean
import Grass.Spec.Console
import Grass.Spec.Resource

namespace Grass.Spikes.HelloWorld

def resources : ConsoleResourceModel :=
  ConsoleResourceModel.singleLine

def message : TextLine := "Hello, World!"

inductive HelloOutcome
  | success
  | failure

def helloContract {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : BehaviorContract resources :=
  Console.writeLineContract resources message HelloOutcome

def helloSpec {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.ofRelational (helloContract resources)
    |>.withLiveness (.terminatesUnder [.environmentResponsive])

theorem helloSpecCorrect {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : MeetsAllSpecificationTheorems (helloSpec resources) :=
  Console.writeLineContractCorrect resources message HelloOutcome

def spec : SpecProcess resources := helloSpec resources

end Grass.Spikes.HelloWorld
```
