# Shared proof frameworks and declaration fronts

Architecture proposal, 2026-09-09. This document proposes how to remove recurring
proof obligations from new consumers. It does not claim that the migrations or
DSLs below are implemented. Spikes owns implementation sequencing; architecture
owns shared boundaries and exceptions. Existing assembly and semantic structures
remain authoritative.

## Design decision

Use a small collection of checked constructors with general laws. Put optional
instruction and API declaration syntax over those constructors after two real
consumers demonstrate the boundary. A declaration supplies distinct semantics;
it must not generate another copy of the common proof script. New consumers
should instantiate proved construction, not reconstruct why it is sound.

The architecture has three layers:

1. Existing semantic receipts and execution relations define the guarantee.
2. Shared checked producers retain exact inputs, intermediate states and success
   equations; general laws discharge recurring construction obligations.
3. Domain declarations select those producers and supply domain-specific checks
   and semantic connections. Syntax elaborates to ordinary kernel-checked terms.

There is no universal instruction/API language in this proposal. Their shared
need is reusable verified construction, not identical domain vocabulary.

## Evidence and present status

Source inspection used main checkout revision `c8eb4243`, together with the
architecture delta `3887deed`. The bounded duplication inventory is pinned to
`2370d929`; it is a lower bound, not a complete stack census.

* `CallEntry.CallPolicy.ofFactory` and `reachedCall?` already centralize fixed
  policy binding and carrier repacking from the actual CALL.
* `ReturnHome.StackPlanFactory.deriveLoaded?` computes return/home coordinates,
  initialized continuation and separation from that CALL. It offers a real
  shared producer, rather than only a common record shape.
* `ReadValue32` and `ReadValue64` still repeat observed-byte extraction, length,
  backing, initialization and endian arguments with widths four and eight.
* `GetStdHandle.EntryHandoff` and `WriteFile.EntryHandoff` still repeat control,
  context, cleanliness and protocol checks, output construction, and storage
  preservation. Their requests, loan obligations and typed views differ.
* `3887deed` makes all three raw API entry adapters use one actual CALL/handoff
  log law. This prevents another proof family; it does not close all API-entry
  duplication. Independent review, full 577-job build and fresh declaration
  audit passed for that delta.

Windows reports dual ReturnHome adoption under validation; library reports
reviewed Push/Call access-failure adoption in `c13468d1` with broad checks still
running. Those reports are not treated here as completed integration evidence.

Follow-up inspection at main `71cf80bf` verifies that RunFactory owns the
access-failure mapping and Push/Call now invoke it. This establishes those two
consumers' adoption, not migration of the other three factory consumers.
Windows subsequently published dual ReturnHome adoption in `2e391f29`; its
reported full build and review passed, with fresh trust/source checks pending.

## API construction framework

For the first Windows implementation, extract a protocol-level checked handoff
producer beneath API-specific modules. The following carrier/control checks are
Windows adapter requirements, not requirements of every target's descriptor.
Its inputs are the exact reached `ExecutionState.State ApiRequest`, concrete
`ApiRequest`, ordered `List LoanRequest`, and agent. Its result is indexed by all
four inputs and retains the actual projection and `CallProtocol.handoff?`
equations. It checks caller control, both registered contexts and cleanliness
once. It computes the fresh CallId, exact protocol result, pending control and
whole heterogeneous record once.

Prove output projection, recorded pending lookup, unrelated pending preservation,
storage preservation, boundary append and freshness once for that receipt.
Keep this module independent of WriteFile. API wrappers may expose typed record
views, but must derive those views from the canonical heterogeneous record.
They may not rebuild a second handoff checker.

For WriteFile, use the existing `selectPending` and
`embedPending_of_selectPending_eq_some` bridge to obtain the typed record with
the same caller, agent, request and minted IDs. Recomputing a plausible typed
record from mint inputs would miss this reuse boundary.

The proposed API declaration interface supplies:

| Input | Obligation retained by the API author |
|---|---|
| Request decoder from the reached machine | Actual ABI arguments equal the semantic request |
| Checked loan-plan producer | API-specific sizes, separation, protection and loan order |
| Typed target binding | Actual selected import, syscall or component binding and nominal operation agreement |
| Entry/continuation realization and completion classification | Target-specific checked continuation; Win64 returning calls use ReturnHome, while nonreturning declarations acquire no fabricated return frame |
| Runtime payload constructor | Payload-specific data is derived from the same entry receipt and plan |
| Provider semantic adapter | Service, result, failure and temporal obligations specific to this API |

Trial consumers are GetStdHandle and WriteFile: one has only the return/home
pair, the other has semantic buffer/count loans plus a fifth argument and
partial-output behavior. Preserve WriteFile's current ordered batch exactly.
ExitProcess is the third-consumer challenge: it must reuse checked handoff and
log construction without proving returning-call obligations or inventing a
return capability. Full native transfer adequacy remains a separate obligation.

The declaration front should initially be a Lean structure or ordinary function
application. Add syntax only if it removes repeated authoring beyond that API.
No author-supplied arbitrary success proposition or replaceable safety relation
may stand in for the computed handoff or fixed platform semantics.

### Attribute-shaped API declarations

Craig suggests attribute annotations on API calls as a promising DSL shape.
Use attributes on the reusable API declaration to register its import identity,
request decoder, checked ABI/loan-plan producer, return mode and semantic adapter.
The attribute elaborator resolves those names into an ordinary typed declaration
consumed by the shared constructors above. Registration is not evidence that any
particular call satisfies the ABI or that a native provider implements it.

An illustrative shape, not implemented Lean syntax, is:

```text
@[grass_api
  import := ("KERNEL32.dll", "WriteFile")
  request := WriteFile.decodeRequest?
  abi := WriteFile.checkedPlan?
  returns := win64
  semantics := WriteFile.contract]
def writeFileApi := ...
```

Names in this sketch describe roles, not existing declarations. Prefer one
attribute referencing a typed descriptor if a long attribute merely duplicates
its fields. Keep provider semantics independently readable and reviewable.

At a call site, an annotation may select this declaration or provide operands
and specialization inputs. The checker still derives the request and plan from
the actual call state, binds the actual dispatch target, and checks the concrete
loan batch. Do not repeat the API contract at each call site, infer a contract
from a convenient result, or let annotations discharge safety by assertion.
If multiple declarations match an import, require explicit disambiguation rather
than registration-order selection. Unannotated custom assembly remains usable
through the same explicit checked constructors.

Evaluate this front with GetStdHandle and WriteFile, then ExitProcess as above.
Success means authoring API-specific facts once and removing the repeated
handoff machinery; a shorter spelling for unchanged duplicate proofs fails.

### Authoring contract and trial worksheet

The API descriptor is indexed by the existing API constructor. Its decoder
returns a request of that constructor together with ABI evidence tied to the
actual reached machine. Its plan producer returns a plan indexed by that same
machine and request. Merely naming arbitrary functions in an attribute is not
enough: their dependent result types and retained success equations enforce the
connections. The fixed profile chooses the provider model; an attribute cannot
replace that model with a contract selected by the caller.

Since the existing `ApiRequest` is a sum, the decoder's API index can be retained
as `{ request : ApiRequest // ApiDispatch.requestApi request = api }`, with the
ABI evidence indexed by that exact request and reached machine. The notation
describes the required connection; it does not introduce a second request model.

| Trial | Authored once | Derived by shared machinery | Still owed outside the declaration |
|---|---|---|---|
| GetStdHandle | RCX low-DWORD selector, API identity and result meaning | Actual CALL binding, common return/home plan, checked handoff, fresh occurrence, record and logs | Actual result/return connection and provider adequacy |
| WriteFile | Handle/buffer/count/fifth-argument ABI checks, semantic loans, partial-output model | Same CALL and ReturnHome construction, whole-batch handoff and general preservation laws | API-specific separation/protection, service/output correspondence, actual return connection |
| ExitProcess | RCX low-DWORD status and nonreturning classification | Same checked handoff with the selected slice's empty loan batch, occurrence and logs | Terminal observation and native teardown behavior; entry success proves neither |

For all three, neither caller nor attribute author supplies a free CallId,
before/after log, continuation address, pending record or shared preservation
proof. Those come from actual checked construction. Distinct API semantics
remain readable declarations and laws; the common receipt packages their
application without duplicating protocol mechanics.

The implementation review must compare the authoring surface with these exact
existing names: `entryHandoff?`, `EntryHandoff.after`, `recorded`,
`storage_unchanged`, and the per-API CALL/log adapters. A new descriptor that
leaves each API reimplementing those mechanics has not delivered this design.
Typed aliases and semantic projections may remain when they contain no second
implementation of the guarantee.

Current dispatch needs a deliberate extension before a DLL attribute can be
treated as a checked constraint. At inspected main revision `71cf80bf`,
`ApiDispatch.Binding.libraryNameExact` records the actual image library name,
but `Binding.MatchesRequest` checks the API constructor only. It does not compare
that name to a descriptor's declared DLL. The attribute implementation must
check the declared logical library identity against that actual name, or clearly
omit a DLL constraint. Keep normalization explicit in the fixed target rules;
do not silently accept aliases or claim native DLL identity from string equality.

Trial rejection cases must demonstrate that annotations cannot bypass checks:

* Correct symbol under a different declared library fails the declared logical
  library constraint, even if the API constructor matches.
* A valid plan from another reached machine or request cannot inhabit the
  required indexed result; a stale CALL receipt cannot authorize a new occurrence.
* A rejected full loan batch yields no successful handoff or inserted runtime
  occurrence. Existing refusal behavior remains unchanged.
* ExitProcess entry cannot produce a returning frame or a terminal observation.
* Conflicting descriptor registrations require explicit resolution; both the
  attribute and explicit-constructor paths use the same checked implementation.

These are acceptance requirements for the proposed implementation, not claims
that these tests exist. Syntax-only compilation is insufficient evidence.

## Linux, WASI, AArch64 and Wasm as design participants

Craig requests Linux and WASI participation in this discussion. Their specialists
are reviewing the declaration boundary; this section is a proposed cross-target
test, not authorization to start ports or a claim that their implementations exist.
It follows the versioned provider boundaries in [PLATFORM_ABI](PLATFORM_ABI.md).

Craig additionally requests AArch64 and Wasm participation. Linux/WASI review
platform and provider interfaces; AArch64/Wasm review execution and instruction
construction. These are separate dimensions: an ISA alone does not select a
platform contract, and WASI is not the semantics of all Wasm instructions.
The existing four specialists are asked for bounded design input, not new work
streams. Their reviews must precede ratifying a supposedly cross-target kernel.
Craig further clarified through Linux that direct syscalls are an explicit
supported declaration use case, not only a future compatibility concern.

Separate a portable demanded operation from each target's concrete endpoint
declaration and checked realization. A console operation may have several target
realizations; that does not make WriteFile, a Linux write syscall and a WASI
operation interchangeable contracts. Each proves its own observation/refinement
connection, including failure, partial progress and terminal behavior.

| Target binding | Declaration-specific data | Obligations that cannot be Windows defaults |
|---|---|---|
| Win32 import | Logical library/symbol, selected Win64 ABI, API request/loan plan | Actual IAT/CALL binding, return/home plan, API-specific result and provider connection |
| Linux direct syscall | Explicit architecture and syscall ABI, syscall identity, argument/result interpretation | Actual syscall transition, user/kernel memory boundary, clobbers, error and interruption behavior; no DLL or Win64 home space |
| Linux library call | Actual library/symbol and selected function ABI | Function-call evidence and a separate connection from wrapper behavior to kernel behavior; do not treat a libc call as the direct syscall |
| WASI core-module interface | Explicit WASI version and module/function identity, core signature and memory convention | Actual Wasm import invocation, bounds/representation checks and version-specific result behavior; no x86 CALL receipt |
| WASI component interface | Explicit package/interface version, world/function and resource types | Component binding, canonical ABI adaptation, resource ownership and selected interface's effect/async rules |

Linux syscall interfaces are architecture-specific; see the kernel's
[syscall interface guidance](https://www.kernel.org/doc/html/latest/process/adding-syscalls.html).
WASI distinguishes its core-module Preview 1 interface from later component
interfaces. Pin the trial's version rather than treating `wasi` as an unversioned
ABI; see [WASI Preview 1](https://wasi.dev/releases/wasi-p1) and
[WASI releases](https://wasi.dev/releases).

Consequently, the common descriptor should select a typed binding family, not
require `dll`, native registers, return addresses or Win64 loans in every entry.
The Win32 `ApiRequest` subtype described above is the first adapter, not the
universal request universe. Likewise, shared logical occurrence/custody laws can
be reused where their premises apply, but a WASI adapter must not manufacture
an X86.State or use a CP handoff as substitute evidence of a Wasm invocation.

Retain shared traversal, initialized-byte decoding, exact-state composition,
occurrence identity and observation laws at the narrowest applicable layer.
Target adapters supply their actual transition receipts and distinct ABI laws.
Portable process requirements and terminal observations stay above these
adapters; target data layouts and transitions stay below them.

Ask Linux and WASI specialists to instantiate an output operation and a terminal
operation on paper. For each, list the attributes authored once, the checked
producer invoked, the common proof reused and the new domain proof still owed.
The test fails if they must restate Windows-only fields, duplicate a general law,
erase a failure distinction, or weaken the existing portable specification.
Explicit custom implementations remain available through the same checked
construction path. Spikes chooses when any target trial becomes implementation.

Linux's initial review sharpens the split: target binding, entry/continuation
ABI, and completion classification are independent descriptor components.
Returning must not imply Win64 ReturnHome. Syscall identity includes the selected
architecture ABI/personality; a syscall number alone is insufficient. A proposed
direct Linux output/termination trial uses write and exit_group, with explicit
descriptor rights/lifetime, raw results, partial progress and signal/restart
scope. Neither failure nor nonreturning classification implies zero prior output
or completed process termination. This is Linux specialist design input; exact
implementation evidence remains to be supplied by the chosen target adapter.

The instruction review asks AArch64 and Wasm to identify actual execution shapes
before reusing x86's post-fetch builder. A shared interface must preserve each
target's own state and receipt indices. No synthetic x86 fetch, register file or
CALL/RET receipt may be required merely to access general proof laws. Request
two differing instruction examples from each specialist and compare remaining
authored obligations with the LEA/branch/arithmetic worksheet. The shared result
should be laws and checked composition over real receipts, not a universal
record that hides target-specific validation, control or refusal behavior.

WASI's initial review proposes a design trial pinned to WASI 0.1/Preview 1,
wasm32 core command, one selected unshared memory and no memory growth during a
synchronous import: fd_write plus proc_exit. This is a review fixture proposal,
not a port/profile release. The real instantiated function, module/field, core
signature and memory identity must be retained. Derive iovec and buffer spans
with bounds, initialization, footprint and descriptor-lifetime evidence; stdout
authority is explicit. Keep errno, traps, partial output and zero progress
distinct. A void result signature does not prove proc_exit never returns, and
entry or a trap does not prove host-observed termination. See the versioned
[WASI 0.1 interface](https://github.com/WebAssembly/WASI/blob/wasi-0.1/preview1/docs.md).

A separately version-pinned component challenge must account for typed resource
ownership/borrowing and actual canonical lift/lower adaptation. It cannot merely
rename Preview 1 imports or inherit a synchronous discipline automatically.
Both platform reviews agree that occurrence/custody laws are reusable only when
the selected protocol discipline and concrete transition evidence satisfy their
premises; physical return, host identity and terminal fidelity remain separate.

### Consolidated decision and implementation boundary

Spikes accepts the bounded framework proposal. Its next dispatched API change
is shared checked CP entry adopted by GetStdHandle and WriteFile; attribute
syntax is deferred until that producer is real. Generic evaluated-CALL
preparation remains separately owned. ReturnHome dual adoption is reported
integrated in main `d2dfacde`, with full build and fresh declaration audit passed.

Represent continuation/completion capabilities with dependent variants or
capabilities whose constructors require the relevant evidence, not a runtime
enum that allows nonsensical field combinations. Keep ABI continuation separate
from response/termination guarantees. Review the elaborated ordinary term: the
attribute must select the same checked constructor as explicit code.

Linux, WASI, AArch64 and Wasm reviews accept the checked-constructor direction,
subject to the target-specific obligations recorded here. This accepts a design
boundary, not a completed cross-target implementation. Do not create a universal
state or semantic relation to satisfy the syntax. An extensible collection of
construction families is sufficient; each new family must retain its fixed
semantics, checker equations and genuine intermediate states.

## Instruction construction framework

The post-FetchedSite producer below is x86-local. Cross-target reuse begins with
composition over each target's selected fixed relation and exact receipts, not
with a common CPU-shaped receipt. Generalize an implementation only after two
actual consumers share its premises; similar English descriptions do not suffice.

Use distinct execution shapes over the existing semantic receipts: access-free
computation, initialized read, write, and multi-stage control transfer. Share
construction within a shape and share lower-level laws across shapes. Do not
force CALL into a single-read template merely to increase reuse.

The initial reusable pieces are:

* A canonical access-free receipt builder from the exact `FetchedSite`, actual
  `RunFactory.accessFree` result and equation. It must not depend on
  `FetchFactory.Success`, which would introduce an import cycle.
* `ReadValue byteCount run`, indexed by the same actual `AccessRun`, with one
  observed-byte, backing, initialization and decoding library. Existing 32/64
  names become aliases at four/eight bytes. Register writes, extension rules,
  effective addresses and return-target semantics remain instruction-specific.
  Share byte observation independently of interpretation: decoding requires the
  selected representation/endianness law, rather than inferring it from width.
* One access-failure reached-state mapping. A rejected access preserves its
  supplied stage input; a failure after execution retains that actual reached
  memory with the corresponding CPU frame. CALL store rejection starts after
  the target read, not at the instruction's original state.

An instruction declaration supplies encoding/operand selection, an execution
shape, descriptor construction and the distinct architectural effect. Its
connection to the existing instruction semantics is proved once per instruction.
It reuses fetch identity, context propagation, receipt packing, common memory
observation and failure transport. Fixed evaluator dispatch still selects the
actual instruction; declarations do not choose a more convenient execution.

Use LEA and conditional branch as the first declaration-interface trials. LEA retains its
effective-address/register effect, encoding, fallthrough and frame laws. Branch
retains its flag-dependent target, taken-only natural range proof and distinct
`targetOutOfRange` refusal. Both share the actual post-fetch access-free run and
its receipt builder. A higher-level adapter may take `FetchFactory.Success`;
the lower-level builder must stay beneath that module to avoid the import cycle.
Place it in a downstream module importing RunFactory and the fetched-site
definition, rather than adding a reverse dependency to AccessFree or RunFactory.

These two already share BodyComputationFactory's private builder, so they test
interface fit but do not by themselves close DUP-05. That migration must also
adopt the shared builder in the existing ComputationFactory MOV consumer and
remove its independently repeated `AccessFree` receipt construction. Its typed
`MoveNormal` construction remains instruction-specific. This distinction keeps
a successful DSL demonstration from being mistaken for duplication removal.

Arithmetic is the third-consumer challenge: retain caller-supplied flags,
`Flags.Allows`, the check before execution, distinct `flagsRejected` behavior
and `status_exact`. Preserve the exact `fetched.after` and actual run endpoint
in the returned dependent receipt. An interface that forces consumers to
reconstruct those indices has erased too much. Do not abstract whole family
factories into a common success record that loses their typed Normal receipts.
Repeated proofs of fetch equality, observation length or context-only state
change fail acceptance.

### AArch64 review and discriminating trials

AArch64 review accepts shared exact-state composition, checker equations and
receipt packing, while keeping fetch/decode, flag rules, address interpretation
and architectural exceptions in its adapter. The x86 Flags.Allows and
targetOutOfRange cases are not mandatory fields in every instruction family.
Access ordering, faults and partial completion retain their target/profile
semantics even when completed-byte observation laws can be reused.

The first paper trial is ADDS W0, W1, W2. The author supplies encoding/operand
legality, 32-bit arithmetic with X0 upper-half zeroing, NZCV effects and control/
register framing. Shared construction retains the actual A64 fetch/decode and
reached body state. Reject witnesses that retain old upper X0 bits or supply
incorrect flags; do not request x86 undefined-flag evidence. Generalizing operand
forms must preserve their distinct interpretation of register 31.

The second is SVC #0 at a selected Linux userspace boundary. Its ISA receipt
establishes an actual exception transition. The Linux adapter separately derives
the request and occurrence from that same boundary under the selected ABI and
profile. Exception execution is neither checker refusal nor API completion.
Identical SVC bytes under a bare-metal environment cannot authorize a Linux
operation; a stale receipt cannot authorize a fresh one. The adapter still owes
exception/continuation adequacy, raw result and clobber interpretation, memory
rights and provider observation, including partial output and restart behavior.
No CALL stack store or Win64 home space is constructed.

These are specialist-reviewed paper trials, not implemented producers. Exact
normative citations and profile admission remain implementation requirements.

### Wasm review and discriminating trials

Wasm specialist review accepts the construction direction with target-local
builders. A future receipt must retain exact module artifact/decoded body,
instantiated module identity, instruction occurrence, reached store/frame,
operand stack/control context and actual reduction equation. Linear memory is
not a substitute executable-byte fetch source; no RIP, flags or native return
slot belongs in the common requirements. Pin Core version and enabled features
when selecting a profile.

Use i32.add and br_if as the Wasm trials. A stack-computation producer for add
derives the actual two-i32 suffix and preserves the untouched prefix, frame and
store; the author supplies modular arithmetic meaning and selected-instruction
connection. A control producer for br_if derives condition, label and carried
arguments from the same reached configuration. Zero continues after consuming
the condition; nonzero takes the structured branch. Block exits and loop
backedges retain their different continuations and arities. Neither case should
be flattened into a generic memory-free computation receipt.

Static validation rejection, runtime trap, host outcome and unsupported-fragment
refusal are separate. Typing alone is not evidence of normal completion. For a
host call, resolve the actual function address through the current instance and
store to the provider; matching import strings/signatures are insufficient.
Retain same-invocation return evidence, with explicit treatment of host store
effects and reentrancy before claiming frames are preserved. Returning does not
imply responsiveness or exclude traps/divergence.

Trial checks distinguish identical indices in different instances, matching
names with the wrong runtime host binding, zero/nonzero branches, loop/block
targets, validation failure/runtime trap, and stale invocation/fresh completion.
Stack-prefix and control transport should first be Wasm-local shared laws;
exact-state composition and trace concatenation may be shared only over the
fixed selected semantics. These are specialist-reviewed design obligations,
not implemented tests. The reviewed [Core execution reference](https://webassembly.github.io/spec/core/exec/instructions.html)
is background; its moving URL does not pin a profile authority.

## Other stack-wide proof libraries

These need shared laws and checked adapters; a DSL is not justified merely by
their repetition.

| Family | Framework boundary | First consumers and preserved distinction |
|---|---|---|
| All-or-none traversal | Existing `List.mapM` plus ordered success correspondence, length and element provenance | Source initialization and import-name resolution; preserve resolver-specific rejection and exact order |
| Counted binary parsing | ReaderCore counted parser/writer law retaining the exact unconsumed suffix | PE section headers and exception runtime functions; preserve zero count, needMore and invalid |
| Placement recovery | Same-address-plan, same-memory, same-actual-run bridge | Push and Call; ReturnSlot retains its own context and target obligations |
| Source/certificate assembly | Indexed products of actual checked stage outputs and success equations | Authored source and fixed platform plan; preserve exact artifact identity and all admitted behaviors |

Do not replace the public certificate with a generic user-supplied profile or
selected successful execution to make construction easier. Proof reuse must
preserve the original theorem, including refusal and complete behavior scope.

### Concrete library interfaces and remaining migration evidence

Follow-up source audit at main `900df7d4` found independent failure-state helpers
still in MemoryMoveFactory (`reached`), ReturnSlotFactory (`accessReached`) and
FetchFactory (`accessReached`). Push/Call adoption is therefore partial DUP-06
closure. The remaining migration should call RunFactory.AccessFailure.reached
with each factory's exact stage input and remove those three private matches.
Do not change the surrounding family-specific Failure constructors.

The same audit confirms that SourceInitialization.resolveEntries? and
SourceImportRequests.resolveNames? each recursively traverse Option results and
reprove projected source order. Replace their recursion with existing List.mapM
and a shared success-correspondence theorem. Proposed theorem shape, not a new
implementation or a claim about an existing theorem name:

```text
mapM f inputs = some outputs
  iff List.Forall2 (fun input output => f input = some output) inputs outputs
```

Derive output length and indexed/member provenance from this correspondence.
For order projection, a consumer supplies only its one-element law
`f input = some output -> project output = input`; shared composition proves
`outputs.map project = inputs` under the explicit mapM-success premise.
SourceUnwindPrefix's existing private mapM_getElem? is the third-consumer
challenge: adopt the shared indexed law and remove that separate proof.
Initialization still owns Store32.resolve?
correctness; import requests still own resolveName?_source. Neither should
induct over lists again. Preserve the existing first-occurrence deduplication
before import resolution; the all-or-none traversal does not replace it.

ImageReader.readSectionHeaders and ExceptionReader.readRuntimeFunctions also
still implement the same counted-reader recursion and writer-append induction.
Proposed ReaderCore interface: `readCount readOne count input`, with zero count
returning the unchanged suffix and positive count using existing continueRead.
Its general round-trip theorem consumes only the single-record law:

```text
readOne (writeOne item ++ suffix) = .done (view item) suffix
  => readCount readOne items.length (writeMany writeOne items ++ suffix)
       = .done (items.map view) suffix
```

The single-record law is universally quantified over item and suffix. Either
make the existing table writers use the shared concatenation or prove their
definitional bridge once. Section-header and runtime-function consumers retain
their distinct field decoding and semantic bounds; the general theorem does
not establish loader acceptance or unwind validity. Counted-reader reuse also
retains the exact needMore/invalid result from the failing element through
continueRead. A zero-count case, two differently sized record types, a nonempty
suffix, and an incomplete second record distinguish the required behavior.
Also retain the exact needMore hint and invalid error, including an invalid
second record; valid-writer round trips alone do not establish these laws.

These source findings make DUP-03/04 concrete law-library migrations. They do
not justify another DSL. The general law correctly takes an explicit parser;
production adapters must instantiate the existing parser and writer, rather
than replacing them with convenient alternatives to discharge a proof.
Library owns the shared law surface, grammar/artifact and source owners review
their adapters, and spikes schedules the work. DUP-02 and DUP-05 remain the
separate read-observation and receipt-construction migrations described above.

### Jump targets and API bindings

Lowering reviewed the proposed crossover and found existing shared construction,
not a need for a new universal target resolver. SourceTemplates retains branch
labels/targets and external-call symbols with continuations; SourceSplice maps
them across inserted code; SourceResolve.Output retains exact source occurrence
and detail equations. SignedRel32 and RipRelative already share displacement
and translation laws. Real consumers include WriteFileLoad.source_branch_target
and SourceImportBindings' source-to-IAT binding.

Preserve the target kind: a ripImport target is an IAT slot address, not the
provider code address read from that slot. SourceFetch/SourceFetched connect the
selected source occurrence to actual fetched bytes; BranchNormal still needs
actual flags and taken/fallthrough evidence, while CallNormal retains the actual
target read and stack store. ApiDispatch and EvaluatedCall bind that same dynamic
receipt. Repeated visits to one source index are distinct execution occurrences.

Block/API annotations may name entry contracts and continuation shapes, but the
checker must prove them over the actual reached state. Reuse exact-state/path
composition; do not infer loop invariants from annotation text or apply call
custody/return laws to jumps. Lowering's immediate two Hello trials are GetStd
actual result through TEST/CMP to unavailable/head, and success/failure paths
through the shared exit label to the actual ExitProcess CALL with correct ECX.
Both reuse existing target laws and still owe endpoint semantics. Preserve the
authored unexpected-return UD2 continuation; nonreturning classification cannot
erase it from raw behavior or turn call entry into termination.

The concrete endpoint decision is in [HELLO_ENDPOINT_MODEL](HELLO_ENDPOINT_MODEL.md).

## Acceptance and sequencing

Spikes schedules bounded migrations beside the demanded implementation. Finish
ReturnHome adoption and the reviewed failure-mapping change, then select the
next family that removes an actual consumer burden. API checked handoff and
width-indexed reads are substantive candidates; no automatic DSL build starts
from this proposal.

For each family, record the owner, existing consumers, shared producer/laws,
remaining domain obligations, and any concrete exception with a revisit trigger.
Completion requires actual adoption by the existing consumers and removal of
duplicate implementations; compatibility aliases may remain. Review a third
consumer before declaring the abstraction sufficient.

Validation includes positive construction with actual receipts, discriminating
refusal/mismatch cases, preserved intermediate-state indices, appropriate build
and trust checks, and independent review of the consumer diff. Compare authored
obligations before and after; generated line counts do not measure proof burden.

Every major spike milestone triggers a cleanup audit: inspect new consumers for
repeated guarantees, obsolete parallel constructors, temporary adapters and
approved exceptions whose revisit trigger has fired. That audit yields bounded
owned work, while duplication already blocking forward progress is addressed
before the milestone.

This proposal is not closure of the active goal. Closure requires reviewed
framework decisions covering the evidenced families, demonstrations that new
consumers no longer repeat the shared obligations, and explicit disposition of
remaining stack gaps. Missing evidence remains open rather than being counted
as eliminated burden.
