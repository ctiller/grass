# Shared proof frameworks and declaration fronts

Architecture guidance and declaration-front proposal, 2026-09-09. The status
section records implemented shared construction; the optional DSLs remain
proposals for removing recurring authoring obligations. Spikes owns implementation sequencing; architecture
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

Current integrated source inspected at `a39e22ae`. These are bounded production
adoptions, distinct from the declaration/DSL proposal below:

- [ProtocolEntry.issue?](../Grass/Platform/Win32/ProtocolEntry.lean) is the shared
  checked handoff used by the actual GetStdHandle entry producer in
  [GetStdHandleRuntime](../Grass/Platform/Win32/GetStdHandleRuntime.lean) and
  [WriteFileHandoff](../Grass/Platform/Win32/WriteFileHandoff.lean). Their request
  preparation and loan obligations remain API-specific.
- `ProviderResume.observeRegisters` is used by
  [GetStdHandleResult](../Grass/Platform/Win32/GetStdHandleResult.lean) and
  [WriteFileReturnCompletion](../Grass/Platform/Win32/WriteFileReturnCompletion.lean)
  to stage observed registers without inventing provider memory effects.
- [ProviderResumeFinalization](../Grass/Platform/Win32/ProviderResumeFinalization.lean)
  supplies the shared final-state, protocol-consumption and log laws to actual
  [GetStdHandleReturn](../Grass/Platform/Win32/GetStdHandleReturn.lean) and
  WriteFileReturnCompletion. This dual adoption is implemented, not an interface-only trial.
- `Raw.Event.between_suffixes` is used by both actual
  [GetStdHandleRawReturn](../Grass/Platform/Win32/GetStdHandleRawReturn.lean) and
  [WriteFileRawReturn](../Grass/Platform/Win32/WriteFileRawReturn.lean) consumers.
  The exact return/read suffixes do not establish native or cross-log causal ordering.

This closes those specific reuse obligations, not every duplication family,
full endpoint assurance or the proposed DSL. The
[endpoint index](ENDPOINT_INDEX.md#issued-call-resume-status) records the execution
frontier and current blockers; the older `2370d929` inventory remains a historical
lower bound, not a current census.

The next shared rewrites are in progress: memory-model owns canonical
synchronization state consumed by the same access checker; process owns replacement
of `Raw.finitePrefixSystem` with the canonical execution system. Neither rewrite
is claimed delivered here.

## API construction framework

Use the existing `ProtocolEntry.Entry` and `ProtocolEntry.issue?` beneath the
API-specific modules. The producer is indexed by the exact reached
`ExecutionState.State ApiRequest`, concrete request, ordered loan batch and agent.
It retains the actual projection and `CallProtocol.handoff?` equations while
checking caller control, registered contexts and cleanliness. Its shared laws
cover projection, exact pending record, unrelated pending preservation, storage,
boundary append and freshness.

GetStdHandle and WriteFile already use this implementation. Typed wrappers and
semantic projections may remain; they must use the canonical heterogeneous
receipt rather than rebuild its checks or reconstruct another record from mint
inputs. New declaration syntax must select this existing producer and retain its
exact inputs and success equations, not trigger another extraction project.

The proposed API declaration interface supplies:

| Input | Obligation retained by the API author |
|---|---|
| Request decoder from the reached machine | Actual ABI arguments equal the semantic request |
| Checked loan-plan producer | API-specific sizes, separation, protection and loan order |
| Logical import identity | Fixed dispatch selection and request-kind agreement |
| Returning or nonreturning classification | Returning declarations use the common ReturnHome producer; nonreturning declarations acquire no fabricated return frame |
| Runtime payload constructor | Payload-specific data is derived from the same entry receipt and plan |
| Provider semantic adapter | Service, result, failure and temporal obligations specific to this API |

Declaration-front trial consumers are GetStdHandle and WriteFile: one has only the return/home
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
Success means authoring API-specific facts once while retaining the implemented
shared handoff machinery; generating fresh duplicate proofs fails.

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
| GetStdHandle | RCX low-DWORD selector, API identity and result meaning | Actual CALL binding, return/home plan, shared checked handoff, observed-register staging and actual return/finalization | External provider/native applicability; observed results remain explicit inputs |
| WriteFile | Handle/buffer/count/fifth-argument ABI checks, semantic loans, partial-output model | Same CALL and ReturnHome construction, whole-batch handoff, shared staging and actual return/finalization | Original-entry/enclosing service-history and output correspondence, external/native applicability |
| ExitProcess | RCX low-DWORD status and nonreturning classification | Checked entry with the selected slice's empty loan batch; completed modeled exit checks exact process/call/status and retains an inert archive | Native applicability and particular duty accounting under [owning protocol laws](OBLIGATIONS.md#observed-process-exit); no universal teardown or empty-inventory requirement |

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

## Linux and WASI as design participants

Craig requests Linux and WASI participation in this discussion. Their specialists
are reviewing the declaration boundary; this section is a proposed cross-target
test, not authorization to start ports or a claim that their implementations exist.
It follows the versioned provider boundaries in [PLATFORM_ABI](PLATFORM_ABI.md).

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

## Instruction construction framework

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
and trust checks, and [semantic review](REVIEW.md#implementation-peer-review) of
changed consumer boundaries. Routine adoption under an established contract uses
targeted checks and evidence of actual production use. Compare authored
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
