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

## API construction framework

Extract a protocol-level checked handoff producer beneath API-specific modules.
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
| Logical import identity | Fixed dispatch selection and request-kind agreement |
| Returning or nonreturning classification | Returning declarations use the common ReturnHome producer; nonreturning declarations acquire no fabricated return frame |
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
