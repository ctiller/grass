# Bounded x86 execution work

The current implementation supplies the carrier, canonical stack-instruction
selection, actual fetched-memory receipts and conditional normal SUB RSP,
register PUSH and register MOV completion constructors. Checked saved-value reads and unwind
reversal remain unfinished.
[The agreed execution boundary](HELLO_UNWIND_BOUNDARY.md) defines the remaining
composition with the actual memory checker and final source.

`Execution.State` embeds `Memory.MachineState` once, alongside the GPR file,
RIP and full 64-bit RFLAGS. The six status flags are a derived view. Its masked
status setter is a representation helper, not an instruction law.

`DecodedSite.check` obtains its encoding from `decodeInsn`, retains the exact
prefix/suffix, and checks a positive length of at most 15 bytes and a
nonwrapping fallthrough cursor. It does not prove fetch permission, executable
placement or final-source membership. A fallthrough cursor is not the next RIP
of a branch. `StackInstruction` selects existing production PUSH register and
SUB RSP immediate encodings by exact equality; it has no second opcode table.
Its completeness laws cover every production GPR and both immediate widths.

`AccessRun` requires the actual selected sequence to contain exactly one access
substep, with its no-fault plan, reached-state preparation and oracle answer,
actual step result and clean ledger. `FetchedSite` adds an initialized execute
read at RIP, a present allocation base, and the exact memory-backed oracle.
Its descriptor has no obligation or authority effects.
The decoder consumes the whole actual observed extent. Placement, decoded
bytes, event size, memory-state and obligation preservation are derived. Final emitted-source
membership remains an assembly adapter obligation.

`SubRspNormal` joins that actual fetch to an access-free operation under the same
policy, context and cause. Its encoding equality fixes the production typed
immediate, including width and sign extension. The result uses the actual final
memory machine, production arithmetic, full-RFLAGS normal rule and fetched
fallthrough RIP. `machine_frame`, `fetched_event`, `events_exact` and
`state_frame` retain the continuous run and observations.

`PushNormal` joins its actual fetch to an actual prepared eight-byte store under
the same policy except for the instruction payload oracle. The execution
context, cause and descriptor contexts are tied together. The descriptor is a
plain write with neutral obligation and authority effects. A non-wrapping RSP
decrement and a successfully prepared placed stack span bound this normal branch.
The payload comes from the pre-instruction source register, including PUSH RSP.
`written_exact`, `memory_written` and `saved_cell` derive the actual initialized
backing bytes, rather than accepting an asserted post-state or event payload.
`events_exact` retains the ordered instruction fetch and saved-value store.

`AccessFree` packages the common continuous fetch-to-access-free-operation run.
`MoveNormal` selects production register MOV at 32 or 64 bits or register
immediate MOV at 32 bits. Its result uses the existing register semantics,
clears RF on ordinary completion, and retains the full memory/obligation frame.
The 32-bit forms derive upper-half zero extension; the actual fetch event fixes
the selected encoding. This receipt supplies no emitted-source membership claim.

These are conditional normal branches, not total instruction execution. Failure
to construct a receipt says nothing about whether another outcome is possible.
Faults, traps, interruptions and their delivered contexts remain obligations of
the later total correspondence. Physical input admissibility and the source
basis remain separate from these model-level constructor laws.

`CompletionFlags` is conditional on ordinary instruction completion before
event delivery. PUSH clears RF; SUB merges its six defined status flags and
clears RF. Other represented bits are retained by these bounded transfer
functions. Physical correspondence requires an admitted 64-bit-mode input
state and source/profile justification; arbitrary reserved-bit patterns are
not asserted to be realizable machines. No IF=0, DF=0 or RF=0 entry assumption
is introduced. These functions do not certify that an instruction completed.

## Source evidence inspected on 2026-09-09

Intel SDM revision 092: [instruction volumes](https://cdrdv2-public.intel.com/922478/325383-092-sdm-vol-2abcd.pdf)
and [system volumes](https://cdrdv2-public.intel.com/922486/325384-092-sdm-vol-3abcd.pdf).
AMD combined APM publication 40332 revision 4.10:
[official download](https://docs.amd.com/api/khub/documents/SLs_hsYJwsu9rrIjE0rGxA/content).
AMD component revisions are Volume 2, 24593 revision 3.45, and Volume 3,
24594 revision 3.38, both July 2026. Manuals remain reference-only and are not
redistributed. These source notes do not discharge declaration-to-ledger debt.

| Matter | Intel printed anchor | AMD printed anchor | AMD combined PDF pages |
| --- | --- | --- | --- |
| PUSH | Vol. 2B, 4-522–4-525 | Vol. 3, 297–298 | 1612–1613 |
| SUB | Vol. 2B, 4-684–4-685 | Vol. 3, 356–357 | 1671–1672 |
| RF and debug/event distinction | Vol. 3B §20.3.1.1, 20-9–20-10 | Vol. 2 §3.1.6, 54–55 | 515–516 |
| Precise fault/restart distinction | Vol. 3A §§7.5–7.6, 7-5–7-6 | Vol. 2 §§8.1.2–8.1.3, 244 | 705 |

Instruction-local flags tables must be read together with the general RF rule.
Precise-fault rollback is not a general store-atomicity law. Its eventual use
must name the admitted fault class and affected registers/bytes. It does not
erase memory-event or fault histories and does not apply unchanged to traps,
interruptions or aborts. The saved fault-frame RFLAGS image is also distinct
from ordinary completed flags; Windows owns that delivery/context connection.

## Checks and remaining work

Fixtures reject truncation, cursor wrap, legacy-prefix inputs, CMP, wrong
register/width SUB and unrelated opcodes. Representation checks retain full
flags; completed-flag checks catch accidental RF preservation. Universal laws
tie selected instructions to the shared decoder and production constructors.

The integrated memory migration supplies prepared backing accesses and the exact
reached-state oracle API. `Op.Completion` derives the selected no-fault run from
the actual step result, then exposes a singleton prepared access at that same
`noteContext` state. Its access-free law frames the memory machine; it does not
execute the arithmetic of a compute substep.

`Op.CompletedAccess` derives event existence from a well-formed descriptor and
a complete answer. A clean actual prepared result then supplies the exact fresh
event suffix and preserved fault/violation histories. Event fields are derived
from the checked constructor. An arbitrary complete oracle answer constrains
presence and length; it does not by itself prove equality to backing bytes.
`Op.ReadCompletion` supplies that equality for the exact `Oracle.ofMemory`
answer and frames allocation/backing tables for every read-only prepared
transition, including refused ones. A successful preparation demanding initialized
bytes establishes initialization of the resolved span; those observations are
independent of the indeterminate-byte provider. Fixtures retain a missing-cell
counterexample where changing that provider changes the observed bytes.

The fetch fixture observes PUSH r12 bytes through an actual execute access and
rejects wrong-address and non-executable preparation. The SUB fixture constructs
the actual fetched normal branch and checks RSP, RIP, RFLAGS and another GPR;
a mismatched immediate has a different encoding. Neither fixture is hardware
correspondence evidence or an all-execution proof.

`Op.WriteCompletion` derives the write payload from the actual memory oracle
answer, and derives the committed memory state from the actual clean prepared
transition with neutral ghost effects. It does not bypass the ordinary
preparation, profile admission or authority checks.

`ArithmeticNormal`, `BranchNormal` and `LeaNormal` add conditional normal
transfers using the production encoders and arithmetic. TEST/XOR keep undefined
flags relational. `PushSavedRead` derives the saved value from an actual
initialized read immediately after the PUSH store; it is not a POP or unwind.

`ObservedFetch` and `Dispatch` select only from actual fetched bytes. Decode,
trailing-byte and unsupported-instruction failures retain the reached fetch
state. `InstructionDispatch` embeds the authored source directly and computes
the production pipeline inventory; its four unsupported entries are the memory
MOV forms owned by the memory implementation. CALL and UD2 recognition supplies
syntax only, with no execution or event-delivery theorem.

`CpuAccessPolicy` and `AddressPlan.descriptor` compute access ranges from current
allocation placement and fixed code/stack provenance. `RunFactory` constructs
the actual singleton or access-free operation and retains unsuccessful reached
states. These are foundations for a fixed instruction factory; callers of the
normal receipt types still provide evidence, and their union is not exhaustive
raw execution. Fault vocabularies alone establish no architectural fault
conditions, priority or delivery behavior.

`FetchFactory.fetch` takes only the fixed policy and current CPU state. It plans
the execute range from actual code placement, then runs the computed access and
classifies its actual observation. Bounded lookahead chooses the access width;
it is not evidence of a completed read. Successful dispatch retains the raw
descriptor and run metadata through `ObservedFetch.dispatch_metadata`.

`ComputationFactory.move` constructs a normal register MOV result from those
same two inputs, including the actual access-free operation step. Other selected
families remain explicit unsupported prefixes. This first constructive path
does not yet execute the full Hello program or settle fault applicability.

`ComputationFactory.subRsp` constructs the generated stack-allocation instruction
through that same fixed operation runner. `Success.extent_of_memory_prefix`
derives the fetch width from pointwise bytes in current code memory and the
production decoder law, so source consumers need not supply an independent
instruction-width assumption.

`PushFactory.push` uses the same fixed fetch path, checks stack underflow, and
computes the eight-byte stack descriptor from the current placed allocation.
Its actual store writes the selected register's pre-instruction value and
constructs `PushNormal`; callers supply no receipt or store payload. This adds
the first Hello instruction family to the constructive path.

`LinearAddress` supplies shared canonicality predicates for unmasked linear
addresses in 48-bit and 57-bit modes, with a sign-extension equivalence and
nonwrapping byte spans. Addresses below 2^47 satisfy both modes; no active mode
is inferred from executable bitness. See the
[Intel paging reference](https://cdrdv2-public.intel.com/671442/5-level-paging-white-paper.pdf).
The memory space's 64-bit representation check remains weaker than architectural
address validity. This additive leaf does not change receipt admission: physical
adequacy still must cover effective addresses and control-transfer targets under
the admitted environment, including any pointer-masking applicability.

`CallNormal` now connects a fetched RIP-relative indirect CALL to an actual
initialized eight-byte target read and an actual return-address store. The
result RIP comes from the observed target value; the stack store contains the
fetched fallthrough address. Its three events and exact memory mutation follow
from those continuous accesses. Windows still owns the exact IAT/API identity,
provider handoff and actual return-slot read; this receipt supplies no provider
return or terminality theorem.

Remaining work composes final emitted source, fixed factory results, CALL target
reads and return-address writes, and actual prefix receipts for unwind reversal.
Rejected, denied and permitted fault outcomes remain separate.
No total x86 execution or partial-unwind proof is claimed by these files.
The [exact Hello coverage plan](X86_HELLO_COVERAGE.md) assigns the other emitted
forms without replacing the production source with a second instruction list.
