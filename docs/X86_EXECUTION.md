# Bounded x86 execution work

The current implementation supplies the carrier, canonical stack-instruction
selection, actual fetched-memory receipts and a conditional normal SUB RSP
completion constructor. PUSH execution and unwind reversal remain unfinished.
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

This is a conditional normal branch, not total instruction execution. Failure to
construct its receipt says nothing about whether another outcome is possible.
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

Remaining work binds final emitted source to these fetched bytes, adds the PUSH
store and checked saved-read branches, and carries actual prefix receipts into
unwind reversal. Rejected, denied and permitted fault outcomes remain separate.
No total x86 execution or partial-unwind proof is claimed by these files.
