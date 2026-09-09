# Source-derived frame memory execution

[FrameMemoryExecution](../Grass/Assembly/FrameMemoryExecution.lean) connects a
resolved source occurrence to an actual instruction fetch and its continuous
data access. [FrameMemorySource](../Grass/Assembly/FrameMemorySource.lean)
selects body stores, inserted initializers, stack arguments, and DWORD loads
from the same `SourceResolve.Result`. Its constructors return computable
witnesses from the actual output list. Frame offsets and instruction bytes
come from those witnesses, rather than separate literal inputs.

[SourceFetch](../Grass/Assembly/SourceFetch.lean) retains the actual initialized
CPU-virtual fetch, the exact selected output, and an explicit image placement
equation. Its `rip_exact` theorem derives absolute RIP as the loaded-image base
plus the source RVA. The caller still establishes the loader/code-region
association and entry reachability.

The source-free x86 interpretation lives in
[MemoryMoveNormal](../Grass/ISA/X86/Execution/MemoryMoveNormal.lean). It admits
RSP-relative immediate DWORD stores, sign-extended immediate QWORD stores, and
DWORD loads. The Assembly wrappers construct this interpretation's receipts;
they do not define another architectural transfer. The actual fetch and data
run share one policy, context, and cause, and the data descriptor uses ordinary
ordering with no authority or obligation transfers.

Both generic normal receipts require a present data-allocation base. A
successful access preparation alone is insufficient: an unplaced allocation
can pass preparation without checking its numeric address. The placement
witness connects the actual resolved allocation and range to the instruction's
effective address.

`StoreNormal.written_exact` derives the payload from the actual memory-oracle
answer. `memory_written` and `stored_cell` derive the initialized backing
mutation from that checked transition. `LoadNormal.read` extracts the actual
completed observation, and the shared `ReadValue32` adapter proves its width,
backing origin, and initialization. The load result uses the canonical DWORD
write-back rule, including clearing the destination's upper half. Both forms
retain the actual post-access memory machine, advance to the fetched
instruction's fallthrough, and apply the common MOV completion flags.

These receipts define conditional clean normal branches. They do not exclude
faults, traps, rejected accesses, or interruptions, and do not constitute a
total CPU step dispatcher. A future checked classifier can select the shared
x86 interpretation; source correspondence remains in Assembly. Ordinary
integer bytes do not create pointer provenance or prove an API argument's
authority merely because its source declaration names a pointer parameter.

[ExecutionFrameRoundTrip](../Tests/ISA/X86/ExecutionFrameRoundTrip.lean) checks
a source-derived DWORD store followed by a DWORD load through four actual
fetch/data steps. The frame starts uninitialized; the load observes the bytes
committed by the store, and DWORD write-back clears the upper register half.
[ExecutionFramePrefix](../Tests/ISA/X86/ExecutionFramePrefix.lean) checks the
inserted DWORD initializer followed by the adjacent QWORD argument store,
including the actual initialized zero cells committed by both writes. These
fixtures begin with an allocated frame at the selected instruction.
[ExecutionMemoryMoveUnplaced](../Tests/ISA/X86/ExecutionMemoryMoveUnplaced.lean)
checks that an unplaced resolution cannot construct either normal receipt.
