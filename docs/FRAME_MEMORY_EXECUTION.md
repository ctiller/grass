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
run share all non-oracle policy fields, context, and cause. Each phase retains
its own concrete memory oracle, and the data descriptor uses ordinary
ordering with no authority or obligation transfers.

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
total CPU step dispatcher. `MemoryMoveSelection.select` checks equality with
the production encoders, and `MemoryMoveFactory.memoryMove` constructs the
actual fetch and operand-derived data access. Source correspondence remains in Assembly. Ordinary
integer bytes do not create pointer provenance or prove an API argument's
authority merely because its source declaration names a pointer parameter.
