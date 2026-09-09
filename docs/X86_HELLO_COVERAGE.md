# Exact Hello instruction coverage

This bounded plan follows the unchanged [Hello source](../Spikes/1_Hello_World/Program.lean).
The inventory was evaluated at `d4fbb3c7`; generated offsets and bytes must be
recomputed when the source, frame derivation, splice, symbols or encoders change.
The inventory is a scheduling aid, not a second executable instruction sequence.

## Population and source binding

Use the production chain exercised by
[SourceResolve's fixture](../Tests/Assembly/SourceResolve.lean): embedded authored
characters, `SourceInput.extractHelloSourceChars`, `SourceFrame.derive?`,
`SourceSplice.derive? frame 0`, then `SourceResolve.resolve?`. Its fixture uses
code base 1000 **decimal**, payload address 2000 with length 15, and IAT cells
3000, 3008 and 3016. These fixture addresses are not Windows loader addresses.

`SourceResolve.Result.outputs` is the ordered population. Export each output's
index, `SourceResolve.sourceOffset result.codeBase result.splice.finalSizes index`,
encoding bytes, origin, template and resolution detail. Flatten those encoding
bytes to obtain the whole code sequence. `indicesExact`, `countExact` and
`encodingSizesExact` check enumeration order, count and sizes; each output retains
its source/splice provenance and resolved encoding. There is no standalone
whole-population exporter at the inventory revision.

The evaluated fixture has 44 outputs and 212 bytes. Three saved-register PUSHes
start at relative offsets 0, 2 and 4. The generated SUB RSP starts at 6, the
generated DWORD initializer at 10, and the first remaining authored instruction
at 21. Generated argument stores and splice insertions belong to the population.
The loaded-image witness must bind the final production output to the bytes
actually observed by `Execution.FetchedSite`; inventory equality alone does not
establish that connection.

## Implementation slices

| Slice | Bounded forms | Reuse and remaining connection | Owner |
| --- | --- | --- | --- |
| Prologue | Register PUSH; immediate SUB RSP | Actual fetch, full RFLAGS completion rule, checked stack store and saved-value read | x86 parent |
| A | Register MOV at 32/64 bits; immediate MOV at 32 bits | Production register semantics/encoders; actual access-free completion, destination update and 32-bit high-half clearing | x86 private builder |
| B | Register ADD/SUB/CMP/TEST/XOR; immediate CMP; rel32 JMP/JZ/JE/JA | Production arithmetic and decoder; defined status flags, relational undefined flags, branch conditions and target arithmetic | x86 private builder |
| C | RIP-relative payload LEA; RSP-relative frame LEA | Production effective-address fields and resolution; register transfer without a data-memory read | x86 private builder |
| D | RSP+32 QWORD argument store; RSP+40 DWORD initializer/store/load | Prepared actual memory accesses, exact width/payload/address, initialized read and register writeback | memory owner |
| Calls and environment | RIP-relative IAT calls; return mechanics; provider results; ExitProcess and UD2 paths | Initialized target cells, return-address mechanics, call protocol, matched returns and terminal provider contract | architecture coordinates Windows/lowering/root |

All normal adapters use the canonical `Execution.State` and a continuous actual
fetch-to-operation run. Decoder agreement selects a transfer; it does not itself
execute it. Conditional normal receipts do not exclude architectural faults,
traps, interruptions or ghost admission failures. Reserved input bits and physical
profile admissibility remain explicit external obligations. Undefined flags must
remain relational rather than acquiring a chosen representative.

Hello has no authored RET or epilogue after ExitProcess. Unexpected return reaches
UD2; the excess-write-count path also reaches UD2. Provider terminality and
physical return behavior are separate from ISA decoding and register transfer.

## Independent boundary campaign

The auditor owns the bounded NASM/NDISASM campaign over the same generated
population. Keep raw and parsed output, tool versions, executable/input/output
digests and exact replay instructions. Force production-selected immediate,
displacement and branch widths for exact-byte comparisons, or report a permitted
alternative encoding separately. An internal decoder roundtrip is not an
independent assembler check.

Record prefix decode, empty trailing suffix and expected typed instruction
identity separately. Appending NOP can preserve a successful prefix decode while
failing whole-single-instruction admission. A cancelling XCHG pair must not enter
through that boundary as one instruction. REX/operand mutations can decode as
different valid instructions; reject their expected identity without claiming
that every mutated encoding is architecturally invalid. This campaign adds no
all-ISA claim and supplies no theorem authority.
