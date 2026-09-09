# Initial campaign and open finding

## Scratch-stack follow-up

The success-only extension described in [STACK.md](STACK.md) was validated on
the same virtualized Intel Windows host, based on integrated `ed8db295`.

```bash
bash Tools/x86-native/build.sh target/x86-native/stack-parent-v2
python -O Tools/x86-native/run_stack.py --worker target/x86-native/stack-parent-v2/windows.exe --output target/x86-native/stack-campaign-2
python -O Tools/x86-native/run.py --worker target/x86-native/stack-parent-v2/windows.exe --output target/x86-native/stack-register-regression-3
```

Results: 21 stack cases, zero mismatches, seven execution/comparator controls
and a footprint-identity negative control; the original 870 cases and nine
controls also pass. The stack cases cover all sixteen PUSH GPRs, resolved
allocations 112 and 128 (signed imm8 versus imm32), and three generated public
prologues with total decreases 72, 72 and 120. Every scratch byte is compared;
arithmetic flags, failed instruction memory and intermediate/out-of-region
effects remain outside this evidence.

Repository checks also passed: `lake build`, `lake build Tests`,
`bash audit-trust.sh` (75 declarations, eight executable modules),
`bash check-source-input.sh` (13 source embeddings),
`bash check-spike-sources.sh`, `bash check-doc-links.sh` (53 documents), and
`git diff --cached --check`.

The memory-model owner and independent harness reviewer approved the final
success-only boundary. Review fixed footprint identity, post-start unexpected
exception handling, and self-validation of a mutable restore slot. The reviewer
independently rebuilt the final worker, ran the controls, and verified a
stack-mode UD2 failure produces unjudged memory. The restore source is now on a
read-only page and completion uses an independent original-RSP value. The
initial concurrent register campaign lost its worker executable while the same
default build path was also used by the reviewer; it was retained as an incomplete run, then replaced
by the successful isolated `stack-register-regression-3` above. Use distinct
worker output directories for concurrent reviews and campaigns.

## Original register campaign

2026-09-09, integration base `28e5767b`. Windows 11 build 26200, x86-64,
CPUID vendor `GenuineIntel`, leaf 1 EAX `722594` (`0x000b06a2`). The hypervisor
bit is set. Microcode is unknown. This is virtualized host execution evidence,
not an Intel/AMD physical-machine matrix or a bare-metal result.

The original campaign preceded the repository's Bash migration. Current
equivalent commands, run from Git Bash at the repository root after merging
main `f60c5ebe` (including the Bash gates at `8b035256`), are:

```bash
bash Tools/x86-native/build.sh
python -O Tools/x86-native/run.py --worker target/x86-native/windows.exe --output target/x86-native/bash-current-main-campaign
lake build
lake build Tests
bash audit-trust.sh
bash check-source-input.sh
bash check-spike-sources.sh
bash check-doc-links.sh
git diff --check
```

All succeeded. The MSVC worker compiles with `/W4 /WX`. Native results: 450
`writeBack` comparisons, 210 SUB reference-arithmetic comparisons, 210 CMP
completion/nonmutation checks; zero mismatches. All nine harness controls pass.
The 420 arithmetic flag results remain unchecked. The trust audit reports 75
named declarations and seven executable test modules, including NativeCorpus.
Existing ledger output still reports nine unconfirmed anchors and AMD source
retrieval debt; this campaign does not change their status.

Original local evidence is retained in `target/x86-native/campaign-3/`; the
post-migration evidence is in `target/x86-native/bash-current-main-campaign/`.
The Bash build also succeeded with output `target/x86-native/bash build space`.
Regenerate
into a fresh output directory rather than overwriting it. The coverage identity
is `c3ea5ec4c8356e7ba6c745684ce55faea505204104b8221986cdcc516a96ecd8`.
It is the SHA-256 of newline-joined TSV label/input-register/input-flags/basis
columns, tab-separated, without a final newline. Instruction bytes and predicted
outputs are deliberately excluded. The host record separately hashes the full
corpus, worker and source files.

Independent review approved the staged checkpoint after reproducing all 870
cases and nine controls in `target/x86-native/review-campaign/`, rebuilding the
worker and Lean corpus, and checking Python syntax and diff whitespace. Review
also verified all completion PC/RIP offsets and RSP invariants in the raw data.
Initial findings corrected before approval: overstated CMP coverage, weak
population identity, unchecked terminal exception/RIP, and implicit RSP masking.
The final-state harness cannot prove a byte sequence is exactly one instruction
or expose canceling intermediate effects; that remains outside this campaign.

Independent review also approved the Bash migration after a separate build to
`target/x86-native/reviewer Bash build space` and another 870-case campaign with
zero mismatches. Checks covered Bash syntax, missing discovery tool, excess
arguments, rejected batch-expansion characters, Windows-form `VSWHERE`, an
unsupported host, and propagation of a simulated compiler failure (exit 42).

## Register semantics extension, 2026-09-09

The public operand-local `RegisterSemantics` now supplies predictions for MOV,
ADD, SUB, CMP, TEST and XOR at 32/64 bits, plus signed SUB/CMP immediates.
The expanded campaign in `target/x86-native/semantics-review-campaign-v3/`
completed 994 cases with zero mismatches and 12 independent harness controls.
It retains the earlier 450 MOV and 420 immediate cases, adds 120 arithmetic
value-boundary cases and four Hello operand selections. The 953 full-status
masks are `0x8D5`; the 41 TEST/XOR masks are `0x8C5`, excluding undefined AF.
The driver independently requires the expected mask by operation label and
rejects weaker masks, unchecked results, and reserved mask bits.

Coverage identity:
`9bdf88e1e44543f42dd87e923e8d9ca0affd0a091f67c6248ff282273f50b643`.
It still excludes bytes and predictions. Host: Windows 11 build 26200,
GenuineIntel CPUID leaf 1 EAX `0xB06A2`, hypervisor bit set, microcode unknown.
This is one hosted machine observation, not a physical Intel/AMD matrix.
The existing scratch campaign also passed 21 cases and seven controls in
`target/x86-native/stack-semantics-regression/`, checking compatibility with the
driver's added optional mask parameter.

The semantic selector retains production decoder errors and exact suffixes,
and attaches effects only after equality with a production encoder. Its
success soundness theorem does not establish full ISA decoding or a complete
machine step. Kernel-checked canonical fixtures cover all 6 families × 2 widths
× 16 destination × 16 source registers, plus unsupported/truncated/noncanonical
cases. Register transfer laws remain separate from fetch, RIP, privilege,
interruptions, memory, faults and call-provider realizations. Formal citation
attachment for the new definitions remains visible ledger debt.

Independent semantic review approved the actual implementation, fixtures,
corpus, mask checks, ledger classification and documentation with no remaining
findings. It re-elaborated both new library modules, both focused fixtures and
`LedgerAudit`, built those five modules, and reproduced 994/0 with 12 controls
in `target/x86-native/semantics-independent-review/`. The retained source hashes
match the reviewed semantics, corpus and runner. The author also reran 994/0 in
`target/x86-native/semantics-parent-confirmation/`. Full library/test builds and
the trust audit passed (75 named declarations, eight executable modules).
Source-input validation re-elaborated 16 embedding modules; spike-source and
documentation-link checks also passed.
The six exhaustive decoder fixture theorems and decoder soundness theorem use
only the accepted `propext` and `Quot.sound` axioms.

## Separate legacy BSF finding

`Tests/ISA/X86/MachineProbes.lean`, `bsfZeroSource`, requires RAX preservation
when the source is zero. The instruction's destination is architecturally
undefined for this input; preserving it on one processor does not establish
portable required behavior. The old row's `isException` label does not turn
that expectation into a model prediction. This row is excluded from the new
campaign, and the finding has been sent to `spikes` for separate disposition.

The eventual legacy fix should retain defined ZF behavior and mask the undefined
destination, or retain destination observations as unjudged data. A narrower
target-specific predicate would require an explicit supported profile and source
authority. Do not adjust `writeBack` merely to fit this historical observation.
