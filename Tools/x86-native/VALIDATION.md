# Initial campaign and open finding

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
