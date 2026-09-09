# Successful scratch-stack effects

This extension follows the prologue priority from `spikes` and the successful
effects boundary reviewed with the memory-model owner. The existing register
campaign is unchanged. From Git Bash on x86-64 Windows:

```bash
bash Tools/x86-native/build.sh
python -O Tools/x86-native/run_stack.py --worker target/x86-native/windows.exe --output target/x86-native/stack-campaign
```

The new Lean corpus generates exact public PUSH, FrameAllocation and
SourcePrologue body bytes. Layout and unwind values supply the expected RSP
decrease; predicted PUSH bytes are an explicit test-local little-endian
reference using the initialized source register. PUSH RSP stores the RSP value
before that push's decrement. This checks the physical connection to the
generated prologue, not a complete Grass memory transition or a proof of native
semantics. SUB/allocation must preserve every observed scratch byte. Arithmetic
flags remain unchecked; pure PUSH cases check arithmetic flag preservation.

## Observed memory and stack switching

Each child reserves a separate scratch mapping: 64 KiB committed read/write,
bounded by two uncommitted no-access pages. Every committed byte is initialized
with `(offset*37 + 0xA5) mod 256` and captured before execution. Entry RSP is
`scratchBase + 65536 - 120`, eight modulo sixteen as required at Win64 function
entry. Corpus deltas are bounded by 8192 bytes, all expected writes are checked
inside the committed range, and all expected ranges are nonwrapping.

The code and two scratch-stack bookkeeping slots use three distinct pages of
another allocation: executable/read-only code, read/write target-RSP output,
and a read-only host-RSP restore source. Native setup and the
comparator check nonoverlap of code, harness data, scratch including boundary
pages, and the original thread stack. `GetCurrentThreadStackLimits` supplies
the host stack bounds; the entry exception checks its original RSP is inside
them before saving it and switching to scratch. The restore source becomes
read-only before target execution; a separate original-RSP variable supplies
the exact completion check rather than trusting a mutable restore slot.

The body is followed by exactly fourteen harness bytes:

```asm
mov [rip + target_rsp_slot], rsp
mov rsp, [rip + host_rsp_slot]
```

Only then does the terminal INT3 run. These MOVs preserve the remaining GPRs
and flags, and the first captures target RSP before the second restores the
host RSP. The context handler verifies restoration and substitutes the saved
target RSP in its observation. It copies the entire 64 KiB scratch region before
printing the observation, while using the host stack. The report includes the
suffix bytes and mapping addresses; the comparator independently checks both
RIP-relative displacement targets. Body bytes remain separate from this suffix.
Successful PC/RIP offsets must equal body length plus fourteen.

This avoids assuming a separate VEH handler stack or excluding an unexplained
exception-delivery footprint from comparison. If a body faults unexpectedly,
Windows might write an exception frame on scratch. Such cases fail and carry
no judged memory snapshot. Exceptions in the suffix are harness errors, not
instruction faults; every post-start exception outside the harness terminates
the child explicitly, preventing another handler from resuming it into agreement.
There is no recovery-and-compare path and no fault, interruption or partially
completed instruction certification.

## Protocol and limits

The stack TSV columns are label, exact body hex, decimal RSP decrease, pushed
GPR indices in execution order (`-` if none), preserved flags (`yes` or `-`),
and prediction basis. The existing encoding-order register list applies.
Run inputs are distinct fixed 64-bit values, recorded in the host report.
The coverage fingerprint pins every TSV field except emitted bytes, including
the expected RSP decrease and pushed-register footprint. This prevents a dropped
write from being accepted by simultaneously weakening its expected footprint.
Encoder-only changes reach the hardware comparator rather than a digest gate.

Successful JSON observations add a `stack` object with base, size, entry offset,
host stack bounds, original host RSP, code allocation base, page size, suffix
hex, and full before/after hex snapshots. Other observations have unjudged or
absent memory. The parent retains every row with its expectations and differences.
Allocation/protection failures, malformed responses, timeouts and faults fail.

Controls include NOP with every scratch byte unchanged, a deliberately wrong
RSP decrease, PUSH RSP, omitted/wrong expected stores, corrupted suffix
relocations, and a changed byte far from the expected writes. The ordinary
870-case campaign exercises the unchanged v1 path.
Final-state comparisons cannot reveal writes outside the declared region,
canceling intermediate effects, or every incorrect instruction-boundary choice.
Only trusted generated bodies are admitted; process isolation contains failures
but is not a security sandbox. No aliases, shifted mappings, permissions-as-Lean
authority, callee stack after CALL, or physical AMD/bare-metal coverage is claimed.

Sources for the harness are Microsoft's
[VirtualAlloc](https://learn.microsoft.com/en-us/windows/win32/api/memoryapi/nf-memoryapi-virtualalloc),
[VirtualProtect](https://learn.microsoft.com/en-us/windows/win32/api/memoryapi/nf-memoryapi-virtualprotect),
and [GetCurrentThreadStackLimits](https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-getcurrentthreadstacklimits).
The instruction reference is Intel SDM Volume 2B, PUSH/SUB/MOV entries, available
through the [SDM collection](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).
The native adapter now requires Windows 8 or later for stack-limit discovery.
These validation sources do not replace Grass's pinned ISA citation ledger.
