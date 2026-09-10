# Linux syscall boundary probes

This auxiliary campaign compiles a native C program and compares an explicit architecture syscall instruction with libc's `syscall(2)` wrapper. The x86-64 path uses `syscall`; the AArch64 path uses `svc 0`. It records bounded small write and read observations, the raw `-EBADF` return versus the wrapper's `-1`/`errno` convention, and parent-observed `exit_group(37)` termination.

Run on Linux from the repository root:

```bash
python3 probes/linux/run.py
```

Results are written to `.lake/linux-probes/results.json` with source, runner, and binary SHA-256 hashes plus kernel, architecture, compiler, timeout, malformed-record, and mutation-control results. These native C programs are neither Grass-emitted artifacts nor proof authority. They are bounded observations from one kernel/CPU/compiler combination. The JSON report lists explicit gaps, including unobserved AArch64 on an x86-64 host, partial completion, interruption, concurrency, pointer faults, and arbitrary failure effects.
