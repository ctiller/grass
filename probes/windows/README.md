# Windows validation samples

Run the Grass-authored Hello World sample from the repository root on Windows:

```powershell
./probes/windows/run-grass-hello.ps1
```

This emits the unchanged Grass source through the production source linker and
PE writer, launches the binary with a timeout, and compares exact stdout bytes
and process exit status. Results and binary hashes are recorded under
`.lake/grass-windows-probes`. See the [initialization checkpoint](../../docs/WINDOWS_LOADER_INITIALIZATION.md)
for checked model facts, the first native result, and open correspondence work.

## Auxiliary API campaign

Grass-authored probe programs use the production PE entry, imports and emitter. This C/Python campaign is retained as auxiliary comparison evidence and will not be expanded. [Lean semantic cases](../../Tests/Platform/Win32ProbeCases.lean) exercise accepted and rejected API outcomes; those individual cases do not yet emit runnable Grass programs.

This directory contains an external validation harness for the bounded synchronous `WriteFile` model. It compiles `writefile.c` with the installed MSVC x64 tools, runs each case in a separate process with a timeout, and writes `.lake/windows-probes/results.json`.

These binaries are native C programs. They are not emitted by Grass, do not test Grass code generation, and are not proof authority. They record observations from one OS, CPU, compiler, source hash, and binary hash with which to challenge the model. Generated files stay under `.lake` and should not be committed.

Run from the repository root on Windows:

```powershell
python probes/windows/run.py
```

The campaign covers a small successful write, a zero-length write, an invalid handle, a broken anonymous pipe, and a large nonblocking named-pipe write. The comparator checks successful writes as bounded observed prefixes. It makes no general claim about effects after failure; only the two purpose-built failure fixtures check their observed zero count. Mutated success records are negative controls for excessive counts, non-prefix bytes, and a reported/observed count disagreement.

The `PIPE_NOWAIT` fixture may return success with zero bytes for a nonempty request. This is retained as a zero-progress observation, but does not cover strict partial success (`0 < count < requested`). Producing that outcome reliably for synchronous `WriteFile` needs a separately justified fixture; its absence is neither a model failure nor exhaustive API coverage. This run observed error 232 for the broken-pipe fixture; it is an observation, not a narrowed error guarantee. Cancellation, interruption, concurrency, pointer-rights faults, and arbitrary failure effects remain outside this bounded campaign.
