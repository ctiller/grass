# Grass

Grass is a high-level, extensible assembler for building programs whose emitted
machine code is proved safe and equivalent to a Lean specification.

The public goal is deliberately simple:

```lean
emitProgram : VerifiedProgram spec → ByteArray
```

`emitProgram v` produces an executable artifact for `v`'s selected platform.
The `VerifiedProgram` certificate establishes functional refinement, memory and
concurrency safety, progress, ABI correctness, obligation handling, and the
connection between the program that was proved and the bytes that were emitted.

The first end-to-end target is a Win32 x64 PE32+ Hello World using
`GetStdHandle`, `WriteFile`, and `ExitProcess`, with ASLR, derived imports,
standard section permissions, and unwind metadata.

Grass is a clean-slate successor to experiments in `gasm` and `wsc`. Their code
and ideas are spare parts, not compatibility constraints.

Start review at [docs/README.md](docs/README.md).

