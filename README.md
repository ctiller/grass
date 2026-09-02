# Grass

Grass is a high-level, extensible assembler for building programs whose emitted
machine code is proved safe and equivalent to a Lean specification.

> **Project status:** early foundation implementation and spike corpus. Grass
> provides a minimal compiling foundation API, but not yet a buildable
> assembler, verified executable, or supported release. The Lean files under
> `Spikes/` remain reviewed authoring fixtures and are not expected to compile.

Its target is large, long-lived systems—games, databases, operating systems,
compilers, graphics and storage engines—not merely small verified examples. The
spikes pressure-test one compositional architecture intended to scale across
those systems. See [docs/VISION.md](docs/VISION.md).

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
Constructive feasibility arguments for the disputed proof machinery are in
[docs/PROOF_FEASIBILITY.md](docs/PROOF_FEASIBILITY.md).
The comment-free expected Lean source for all five design spikes is in
[Spikes/README.md](Spikes/README.md). The contract relating those authored files
to the annotated spike documents and generated expansions is
[docs/SPIKE_AUTHORING.md](docs/SPIKE_AUTHORING.md).

Cross-provider implementation agents coordinate through the orphan-branch
protocol in [docs/AGENT_BUS.md](docs/AGENT_BUS.md), with exact event types in
[docs/AGENT_BUS_SCHEMA.md](docs/AGENT_BUS_SCHEMA.md). Product changes follow
[docs/AGENT_REVIEW.md](docs/AGENT_REVIEW.md): an author nominates a distinct
reviewer, and that reviewer—not the author—reviews and cleanly merges a selected
snapshot of the named product branch.

## Repository validation

Build and check the foundation API and its transitive trust closure with:

```powershell
lake build
lake build GrassTests
pwsh ./audit-trust.ps1
```

The trust script generates a temporary audit import over every library and test
module. Its Lean command discovers every concrete `VerifiedProgram` producer
from the normalized elaborated result type, then checks its exact fully
qualified declaration and transitive axiom closure. Auditing only the generic
composition theorem would not inspect axioms used to construct a concrete
certificate.

The corpus checks verify that annotated spike documents and their comment-free
authored Lean views remain exact:

```powershell
pwsh ./check-spike-sources.ps1
pwsh ./check-doc-links.ps1
```

The last two commands are corpus consistency checks, not compilation or proof
checking. The implementation ratchet remains documented in
[docs/IMPLEMENTATION_RATCHET.md](docs/IMPLEMENTATION_RATCHET.md).

## Contributing and security

See [CONTRIBUTING.md](CONTRIBUTING.md) before proposing a change. Suspected
vulnerabilities or sensitive disclosures must follow
[SECURITY.md](SECURITY.md), not a public issue or agent-bus event.

## License

Grass is licensed under the [Apache License, Version 2.0](LICENSE). Files
authored for Grass on this development system are copyright Craig Tiller; see
[NOTICE](NOTICE).
