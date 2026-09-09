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

The intended contract is safe emitted code matching `spec`. Authors prove
properties such as termination, responsiveness, fairness, and latency about
the specification. Those proofs are separate from the lowering certificate:
the compiler proves safety and semantic correspondence, not a new certificate
for each author theorem. Correspondence must account for divergence and waiting
and connect the proofs to the exact emitted bytes.

`emitProgram v` produces an executable artifact for `v`'s selected platform.
The current minimal `VerifiedProgram` certificate composes exact adjacent
behavior refinements, terminal-trace acceptance, a terminal-or-infinite
continuation available from every finite frontier, selected demand
certificates, and the connection between the
modeled loaded artifact and the bytes that were emitted. This is a non-stuck
may-completion property, not universal termination or liveness: a relational
system may still admit other infinite executions. The current forward-inclusion
proof is not yet the full abstract-behavior equivalence required to transport
arbitrary authored properties; in particular it does not reflect all portable
choices or possible executions. Concrete memory, concurrency,
ABI, and other domain guarantees become part of the result only when a domain
layer exposes them as explicit demands and supplies their certificates.

The first end-to-end target is a Win32 x64 PE32+ Hello World using
`GetStdHandle`, `WriteFile`, and `ExitProcess`, with ASLR, derived imports,
standard section permissions, and unwind metadata.

Grass is a clean-slate successor to experiments in `gasm` and `wsc`. Their code
and ideas are spare parts, not compatibility constraints.

Start review at [docs/README.md](docs/README.md).
For code and implementation evidence, start at the
[endpoint index](docs/ENDPOINT_INDEX.md); use the
[validation command map](docs/CHECKS.md) to find the appropriate checks.
Constructive feasibility arguments for the disputed proof machinery are in
[docs/PROOF_FEASIBILITY.md](docs/PROOF_FEASIBILITY.md).
The comment-free expected Lean source for all five design spikes is in
[Spikes/README.md](Spikes/README.md). The contract relating those authored files
to the annotated spike documents and generated expansions is
[docs/SPIKE_AUTHORING.md](docs/SPIKE_AUTHORING.md).

Development proceeds one spike at a time, beginning with the existing Hello
World source. The Lean correctness specification and prose implementation brief
are maintained inputs; implementation is rebuilt beneath them. See
[docs/VISION.md](docs/VISION.md) and [CONTRIBUTING.md](CONTRIBUTING.md).
Changes receive independent peer review under [docs/REVIEW.md](docs/REVIEW.md).
The former agent coordination system and implementation plans are retired; Git
history and the retained agent branches preserve their spare parts.

## Repository validation

Build the foundation API without warnings (so `sorry` is an error), audit every
concrete `VerifiedProgram` producer, and check the named public theorem roots
with:

```bash
lake build
./audit-trust.sh
```

The validation scripts require Bash and Perl. They run on Linux and in Git Bash
on Windows.

The trust script generates a temporary audit import over every library and test
module. Its Lean command unfolds even irreducible result aliases to discover
concrete `VerifiedProgram` producers and audits every declaration originating
in those project modules, including declarations outside the `Grass` namespace.
It also follows the transitive dependency closure of certificate-bearing and
emission-consuming declarations across arbitrarily named imported modules, then
follows their downstream runtime dependencies to reject unverified
`implemented_by` and `extern` replacements. Participating module cohorts and
persisted non-meta compiler dependency modules keep scoped `csimp`
substitutions covered after their attribute state expires. Finally, it checks
configured public theorem roots as an explicit manifest. The build's
warning-as-error setting independently rejects admission mechanisms.

The corpus checks verify that annotated spike documents and their comment-free
authored Lean views remain exact:

```bash
./check-spike-sources.sh
./check-doc-links.sh
```

The last two commands are corpus consistency checks, not compilation or proof
checking. The implementation ratchet remains documented in
[docs/IMPLEMENTATION_RATCHET.md](docs/IMPLEMENTATION_RATCHET.md).

## Contributing and security

See [CONTRIBUTING.md](CONTRIBUTING.md) before proposing a change. Suspected
vulnerabilities or sensitive disclosures must follow
[SECURITY.md](SECURITY.md), not a public issue or discussion.

## License

Grass is licensed under the [Apache License, Version 2.0](LICENSE). Files
authored for Grass on this development system are copyright Craig Tiller; see
[NOTICE](NOTICE).
