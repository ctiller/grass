# Target seams

Status: architecture, 2026-09-10. This document owns the interfaces through
which every platform, ISA, artifact format, and graphics API plugs into the one
certificate chain (`Grass/Certificate.lean`, `Grass/Verify/VerifiedProgram.lean`).
It replaces the program-shaped Win32/WriteFile machine tier that the previous
build accumulated. The rule that made that tier unacceptable still holds and
now has a mechanical shape: **nothing above a seam may name anything below
it, and nothing below a seam may name a program, a spike, or another target.**

## The layers

```text
SpecProcess (precious, resource-indexed)                 Grass/Semantics, Grass/Spec/*
   ↑ PortableProgramCertificate: behavior over spec audit events
Service.Domain / Service.Event                           Grass/Service/Domain.lean
   the portable vocabulary of external requests (console, heap, clock, sockets,
   window, gpu, ...) and typed responses. Every spec facade's AuditEvent is built
   from Service.Event, with `silent` for internal steps.
   ↑ driver/provider refinements: portable I/O → platform-realized I/O
Target.Machine  (GENERIC)                                Grass/Target/Machine.lean
   RelationalSystem over Service.Event built from ONE ISA step function and ONE
   Platform native-call mapping. Adequacy of this system is memory/control safety.
   ↑ machine refinement: proved per program by the assembly verifier
Target.ISA      (per ISA: X86_64, AArch64, Wasm32)       Grass/Target/ISA.lean
Target.Platform (per platform: Win32, Linux, WASI, BareMetal)  Grass/Target/Platform.lean
Target.Artifact (per format: PE, ELF64, WasmModule, FlatImage) Grass/Target/Artifact.lean
   instantiates Certificate's `ArtifactFormat` with a real writer, a real
   reader, the round-trip theorem, and `loadedBehavior := Machine.behavior`.
Target.Device   (per API: Vulkan+SPIR-V, WebGPU+WGSL)    Grass/Target/Device.lean
```

The certificate composition is unchanged. What is new is that the machine tier
and the artifact tier are **one construction each**, parameterized by the seam
records, so a new ISA, platform, or format supplies its record and inherits
every generic theorem (`ISA.decodeAll_encodeAll`, `Machine.*`, `Artifact.*`)
instead of re-proving its own copy.

## The seam records

- `Grass.Target.ISA` (`Grass/Target/ISA.lean`): `Instr`, canonical
  `encode`/`decode` with `decode_encode`, the assembled `Raw` program, the
  whole machine `State` (memory included), `initial`, and `step` returning
  `internal | external call resume | halted | fault`. A native call carries the
  ISA-level view (registers, stack, memory reader) the platform decodes; a
  native return carries the ISA-level effect (result registers, memory writes).
  The ISA never knows what a call means.
- `Grass.Target.Platform` (`Grass/Target/Platform.lean`): the environment
  (arguments, stdin, console availability, ...), how it fills the ISA's
  `InitialContext`, how a `NativeCall` decodes to a `Service` request, which
  responses the environment allows and how the environment evolves, and how a
  response is encoded as a `NativeReturn`.
- `Grass.Target.Machine` (`Grass/Target/Machine.lean`): the generic
  `RelationalSystem` and `ProgramBehavior`. Faults and undecodable calls are
  stuck states; a stuck reachable state makes `Adequate` unprovable.
- `Grass.Target.Artifact` (`Grass/Target/Artifact.lean`): a `Format` is a
  writer, a reader, and the round-trip theorem over `isa.Raw`; the generic
  construction turns it into Certificate's `ArtifactFormat spec`.
- `Grass.Target.Device` (`Grass/Target/Device.lean`): shader languages and
  graphics APIs. A shader module is a second artifact embedded in the host
  program's data; the API is a `Service.Domain` family.

## What the generic tier already proves

- `ISA.decodeAll_encodeAll`: whole-code decode of a canonical encoding, from
  each ISA's single-instruction `decode_encode`.
- `Machine.stuck_of_fault`, `Machine.stuck_of_undecoded`: the two ways a
  program gets stuck, so an ISA fault or an unrealized platform call is a
  visible refusal, never silent progress.
- `Machine.adequate_of_invariant` (`Grass/Target/Safety.lean`): the
  certificate's `Adequate` obligation for the machine tier follows from an
  inductive invariant that holds initially, is preserved by every step, and
  excludes stuck states, plus platform input coverage. A block-structured
  assembly verifier produces exactly that invariant: block contracts at
  labels, preserved between them. This is the theorem that makes per-program
  proof work target-independent.
- `toArtifactFormat`: `loadExact` for every container format from its
  `read_write` law alone.

## Rules for every contributor (agents included)

1. Do not edit `Grass/Target/*.lean` or `Grass/Service/Domain.lean`. If the
   seam cannot express what your target needs, stop and report the exact
   missing field or law; do not route around it.
2. No spike, program, payload, label, or register-allocation knowledge below
   the machine seam. A file under `Grass/ISA`, `Grass/Platform`,
   `Grass/Artifact`, `Grass/Shader` that mentions Hello, sort, gzip, HTTP,
   cube, `payload`, `write_head`, or a fixed frame layout is wrong.
3. Every construction must serve the second and third consumer: an ISA record
   for x86 must be shaped so AArch64 and Wasm fill the same record; a platform
   record for Win32 must be shaped so Linux, WASI and bare metal fill it.
4. Correctness is by proof. Lean tests exist only to compare a model with the
   real world (a native corpus, a real loader, a real GPU validator). A test
   that checks a theorem-shaped fact is a theorem that has not been written.
5. No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, `implemented_by`,
   `extern`. `warningAsError` is on: no unused variables or simp arguments.
6. Build only the modules you own: `lake build Grass.ISA.X86.Target`, never a
   bare `lake build`. Do not run git; the integrator commits.
7. Review asks one question of a typechecked theorem: what bad thing does the
   statement still allow? Vacuous premises, definitions that admit the
   failure they claim to exclude, and quantifiers over the wrong set are the
   findings. A typechecked proof with no banned construct is not re-read.

## Spare parts

`../gasm` (same Lean toolchain) reached emitted executables for x86-64,
AArch64 and Wasm on Windows, Linux, WASI and bare metal: encoders, decoders,
round-trip gates, PE/ELF/Wasm writers, syscall/WASI/Win32 ABIs, a UART
device, and a verified zlib/gzip. `../wsc` is older. Grass branches listed in
`docs/DRIVER_HANDOFF.md` hold AArch64, ELF, SPIR-V and bare-metal slices. Port
ideas and code into the seam shapes; do not merge their architectures.
