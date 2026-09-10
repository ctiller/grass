# Driver handoff — 2026-09-10

**No spike is complete.** This session replaced the program-shaped Win32
machine tier with target-generic seams and landed the first instances across
the matrix. Start with [TARGET_SEAMS.md](TARGET_SEAMS.md).

## Landed on main this session (`ae5c8350`..`b57f7e2c`)

- Seams: `Grass/Service/Domain.lean`, `Grass/Target/{ISA,Platform,Raw,Machine,
  Artifact,Device,Safety}.lean`. `Machine.adequate_of_invariant` reduces the
  certificate's machine-tier adequacy to an inductive invariant for every
  ISA and platform; `toArtifactFormat` gives `loadExact` from a format's
  `read_write`.
- Spec root: `Grass.SpecProcess resources` (`Grass/Spec/Root.lean`) over
  `Grass.SpecRoot`; facades `Grass.Spec.{Console,Resource,Grammar,Graphics}`.
  `Spikes/1_Hello_World/Spec.lean` elaborates unchanged.
- ISAs: `Grass.ISA.Wasm.isa` (104 instructions, full round trip, step),
  `Grass.ISA.AArch64.isa` (8 families), `Grass.ISA.X86.isa` (33 register-direct
  and immediate/rel32 families with round trip; no memory-operand addressing
  yet: `[base+disp32]`, `[rip+disp32]`, `lea`, `call qword ptr [rip+disp32]`
  were removed because their ModR/M round-trip proofs did not close; the
  machinery remains in `Grass/ISA/X86/Target/Encode.lean`).
- Platforms: hosted environment (`Grass/Platform/Hosted`), bare-metal UART
  device, and wired records for WASI/Wasm, Linux x86-64 and AArch64,
  Win32 x86-64 and bare-metal AArch64. A concurrent session added
  `Grass/Target/Checkpoint.lean` (`adequate_of_checkpoints`: bounded progress
  between checkpoint states, the shape a block verifier produces) and deleted
  the legacy Win32/WriteFile machine tier (20k lines).
- Devices: `Grass.Shader.SPIRV.language`, `Grass.Shader.WGSL.language`
  (a canonical prefix token text with a proved round trip, not WGSL concrete
  syntax a browser accepts), `Grass.Device.Vulkan.api`, `Grass.Device.WebGPU.api`.
- Formats: Flat boot image and ELF64 (`read_write` proved); PE adapter over
  the existing round-trip writer not yet written; Wasm module format not yet.
- Models: gasm's fixed-Huffman DEFLATE/gzip (`Grass.Std.Zlib.Fixed32K`,
  proofs ported verbatim) and a stable bottom-up merge sort
  (`Grass.Std.Sort.Stable`).
- Front end: `Grass.Assembly.Syntax` parses the spikes' `asm_source` surface
  into a target-generic AST with a decidable well-formedness check.
- `Tests/` reduced to 12 model-versus-real-world files.

## Open findings (adversarial review, 2026-09-10)

1. `MeetsAllSpecificationTheorems` is vacuous when a spec declares no
   liveness demand; require a terminating demand or reject empty lists.
2. No spike yet applies `adequate_of_invariant` to a real program; the seam
   has no end-to-end consumer.
3. `Console.writeLineContract` writes the logical text without a newline while
   the legacy `TargetProjection` renders CRLF; retire the legacy model.
4. Seam gaps: `NativeReturn` needs a map-region effect (Linux `mmap`, heap
   growth); `Platform.entry` cannot see the module to resolve WASI `_start`;
   bare metal needs MMIO/port I/O reported as `external` by the ISA.
5. `Grass/Platform/Linux/Target/AArch64.lean.pending` must be re-typed
   against the BitVec register view and re-enabled.

## Next steps

- Add the x86-64 memory-operand families (prove ModR/M round trips through
  named `ofByte_toByte` lemmas by rewriting, never `cases <;> rfl`), then the
  PE adapter over the existing round-trip writer and the Wasm module format;
  that closes the first Hello World chain candidate.
- Print and parse real WGSL concrete syntax over the WGSL AST.
- Lower `Grass.Assembly.Syntax.Source` to each ISA's `Instr` with label
  resolution and frame layout, producing `Sectioned`; then the block-contract
  verifier that discharges `Machine.Invariant`.
- Add authored target variants under `Spikes/` (`ProgramAarch64.lean`,
  `ProgramWasm.lean`, Linux/WASI/bare-metal variants) as approved by Craig.
- Delete the remaining program-shaped `Grass/Assembly/Source*` modules once
  the lowering from `Grass.Assembly.Syntax` replaces them.
- Linux execution of emitted ELF images can use the `polonius` host over ssh.
