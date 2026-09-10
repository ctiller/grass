# Bounded SPIR-V source witness

`Grass/ISA/SPIRV/SourceModule.lean` connects an exact standalone `spirv_asm`
command to its parsed statements and emitted module words. Its `Checked command`
retains three equations: shared capture succeeded on `command`, the complete
captured body parsed to the retained statements, and `Module.compile` produced
the retained output from those statements. Entry metadata comes from that same
compilation. `Output.words : Array (BitVec 32)` is the canonical supplier artifact;
Vulkan can use that field directly as its `Request.words`. The instruction codecs
use lists internally, with one array construction at module completion.
Consumers connect `output.words` to their own actual request words;
the witness supplies no provider-memory or Vulkan execution fact.

## Shared source capture

`Grass/Assembly/SourceInput.lean` owns the command scanner. Both `asm_source`
and `spirv_asm` use its marker-parameterized implementation; existing assembly
entry points delegate with `asm_source`. Capture still requires a standalone
declaration. The syntax-offset entry point recomputes and compares offsets.

Named selection is generic test tooling in `Tests/Assembly/SourceSelection.lean`.
Its result retains the original file, half-open range, and exact drop/take
equation. `Tests/ISA/SPIRV/SourceModule.lean` reads the authored cube file and
selects its two declarations; it maintains no copied shader body. File embedding
creates data, not proof authority. Re-elaborate the fixture after authored source
changes, as with the existing source-input fixtures.

## Evidence boundaries

The parser accepts a bounded assembly spelling with character offsets, including
instructions sharing a line and operands spanning lines. Unsupported characters,
quoted escapes, and semicolon comments are refused. Opcode and operand meanings
belong to the module checker. Statement framing proves only a range within the
captured body; it is not a separate lexical correctness theorem.

The module checker assigns IDs from actual declarations and checks its supported
instruction family against the resulting type/value environment, including
single-block instruction placement and supported decoration applicability.
The output retains type declarations, decorations, and typed interface records
with pointer type, storage class, and pointee. Composite
operations reuse the existing [composite primitive](SHADER_PRIMITIVES.md).
The checked compilation equation identifies the producer's result; it is not a
proof of complete SPIR-V validation, control-flow semantics, floating-point
execution, Vulkan environment conformance, or rendered output.
In particular, complete logical-section ordering before the function,
duplicate/conflicting decorations, and all environment-specific interface and
layout rules are not checked by this pass. Compilation success must not be
described as complete SPIR-V validity.

The decimal literal encoder uses integer arithmetic and accepts a candidate only
when its sign and decoded binary32 rational magnitude exactly match the parsed
decimal. `float32Exact?_sound` proves that acceptance property. No rounding or
completeness claim is made. Exponent notation and non-finite literals are outside
the supported spelling. See the [source register](REFERENCES.md#shader-composite-primitives).

WGSL provider selection and Vulkan API/provider receipts remain separate work.
This source witness does not change the WGSL primitive or select a WebGPU backend.

## External validation

On 2026-09-09, `Tests/ISA/SPIRV/ExportSource.lean` selected the two declarations
from the original authored file, checked them, and serialized their actual output
arrays for Khronos SPIRV-Tools `v2026.4.rc1-4-ge265f557`. Both passed
`spirv-val --target-env vulkan1.2`: vertex 471 words with ID bound 86, fragment
102 words with ID bound 18. These are external regression results, not Lean proof
authority or GPU execution evidence. The tool was obtained from Khronos's
[Windows continuous build](https://storage.googleapis.com/spirv-tools/artifacts/prod/graphics_shader_compiler/spirv_tools/windows-vs2022-amd64-release/continuous/202/20260909-124536/install.zip).

Reproduce the export from the repository root:

```text
lake env lean --run Tests/ISA/SPIRV/ExportSource.lean Spikes/5_Spinning_Cube/Assembly.lean cubeVertex vertex.spv
lake env lean --run Tests/ISA/SPIRV/ExportSource.lean Spikes/5_Spinning_Cube/Assembly.lean cubeFragment fragment.spv
spirv-val --target-env vulkan1.2 vertex.spv
spirv-val --target-env vulkan1.2 fragment.spv
```

## Reviewed checkpoint

Independent agent review approved the complete source slice and its final fixes.
Review required shared function-body placement guards, deferred decoration
checks, a retained original-file witness, discriminating exact-error tests, and
an independent exact-word fixture. Those changes are included. The acceptance
and word fixtures use executable assertions as regression evidence; the general
source equations, framing theorem, and literal soundness theorem remain Lean
proofs. No evaluator-backed axiom is introduced.

Validation on the merged `baa2094d` baseline, with the reviewed docstring repairs:

- Full library build: 665 jobs passed. Final changed test targets and the
  source-freshness gate's 640-job test build passed.
- Source freshness: both embedding modules re-elaborated successfully.
- Trust audit: 75 named declarations and nine executable test modules passed;
  the project scan covered 42,090 declarations. The source-check runtime audit
  covered 1,851 declarations. Printed proof roots use only the repository's
  allowed `propext`, `Classical.choice`, and `Quot.sound`.
- Docstring, observation-coverage, authored-spike mirror, relative-link, and
  whitespace checks passed.
- Both actual shader word arrays passed the external validation described above.

Vulkan adoption is pending the consumer's connection of this exact output array
to its request and existing provider receipt. This checkpoint does not claim
that integration is complete.
