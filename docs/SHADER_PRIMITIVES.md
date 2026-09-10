# Shader composite primitives

This work is the first bounded shader slice for the cube acceptance surface in
[Spike 5](SPIKE_5.md). The authored vertex and fragment modules extract vector
components and construct vectors. These operations can be checked before the
floating-point arithmetic, full module validator, and graphics provider exist.

SPIR-V lives under `Grass/ISA/SPIRV/`; WGSL lives under
`Grass/Shader/WGSL/`. WGSL is a shader language, not a machine ISA. Both targets
must preserve the selected component and constructor operand order. The scalar
value model at this boundary does not supply floating-point arithmetic or a
claim about NaN payloads, rounding, or physical register bits.

The SPIR-V target remains the cube's SPIR-V 1.5 / Shader selection. The inspected
Khronos authority is Unified 1.6 revision 7, whose composite instruction entries
cover these existing instructions; using that document does not upgrade the
selected module version. WGSL references the dated 31 August 2026 W3C Candidate
Recommendation Draft. These source choices do not select a WGSL GPU provider.
The opcode/operand cross-check also uses Khronos SPIRV-Headers tag `1.5.4`,
whose core grammar declares SPIR-V 1.5 revision 4.

## Implemented interfaces

- [SPIR-V composite family](../Grass/ISA/SPIRV/Composite.lean): exact instruction
  words, an explicit type/ID context, a checked prefix decoder, and operand-local
  component transfer. Only one-level vector extraction and four-scalar vector
  construction are in this family.
- [WGSL composite family](../Grass/Shader/WGSL/Composite.lean): a bounded token
  parser for `vec4<f32>` with four indexed vector-value operands, typed lane
  checking, and a canonical text renderer using generated names such as `v0`.
  The input operands are `vec2/3/4<f32>` values. There is no text lexer or proved
  text round-trip. An enclosing module must establish that `vec4` and `f32`
  resolve to the built-ins and that the operands resolve to these values.
- [Common component connection](../Grass/Shader/CompositeConnection.lean):
  `checked_construct4_agrees` connects the decoded SPIR-V words and parsed WGSL
  tokens under explicit correspondence of the four input values. It does not
  derive an identifier-to-ID mapping or assert that an arbitrary translation
  preserves semantics.

The corresponding [SPIR-V tests](../Tests/ISA/SPIRV/Composite.lean),
[WGSL tests](../Tests/Shader/WGSL/Composite.lean), and
[connection trust audit](../Tests/Shader/CompositeConnection.lean) are focused
checks of this boundary. The authored cube sources are unchanged.

## Connection boundaries

An instruction decoder or expression checker establishes only its stated local
typing and transfer laws. It does not establish a complete shader module's
entry point, interface, dominance, control flow, memory effects, or execution.
Likewise, round-trip serialization is not functional shader refinement.
The local SPIR-V context does not parse a module header or enforce its ID bound.
The complete module checker must also establish that the supplied context
faithfully describes its definitions. Local value-ID freshness does not prove
module-wide ID uniqueness or dominance.

The Vulkan consumer uses an array of 32-bit words. SPIR-V instruction streams
use lists of 32-bit words for prefix/suffix proofs; a consumer must preserve the
exact list when converting to an array. The eventual complete connection must
retain the emitted words, shader-create byte count and pointer range, returned
module handle, selected pipeline stage and entry name, bindings, and execution
proof. WGSL has a separate source/provider connection and is not implicitly
consumed by native Vulkan.

The full authored cube remains an acceptance fixture. Missing obligations
include module validation and execution, shader I/O and storage, floating
rotation refinement, graphics synchronization, provider assumptions, and the
final specification-to-artifact certificate. The primitive slice must not be
reported as closing them.

## Predecessor reuse

The predecessor at `C:\Users\craig\wsc` contains instruction layouts, a decoder,
a local Khronos grammar, and differential validation tools. These are candidates
for selective reuse, not authority for a full execution model. Its
`SPIRV/Program.lean` executes the instruction array linearly, and its
`SPIRV/Instr/Core.lean` writes an integer zero for `OpUndef` and `OpConstantNull`
without consulting the result type. Neither behavior supplies the demanded
typed shader execution proof. See the source authorities in
[the reference register](REFERENCES.md#shader-composite-primitives).

## Validation at the initial checkpoint

Base: `8fc533af`. The focused command passes with the repository's strict Lean
options:

```text
lake build Grass.Shader.CompositeConnection Tests.Shader.CompositeConnection Tests.ISA.SPIRV.Composite Tests.Shader.WGSL.Composite
```

The runtime dependency audits cover 504 declarations for each SPIR-V seed,
406 for the WGSL checker, and 803 for the common theorem. The printed semantic
and decoding proof roots depend only on the allowed `propext` and `Quot.sound`
axioms. Independent review covered both models, the connection, the regression
tests, and these evidence boundaries; the discovered value/type ID freshness
holes and unchecked identifier spelling were corrected before acceptance.

The authored-spike mirror and relative documentation-link checks pass. The
baseline's `Tests/Memory/Spike1Reference.lean:93` still references the removed
`Grass.ABI.Win64.spike1FrameLayout`; a separate sequential build of that target
fails there. This prevents claiming a green full repository build or
source-input gate. No shader change repairs or depends on that fixture.
