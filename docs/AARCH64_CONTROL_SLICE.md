# AArch64 control instruction slice

This bounded implementation starts from `8fc533af`. It supports the parallel
spike work through reusable instruction semantics, not a program-specific recipe.

`Grass/ISA/AArch64/Control.lean` models CBZ W/X word encoding, canonical decoding,
register testing and normal PC calculation. It preserves GPRs and NZCV, handles
Rt=31 as ZR, and sign-extends the scaled displacement relative to the instruction
PC. Round-trip theorems quantify every operand combination. SVC has an exact
word decoder and a request indexed by that word and the reached CPU projection.
`Request.register` reads the indexed CPU rather than reconstructing an ABI snapshot.

`Grass/ISA/AArch64/Source.lean` uses the existing shared four-byte little-endian
reader/writer. `SourceWord` retains the input and exact suffix equation;
`readSource` preserves parser refusal. `SourceBodyStep.cases` covers every outcome
admitted by this bounded body relation, retaining the actual decode and branch
condition or SVC request. This is not an all-machine-transition VC theorem.

## Explicit remaining obligations

- These CPU projections have no separate memory store. Actual fetch provenance,
  current-code binding, permissions, alignment and profile admission are still
  needed from the machine/memory realization.
- CBZ describes normal instruction-body control. Debug/interrupt outcomes,
  system effects of BranchTo and any later target-fetch fault are not modeled.
- SVC records a decoded exception request. Arm's `CheckForSVCTrap` and configured
  exception entry remain unimplemented. Neither Linux dispatch nor return nor
  provider completion follows from this receipt.
- Linux must connect its selected ABI/personality, request/result and provider
  protocol to the actual machine exception occurrence. Bare-metal uses its own
  execution context; the instruction alone selects no provider.
- No AArch64 source frontend, executable artifact, hardware execution test,
  complete machine model or verified spike is claimed by this delta.

## Evidence

Run `lake build Tests.ISA.AArch64.Control`. The targeted build covers the new
modules and their dependencies; it is not a full repository build. Fixtures test
W/X disagreement on high-only values, register/flag preservation, ZR, signed
offset extrema, backward control, modular PC arithmetic, exact bytes/suffix,
short input and rejection of neighboring instruction families. Printed axioms
for the key round-trip/source/body/citation theorems are only `propext` and
`Quot.sound` (citation checks use `propext` alone).

Independent assembler input is `Tests/ISA/AArch64/control.s`. Clang's AArch64
integrated assembler produced the eight expected words:
`b4000040 34ffffe1 b4ffffff d4000001 d41fffe1 d4000002 d4000003 d4200000`.
The object `.text` was checked using ELF section extraction and `readelf -x .text`.
This tests encoding examples; it is not execution or proof authority.

`Grass/ISA/AArch64/Sources.lean` pins Arm DDI 0602 ID032025 and A64 Guide 1.3,
records declaration subjects and exact locators, and checks citation shape and
retrieval metadata. The instruction diagrams and operation entries were inspected
at PDF pages 142/1012 (printed 139/1009). PDFs are reference-only and are not
committed. The generic citation records currently reside under the X86 directory;
reusing them imports no x86 semantics or dual-vendor policy.
