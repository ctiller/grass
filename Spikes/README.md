# Comment-free spike source corpus

These files are the expected author-owned Lean source corresponding to the
annotated designs in `docs/SPIKE_1.md` through `docs/SPIKE_5.md`. They are design
fixtures, not a compiled Grass implementation: the imported `Grass.*` libraries
do not exist yet by deliberate project scope.

Each spike separates:

- `Resource.lean`: the reviewed selectable resource-model parameter;
- `Spec.lean`: the precious portable specification function and selected instance;
- `Projection.lean`: the reviewed faithful target projection;
- `Process.lean`: the canonical or explicit process realization;
- `Cancellation.lean`: optional cancellation summaries for processes which
  advertise cancellation, supervision, or bounded shutdown;
- `Model.lean`: a reusable algorithm model when the spike needs one;
- `Plan.lean`: the coherent platform/provider selection;
- `Data.lean`: exact static objects and derived imports when the program has them;
- `Constructors.lean`: typed Lean fragment constructors and their family
  theorems when the program uses them; an older spike may still use the
  historical `Macros.lean` filename, which never implies a textual preprocessor;
- `Assembly.lean`: the first-class authored x86-64 and, for Spike 5, SPIR-V;
- `SourceClosure.lean`: exact constructor/static/import closure and raw expansion when
  kept separate for a larger spike;
- `Bindings.lean`: named model/component adjacencies;
- `Program.lean`: `VerifiedProgram` closure and `emitProgram`; and
- `Artifact.lean`: writer/parser, loaded-code, embedded-component, and exact-byte
  connections.

The `.lean` files intentionally contain no explanatory comments. Their proof
burden, rejected alternatives, and change-locality analysis live in the paired
documents. Missing modules or theorem names are library requirements exposed by
the spike, not placeholders authorized to become axioms, `sorry`, or unsafe
promotions.

| Spike | Source | Annotated design |
|---|---|---|
| 1 Hello World | [`1_Hello_World`](1_Hello_World/) | [`docs/SPIKE_1.md`](../docs/SPIKE_1.md) |
| 2 Sort | [`2_Sort`](2_Sort/) | [`docs/SPIKE_2.md`](../docs/SPIKE_2.md) |
| 3 Gzip | [`3_Gzip`](3_Gzip/) | [`docs/SPIKE_3.md`](../docs/SPIKE_3.md) |
| 4 Web server | [`4_Web_Server`](4_Web_Server/) | [`docs/SPIKE_4.md`](../docs/SPIKE_4.md) |
| 5 Spinning cube | [`5_Spinning_Cube`](5_Spinning_Cube/) | [`docs/SPIKE_5.md`](../docs/SPIKE_5.md) |
