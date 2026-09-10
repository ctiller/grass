# Wasm ISA implementation boundary

The initial implementation is a reusable integer/local/direct-host-call family,
activated for the parallel spike work. It is not a completed Wasm port or a
`VerifiedProgram` realization. The portable spike specifications are unchanged.

The selected semantic reference is [WebAssembly Core 2.0](https://www.w3.org/TR/wasm-core-2/),
particularly Binary Format (integers, instructions, modules), Execution (runtime
structure, numeric/variable instructions, calls), and Validation. This slice
admits only its explicit integer family; absence of floats, references, memory,
tables and structured control is an implementation boundary, not a claim that
Core 2.0 lacks those features. A future extension must preserve these cases.

## Implemented construction

* [Types](../Grass/ISA/Wasm/Types.lean) owns integer values, signatures and distinct
  logical function/module/host addresses. None is a linear-memory or native address.
* [Module](../Grass/ISA/Wasm/Module.lean) owns the original instruction/module
  carrier and production binary emitter. Import and defined-function signatures
  determine the emitted type table; the same source supplies function bodies.
  Counts and indices outside unsigned 32-bit representation are refused.
  `Artifact` retains equality with the complete emitted output, including its
  header and sections. It rejects extra trailing bytes as a canonical mismatch.
  This canonical-output checker is not a general parser or a module validator.
* [Invocation](../Grass/ISA/Wasm/Invocation.lean) checks the reached activation's
  function, owning module instance, definition, function-address mapping, locals
  and current source instruction. `HostInvocation.check` then resolves that actual
  CALL through the module's import/address mapping to a host function in the same
  store. It checks signature, stack arity and argument types. Parameter order is
  derived by reversing the consumed stack prefix (represented top first). General laws retain the
  source CALL, production bytes, stack decomposition and unchanged locals.
* [LocalStep](../Grass/ISA/Wasm/LocalStep.lean) computes integer constants,
  add/subtract/zero-test, local get/set, drop, nop and unreachable. A `LocalRun`
  uses the exact checked source site, retaining the actual outcome equation.
  Add/subtract laws quantify over arbitrary operands and stack prefixes.

`HostInvocation` is the interface for the WASI owner. Its `importDecl` contains
the exact source namespace, field and type; `hostLookup` retains actual store
resolution and `hostId`. `arguments` is in parameter order. `continuation` is
the caller activation with arguments consumed, before result insertion; it is
not proof that the host returned. Provider binding, behavior, resource effects
and result/return connection require separate evidence. Equal names and types
do not establish a provider's identity or adequacy.

The pure invocation-input receipt is reusable for the same store/activation
snapshot. It does not mint a fresh dynamic occurrence or a single-use capability.
The consuming provider handoff must derive that identity from its actual protocol
transition and bind completion to it; an old `HostInvocation` alone cannot supply
completion authority for a later call with identical values.

## Explicit remaining obligations

The supplied store snapshot and activation are indices, not a proved reachable
execution from instantiation. The selected lookups are checked locally. Global
module/store validity, artifact decoding and instantiation adequacy are still
owed. In particular, encoding success does not check export validity, all body
stack types, or every function's local/call indices. No module can be promoted
to the public verified gate from these receipts alone.

The emitter's correspondence to the standard binary grammar still needs a
kernel-checked parser/encoding theorem. Exact equality with production bytes
prevents a second program from being substituted; it does not prove that the
emitter implements the standard. This external-model correspondence remains a
trust boundary, and the grammar proof is open.

Current source sites address flat function bodies. Structured labels, block/loop
typing, internal calls, caller stacks, function end/return, host completion,
traps across activation boundaries, memory and table instructions remain to be
implemented. `return_` and direct calls are explicitly refused by the local-step
adapter; imported host calls have their separate checked constructor. An invalid
stack or unsupported control request is a checker refusal, distinct from the
architectural `unreachable` trap. The current leaf is not an exhaustive evaluator
for arbitrary Core modules and supplies no whole-program safety or progress claim.

## Validation

[Binding tests](../Tests/ISA/Wasm/Binding.lean) exercise argument order, actual
source-call selection, signature/arity/type rejection, stale caller mappings,
distinct host resolution for identical local indices in different module
instances, changed artifact bytes, subtraction order and integer wrapping.
These closed examples supplement the universal library laws.

[WasmProbe](../Tools/WasmProbe.lean) emits test modules through the production
emitter; [the Node probe](../Tools/wasm-probe.cjs) validates and instantiates those
actual bytes with Node's WebAssembly engine. Run:

```text
lake build Tests.ISA.Wasm.Binding
lake env lean --run Tools/WasmProbe.lean
node Tools/wasm-probe.cjs
```

Native engine observations validate the model and emitter. They provide no Lean
proof, module-validity certificate, provider certificate or spike completion.
