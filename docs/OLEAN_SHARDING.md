# Lean module and `.olean` sharding design

Status: required implementation architecture for proof locality. This document
does not claim measured build performance.

## Goal

A local instruction edit must not place the complete program in a changed
theorem type or force every caller, model, specification, and sibling subsystem
to elaborate again. Grass uses Lean modules as the physical unit of proof
reuse, verified-object summaries as the logical boundary, and a bounded-fanout
certificate DAG as the aggregate proof.

This design relies on Lean's actual compilation model:

- a Lean source module elaborates to `.olean` environment data which importers
  load without re-executing the source commands;
- Lake treats a module as its smallest visible build unit and exposes an
  `olean` build facet;
- Lean's module system separates public, private, and language-server `.olean`
  data and supports public/private scopes; and
- definitional unfolding across a boundary defeats abstraction, so relevant
  facts must be proved in the owning module and exported as theorems rather than
  recovered by unfolding implementation bodies.

See the official Lean [source-file and module
reference](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
and [Lake build-facet API](https://lean-lang.org/doc/api/Lake/Build/Facets.html).

## 1. One shard, four artifacts

A shard is normally one function, assembly fragment, shader module, static-data
unit, or bounded CFG region. Very small mutually dependent regions may share a
shard; a shard has a configured upper bound so “one function” cannot become a
million-instruction escape hatch.

```text
Foo/Sig.lean       stable public boundary
Foo/Impl.lean      exact authored/generated source and local proof
Foo/Cert.lean      opaque exported verified-object certificate
Foo.gobj           serialized relocatable object emitted by a Lake facet
```

`Sig.lean` exports only:

- nominal scope/export identities;
- entry and exit contracts;
- call targets and their imported summaries;
- memory, register, fault, obligation, resource, and cancellation effects;
- ABI and feature requirements; and
- stable theorem statements consumers need.

It contains no instruction list, private CFG state, register-allocation map,
proof term, relocation array, or body hash. Callers import `Sig`, not `Impl` or
`Cert`.

`Impl.lean` owns the exact source, typed layouts/placements, local representation
relations, expansion, symbolic proof, encoding, relocations, and the theorem
that the resulting object realizes `Sig`. It may use private declarations and
local definitional unfolding freely. Nothing outside the shard obtains that
body by `import all`.

`Cert.lean` exports an opaque value with a small public type:

```lean
public structure ShardSummary where
  scope : StableScopeId
  boundary : MachineBoundarySummary
  imports : FiniteMap StableScopeId MachineBoundarySummary

public opaque fooObject : VerifiedObject fooSummary
```

Construction of `fooObject` occurs in the owning module from the exact
implementation theorem. The value internally retains source/object identity;
its public type does not contain the source vector. The kernel checks the
constructor application once. Downstream composition uses the exported
certificate and cannot unfold or replace it.

The `.gobj` file is a deterministic serialization of the same verified object.
Its Lake facet records a digest and a theorem-bearing manifest. Cache hashes and
digests locate artifacts; they are never accepted as proof of correctness.

## 2. Import discipline

The central rule is:

```text
semantic/model consumer  -> imports Foo.Sig
machine implementation    -> imports required Callee.Sig modules
aggregate certificate     -> imports child Cert modules
artifact linker           -> consumes child .gobj facets + aggregate certificate
```

Forbidden dependency edges include:

- a caller importing a callee implementation merely to unfold it;
- a portable model/spec importing a machine certificate;
- a leaf importing a whole-program umbrella;
- an aggregate theorem whose type contains every descendant source; and
- application modules using `import all` across a shard boundary.

Within one shard, `Impl` may import private implementation support. Across a
shard boundary, definitions required for reduction must be deliberately exposed
in the signature; the preferred design exports the needed theorem and keeps the
body hidden. `lake shake` is used to find accidental broad imports, with
reviewed exceptions for deliberate public re-exports.

### What `.olean` reuse does and does not buy

The localization is an import-graph property, not a magical comparison of old
and new declarations. Editing any command in `Foo/Impl.lean` rebuilds that
module. Because `Foo/Cert.lean` imports it, the certificate and object facet also
rebuild. An aggregate importing `Foo.Cert` then rebuilds, followed by its
ancestors. That is the intended changed path.

A caller body imports only `Foo.Sig`. Since a body-only edit does not touch that
file, Lake can reuse the caller's `.olean`; it need not discover that two
versions of `Foo.Impl` happen to expose extensionally equal declarations. If a
caller imported `Foo.Cert`, or if generated source rewrote `Foo.Sig` on every
body edit, the boundary would fail even when the visible contract was textually
unchanged.

The signature therefore describes an unresolved verified import, not an axiom
that the callee exists. A caller shard proves its local behavior conditional on
the named imported summary. The aggregate which imports both certificates
checks that one exact verified object supplies that summary and closes the
import. No leaf proof assumes an unverified implementation.

For example, changing an HPACK instruction while preserving the HPACK boundary
rebuilds:

```text
Hpack/Impl.lean
  -> Hpack/Cert.lean + Hpack.gobj
  -> Web/CodecAggregate.lean
  -> Web/ServerAggregate.lean
  -> Win64ArtifactAggregate.lean
```

The HTTP/2 behavior proof, worker implementation, IO provider, Vulkan sibling,
and callers importing `Hpack/Sig.lean` remain reusable. Changing the HPACK
boundary instead deliberately rebuilds direct signature consumers and the
resulting semantic dependent cone.

## 3. Hierarchical certificate DAG

Leaf certificates do not all flow directly into one root module. Generated
aggregate modules form a balanced, bounded-fanout tree over the dependency DAG:

```text
block/function certificates
        ↓
component aggregate certificates
        ↓
subsystem aggregate certificates
        ↓
process/platform aggregate certificate
        ↓
artifact/link certificate
        ↓
VerifiedProgram exactSpec
```

Each aggregate imports a bounded number of child `Cert` modules and exports one
opaque certificate over a small composed summary. Its private proof checks:

- boundary compatibility;
- call/CFG edge closure;
- symbol/import/relocation uniqueness in its namespace;
- resource and obligation composition;
- requirement-key coverage for its owned range; and
- exact object concatenation/link-plan structure.

The parent type mentions only child public summaries and the aggregate summary,
not child source bodies. A leaf edit therefore recompiles the leaf
implementation/certificate and one aggregate path to the root. Unchanged
sibling `.olean` files remain reusable.

Mutually recursive calls form an SCC. The SCC receives one shared signature
module declaring all call contracts; bodies remain separate leaf shards where
possible, and one SCC aggregate proves internal call closure. Changing an SCC
signature deliberately rebuilds its external callers. Changing one body while
preserving the signature rebuilds that leaf and the SCC/aggregate path.

## 4. Exact source without whole-source theorem types

Exactness is preserved by hierarchical existential ownership:

```lean
structure VerifiedObject (summary : ShardSummary) where
  private source : RawInstructionHierarchy
  private object : RelocatableObject
  private sourceExact : SourceHasSummary source summary
  private encodingExact : EncodesRelocatable source object
  public exports : ObjectExportsSummary object summary
```

The exact source is not erased; it is owned behind the checked certificate.
Composition constructs a new certificate whose private witness is the tree of
child objects and link steps. The final `VerifiedProgram spec` theorem refers
to that root certificate. It does not assert equality between two flattened
million-element arrays.

Review and emission still need the bytes. The build tool streams each `.gobj`
and its compact manifest through the verified linker/writer. A small generated
Lean module records the link tree and consumes the object certificates. No Lean
declaration materializes the full concatenated instruction program merely to
compute a boolean or prove `rfl`.

## 5. Generated metadata is sharded too

Registries, source maps, citations, requirement coverage, imports, symbols,
relocations, unwind ranges, and artifact manifests use the same tree:

- a leaf manifest covers one shard;
- an aggregate manifest stores child IDs, small namespace summaries, and
  cross-child edges;
- global uniqueness/coverage is a fold over summaries; and
- detailed source-map data remains in the leaf artifact and is loaded on
  demand for review or diagnostics.

Clean global checks are necessarily at least linear in the compact manifest
graph. They must not be linear in all instructions when their inputs are only
symbols or requirement keys. Incremental checks revisit changed leaves and
affected aggregate/SCC nodes.

## 6. Expected rebuild cones

| Edit | Must rebuild/check | Must remain reusable when boundary is unchanged |
|---|---|---|
| one instruction | leaf `Impl`, leaf `Cert`, affected `.gobj`, aggregate/link path | portable spec, model theorem, callee/caller bodies, sibling shards |
| local invariant | affected leaf/CFG-region proof and aggregate path | algorithm theorem and callers that consume only unchanged summary |
| register allocation | machine leaf, unwind/encoding/object, aggregate/link path | portable/model proofs and unchanged signatures |
| exported contract | signature, implementation, direct importers, affected SCC and aggregate closure | unrelated subsystems |
| specification key | owning spec fragment, derived staged key path, implementations consuming that key, root closure | implementations whose imported requirement summaries are unchanged |
| layout | shards whose typed operands/representation use it, then encoding/link path | portable behavior and unrelated algorithm proofs |
| provider profile | projection/provider summaries and machine shards using changed calls | portable protocol/application proofs |

A no-op build should load/validate existing module and facet traces. This is a
measurement target, not a claim that current Lake always performs zero work.

## 7. Lake integration

Grass defines Lake facets for:

```text
Shard.lean:olean       kernel-checked public certificate/module data
Shard.lean:olean.private  private implementation proof data where required
Shard.gobj             deterministic relocatable verified object
Shard.gmanifest        compact symbols/imports/relocations/citations/source map index
Aggregate.gmanifest    child IDs, public summaries, dependency edges
```

The build graph derives these from module imports and explicit manifest edges.
The generator writes one module per bounded shard plus balanced aggregate
modules; authors do not maintain the tree. Outputs use content-addressed cache
keys including toolchain/profile versions, source, imported summaries, and
generator version. A cache hit is used only after importing the kernel-checked
certificate and validating the artifact digest named by that certificate.

Parallelism follows independent Lake module jobs. Linking and manifest folds
stream child artifacts and bound in-memory fanout. The project forbids a build
step which first flattens every shard into one Lean array.

## 8. Validation without a 10M-instruction corpus

Grass does not require materializing one or ten million instructions merely to
claim scale. The design is validated in three ways:

1. **Structural theorems.** Prove that a body-only edit preserving a public
   summary changes only the leaf identity and aggregate ancestor identities;
   sibling and caller signature dependencies are equal.
2. **Graph simulation.** Exercise very large abstract shard/SCC/dependency DAGs
   whose nodes contain compact summaries, and verify affected-node computation,
   manifest folds, cache keys, and bounded fanout without generating instruction
   bodies.
3. **Calibrated real builds.** Use representative emitted shards large enough
   to measure elaboration, kernel, import, encoding, and linking behavior; grow
   them only until cost curves and bottlenecks are clear.

Reports record changed/re-elaborated modules, kernel-checked declarations,
`.olean` and proof bytes, `.gobj` bytes, import/cache hits, wall time, and peak
memory for cold, no-op, instruction, invariant, interface, spec-key, layout, and
provider edits. The acceptance criterion is locality of the measured rebuild
cone and bounded per-shard memory—not reaching an arbitrary instruction count.

## 9. Failure conditions

The sharding design is rejected if implementation shows any of the following:

- theorem types or public summaries grow with complete descendant instruction
  streams;
- leaf consumers require implementation unfolding across module boundaries;
- a local body edit recompiles all callers despite an unchanged signature;
- aggregate modules import every leaf directly;
- source/manifest registries become single generated god modules;
- exactness relies on a digest rather than a checked certificate; or
- linking/encoding requires a fully flattened Lean value in memory.

If Lean/Lake's measured module behavior cannot sustain the intended boundary,
Grass must change the module/object factoring before implementing more ISA or
platform libraries. This is foundational build architecture, not a late build
optimization.
