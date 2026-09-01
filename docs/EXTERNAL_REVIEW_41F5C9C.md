# Response to the architectural review of `41f5c9c`

## Disposition

The review found several real proof-economics risks, but it also measured
generated audit projections as application ceremony, treated deliberate spike
contracts as accidental omissions, and proposed weakening the final theorem in
order to reduce build invalidation.  Grass accepts the diagnosis where it
improves locality without changing meaning.  It rejects remedies which create
a second semantic tower or cause the final executable to cease being a proof of
the exact precious specification.

| Review proposal | Disposition | Result |
| --- | --- | --- |
| Separate semantic resource budgets from physical execution envelopes | accept | `RESOURCES.md`; Spike 4 now captures only its semantic budget and proves the selected Win32 envelope realizes it |
| Derive manifests, cancellation maps, frames, and artifact boilerplate from the typed assembly AST | accept | assembly construction now has one derived-metadata owner and staged checker phases; checked-in projections are review views |
| Named placement and generated ABI/frame structure | accept | the spike author surfaces use logical invariant names and explicit `@placement`; raw registers and offsets remain legal escape hatches |
| Verified object files and hierarchical linking | accept | `VERIFIED_OBJECTS.md` introduces signature-indexed subsystem objects and reconstructs an exact-root `VerifiedProgram` at final link |
| Split one opaque assembly tactic into auditable phases | accept | elaboration, symbolic execution, frame reasoning, arithmetic, ghost closure, and final closure have distinct residual-goal boundaries |
| Demonstrate an optimized assembly refinement | accept as an outstanding spike obligation | an optimized kernel must refine the same local contract; no claim about SIMD economics is accepted without a checked fixture and measurement |
| Add a second sequential semantics | reject | standard sequential programs already have a one-expression application surface and a proved embedding into the sole process semantics |
| Index final `VerifiedProgram` only by an extensional signature | reject | stable signatures are correct at object/export boundaries; final emission must retain equivalence to the exact precious root |
| Remove existential `ProcessRequirement` from specifications | reject | “a process implementing this parser” is a valuable abstract demand; the carrier and substitution theorem must be repaired, not deleted |
| Mandate Iris cameras as the concurrency model | reject as premature mechanism choice | Grass requires the algebraic laws and local frame theorem, not one library vocabulary before the implementation experiment |
| Require external sort, TLS, dynamic Huffman, and GPU recovery in these spikes | reject as scope substitution | those can be later specifications; several directly contradict the programs requested for the current spikes |

Numeric speed, memory, percentage, and line-reduction estimates in the review
have no supplied benchmark artifacts.  They are hypotheses, not architectural
facts, and are not copied into the normative corpus.

## One semantics without sequential ceremony

The review describes Hello, Sort, and Gzip as if their authors manually build
actor populations and prove occurrence-bag arithmetic.  They do not.  A
registered standard constructor is selected as follows:

```lean
def processRealization : ProcessRealization spec :=
  ProcessRealization.standard (Grass.Std.Realizers.lookupExact spec)
```

The implementor of a new standard sequential constructor proves the larger
`DirectRelationalProgram` package once.  Typed read, write, allocation, and
terminal combinators derive occurrence identity, pending equations, child
bindings, escrow, and terminal disposition.  A gzip application supplies its
precious byte relation, compressor correctness, failures, bounds, progress, and
assembly refinement—not a synthetic actor network.

The follow-up review correctly asks what happens outside the closed registry.
Grass therefore distinguishes three surfaces rather than a registry cliff:

1. a registered standard relation is one lookup expression;
2. a novel serial program over known effects uses `SequentialMachine`, whose
   typed decision syntax structurally derives occurrences and pending equations;
3. only a transition which deliberately issues or resolves multiple effects at
   once uses the fully general `DirectRelationalProgram` escape hatch.

A custom gzip header, extra pass, or different error policy normally changes
the sequential state and decision function and remains in the second category.
It does not justify hundreds of lines of handwritten bag algebra.

The adapter theorem has a constructive shape.  Its generated network state is
the direct state paired with a finite map of live effect occurrences.  Initial
and transition equations show that erasing the map equals the direct pending
bag exactly, including multiplicity.  Each issue inserts a fresh mapped child;
each result, cancellation, interruption, or fault consumes the correlated
entry; terminal disposition classifies every entry still live.  Induction gives
finite-prefix correspondence and the supplied completeness/progress package
lifts it coinductively to infinite executions.  Inversion on the generated
transition constructors gives the reverse simulation.  Therefore flattening
the adapter is bisimilar to the direct program.

A separate `SequentialSpec` would duplicate observation, fault, termination,
resource, obligation, cancellation, and infinite-execution laws, then require
new bridges whenever a formerly serial component is combined with callbacks,
workers, devices, or interrupts.  The useful proposal—local Hoare/WP assembly
proof—is already compatible with the single algebra: it proves a local serial
function or direct program, and the canonical adapter supplies the process
presentation.  If a standard application needs more than one realization
expression, Grass treats that as an adapter/library failure.

The claimed “millions of synthetic actor tokens” also misstates the lowering.
The adapter represents outstanding external effect occurrences, not assembly
instructions, scalar loop iterations, or ordinary local function calls. The
DEFLATE kernel is a serial component with a local model/Hoare certificate. A
generic opaque adapter theorem is applied at a subsystem boundary; its proof is
not textually regenerated once per instruction. Whether even this compact
application checks economically at target scale is an empirical gate, so Grass
retains measured locality gates instead of asserting unmeasured kernel costs in
either direction. Those gates are specified in
[OLEAN_SHARDING.md](OLEAN_SHARDING.md) and do not require a synthetic
million-instruction program.

The follow-up review correctly challenged the eleven-file gzip directory. The
project intent is that `Spikes/` shows what agents actually author, so placing
generated source closure, bindings, and artifact wrappers there did make them
appear to be author-maintained ceremony. The repaired corpus gives those
projections in the annotated spike document or generated tool output and keeps
only authored abstractions in the directory. Generated material still counts
for build and kernel cost; the scale fixture measures it separately.

## Why the final program retains the exact specification

`ProgramSignature` is a good stable boundary for separately checked objects.
It is insufficient as the final theorem index because two specifications can
have the same public signature while differing in non-exported safety,
resource, progress, or provenance demands.  Existentially hiding the chosen
specification in `VerifiedProgram sig` would let emission prove only that some
hidden specification was met, not that the emitted bytes implement the exact
precious program the author reviewed.

Grass instead uses:

```text
VerifiedObject publicSignature
        + independently reusable local certificate
        + symbolic relocations
                    |
              verified link plan
                    |
          VerifiedProgram exactRootSpec
```

Changing an object body rechecks that object and affected link/layout nodes.
Changing the precious root deliberately rechecks the final composition theorem.
This contains implementation blast radius without weakening what
`emitProgram` means.

## Why abstract process requirements remain

A parser grammar and a demand for some process implementing that grammar are
different facts.  The first defines accepted and rejected inputs.  The second
lets a large specification require a replaceable component without prescribing
whether its witness is a serial function, streaming process, captured graph, or
assembly component.

The required substitution proof is parametric.  A requirement carries an exact
boundary and resource view.  An acceptable witness is indexed by that same
boundary and proves the required relation.  Replacing the abstract boundary by
the witness preserves the root trace relation, demands, and resource
entailments; substitutions compose and captured subgraphs hide associatively.
The current corpus must carry this demand family through fragments, suite,
capture, and refinement.  Its incompleteness is a defect identified by smeller,
not a reason to erase the abstraction.

## Resource stratification

The review correctly found that Spike 4 mixed a portable capacity contract with
a particular Win32 worker pool.  The repaired split is:

```text
precious behavior + semantic budget
                    |
        RealizesSemanticBudget
                    |
replaceable Win32 execution envelope
```

The semantic budget can be instantiated differently for a data-center server
and a microcontroller.  A concrete envelope chooses threads, handles, sockets,
buffers, scheduling quanta, and allocation policy, and proves it realizes the
selected budget.  Neither layer is folded into the behavior relation; the
resource model remains a parameter of that relation.

## Assembly construction and optimization

Raw offsets, pinned registers, arbitrary instruction sequences, and custom
macros remain first class.  They are not mandatory proof vocabulary.  Named
layouts, `withStack`, placements, and typed fragment constructors provide a
concise route whose expansion is exact and reviewable.  Their local theorems
bank facts that symbolic execution would otherwise rediscover.

Optimization is proved at a local contract boundary.  A vector or unrolled
kernel first proves a forall-input algebraic equivalence to the scalar contract;
the surrounding block proof handles feature selection, readable ranges,
alignment, tails, progress, and ABI state.  `bv_decide` is acceptable for a
finite universally quantified word theorem.  Execution or fuzzing is model
validation, never the proof.  The review is right that the corpus needs an
actual optimized fixture before claiming this economy; its proposed performance
numbers and CRC instruction choices are not accepted without such evidence.

## Concurrency algebra

Grass needs compositional resource algebras, exclusive and fractional
authority, local update laws, separating frames, and a theorem that untouched
resources remain untouched.  Those requirements are compatible with
Iris-inspired cameras, but the review supplies neither a Lean implementation nor
evidence that the named mechanism is the best fit for Grass's memory,
obligation, process, and heterogeneous-device domains.  The normative corpus
therefore specifies laws and mutation fixtures.  The implementation spike may
adopt cameras, another partial commutative algebra, or a smaller construction if
it proves the same laws and scales under measurement.

## Scope corrections

- Spike 2 was explicitly requested to buffer as much as memory permits and emit
  nothing when allocation fails.  Disk spilling would implement a different
  specification.
- Spike 2 was explicitly requested to be stable. Equal byte strings make that
  property invisible in the final byte projection, but erasure does not license
  deleting an expressly demanded algorithmic theorem. Occurrence ordinals are
  ghost identity used to state stability; they do not prescribe a physical
  record representation. A future weaker CLI spec may omit stability, but this
  spike may not silently substitute it.
- Spike 3 is a compressor.  Its round-trip theorem uses a modeled decoder; the
  emitted program need not contain a decompressor.  Fixed Huffman is a valid
  bounded first encoder, not the completed `Std.Zlib` performance target.
- Spike 4 was explicitly requested as an in-memory server with no SSL.  HTTP/2
  flow control, cancellation, composite streams, and bounded resources are its
  pressure points; TLS is a separate composition.
- Explicit failure on Vulkan device loss is a safe program policy.  Transparent
  device recovery is a stronger future specification, not a prerequisite for
  proving the selected cube behavior.
- Async completion I/O and kernel-loaned buffers must remain unblocked by the
  architecture.  The first Win32 realization need not silently become an IOCP
  server in order to prove that later staged substitution is possible.

## Remaining evidence required

The review is correct that prose and comment-free design fixtures are not an
implemented library.  Before implementation claims are made, Grass still needs
elaborated interface fixtures, executable rejection mutations, an optimized
kernel refinement, measured tactic reports, and hierarchical scale fixtures.
The scale fixture here means the structural, compact-graph, and calibrated-build
ratchet in [OLEAN_SHARDING.md](OLEAN_SHARDING.md), not a giant synthetic source.
Those are acceptance gates. This document does not convert them into claims of
completion.
