# Operations, instructions, and ISA profiles

## 1. Open extensibility

Ghost and raw operation sequences use existential packaging behind narrow
interfaces. New ISA instructions, API calls, macros, proof operations, and ghost
protocol operations may be added without editing a closed master sum type.

An operation family supplies only the facets it uses, through separated
interfaces rather than one god class. Mandatory facets include applicability and
step semantics; conditional facets include encoding, decoding, memory events,
control flow, relocation, faults, atomicity, ordering, pretty printing, and
validation metadata.

All reachable operations must close every facet required by their selected
profile. Missing metadata is rejection, not a default empty effect.

## 2. Ghost-bearing layer and erasure

The last verified representation may contain:

- assertions and proof hints;
- obligation and capability manipulation;
- nominal provider evidence;
- typed macros and computed sequences;
- abstract calls and block requirements already connected to realizations;
- ghost state used to simplify local before/after proofs.

Erasure produces only raw instructions, platform call encodings, layout, and
link metadata. Its behavioral-inclusion theorem is oriented from raw executions
to matching ghost executions: erasure may not introduce a raw behavior that the
verified program lacks. It couples initial states and external choices and
covers finite/infinite traces, faults, divergence, terminal states, mandatory
audit events, and projected observations. Proving only that every ghost step has
some raw implementation is insufficient. Ghost operations cannot repair a
physically invalid raw sequence.

## 3. Raw instructions

`RawInstruction profile` carries sufficient information to step and, where
supported, encode the selected operation. Exact encoding choice may be retained
separately from normalized semantics. The primary correctness demand is semantic:
decoded emitted bytes must have the same step relation as the raw program.

An exact encoding type may additionally prove byte round-trip. Redundant prefix,
alias, or width distinctions need not pollute semantic reasoning merely to obtain
syntactic equality.

Each instruction model declares:

- mode, privilege, feature, operand, and encoding applicability;
- register/flag reads, writes, and over-approximated clobbers;
- memory and causal events;
- control successors and indirect-target constraints;
- faults, traps, interrupts, restartability, and partial effects;
- atomicity and memory ordering;
- relocation-bearing fields;
- authoritative citations and validation hooks.

## 4. Macros

Macros are verified computed sequences with before/after contracts. They may
contain CFGs, create obligations, or expose fault/interruption points. They are
not semantically atomic unless a target theorem proves that property. Physical
observability, concurrency, and interruption behavior are always inherited or
explicitly summarized with proof.

Every macro declares its raw-instruction expansion, hygienic labels, complete
register/flag/stack/memory clobber set, introduced back edges, entry/exit
contracts, and all fault/pending/interruption/violation exits. A macro containing
a loop or call cannot present itself as a straight-line atomic operation. Spike
diagnostics print the instantiated expansion; an unexpandable convenience form
cannot enter `VerifiedProgram`.

## 5. Authored CFG surface

`asm_source` is a first-class assembly authoring surface, not a final compiler
dump or a certificate. It parses instructions, resolves syntactic operand/label
forms, checks profile-independent source well-formedness, and emits a stable
`AsmSource plan`. Functional outcomes, terminal bindings, frontier refinement,
and platform contracts are checked only by the later `verify_assembly` phase.

`asm_source` is a command-level generator, not one monolithic term elaborator.
It emits alpha-normalized per-block source declarations plus a manifest with
canonical source and boundary identities. `verify_assembly` consumes a
`PlatformContract spec plan`, the process-plan refinement witness, and that
manifest; within each named block it symbolically composes instruction
semantics and emits a separately cached local `ImplementsBlock` certificate. Explicit
headers provide entry contracts, nontrivial loop invariants, and named exit tags;
ordinary fallthrough and direct branch postconditions are inferred and checked.
The verifier resolves labels, checks calls/jumps against target entry
contracts, and constructs the `SubCFG.plug` proof. Those generated objects remain
inspectable, but authors do not write a parallel list of block certificates.

Straight-line symbolic verification is a deliberately bounded, decidable
forward fragment: concrete register/flag transfer, bitvector arithmetic,
shaped reads/writes, disjoint framing, and calls with selected summaries. It
does not search for loop invariants, heap partitions, aliases, recursion
measures, or provider contracts. Failure leaves an exact local goal rather than
starting unbounded proof search. This is the zero-annotation path for ordinary
straight-line assembly and remains predictable enough for per-block caching.

Standard ABI profiles derive call frames, saved-register restoration, call-loan
phases, pending states, and unwind metadata from literal prologue/call
instructions. Assembly authors retain control of registers, stack offsets,
instruction selection, ordering, and any nonstandard frame or obligation policy.
Unmodified nonvolatile registers and disjoint stable resources are automatically
framed across straight-line regions and loop headers when every call and back
edge preserves them. Loops retain an explicit invariant for changing state and
an explicit measure/frontier law.

A bare literal `call` never silently inserts stack adjustment, spills, status
loads, probes, or cleanup: doing so would make the emitted source differ from the
assembly the author reviewed and would obstruct deliberate frame/register
tuning. The verifier checks that the authored pre-call state already satisfies
the ABI. A transparent verified call macro may allocate canonical shadow space,
align the stack, marshal arguments, and restore it; its raw expansion is the
selected source and can be inlined or replaced. Grass rejects implicit ABI code
rewriting while providing an economical explicit macro route.

The measure may be discharged automatically by linear arithmetic or a named
loop combinator, and routine source need not contain a handwritten proof term.
Grass nevertheless keeps the measure/frontier declaration at a loop boundary:
termination/productivity is semantic, an optimization can invalidate it while
preserving every straight-line postcondition, and heuristic measure discovery
would make proof behavior and invalidation unpredictable. Transparent verified
loop macros may supply the declaration and proof together; novel loops state the
ranking or external frontier they genuinely use.

An author may declare a `FrameLayout` with symbolic named slots, field shapes,
alignment, outgoing shadow/argument area, and optional saved-register regions.
Operands such as `[rsp + SortFrame.bytesRead]` elaborate to exact literal
offsets; the layout theorem proves non-overlap, call-site alignment, shaped
access, and unwind correspondence. The expansion and final offsets are review
output, and a literal-offset frame remains a fully supported peer for deliberate
tuning. Adding a symbolic slot invalidates layout-dependent instructions and
unwind data without forcing unrelated block contracts to change.

The assembly surface accepts both literal and symbolic operands. An author may
write `mov ecx, 3` to control exact machine source, or a refactoring aid such as
`mov ecx, $policy.status(.noProgress)` that elaborates to an immediate and retains
the same encoding proof. Likewise, literal stack offsets remain valid while
proved layout names or verified call macros can derive routine shadow-space and
slot offsets. Symbolic forms never conceal which raw instructions or bytes were
selected; their expansion is inspectable, and literal custom assembly remains a
peer route.

Containment annotations are proof-only source metadata and attach an exact violation class and
affine return envelope to a literal authored edge or tail, for example
`ja bad @violation_edge(.excessWriteCount)` and
`ud2 @containment_tail(.excessWriteCount)`. They never synthesize, remove, or
rewrite instructions. Verified macros may generate a transparent sequence, but
then the source names the macro rather than duplicating its expansion.

Defensive post-violation containment is optional hardening, never a prerequisite
for the conforming correctness theorem. An author may write literal trap/
recovery assembly, invoke a transparent verified hardening macro/pass, or omit
the post-violation path entirely and end assurance at the first environment
violation. The selected choice remains first-class source and affects only the
separate containment certificate.

Containment is not silently enabled by a global verifier switch because the
comparison, branch, and trap are real performance/size/control-flow choices.
Profiles and macros may provide a transparent `trap`, `report`, or `omit`
policy, but invoking it selects and displays concrete instructions. Spike 1
keeps literal branches to expose the baseline theorem; repetition in larger
programs should normally use the verified macro or omit post-violation code.

The CFG proof library includes parameterized invariant combinators such as
`SliceConsumer`, `CountPrefix`, and `MergeCursors`. They are generic over the
logical relation, selected registers or symbolic locations, physical slice
representation, and relevant comparison/order law. They derive routine
partition, residual readability, bounds, disjointness, and update lemmas while
leaving the program-specific invariant and measure visible. They are CFG
contract templates, not part of the pure sequence standard library and not a
restriction on custom loop invariants.

For a typed `StructLayout`, a proved disjoint copy, move, swap, or permutation of
whole initialized elements transports the layout's logical occurrence map
automatically from the actual instruction semantics. Scalar loads/stores,
`movdqa`/other vector moves, and a transparent copy macro are peers when their
read/write footprints establish the same typed transfer. Authors do not insert
`@ghost move_occurrence` inside routine merge or swap loops. Partial copies,
overlap, type punning, bytewise mutation, or novel representations leave an
explicit ghost/refinement goal; custom ghost instructions remain first-class
and are never prohibited.

For a process driver, `ProcessLoopInvariant` lifts process-local invariants,
population/state ownership, channel correlation, shared-access laws,
obligations, committed observations, and physical representation into one
global-loop contract. Dispatch blocks prove one named process transition and
the library frames every untouched process. This derived contract is inspectable
and replaceable by a custom global invariant; it never excuses unverified loop
instructions.

## 6. Decoder registry

Decoders register into a global profile registry with enough metadata to
dispatch by ISA, mode, prefix/opcode space, feature set, and priority/conflict
rules. Registration proves nonambiguity or declares an explicitly resolved
overlap. Unknown and ambiguous byte streams return structured errors.

Imported code is decoded into raw instructions and stepped by the same semantics
used for authored code. Direct targets may be found recursively. Indirect
control requires annotations, relocation/symbol evidence, abstract interpretation,
or another proof that every reachable target belongs to the typed CFG.

## 7. Common x86-64

The initial ISA is a common x86-64 profile defined as the reviewed intersection
of Intel and AMD architectural contracts, plus a Win64 execution profile.
Instructions outside the intersection require a vendor/feature refinement.

Every common rule records both vendor citations with document revision and
anchor. Conflicts select the weaker common guarantee, split into refinements, or
exclude the construct. Validation runs separately on Intel and AMD machines.

Primary reference families:

- Intel 64 and IA-32 Software Developer's Manual, especially Volumes 2 and 3:
  https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
- AMD64 Architecture Programmer's Manual, Volumes 1-5:
  https://docs.amd.com/v/u/en-US/40332_4.09_APM_PUB

The profile/refinement mechanism is a versioned extension point intended for x86
variants, ARM, RISC-V, Wasm, SPIR-V, WGSL, Verilog, and other instruction-like
targets. A new target may conservatively extend foundational vocabulary after
review and must provide migration/refinement theorems for existing profiles. The
initial interface is not presumed permanently sufficient for unlike targets.
