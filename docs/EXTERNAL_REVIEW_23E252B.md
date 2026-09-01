# Response to the architectural review of `23e252b`

## Disposition

The review's four headline tensions are accepted as actionable:

1. the specification surface is doing work that should be captured or derived
   by its DSLs;
2. the assembly surface alternates between unnecessary raw bookkeeping and
   macros whose physical effects are not visible enough;
3. several short closing phrases do not yet expose the representation relation,
   invariant, or residual goals that make their promised proofs believable; and
4. the long-lived spikes do not yet demonstrate enough lifecycle, async, and
   modular pressure to justify the large-system claim.

Acceptance of a diagnosis does not imply acceptance of every proposed remedy.
In particular, HTTP/2 grammar remains precious, raw assembly remains legal, and
IOCP remains a replaceable realization. The repair is to make those choices
cheap, explicit, and locally provable—not to remove them.

This review examined `23e252b`. The explicit standard sequential-process
derivation and cube machine-proof junction added in `2664d46` postdate it.

## 1. Specification authoring must stop resembling manual IR construction

Resource semantics remain a parameter of the specification. That is what lets
one behavior receive a data-center budget or a microcontroller budget. Repeating
the same `{R}`, `ResourceModel`, and domain instances in every declaration is
not semantics. The application surface should use scoped variables or a small
domain binder while preserving fully explicit exported types.

Likewise, the HTTP/2 frame and HPACK languages are precious because accepted
and rejected bytes are observable behavior. But an application author should
select the HTTP/2 profile once. That profile must introduce its parser-process
requirements and prove their connection to the protocol suite. Manually
constructing `frameParserRequirement` and `hpackParserRequirement` in every
server is rejected as ceremony.

The proof sketch for the derived form is structural. A profile owns a finite
family of grammar fragments and their parser demands. Capturing the profile
unions those demands into the root requirement family with origin keys.
Selecting a parser witness proves the exact boundary, resource view, and
grammar relation; occurrence-exact substitution replaces the demand. Changing
routes cannot change that closed transport subfamily, while changing the HTTP/2
profile invalidates it deliberately.

Named outcome types remain useful product vocabulary. Libraries should derive
eliminators, target projections, and routine failure routing from them; they
must not force authors to spell nested generic sums or erase the reviewed
choice of which physical causes share one semantic outcome.

A named correctness theorem containing only a projection already stored by a
captured suite is also ceremony. `capture` should derive and expose it. Novel
domain theorems remain authored and precious.

## 2. Assembly stays first class, with a defensible default surface

Literal registers, offsets, and instruction sequences remain legal. Maintained
spikes should normally use typed layout operands such as
`[records + i * LineDesc.stride]` and named fields. Elaboration returns the
exact legal x86 burst and a layout theorem; the expanded view prints the shift,
address calculation, and numeric displacement. An author may pin or replace
that burst with literal instructions and prove the same local contract.

Placement is physical author control, not repetitive proof vocabulary. A
placement flows along a CFG edge and through a lexical region until an authored
delta changes it. Joins check compatible incoming placements. A register
reassignment therefore needs one delta, while a hand-tuned block can still pin
its complete physical entry state.

Routine failure exits should be generated from an authored outcome routing
table. That table is semantic and reviewable; repeated `mov status; jmp exit`
bodies are not. Expansion retains each actual terminal block and instruction.

Every fragment contract covers register and flag clobbers, stack delta,
read/write footprint, faults, obligations, resources, cancellation, and every
exit. The caller need not repeat that list at each splice: the dependent
fragment type is checked against live caller state and its instantiated summary
is printed beside the expansion. Symbolic effect deduction may be conservative;
it may never omit an instruction or API effect. A `$(fragment)` without such an
inspectable signature and exact expansion is not an acceptable spike example.

## 3. Short proof syntax needs a visible theorem factorization

`using_model fixed32KModelCorrect` proves algorithmic mathematics. It cannot
invent what the model's window, chains, CRC, accumulator, and output prefix mean
in machine memory. Gzip must name an application-specific representation and a
local simulation over the exact codec CFG. An inline parser witness likewise
must name the parser-state representation and the CFG cut points that connect
bytes, descriptors, and logical occurrences.

The required factorization is:

```text
model theorem
  + explicit machine/model representation
  + local CFG simulation
  + component/spec junction
  = selected implementation witness
```

Each conjunct has a distinct invalidation cone. The model theorem moves with
the reusable algorithm. Representation and simulation move with layout and
assembly. The junction moves with the precious requirement. A tactic may
consume these terms and report residual goals; it may not infer the relation
from similarly named fields.

Every authored cycle also names its inductive invariant. A measure proves
progress, not preservation. Entry establishes `I`; each body path establishes
an exit postcondition or `I` at the back edge; the measure/frontier proof is
separate. Removing the invariant must leave a residual goal at the first cyclic
edge. Standard loop constructors may instantiate a library invariant, but the
instantiation and effect summary remain visible.

For arbitrary application predicates, one satisfying trace is not enough.
Capture must require total response-or-pending behavior for every reachable
accepted input/provider choice and a nonempty admissible initial domain. The
cube's logical update/render proof should supply that consistency/productivity
witness; a library theorem cannot prove an opaque predicate by inspection.

## 4. The large-system claim needs stronger spike pressure

The review is right that “replace it later” is not evidence of scale. The
current bounded HTTP/2 polling realization may remain a valid first
realization, but it must not be presented as the only large-server shape. The
process contract must support a staged IOCP replacement with submitted-buffer
custody, correlated completions, cancellation races, and the same partial-byte
channels. A later implementation fixture must perform that substitution and
measure its invalidation cone.

Fixed capacities are valid resource profiles, not universal limits. The
four-connection server must prove admission, backpressure, cancellation,
reclamation/reuse, and no growth for every reachable execution within its
profile. A larger profile changes the resource envelope without changing the
HTTP/2 behavior. Grass must not infer data-center throughput from the small
fixture.

`ExitProcess` is only the final provider action. The server and cube must first
prove steady-state reachable ownership/resource invariants and explicit normal
shutdown cleanup; failed termination may adopt only obligations authorized by
the platform contract. Future spikes must exercise arena reset/object pools and
at least one concurrent reclamation discipline. Those mechanisms need not be
artificially inserted into terminating Hello, sort, or gzip.

The current single large `asm_source` terms are also insufficient evidence for
10M-line locality. Their intended typed object/shard boundaries must appear in
the authored example, and implementation acceptance must show that editing one
HPACK, worker, host, or shader shard rechecks that shard and ancestor interfaces
without reopening unrelated siblings.

Dynamic shader permutations are a valuable later pressure test, not part of the
one-pipeline cube behavior. The actionable finding is that the present
host/shader boundary and exact cross-ISA connections must be modular and
replaceable, not that this spike must silently become a render-graph system.

## Evidence boundary

Generated expansion, exact effect reports, rejected mutations, proof sizes,
incremental builds, IOCP substitution, and million/tens-of-millions scale runs
remain implementation acceptance gates. The design corpus must state their
interfaces and falsification tests now, but must continue to label their results
`not generated` or `not measured` until they run.
