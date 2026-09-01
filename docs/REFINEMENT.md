# Refinement pipeline

Grass follows six conceptual acts. They need not each be one stored datatype;
they must occur in order and each adjacent change must have a cheap, reusable
proof interface.

## Act 1: high-level refinement

Authors express structure using high-level monads and ordinary Lean models. They
prove demanded functional, safety, progress, and liveness properties at the
highest useful level. Missing lower-layer facilities are introduced as nominal
typeclass requirements with laws, not assumed implementations.

Portable code may demand an abstract effect; target-specific code may demand a
specific provider family. Requirements remain explicit data/propositions so
they can be propagated and reviewed.

## Act 2: weave

Weaving composes programs, specifications, observations, requirements, and
proofs. It includes sequencing, parallel composition, linking, shared-state
composition, adapters, and proofs of noninteraction between independently
running components.

Weaving must preserve existing theorems and may introduce new interference,
provider-coherence, resource, progress, or obligation requirements. It must not
silently resolve conflicts through instance priority.

## Act 3: platform realization

An explicit `PlatformPlan` owns a `ProviderEnv` assigning nominal provider keys
to cited API/platform profiles and proves compatibility. Typeclasses are
projections of that explicit environment; the plan does not perform a later
ambient search. Realization proves that the exact dictionary used by upstream
definitions and proofs is the selected provider. Provider identities and
environment evidence are ghost-propagated through requirements, ABIs, blocks,
calls, and obligations.

One provider key has one realization. Intentional multi-backend programs use
distinct keys and prove their coexistence. Platform, ISA, and API set are
independent axes constrained by the plan.

Each high-level operation is refined to its provider operation with a simulation
or equivalence theorem over all results the provider permits.

## Act 4: CFG realization

Monadic structure becomes a typed CFG. Platform operations become typed calls.
Block bodies may still contain Lean requirement descriptions. Each block entry
contract names registers, stack, memory shape, ghost state, obligations, and
progress assumptions. Each edge proves it satisfies the target contract.

Labels are Lean identifiers (`Name`) wrapped with a scope-unique nominal identity
and a no-duplicate proof. They are not unvalidated strings or final addresses.
Indirect edges require a proved finite target set or are rejected.

## Act 5: fractal lowering

A requirement description is repeatedly replaced by concrete operations or
calls/edges to further blocks. Lowering may produce zero, one, or many operations
and dependent outcomes. Mixed realized and unresolved bodies are allowed during
construction; `VerifiedProgram` requires closure.

The process stops only when every reachable body is a raw-erasable CFG over the
selected ISA and platform calls. A `StraightLineOp` may internally contain CFG
structure only with a proof that its only normal exit is after its final logical
operation; all other fault/interruption exits remain declared.

## Act 6: optimization

Optimization may occur at high-level structure, CFG, layout, or instruction
sequences. Each pass proves preservation of the relevant projected functional
behavior and every independent mandatory demand. Proofs should depend on
abstract block/effect theorems so instruction scheduling and layout changes do
not re-prove unrelated high-level properties.

## Libraries and proof economy

Libraries package specifications, requirements, refinements, ABIs, verified
blocks, exports, serializers, and automation. Reusable theorems own routine
drudgery. Automation may construct proof terms; it may not replace kernel
checking or hide unresolved cases.

The pipeline is complete only with a composed connection chain from the original
specification to the final loaded artifact. Pairwise theorems that are never
composed are insufficient.
