# Glossary

**SpecProcess** — The one precious root semantic process indexing
`VerifiedProgram`. It captures composed specification DSLs and semantic child
processes behind one public transition/observation boundary, independently of
one target realization.

**Specification layer** — The neutral dependency layer imported independently
by `Semantics` and `Process`. It owns typed junctions, demand/result boundaries,
requirement keys, and other common contract vocabulary. It does not own the
precious behavior of a `SpecProcess` or a selected process realization.

**Behavior contract** — The portable part of a resource-parameterized specification which
names domain values, admitted inputs, observations, outcomes, safety, progress,
and functional relations without choosing a target representation.

**Resource model** — An application-independent selectable parameter stating
quantitative and lifecycle semantics over an extensible resource algebra,
including but not limited to memory. A specification depends on this model.

**Specification family** — The precious root-process definition parameterized by a
resource model. Different selected models instantiate the same program for
different deployment envelopes without reversing the dependency into
`ResourceContract behavior`.

**Selected resource semantics** — The finite, uniquely keyed snapshot of axis,
limit, exhaustion, lifecycle, and named capability operations used while
constructing one specification value. Downstream certificates recover it from
the exact `spec`; they do not repeat typeclass selection.

**Natural specification front end** — Relational, stream, trace/reactive,
grammar, protocol, temporal, resource, or domain syntax suited to a problem and
captured into the one common root-process behavior contract. These are
authoring modalities, not separate
refinement foundations.

**Target projection** — A reviewed mapping from an instantiated specification's
abstract observations, outcomes, capabilities, and demands to one coherent
platform/API/ISA profile, together with a theorem that the mapping preserves the
product claims. It is replaceable unless target representation is itself
part of the precious specification function.

**Modeled execution** — The disjoint union of a conforming execution and an
environment-violation execution. Runners may expose either.

**Conforming execution** — A finite or infinite execution whose ISA/platform and
environment behavior remains inside every selected profile contract.

**Environment-violation execution** — An execution carrying a first external
contract-violating event and the maximal conforming prefix before it. Assurance
ends at that boundary.

**Permitted execution** — Exactly a conforming execution. This term never
includes an environment-violation execution.

**Observation** — A typed event exposed by semantics. A specification selects a
projection; mandatory safety and ABI demands are never filtered away.

**Requirement** — A separate theorem demand imposed downward by a specification,
weave, provider, ABI, platform, or ISA.

**Requirement kind** — An invalidation and diagnostic facet attached to a
theorem demand. Its nominal extension key identifies a separately registered
kind exactly; it is not fallback semantics. A consumer needing kind-specific
laws must resolve the key through a typed registry or reject it.

**Process protocol** — A portable logical state/event/demand/result relation
for one process role. API and library operations are child process protocols.

**Semantic child process** — A process contract constructed or existentially
demanded by a specification DSL and captured behind the precious root
`SpecProcess`. Its contract may be precious; its selected witness and private
decomposition are not.

**Process realization** — A reviewed replaceable model/plan/driver which proves
refinement to the root `SpecProcess`. Its population,
state partition, channels, scheduling, and execution strategy are not precious.

**Partial process realization** — A graph indexed by an exact staged process
presentation of the root in which some finite role schemas have subsystem
certificates and others remain abstract. It carries proofs and accumulated
requirements but is not executable or emittable.

**Portable blend** — Repeated local process refinement which preserves exact
abstract boundaries and accumulates provider/resource/obligation requirements
without claiming a target ISA or artifact.

**Machine blend** — The post-projection family assigning exact heterogeneous
machine sources and cross-ISA connections to every closed portable scope. The
machine certificate consumes this same value and proves complete coverage.

**Process plan** — A reviewed replaceable realization choice describing process
instances/population, local and shared logical state, channels, routing,
supervision, and composition. It proves refinement to the precious
specification; it is not itself precious unless a detail is observably demanded.

**Hoare channel** — A process channel whose send and receive transitions carry
exact pre/post contracts for process state, message occurrence identity,
ownership, obligations, and framed nonparticipants. Send deposits them in a
stable in-flight escrow assertion which is the receive precondition; escrow owns
one affine resolve token for the exact historically fresh occurrence, so it can be received or disposed at
most once. Unrestricted pending may retain it forever.

**Flattening** — Hiding a proved process network behind one process protocol
whose private state is the logical network and whose steps are exact network
transitions. The result may be registered as one node for fractal composition.

**Serialization of a process plan** — A proved relational single-threaded
executor preserving and reflecting the plan's complete execution behavior.
Unlike semantic flattening, physical serialization requires branch completeness,
commutation/linearizability, observation, obligation, and progress proofs.

**Byte flow** — An ordered asynchronous byte protocol in which partial reads
produce chunks and partial writes commit prefixes without treating provider call
boundaries as application framing. Functional rechunking erases timing/capacity/
cancellation cuts; full asynchronous relations preserve and map those cuts.

**Resource metric** — An axis-indexed valuation of owned network resource state.
Reachable-state invariants and explicit scope-flux/composition witnesses derive
bounds for bytes, descriptors/handles, threads, GPU objects, work, or products.

**Process independence** — A proof that two enabled network transitions have
disjoint or commuting local/shared state, channel escrow, obligations, provider
effects, and boundary observations. Independence yields a diamond and permits
an adjacent syscall-trace swap.

**Process loop invariant** — The derived global-loop relation combining every
live process invariant, population, shared-access and channel laws, outstanding
children, obligations, observations, progress state, and physical
representation.

**Specification suite** — The precious finite composition of domain-specific
DSL components and typed semantic junctions. It is captured into the single
root `SpecProcess` consumed by `VerifiedProgram` without specifying execution
weaving.

**Contract fragment** — The common denotational interface exported by a
specification DSL: typed ports, assumptions, guarantees, observations, failures,
progress, and selected-resource use.

**Spec junction** — A precious typed relation connecting ports of two contract
fragments and proving coverage and preservation. It describes semantic flow,
not assignment to processes, APIs, buffers, or instructions.

**Obligation** — A linear ghost resource whose current holder must perform or
lawfully transfer a future action.

**Ghost operation/state** — Proof-relevant structure used before emission and
erased before raw instructions are serialized.

**Fragment constructor** — A typed Lean function that generates an exact finite
instruction fragment and exports a parametric theorem for the entire generated
family. Assembly quotation and splicing are its source surface; it is not a
textual substitution phase.

**`withStack` binder** — A lexical assembly construction form that introduces
typed addressable stack objects and contributes their layout/lifetime demands
to an inspectable frame plan. It tracks initialization, provenance, loans, and
non-escape without implying hidden initialization or finalization.

**RawProgram** — A program containing only concrete target operations and
layout/link information. It is executable and fuzzable but unverified by itself.

**Provider key** — A nominal identity used to propagate one coherent API choice
through composed subsystems.

**Platform plan** — The explicit mapping from provider keys and requirements to
platform/API/ISA profiles.

**Provenance** — Generative allocation identity and ancestry that authorizes a
pointer to designate storage. Numerical address equality is insufficient.

**Loan** — A uniquely identified temporary transfer or sharing of access
authority. A count may be derived; identities are authoritative.

**Frontier** — A law-bearing protocol state that performs a specification-level
interaction or transfers agency to a named environment/context. A label, no-op,
or immediately returning synthetic yield is not a frontier by itself.

**Cancellation summary** — Optional compositional metadata describing a
process's safe cancellation points, custody of an affine pending request,
progress/delay premises, and exact terminal disposition. Ordinary serial
functions need no richer cancellation proof; explicit combinators derive
stronger summaries under sequencing, choice, loops, parallel composition, and
supervision.

**Connection theorem** — A proof that two adjacent representations describe the
same permitted behavior, especially that emitted bytes decode/load to the raw
program whose semantics were verified.

**Profile** — A cited, versioned contract for an ISA, ABI, platform, API, binary
format, or validation environment.
