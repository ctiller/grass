# Glossary

**Specification** — A Lean program or relation describing accepted observations
and functional behavior, independently of one target realization.

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

**Obligation** — A linear ghost resource whose current holder must perform or
lawfully transfer a future action.

**Ghost operation/state** — Proof-relevant structure used before emission and
erased before raw instructions are serialized.

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

**Connection theorem** — A proof that two adjacent representations describe the
same permitted behavior, especially that emitted bytes decode/load to the raw
program whose semantics were verified.

**Profile** — A cited, versioned contract for an ISA, ABI, platform, API, binary
format, or validation environment.
