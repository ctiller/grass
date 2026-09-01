# Execution semantics

This document owns execution, nondeterminism, observations, safety, progress,
and liveness. Memory-event validity is owned by [MEMORY_MODEL.md](MEMORY_MODEL.md).

## 1. Relational authority and executable runner

The normative semantics is relational. Given one complete state, it may admit
multiple next transitions for scheduling, interrupts, weak-memory choices,
spurious wakes, allocation addresses, API results, and specified implementation
choice.

Conceptually, a modeled execution packages the state/event sequence with one
coherent global execution witness:

```lean
Execution : InitialState -> Trace -> ExecutionGraph -> Prop
StepExtension : ExecutionPrefix -> ExternalChoice -> ExecutionPrefix -> Prop
```

`StepExtension` monotonically extends the same graph witness. It may not choose
independent per-step reads-from or ordering facts that compose into a forbidden
cycle. Every finite runner prefix carries a proof that it is extendable to an
admitted finite terminal execution or infinite execution. Infinite executions
have a profile-defined limit condition whose finite restrictions agree with the
monotonic graph and whose complete graph satisfies global consistency.

The executable interpreter consumes a `ChoiceOracle` and fuel. It must prove
that every produced prefix is admitted and remains extendable; local choices
that lead to no coherent complete execution are not permitted runner prefixes.
The oracle makes runs replayable; it does not reduce the universal proof demand.
`VerifiedProgram` quantifies over all modeled executions, not only executions
selected by one runner.

Malformed, unavailable, or exhausted environment/oracle responses are explicit
outcomes. The interpreter must never invent a friendly default.

Environment interaction is a dependent request/response protocol. For each
request `q`, its profile defines `Response q` and `Allowed q r`. A permitted
execution may choose any `r` satisfying `Allowed q r`; subsequent memory and
control state may depend on that exact response. This covers return values,
output buffers, partial I/O, callbacks, and cancellation without separating a
value stream from the state changes it authorizes.

The choice oracle has namespaced channels for environment responses, scheduler
selection, interrupt/fault delivery, allocation/layout choice, and
architecture-specific consistency witnesses. Consumers cannot read another
channel accidentally. Fixing all channels makes the runner deterministic;
proofs remain universal over every well-formed oracle.

## 2. Execution forms

Executions may be finite or infinite. A finite execution ends in exactly one:

- successful program result;
- specified program failure;
- handled or terminal architectural fault;
- environment-contract violation;
- no admitted transition from a state declared terminal;
- fuel exhaustion in the executable runner only.

Fuel exhaustion is not a semantic program outcome. It returns a proved safe
finite prefix and is otherwise inconclusive.

Architectural faults are events with specified control behavior. A fault may
terminate, transfer to a handler, or be returned by an API. Audit violations are
separate monotonic evidence that a modeled safety demand was broken. Verified
programs prove that no reachable conforming execution appends such a violation
and that no disallowed fault occurs.

An environment-contract violation is a modeled execution boundary but is not a
conforming environment behavior. The fundamental theorem gives full guarantees
to conforming executions and only a matched safe prefix ending immediately
before the first contract violation. It must not project or normalize the
post-violation suffix as if it satisfied the specification.

## 3. Observations

The complete audit trace may include:

- input and API return values;
- output requests and partial completions;
- syscalls and API calls;
- memory and synchronization events;
- allocation and provenance events;
- faults, interrupts, cancellation, and process/thread lifecycle;
- obligation creation, transfer, discharge, and terminal disposition;
- program results and exit codes.

A specification owns an `ObservationProjection` selecting and normalizing only
the functional events it cares about. Projections may coalesce permitted partial
writes or hide internal calls only when a theorem establishes that normalization
is lawful. They cannot suppress safety, ABI, applicability, connection, or
obligation demands; those are independent `VerifiedProgram` fields.

For an input routine or imported call, equivalence quantifies over every result
allowed by its profile, including short operations, interruptions, failure
codes, and dependent output memory.

## 4. Safety over prefixes

Safety is prefix-closed. `PrefixSafe p` states that a finite execution prefix:

- contains no memory, race, provenance, initialization, or permission violation;
- takes only applicable instructions and APIs;
- follows typed CFG edges and ABI contracts;
- preserves the obligation ledger;
- has only declared faults, interrupts, and effects.

`VerifiedProgram` proves `PrefixSafe` for every finite prefix of every permitted
execution. This establishes infinite-run safety because any safety violation has
a first event in a finite prefix.

## 5. Progress and liveness

Safety does not imply progress. Each reachable nonterminal state and every
permitted continuation must establish one explicit `ProgressCase`:

- it reaches a terminal state in finitely many internal steps;
- it reaches a law-bearing environmental frontier in finitely many internal
  steps and transfers agency or performs a specification-meaningful interaction;
- it is currently waiting at such a frontier under a specified protocol; or
- it transfers control to a separately verified component with an equivalent
  progress demand.

Every reachable cyclic CFG strongly connected component must either have a
well-founded decreasing rank or necessarily cross a declared frontier. Nested
reactive loops satisfy the rule recursively. Merely having an exit condition is
insufficient if execution can spin internally before observing it.

A frontier is a protocol state, not a user-applied label. Its laws identify the
external request/yield, the party receiving agency, its possible responses, and
the resulting trace event. A synthetic no-op or yield that immediately returns
control cannot certify a cycle unless a separate productivity theorem connects
it to a specification observation. The rule is universal: one good branch does
not excuse another permitted branch that spins.

A reactive contract proves:

- safety for all finite and infinite input histories;
- productivity under stated platform/fairness assumptions;
- finite handling between frontiers; and
- conditional termination, for example `EventuallyQuit input -> Terminates`.

Unconditional termination is required for programs whose specification demands
it. Interactive programs may instead use the reviewed reactive contract.

Fairness and responsiveness are never global axioms. A liveness theorem names
the precise scheduler, API, device, or user-response assumptions it consumes.
Safety must not depend on them. If an environment never answers a permitted
blocking request, a program may remain at that frontier without violating local
progress; it cannot claim conditional termination unless its assumption requires
that response.

## 6. Refinement

For a deterministic specification, every conforming execution must produce its
specified projected observation for the same environmental choices. For a
permissive specification, implementation observations must be a subset of the
allowed behavior relation. Infinite traces use coinductive/trace refinement;
finite terminating cases may use ordinary equality or simulation.

Optimization may change instruction traces, layout, timing, or internal API
structure only if it preserves the selected functional observation and every
independent mandatory demand.

## 7. Adequacy and non-vacuity

Every execution profile supplies an adequacy package:

- the set of valid initial states is nonempty;
- each valid initial state has at least one admitted finite or infinite modeled
  execution;
- a terminal initial state admits a zero-step conforming execution carrying its
  terminal result, observation, ABI state, and obligation ledger/dispositions;
- each reachable environment request has an allowed response or a modeled
  pending/infinite-wait execution;
- the initial empty execution prefix exists and is extendable;
- oracle well-formedness has witnesses for every admitted choice pattern
  required by the profile.

Universal safety/refinement theorems do not count if their execution or response
domains are empty. Adequacy is a separate `VerifiedProgram` requirement so a
proof cannot hide non-emptiness inside an opaque semantic predicate.
