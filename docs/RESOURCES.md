# Semantic budgets and execution envelopes

Resource reasoning has two independently replaceable tiers. Mixing them makes a
portable specification accidentally select an operating-system architecture;
separating them does not remove resource behavior from the specification.

## 1. Semantic budget

A `SemanticBudget` is a parameter of the precious specification family. It
contains only facts which change admitted behavior or promised observations:

- maximum admitted concurrent sessions or streams;
- protocol-visible frame, header, window, and request limits;
- externally promised deadlines and backpressure behavior;
- exhaustion outcomes visible at the product boundary; and
- resource axes over which the specification exports a bound.

The specification function is precious; a selected budget value is a reviewed
build parameter. A web-server definition may therefore be instantiated for a
microcontroller and a data center without rewriting its behavioral relation.

## 2. Execution envelope

An `ExecutionEnvelope` belongs to the process/platform plan. It includes:

- worker/thread population and scheduling policy;
- socket, handle, file-descriptor, completion, and queue capacities;
- polling quantum or completion-provider configuration;
- concrete buffer, arena, stack, and static-object sizes;
- allocator/storage strategy; and
- platform-specific reserve needed to realize the semantic budget.

Changing a four-thread `WSAPoll` realization to one IOCP dispatcher does not
change the root specification when both realize the same semantic budget.

```lean
structure RealizesSemanticBudget
    (envelope : ExecutionEnvelope platform)
    (budget : SemanticBudget) : Prop where
  admission : envelope.capacity >= budget.maxAdmitted
  representation : EverySemanticHoldingHasPhysicalRepresentation envelope budget
  backpressure : PhysicalQueuesImplementSemanticBackpressure envelope budget
  deadlines : SchedulerAndProviderBoundsMeetPromisedDeadlines envelope budget
  exhaustion : PhysicalExhaustionRefinesSemanticOutcome envelope budget
  lifecycle : PhysicalCustodyDischargesSemanticResourceLaws envelope budget
```

This is not generally a one-line arithmetic `decide`: capacity inequalities may
be decidable, while queueing, scheduling, lifecycle, and exhaustion require
proved plan theorems. A materialized machine resource policy is derived from the
pair and remains non-precious.

## 3. Classification rule

The ownership test is counterfactual:

- if changing the value may lawfully change admitted or observed product
  behavior, it belongs in the semantic budget;
- if changing it only changes how the same behavior is realized, it belongs in
  the execution envelope;
- if both are affected, define a semantic demand and a separate physical
  provision connected by `RealizesSemanticBudget`.

Thus HTTP/2 maximum admitted streams and an externally promised stream deadline
are semantic. Worker count, socket-handle reserve, receive-ring bytes, and a
10 ms polling quantum are physical. The envelope theorem connects the latter to
the former without copying physical constants into `Spec.lean`.

## 4. Composition and bounds

Both tiers use the open resource algebra. A composed specification combines
semantic demands axis by axis. A composed plan combines physical provisions,
holdings, and flux proofs. The realization theorem is framed: an unrelated axis
is preserved automatically, and subsystem envelopes may be changed
independently when their exported provisions and shared-axis equations remain
unchanged.

Process blending may therefore lower Vulkan resources in one proof and IOCP
storage in another. The final plan proves that all envelopes jointly cover the
one captured semantic budget and that shared physical resources do not double
count custody.

## 5. Spike rule

Maintained spikes place semantic budgets in `Resource.lean` and selected
physical envelopes in `Envelope.lean` or `Plan.lean`. `Spec.lean` imports only
the former. Generated dependency reports must demonstrate that changing worker
count, polling mode, buffer layout, or provider capacity does not re-elaborate
the precious specification module.

Spike 4 is the first acceptance fixture: its HTTP/2 limits and externally
promised deadlines are semantic, while its four-worker Win32 polling pool,
handles, buffers, and fixed-after-ready storage are one replaceable envelope.
