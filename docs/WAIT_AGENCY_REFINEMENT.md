# External agency and completed replies

The shared [WaitBoundary](../Grass/Semantics/Waiting.lean) distinguishes an
externally controlled step from a completed response. At an exact pending
occurrence, every actual outgoing step must require the selected external
agency. A service step may retain that occurrence. An actual reply must be
allowed by its protocol and end that same occurrence's pending state.

Every allowed response has an actual finite realization: an existing
choice-bearing `Path` with no earlier reply, followed by the actual response
edge. The path retains intermediate states, graphs, choices and events,
including publication before the API response. The path laws derive pending
identity and external ownership at intermediate cuts. A permanently waiting
history itself still takes no step.

The existing [ReplyExtension](../Grass/Refinement/BehaviorMatching.lean) stores
that service path, final response edge and subsequent tail. Directed reply
translation compares actual completed responses and their retained histories;
it does not encode a provider action as a response or require an implementation
to produce every optional abstract error.

## Responsiveness concerns actual responses

[Environment.Settles](../Grass/Semantics/Environment.lean) requires an actual
allowed reply choice in a finite path or at an index of the supplied infinite
continuation. Taking a service step is insufficient. The strategy named
`responding` excludes stationary permanent waits; proving it responsive also
requires `InfiniteEventuallyReplies`. A model's independently proved absence of
infinite runs can discharge that premise. No fairness condition or filtering of
actual infinite continuations is introduced.

The [service regression](../Tests/Semantics/ServiceWaiting.lean) exercises an
external service step before a possible reply and an infinite unanswered service
stream. The latter remains an infinite complete execution and does not settle
the pending request merely by continuing to act.

## Exact correspondence and directed implementation

Exact [BehaviorCorrespondence](../Grass/Refinement/BehaviorCorrespondence.lean)
keeps the strict shared `BehaviorMatching.CompleteMatch`: terminal matches
terminal, infinite matches an actual infinite continuation, and waiting matches
waiting.

[ImplementationConformance](../Grass/Refinement/ImplementationConformance.lean)
reuses that strict witness and additionally admits a proved external-nonresponse
case. It retains the actual lower infinite continuation and an explicit finite
cut. At that cut there must be a permitted lower wait matching the upper wait.
At every subsequent actual cut:

- The same lower occurrence remains pending.
- The selected external agency owns the actual next choice.
- That choice is not a completed reply for the occurrence.
- The finite simulation relates the reached lower history to the same upper
  waiting history. Its observation law gives exact projected-observation
  equality at every such cut.

Finite publication before the selected cut remains in the matched history.
Subsequent publication cannot disappear merely because a step is called silent.
The raw infinite stream and its edges remain evidence; they are not equated to
the stationary lower-wait constructor. Program-owned infinite work has no new
matching case. There are no added upper self-loops and the authored
specification remains unchanged.

This corrects the overly broad interpretation that every *raw* infinite
execution must have an infinite authored counterpart. That rule remains valid
for exact correspondence and for program-owned divergence. Directed refinement
can abstract environment-owned activity only with the concrete evidence above.
The [directed regression](../Tests/Refinement/ExternalNonresponse.lean) constructs
this case and rejects non-external activity, completed replies and observation
disagreement; the existing [implementation tests](../Tests/Refinement/ImplementationConformance.lean)
still reject omitted errors, waits and program-owned divergence.

The fixed raw public `BehaviorModel` remains unfinished. In particular, checked
reply-path completeness and protocol permission at actual raw frontiers still
need domain proofs. The GetStdHandle gaps include exact protocol handoff/return
roundtrip and positive checked return-slot admission. This slice supplies no
native API proof, full raw deadlock theorem or public certificate substitute.
