# Channel agency prerequisite for deadlock proofs

Experimental evidence, based on directed-conformance checkpoint `36ebd13c`.
This is not a deadlock-freedom theorem or a new certificate gate.

The selected baseline must exclude an internally blocked subset even while
unrelated participants can run. Permitted external nonresponse and declared
idle behavior remain distinct from internal deadlock. Termination, starvation
freedom and responsiveness are separate obligations. An enabled action somewhere
in the network is therefore insufficient evidence for this baseline.

## Checked facts

- [ReceiveCoverage](../Tests/Process/ReceiveCoverage.lean) checks every current
  `NetworkTransition` constructor. A changed delivery cursor forces the exact
  receive constructor on that same edge and session, with its actual `Delivers`
  witness. Close and channel death preserve the cursor explicitly; the other
  non-receive constructors preserve it through their scopes. This proves neither
  process progress nor demand settlement.
- [ChannelAgencyGap](../Tests/Process/ChannelAgencyGap.lean) reuses the existing
  exact initial network and the canonical send and receive steps. The receive
  frontier has no instance in the exact receiver slot named by the session;
  the post-world still has none. Separately, `Delivers.scope` preserves every
  process instance, including its local state and outstanding bag.
- The same file constructs an actual local result step at an empty-channel
  frontier and excludes every channel delivery there. That frontier is not
  asserted reachable. A genuine external result needs no channel receipt, so
  this is not a claim that the demonstrated tick is invalid. It shows that a
  local result step alone does not establish an internal source.
- [ReceiveReadiness](../Tests/Process/ReceiveReadiness.lean) studies the selected
  channel's operational guards and proves their equivalence to the exact receive
  witness for an arbitrary pre-world, using an explicit updated world. The
  selected wire, occurrence and cursor-zero condition remain fixture-specific.
  Missing, resolved and
  concretely different-session cases exclude that receive. This concerns the
  current escrow/cursor operation; it cannot certify a live receiver or handling
  of the receiver's declared event.
- [EscrowReceiveUpdate](../Tests/Process/EscrowReceiveUpdate.lean) constructs the
  deterministic ledger update for an outstanding occurrence, retaining the
  other resolutions, creation order, cancellation data and ledger invariants.

## Missing operational connection

`ChannelContract.receiverInput.arrives` names the event a message means at the
receiver. Its `arrivesUnsettled` law says that arrival settles **none** of the
receiver's existing demands. `NetworkTransition.receive` does not invoke that
event's local protocol transition. Conversely, `StepsLocally.protocolStep`
checks the local step and demand accounting but carries no concrete event source.
`senderOutput.emits` is also not consumed by the send transition.

Resolving escrow by timeout or drop does not by itself answer a process demand.
Likewise, `ProcessEvent.arrivesFromOutside` classifies results syntactically and
cannot establish that an internally produced result is an external escape.
These distinctions must survive any eventual dependency analysis.

The bounded reuse search covered current `Grass/Process`, newer architecture,
frontend and memory checkouts, and the spare branches
`agent/c-process/docstring-claims-swept`,
`agent/c-process/m4-reach-the-dead-worlds`, and
`agent/c-process/m4-weave-and-composition`. No operational consumption of the two
channel embeddings was found there. `Mailbox.SelectiveReceive` supplies useful
occurrence/residual accounting, while `ChildDemandBinding` supplies outcome
classification; neither is currently spent by this channel/local transition.
This is a scoped search result, not an assertion about every repository branch.

## First correction reviewed by architecture

Treat the existing receive as consumption: `ChannelSession.delivered` already
describes how many occurrences the receiver consumed. Reuse the local semantic
effects of `StepsLocally` at the exact `receiverInput.arrives` event, pinning the
live receiver to the session's receiver reference including generation. Combine
the local instance, actual shared writes and pending-observation scope with the
exact escrow/session scope. Factor the shared local effects once instead of
duplicating protocol, demand, identity and observation obligations.

This would consume one actual outstanding message and perform its declared
receiver transition together. Arrival still does not answer an old receiver
demand; the local step may issue new demands. Sender authorization and provenance
of other local events remain separate missing connections. The existing weaker
ledger fixtures can test ledger mechanics, but must not stand in for a complete
network receive after that correction.

An explicit inbox with separate delivery and consumption is an alternative if
the selected semantics requires those to be separate observable scheduling
points. It needs actual world storage, exact occurrence consumption and framing;
an unspent receipt proposition is insufficient. The proposed atomic operation
does not yet claim equivalence to all asynchronous implementations.

Once the operational connection is sound, the bounded composition cases are a
reachable A/B cycle with runnable C, an ordered successful execution, a real OR
escape and an exact permitted external wait. Every sufficient alternative must
be covered by actual transitions. A finite graph theorem alone, an assumed
global freedom property, or the existence of some complete continuation does
not close the baseline or its preservation through lowering.
