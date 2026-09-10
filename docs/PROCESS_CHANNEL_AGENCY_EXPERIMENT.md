# Channel agency prerequisite for deadlock proofs

Receiver-agency implementation note. Diagnostic checkpoint `ae8a9fa0` is based
on directed-conformance checkpoint `36ebd13c`; the correction below builds on
that evidence. This is not a deadlock-freedom theorem or a new certificate gate.

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
- At `ae8a9fa0`, `ChannelAgencyGap` reused an exact initial network and canonical
  send/receive steps to exhibit consumption with no receiver instance before or
  after. The corrected [regression](../Tests/Process/ChannelAgencyGap.lean)
  retains the initialized send but rejects consumption at that absent-receiver
  frontier. Unrelated instances remain framed; the receiver now performs its
  declared local transition.
- The same file constructs an actual local result step at an empty-channel
  frontier and excludes every channel delivery there. That frontier is not
  asserted reachable. A genuine external result needs no channel receipt, so
  this is not a claim that the demonstrated tick is invalid. It shows that a
  local result step alone does not establish an internal source.
- [ReceiveReadiness](../Tests/Process/ReceiveReadiness.lean) studies the selected
  channel's escrow/cursor guards and proves their equivalence to its ledger
  operation for an arbitrary pre-world, using an explicit updated world. The
  selected wire, occurrence and cursor-zero condition remain fixture-specific.
  Missing, resolved and concretely different-session cases exclude that ledger
  operation. It is now explicitly `EscrowDelivery`, which has no network-step
  constructor. These guards alone do not certify actual receiver readiness.
- [EscrowReceiveUpdate](../Tests/Process/EscrowReceiveUpdate.lean) constructs the
  deterministic ledger update for an outstanding occurrence, retaining the
  other resolutions, creation order, cancellation data and ledger invariants.

## The diagnosed connection and remaining gaps

`ChannelContract.receiverInput.arrives` names the event a message means at the
receiver. Its `arrivesUnsettled` law says that arrival settles **none** of the
receiver's existing demands. Before the correction, `NetworkTransition.receive`
did not invoke that event's local protocol transition. `StepsLocally.protocolStep`
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

## Receiver correction reviewed by architecture

The corrected receive is consumption: `ChannelSession.delivered` already
describes how many occurrences the receiver consumed. `Delivers` reuses the
factored `LocalStepEffects` at the exact `receiverInput.arrives` event, pinning
the live receiver to the session's receiver reference including generation.
The receive constructor retains the selected boundary emission, issued bag and
local observation segment as data, matching the ordinary local-step constructor.
An existential proposition would erase the selected local outputs when their
boundary projections agree. The [choice/interference
regression](../Tests/Process/ReceiveInterference.lean) proves distinct local
outputs remain distinct transitions at identical worlds and boundary output.
`DeliveryScope` combines the local instance, actual shared writes and changed
pending observations with the exact escrow/session scope. Local steps and
receives share the protocol, demand, identity and observation obligations.

This consumes one actual outstanding message and performs its declared
receiver transition together. Arrival still does not answer an old receiver
demand; the local step may issue new demands.
[Receive](../Grass/Process/Network/Receive.lean) derives receiver liveness, the
impossibility of consumption without a receiver, unrelated-instance framing,
and the actual receiver transition's demand equation. Sender authorization and provenance
of other local events remain separate missing connections. The existing weaker
ledger fixtures test ledger mechanics, and cannot stand in for a complete
network receive.

[InitializedReceiveFixtures](../Tests/Process/InitializedReceiveFixtures.lean)
supplies an exact initial network for its selected plan, spawns a fresh
generation-1 receiver, sends onto the matching session, and consumes through
the receiver's actual protocol step. Its final well-formedness follows through
those three concrete steps. The old raw fixture's conditional well-formedness
claim is not used as positive execution evidence. The channel relation and
contract are parameterized once, with both fixture plans using that construction.

An explicit inbox with separate delivery and consumption is an alternative if
the selected semantics requires those to be separate observable scheduling
points. It needs actual world storage, exact occurrence consumption and framing;
an unspent receipt proposition is insufficient. The atomic operation
does not yet claim equivalence to all asynchronous implementations.

Once the operational connection is sound, the bounded composition cases are a
reachable A/B cycle with runnable C, an ordered successful execution, a real OR
escape and an exact permitted external wait. Every sufficient alternative must
be covered by actual transitions. A finite graph theorem alone, an assumed
global freedom property, or the existence of some complete continuation does
not close the baseline or its preservation through lowering.

## Validation scope

All 110 process-library and process-test build jobs pass. The imported-closure
trust check covers 8,160 project declarations across 123 project modules,
allowing only the established standard axioms and rejecting unsafe declarations
and compiled replacements. Spike-source mirrors and all 71 documentation files'
relative links pass their checks.

The full/source-input build remains blocked by the inherited, unchanged
`Grass.Certificate` migration on this branch's parent. These results do not
claim a passing whole-repository certificate build or completion of the
deadlock-freedom baseline.
