# Bounded synchronous call ordering

The shared memory checker consumes the synchronization state carried by the
actual `MachineState`. This is the selected abstract interpretation of
`CallProtocol.handoff?` and `CallProtocol.return?`; generic loan transfer does
not create synchronization. It is not a claim about native CALL instructions,
DLL exports, or arbitrary external providers.

## Execution provenance

An ordering query returning `true` is not a race-freedom theorem about an
arbitrary constructed machine. The interpretation requires an admitted initial
state and the actual transition history:

- `MachineState.initial` starts with empty synchronization. The fresh Win32
  loader also checks `inputs.environment.synchronization = .empty`; its supplied
  memory-event history is retained.
- Ordinary `Op.step` execution extends only the performing context's frontier
  with its actual committed event. Refusal cannot invent a committed event.
- Successful synchronous handoff joins the caller frontier into the agent and
  records the exact call, caller, agent, and complete ordered loan-ID list.
- Successful return requires that captured occurrence and joins the agent
  frontier into the caller. Issued call identities remain recorded after return.
- Raw execution and provider receipts must retain the actual predecessor and
  resulting machine. Replacing its synchronization field with a state from
  another derivation does not establish an admitted transition.

Constructor privacy is not the source of execution authority. The initial
condition and closure under the actual operation and call transitions are the
required provenance invariant. Native applicability and correspondence between
separate provider and raw histories remain their existing refinement obligations.

## What the checker consumes

`MemoryEvent.Conflicts` remains a structural predicate over captured backing
footprints and atomic compatibility. Each conflicting event from another
context is refused unless the canonical frontier orders that exact earlier
event before the prospective event. A permitted predecessor cannot hide a
second unordered conflict.

The query checks the complete stored history prefix, earlier-event membership,
the prospective fresh identity, and absence of that identity from the current
history. Replaying a memory suffix derives only within-context program order.
Neither list position nor event-ID magnitude creates cross-context ordering.
Frontier joins retain transitive predecessors.

Return changes synchronization even when it appends no memory event. This is
why evidence lives in the canonical machine rather than in an independently
selected policy or a certificate matched only against an event-list prefix.

## Shared evidence and regression coverage

`Synchronization` supplies history and frontier preservation laws.
`CallProtocol.handoff?_synchronization` and
`ReturnEffects.synchronizationReturned` expose the exact checked updates;
their framing laws preserve memory-event history and unrelated machine fields.
There is one operation-step engine, shared by provider operations and CPU
receipts.

`Tests/Memory/CallProtocolOrdering.lean` checks the actual caller store,
handoff, provider write, matched return, and caller reload. Its controls cover
missing synchronization, pre-return access, wrong tuples, replay, stale/future
history, an unrelated conflicting context, and transitive joins. These are
bounded model checks, not a general native memory-consistency certificate.
