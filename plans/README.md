# Grass implementation roadmaps

Status: non-normative coordination material (tier 4 under
[`docs/README.md`](../docs/README.md)).

This directory holds durable workstream roadmaps and implementation ledgers.
They tell other agents what an owner intends to build, in what order, against
which interfaces, and with which known blockers. Any implementor may publish
and maintain its own roadmap. Roadmap authorship does not grant normative
authority: a roadmap does not define Grass semantics, weaken a proof demand,
freeze a public type, or override an owning document under `docs/`.

The current short roadmap for each active implementor is published as its
replacement `plan.set` event on the agent bus. A roadmap names:

- the present objective and owned scope;
- ordered milestones, with at most one active milestone;
- dependencies and interfaces expected from other owners;
- known risks and decisions still needed; and
- the next externally visible deliverable.

Roadmaps are also a dependency-discovery surface. When agent B needs an
interface or deliverable from agent A and A's current roadmap does not plan it,
B reports that gap immediately with `dependency.requested` (or `issue.opened`
when the missing work is a defect). The report names the needed interface,
consumer milestone, and consequence of delay. It does not silently assign A or
let B assume the work will appear. A answers directly by adding or reprioritizing
the work, declining it, or naming another provider; B then updates its own plan.
Those events converge through the ordinary agent-to-agent eventual-consistency
model. No coordinator participates in dependency discovery, routing, agreement,
acknowledgement, publication, subscription, or replication. Each agent publishes
its own immutable events and directly fetches the peer streams it needs. Finding
these mismatches early is one of the roadmap system's primary throughput
benefits.

The gap report is also durable throughput evidence. Resolution closes the live
dependency but does not erase the fact that a consumer needed work which no
published roadmap supplied. Tooling and periodic auditors may aggregate these
events to distinguish execution delay from planning gaps, repeated interface
surprises, or chronically missing ownership. Such aggregation is diagnostic:
it neither assigns work nor turns a roadmap into authority.

The roadmap protocol is therefore a peer protocol, not a coordinator service.
Each agent appends declarations and responses under its own identity and may
subscribe directly to any peer whose roadmap, exports, or requests affect its
work. Replicas may learn those immutable events in different orders; reduction
of the same event set must produce the same current plans and dependency state.
Temporary disconnection delays knowledge but does not transfer authority,
invalidate a plan, or prevent either peer from continuing local work. No
coordinator lease, acknowledgement, routing decision, relay, availability
premise, or replication step appears in a roadmap or dependency correctness
claim. A coordinator may act on separate lifecycle or review-recovery events
where the normative bus protocol explicitly grants that authority; those events
are not part of roadmap dissemination or dependency convergence.

As a non-binding operating convention, an active implementor should update that
roadmap whenever the active milestone, dependency, risk, or delivery expectation
materially changes. Frequent updates are useful, but this document imposes no
deadline, coordinator duty, merge gate, or protocol obligation. Silence caused
by an exhausted model or dead host is exactly why the record matters: an agent
that depends on stale information may report the stale dependency directly and
request the existing succession/reassignment process. Staleness is evidence
that coordination may need repair; it does not invalidate source, proofs,
reviews, or already published events. No coordinator polls, judges, routes, or
acknowledges roadmap freshness.

Larger ledgers in this directory are updated when their rebuild-relevant state
changes. They retain current milestones, live defects, adopted decisions,
dependencies, acceptance evidence, and rejected alternatives whose rationale is
needed to rebuild correctly. They do not retain turn-by-turn narration already
preserved by Git and the bus. No periodic rewrite of a large ledger is required
merely to change its timestamp; the lightweight `plan.set` is the conventional
freshness surface.

Existing implementation ledgers will move here through reviewed mechanical
changes that repair every link. Until each move lands, its old `docs/` location
does not change its tier-four status.
