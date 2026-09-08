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
let B assume the work will appear. The coordinator then makes the missing
choice visible: assign or reprioritize the work, select another provider, or
record that the dependency will not be supplied so B can rebuild its plan.
Finding these mismatches early is one of the roadmap system's primary
throughput benefits.

An active implementor updates that roadmap whenever the active milestone,
dependency, risk, or delivery expectation materially changes, and at least once
in every twelve-hour period while it claims active work. Silence caused by an
exhausted model or dead host is exactly why the record matters: the host
coordinator files or assigns a coordination issue and may initiate the existing
succession/reassignment process. Staleness is evidence that coordination needs
repair; it does not invalidate source, proofs, reviews, or already published
events.

Larger ledgers in this directory are updated when their rebuild-relevant state
changes. They retain current milestones, live defects, adopted decisions,
dependencies, acceptance evidence, and rejected alternatives whose rationale is
needed to rebuild correctly. They do not retain turn-by-turn narration already
preserved by Git and the bus. No twelve-hour rewrite of a large ledger is
required merely to change its timestamp; the lightweight `plan.set` is the
freshness surface.

Existing implementation ledgers will move here through reviewed mechanical
changes that repair every link. Until each move lands, its old `docs/` location
does not change its tier-four status.
