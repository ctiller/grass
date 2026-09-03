# Agent workstreams and provider transition

Status: candidate for adversarial review. This document does not amend the
active version-one bus. It defines the responsibility boundary required for
provider exhaustion, replacement, and later return, plus an immediate
version-one operating procedure and the intended version-two representation.

## 1. Problem

Names such as `g-x86`, `c-x86`, and `c-reviewer` are useful provenance. They
identify the worker identity and, by convention, the model-provider family.
They are not durable organizational roles. GPT capacity may be exhausted while
x86 work remains; later, `g-x86` may legitimately take responsibility back from
`c-x86`.

Treating the prefix as authority produces two bad choices:

- rename a live identity and lose an honest authorship and review trail; or
- make `x86` depend permanently on the availability of one provider.

Grass instead separates an immutable **agent identity** from a transferable
**workstream**. Provider loss changes the assignment edge between them. It does
not rewrite either one's history.

This is an operational design, not a license to infer authority from silence.
Token exhaustion, provider failure, elapsed time, and a suggestive agent name
cannot transfer product scope or review authority by themselves.

## 2. Vocabulary

An **agent identity** is the single-writer bus identity already defined by
[AGENT_BUS.md](AGENT_BUS.md). Its registration, primary protocol role, event
history, and authored commits remain immutable. The human naming convention
may expose provider family, but validators never derive authority by parsing an
agent name. `provider` and `model` are diagnostic registration metadata.

A **workstream** is a stable, provider-neutral responsibility such as:

```text
design-steward
x86
spirv
win32
vulkan
process
stdlib
proof-kernel
vertical-integration
host-coordination/<host>
review/<pool>
```

Its charter states its purpose, required primary role, product scope, exported
interfaces, subscriptions, and any child workstreams. A broad workstream may be
split when parallel ownership is useful; shared writing is not smuggled in by
assigning one name to several simultaneous executors.

An **assignment epoch** is the exclusive, non-clock-based custody of one
workstream by one active agent identity. It pins:

```text
workstream key
generation
holder
predecessor assignment, if any
exact product checkpoint
active product branch
scope and export snapshot
accepted handoff
user or standing-policy authority
```

“Epoch” or “lease” does not mean timeout. It ends only through a validated
successor transition, explicit release, or authorized retirement. Silence never
expires it.

The assignment holder is the accountable custodian and default target for the
workstream. Other agents may contribute through separately claimed child scope,
dependencies, or recorded co-authorship. They do not acquire the custodian's
authority implicitly.

## 3. Invariants

The reduced bus state must enforce all of the following:

1. Every workstream key has at most one current assignment.
2. Every current holder is registered and has the workstream's required
   immutable primary role. Operational authority additionally requires the
   holder's lifecycle to be active. A paused or blocked holder retains custody
   in a suspended state; that state does not select a successor.
3. An assignment transition names the exact preceding assignment. Concurrent
   successors conflict; timestamps do not select one.
4. The successor explicitly accepts the exact checkpoint, scope, branch, open
   work inventory, and known limitations before activation.
5. Activation ends predecessor authority and begins successor authority in one
   registry transition. There is no interval with two valid custodians.
6. Product history, bus events, findings, and acknowledgements made by the
   predecessor remain attributed to it.
7. Product refs advance only by fast-forward or reviewer-owned merge. Transfer
   never permits force-push, deletion, or history replacement.
8. All commits introduced by a reviewed snapshot are attributed to their actual
   authors, regardless of the current holder or branch spelling.
9. Changing holder does not clear an issue, dependency, finding, obligation, or
   required acknowledgement.
10. Primary protocol role remains separate from workstream. An implementor does
    not become a reviewer by accepting a review workstream, and a reviewer does
    not gain product-authoring authority.
11. Provider diversity may be policy or useful review evidence, but correctness
    authority is never inferred from a `g-`, `c-`, or other prefix.
12. A returning former holder uses a new assignment epoch. It does not resume
    from its stale local branch or stale understanding of the bus.

These invariants make transitions reversible. For example, `g-x86` may hold
generation 7, `c-x86` generation 8, and `g-x86` generation 9 without either
identity impersonating the other.

## 4. Checkpoint contract

A handoff checkpoint is compact because the bus already owns most of its data.
It must nevertheless be mechanically complete:

```text
workstream
exact product commit
product branch
effective exclusive and shared scope
exported interfaces and consumed dependencies
completed verification with commands or evidence references
open issues and dependencies
open review nominations and findings
known limitations
next intended step
```

The checkpoint references existing bus events instead of pasting their prose.
The successor checks that the product commit exists, is reachable from the
named branch or immutable candidate as claimed, and matches the advertised
scope state. A summary without the exact commit is not a checkpoint.

Capacity information is deliberately coarse. An agent may report `paused` with
a reason such as “provider capacity unavailable.” Quota quantities, account
identifiers, credentials, and private provider state do not belong on the bus.

## 5. Transfer protocol

### 5.1 Cooperative transfer

The current holder prepares the checkpoint and proposes the successor. The
successor may inspect the checkpoint and build locally without authority, then
accepts or declines it. A host coordinator activates the accepted assignment by
compare-and-swap against the named predecessor assignment.

Activation is the linearization point. It simultaneously:

- makes the predecessor historical;
- installs the new holder and generation;
- transfers the workstream's effective scope and subscriptions;
- makes new work route to the successor; and
- preserves the checkpoint and complete predecessor chain.

The predecessor may answer questions afterward, but cannot author under the
transferred scope unless it receives a later assignment or a nonconflicting
child scope.

### 5.2 Unavailable holder

If the holder disappears before offering a handoff, a bootstrap-authorized
coordinator may propose a successor only under recorded user authority or an
already recorded standing failover policy. The proposal pins the last verified
product and bus checkpoint; it does not invent unfinished local work.

Wall-clock expiry and coordinator opinion are insufficient. Without user or
standing-policy authority, the workstream remains globally blocked even when a
replacement is obvious.

### 5.3 Return to a former provider

A returning worker first synchronizes the current workstream chain and exact
checkpoint. The current holder then follows the ordinary cooperative transfer.
The returning identity receives a new generation and works from that checkpoint.
Its older branch may remain as audit history, but is never treated as current
merely because its name again matches the preferred provider.

### 5.4 Splitting a live workstream

Splitting is one atomic registry transition, not several independent successor
assignments. `workstream.split.propose` names:

```text
the exact current parent assignment
the parent's retained charter, scope, exports, and holder
one or more new child keys and charters
each child's disjoint exclusive scope, exports, proposed holder, and checkpoint
the disposition of every open item routed to the removed parent scope
```

Every proposed child holder accepts its exact child assignment before the split
can activate. `workstream.split.activate` then performs one registry
compare-and-swap against the current parent assignment. It creates a successor
epoch for the parent over only its retained scope and creates the initial child
assignment epochs simultaneously. If the parent retains no scope, activation
releases its assignment and leaves the parent key as a historical namespace.

The retained parent exclusive scope and all child exclusive scopes are pairwise
disjoint. Their union is exactly the former parent exclusive scope: a split
neither duplicates authority nor silently abandons it. Shared paths may overlap
only when each resulting charter declares them shared. The parent holder has no
authority over a child's scope after activation unless that same identity is
also the child's accepted holder.

Version one cannot make this multi-assignment transition atomic. Its safe
fallback is gap-producing: the parent first narrows its `scope.set` to the
retained scope, then each accepted child holder claims its disjoint released
scope. Child claims before the parent release are invalid exclusive/exclusive
conflicts. A split that cannot tolerate the temporary unowned interval waits
for version two.

## 6. Product branches and review

A product branch is a collaboration and review vehicle, not an identity. A
successor may continue the named branch by fast-forward from the exact
checkpoint, or may create a new named branch from it when that gives a clearer
review boundary. Existing branches are never reset to manufacture continuity.

Authorship is computed over the commits selected for review. Therefore:

- if transfer occurs before nomination, the nomination names every actual
  author represented in the selected history;
- if a successor adds commits to an already nominated branch, the old
  nomination cannot silently expand its author set: finish the nominated
  snapshot or withdraw it and nominate a new snapshot with the complete author
  set;
- if an original author is unavailable and therefore cannot withdraw a
  stranded nomination, its named reviewer closes it with
  `review.nomination_declined`; the successor then creates a fresh nomination
  naming the complete actual author set. If that reviewer is also unavailable,
  an authorized `review.reassigned` first selects a replacement reviewer, who
  must personally decline the inherited nomination. No one fabricates an
  author withdrawal;
- a reviewer transition uses the existing `review.reassigned` chain, carries
  all findings forward, and requires the replacement reviewer to inspect and
  accept them personally; and
- an agent must not review work it materially produced through another identity.

An authorization already published remains candidate-specific under the active
review protocol. Provider transition does not broaden it. If its reviewer is
unavailable and the candidate did not win, the replacement constructs and
authorizes a fresh candidate.

## 7. Immediate version-one procedure

The current bus can perform a safe, slightly non-atomic cooperative transition
without waiting for version two:

1. While still active, the outgoing GPT-backed implementor publishes
   `handoff.offered` to a newly registered replacement identity, pinning its
   product branch and exact checkpoint commit.
2. The replacement inspects and publishes `handoff.accepted`.
3. The outgoing agent publishes an empty `scope.set`.
4. The replacement publishes its complete `scope.set` and plan from the exact
   checkpoint. This is the version-one operational cutover.
5. The outgoing agent publishes `agent.status = paused`, including its product
   branch and checkpoint commit.
6. The opener or coordinator reassigns every open issue and dependency. Open
   reviews follow [AGENT_REVIEW.md](AGENT_REVIEW.md), not the product handoff.
7. The coordinator publishes a concise progress notice recording the current
   provider-neutral responsibility map.

The release-before-claim order deliberately permits a short unowned interval
rather than overlapping authority. Product publication pauses across that
interval. A transition requiring continuous atomic custody waits for version
two.

If the outgoing identity has already become unavailable, version one cannot
fabricate `handoff.offered`: only the implementor may emit that event. Under
explicit user authority, a bootstrap coordinator instead retires the missing
identity, which deactivates its scope. The replacement then claims the released
scope from the last independently verified checkpoint, and the coordinator
records the takeover in a progress notice. This is auditable recovery, but it
is not misreported as an accepted handoff. Version two supplies the missing
coordinator-proposed assignment transition.

No old identity is renamed. In particular, `c-x86` takes responsibility for
`x86`; it does not call `agent.resumed` as `g-x86`. If the original `g-x86`
later returns, it may use `agent.resumed` for its own identity and then accept a
new handoff from `c-x86`.

## 8. Version-two representation

Version two should put workstream definitions and current assignments in the
low-volume protected `agent-registry` described by
[AGENT_COORDINATION_EVOLUTION.md](AGENT_COORDINATION_EVOLUTION.md). Ordinary
progress remains in sharded agent streams; assignment changes are rare and need
the registry's compare-and-swap membership cut.

The conceptual operations are:

```text
workstream.register
assignment.propose
assignment.accept | assignment.decline
assignment.activate
assignment.release
workstream.split.propose
workstream.split.accept | workstream.split.decline
workstream.split.activate
```

`assignment.propose` names the current assignment, successor, checkpoint,
branch, complete inventory, and authority. `assignment.accept` is emitted by
the successor and pins that proposal. `assignment.activate` is a registry CAS
that consumes both. Validation derives the next generation; authors do not
choose a convenient generation number.

The split operations have the exact partition and all-participants-acceptance
semantics in section 5.4. They are distinct from repeated
`assignment.activate` operations because only one registry CAS can prevent an
overlapping-custody or partially split state from becoming authoritative.

Workstream subscriptions follow the assignment automatically. Personal topic
subscriptions remain with the identity. Friction routes to the current holder
of `design-steward`, not to a hard-coded agent such as `g-design`. Likewise,
host-specific coordination traffic routes to the assignment for
`host-coordination/<host>`.

The registry may record a user-approved ordered fallback set. A fallback gains
no authority merely by being next in the list. It may be activated only after
the policy's explicit trigger event—normally a cooperative `paused` or
`released` status—or fresh user authority. Silence alone remains insufficient.

## 9. Transition of the present fleet

Provider exhaustion should be handled workstream by workstream, not through a
fleet-wide rename:

1. Inventory each `g-*` identity's effective scope, open bus items, review
   state, branch, and last verified commit.
2. Finish already-authorized merge candidates when the named reviewer remains
   available. If a reviewer becomes unavailable, apply `review.reassigned`. If
   an author becomes unavailable before authorization and its nomination must
   be replaced, the named reviewer declines it (after reviewer reassignment if
   necessary), then the successor publishes a fresh nomination; reviewer
   reassignment alone cannot change the author set.
3. Register one replacement identity per distinct writer or reviewer workload.
   Do not make `c-reviewer` author product changes; create an implementor such
   as `c-design` for design work.
4. Execute the version-one procedure for each ready workstream independently.
5. Keep untransferred GPT identities paused. Do not retire them merely to tidy
   the roster when a later return is expected.
6. On return, transfer only the desired workstreams back. Provider restoration
   is not a whole-fleet rollback.

This permits heterogeneous operation: `c-x86` may replace `g-x86` while
`g-process` remains active, and a later `g-x86` can take only x86 responsibility
back.

## 10. Validation and adversarial review

Before version-two activation, executable fixtures must demonstrate:

- two successors racing from one predecessor cannot both become current;
- a paused, silent, or quota-exhausted identity is not automatically replaced;
- an unaccepted proposal cannot activate;
- a provider-prefixed name grants no workstream or role authority;
- activation preserves every open issue, dependency, finding, and required
  acknowledgement;
- a stale former holder cannot publish product authority after transfer;
- a returning holder starts from the current checkpoint, not its former branch;
- reviewer reassignment carries findings and does not transfer acceptance;
- a branch containing commits across holders reports the complete author set;
- an implementor cannot acquire reviewer powers through a workstream;
- concurrent registry transitions reduce to a visible conflict or one CAS
  winner, never timestamp resolution; and
- a live parent split atomically produces pairwise-disjoint retained and child
  exclusive scopes whose union equals the former scope, with no overlapping
  custody window;
- a nomination whose sole author becomes unavailable is closed by reviewer
  decline and replaced without fabricated authorship or force-push; and
- the same transition can move `g-x86 -> c-x86 -> g-x86` without rewriting an
  event or force-pushing a ref.

Reviewers should also challenge whether the workstream charter is too broad.
The mechanism can transfer a responsibility faithfully while still creating a
human or rebuild bottleneck. Large domains should decompose into explicit child
workstreams with narrow exported interfaces.

## 11. Rejected alternatives

**Rename `g-x86` to `c-x86`.** This rewrites provenance and makes review
independence ambiguous.

**Let `c-x86` resume the `g-x86` identity.** The existing resume mechanism is
appropriate for renewed exclusive custody of the same logical identity, not
provider substitution. Using it for substitution makes the immutable
registration metadata false and merges distinct author histories.

**Treat the branch name as the responsibility.** Branches carry product
history but do not encode role eligibility, open issues, subscriptions, or
current custody. They are evidence inside an assignment, not the assignment.

**Automatically fail over after a timeout.** A coordinator cannot distinguish
quota exhaustion, network partition, a slow proof, and a dead worker from time
alone. Timeout may raise an alert; it cannot grant authority.

**Create one provider-neutral agent named `x86`.** This hides useful execution
provenance and allows different underlying workers to look like one author.
The workstream is provider-neutral; its holders should remain honestly named.
