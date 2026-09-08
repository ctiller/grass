# Review integration successor protocol

Status: normative successor design. The active agent-bus schema remains
authoritative until a reviewed implementation, dual reader, migration fixture,
and explicit schema activation exist. Historical authorizations and receipts
are never rewritten.

This document corrects one scaling defect in [AGENT_REVIEW.md](AGENT_REVIEW.md):
review of an immutable source snapshot must not expire merely because unrelated
work advanced `main`. The live protocol puts `previous_main` and an exact merge
candidate into `review.merge_authorized`, then waits for that event to be
published before the reviewer may push. Under a busy fleet, publication latency
invalidates completed reviews and makes a queue of `N` ready changes require up
to `N + (N - 1) + ... + 1` integration attempts.

The successor separates **durable snapshot acceptance** from **current-main
integration**. The reviewer still performs the merge. A non-force Git push is
still the unavoidable atomic update of `main`, but the reviewed verdict is not
keyed by that moving ref and no coordinator or bus publication lies between the
final integration check and the push.

## 1. Required properties

The successor preserves these existing guarantees:

- every product change has at least one attributed implementor and a distinct,
  eligible nominated reviewer;
- acceptance names one immutable reviewed commit, never a branch head;
- all findings have an explicit terminal disposition;
- conflict resolution is authored content and receives independent review;
- the merge commit has exactly two ordered parents, a fixed reviewer trailer,
  and the deterministic clean-merge tree;
- every changed path remains inside the nominated scope;
- authors do not merge their own work and reviewers do not author the source
  content they accept;
- force pushes remain forbidden; and
- `audit-main` detects missing acceptance, injected merge content, wrong
  authorship, wrong reviewer, and missing or mismatched receipts.

It adds these scaling properties:

- advancing `main` does not invalidate snapshot acceptance;
- the ordinary retry path performs no bus write or coordinator round trip;
- a retry reruns only integration checks whose declared inputs changed;
- checks with whole-tree inputs are honestly whole-tree and may still rerun;
- a clean change in the reviewed scope is not rejected merely because another
  clean change touched that scope first; and
- local source work, bus reads, and candidate construction take no global Git
  lock. Expensive checks run outside all bus and repository coordination locks.

## 2. Stable reviewed source

At acceptance, the reviewer records `source_base` and `reviewed_commit`.
`source_base` is the unique merge base selected by the reviewed merge policy at
the time the snapshot is inspected. It is an ancestor of `reviewed_commit` and
of target `main`. The exact reviewed commit set is reconstructed from these
objects; every introduced non-review merge commit has exactly one
`Agent-Bus-Agent` trailer, the resulting author set equals the nomination, and
the reviewer occurs in neither set.

The reviewer checks the exact tree delta from `source_base` to
`reviewed_commit`. Later branch motion is irrelevant. At integration time,
current `main` must still descend from `source_base`; otherwise the ancestry and
authorship statement is no longer the one reviewed and a new acceptance is
required. Mere advancement from that base is expected, not stale state.

## 3. Snapshot acceptance event

The successor introduces this event; its final wire name is schema-versioned:

```text
review.snapshot_accepted = {
  nomination : EventId,
  product_branch : Branch,
  source_base : ObjectId,
  reviewed_commit : ObjectId,
  source_tree : ObjectId,
  source_checks : List<ScopedCheckResult>,
  finding_dispositions : List<FindingDisposition>,
  evidence : StringSet<EventId>,
  reviewed_scope : StringSet<PathClaim>,
  limitations : List<Text>,
  summary : Text
}
```

Only the accepting nominated reviewer emits it. `source_tree` equals the tree
of `reviewed_commit`; it is retained explicitly so linked validation cannot
silently inspect a different object. `reviewed_scope` equals the nomination's
scope exactly. Every source delta path is within it. Every required source check
is present and passed, and every finding is cleared or explicitly superseded.

An acceptance is an immutable verdict about that source snapshot. It contains
no `previous_main`, candidate merge commit, candidate tag, merge-engine epoch,
or reusable authority for future branch commits. It becomes unusable if the
nomination is withdrawn or superseded, the reviewer loses eligibility, a
blocking issue applies to its chain, or a later explicit
`review.snapshot_withdrawn` names it. Silence and `main` movement do not revoke
it. Reassignment never transfers an acceptance: the successor reviewer accepts
the snapshot independently.

The accepting reviewer may retract an unintegrated verdict explicitly:

```text
review.snapshot_withdrawn = {
  acceptance : EventId,
  reason : Text
}
```

Only that reviewer emits it, it references the acceptance exactly, and it is
terminal for that acceptance. Withdrawal of the containing nomination by an
author has the same prospective effect. Neither event rewrites a merge already
present in product history. If several snapshots of one nomination have been
accepted, integrating any one closes the nomination and makes the others
unusable; later branch commits require another nomination.

## 4. Scoped check evidence

```text
ScopedCheckResult = {
  name : CheckName,
  command : Text,
  result : passed,
  input_kind : source | integration,
  input_root : ObjectId,
  dependency_manifest : ObjectId,
  input_fingerprint : Digest,
  limitations : List<Text>
}
```

The digest is a cache locator, never proof. The versioned check owner defines
and validates `dependency_manifest`: the exact paths, imported signatures,
configuration, tool versions, authority ledgers, and other inputs on which the
result depends. A result is reusable only when a checked reconstruction gives
the same fingerprint from the new candidate. An unknown, missing, or changed
input forces a rerun. A whole-tree check declares the complete tree and is not
relabelled local to make a retry cheaper.

Lean checks use the reviewed shard DAG and `.olean` dependency graph. A local
source edit invalidates its shard and semantic dependents; an unrelated merge
does not make every theorem a new proof obligation. Global manifest checks may
remain linear on a clean run, but consume compact summaries and reuse unchanged
leaves. This mechanism is also how one integration gate may validate several
successive clean candidates without pretending the candidates are identical.

## 5. Reviewer-owned integration

For one accepted snapshot, `agent-bus integrate` performs:

1. fetch the complete current bus receipt, current `main`, the acceptance's
   exact source objects, and the selected merge-engine implementation;
2. validate the acceptance, reviewer role, nomination, finding dispositions,
   blocking issues, source ancestry, authorship, scope, and source tree;
3. require current `main` to descend from `source_base`;
4. construct a deterministic clean merge with current `main` as first parent
   and `reviewed_commit` as second parent;
5. stop if conflict resolution, unsupported filters, submodule ambiguity, path
   collision, or any other material choice is required;
6. reconstruct every required integration-check input, reuse only exact matches,
   and run the remainder outside all coordination locks;
7. re-probe current `main` and the bus immediately before push; if either change
   invalidates the candidate or acceptance, rebuild locally;
8. push the exact candidate directly to `refs/heads/main` without force; and
9. enqueue the post-push integration receipt.

There is no authority event, candidate-tag publication, coordinator drain, or
remote waiting between steps 7 and 8. If the non-force push loses a race, the
review remains accepted: reconstruct against the new `main`, reuse checks whose
declared inputs are unchanged, and retry. The author acts only when the clean
merge or reviewed contract no longer holds.

If `reviewed_commit` is already reachable from current `main`, the helper
refuses an empty duplicate review merge and reports the existing integration for
receipt/reconciliation. Before retrying after an uncertain push result, it
checks product first-parent history; it never pushes the same acceptance twice.

The final bus probe and product push cannot form one transaction, and this
protocol does not claim otherwise. The gate records the exact bus receipt it
used. A withdrawal or blocking report already visible there prevents the push;
a later event does not rewrite an earlier product fact. This is the same
cooperative cross-ref boundary as the current protocol, without adding a remote
publication delay inside its race window.

Candidate metadata remains deterministic. The commit has exactly the two
ordered parents above, fixed `Grass Agent Bus <agent-bus@invalid>` identity,
the schema-defined timestamp and message, and exactly one
`Agent-Bus-Reviewer: <reviewer>` trailer. Reviewers never edit its tree.

## 6. Integration receipt and audit

After the successful push, the reviewer emits:

```text
review.integrated = {
  acceptance : EventId,
  previous_main : ObjectId,
  main_commit : ObjectId,
  product_branch : Branch,
  reviewed_commit : ObjectId,
  merge_engine_epoch : EventId,
  integration_checks : List<ScopedCheckResult>,
  summary : Text
}
```

The receipt records a completed product fact; it does not retroactively grant
authority. `main_commit` is the actual two-parent first-parent-history child of
`previous_main`. Linked validation and `audit-main` reconstruct its tree using
that actual parent, the accepted `reviewed_commit`, and the named engine. They
verify commit metadata, source authorship, scope, all source and integration
checks, and the absence of injected content.

If the reviewer disappears after the push, a bootstrap-authorized coordinator
may emit `review.integration_reconciled` only when product history and the prior
snapshot acceptance already prove every field. Reconciliation cannot construct
a missing acceptance or excuse a failed integration check.

## 7. Concurrency and trains

Independent reviewers may still race on the non-force `main` push; one wins and
the others rebuild locally. This is ordinary Git serialization, not review
identity and not a distributed lock. Advisory merge slots may reduce wasted
work but grant no authority.

A reviewer holding several accepted snapshots may construct an ordered local
train and run shared integration checks once when every acceptance remains
individually auditable and every merge commit retains its own accepted snapshot
as second parent. The single push advances the whole first-parent chain
atomically. A reviewer may not place another reviewer's acceptance in such a
train; transfer requires a fresh acceptance by the integrating reviewer.

The protocol does not promise zero retries. It promises that queue depth does
not invalidate verdicts by construction, and that a retry cost follows actual
changed check inputs rather than the total number of waiting reviews.

## 8. Migration

This is a schema successor, not an in-place reinterpretation of
`review.merge_authorized`:

1. implement dual readers and reducers for historical authorization/receipt and
   new acceptance/integration chains;
2. add linked validation, audit, query, and crash-recovery support;
3. run old and new acceptance corpora plus the fixtures below;
4. activate the successor at one exact schema epoch;
5. allow already-published old authorizations either to complete under their
   old rules or be abandoned in favor of a new snapshot acceptance; and
6. retain old history forever and remove old writers only after the declared
   compatibility window.

No document change activates the protocol. Until the reviewed helper and
schema epoch land, [AGENT_REVIEW.md](AGENT_REVIEW.md) and
[AGENT_BUS_SCHEMA.md](AGENT_BUS_SCHEMA.md) describe the live behavior.

## 9. Required fixtures and measurements

Positive fixtures cover:

- acceptance followed by several unrelated `main` advances and one clean
  integration without re-acceptance;
- a clean overlapping edit whose combined candidate passes integration checks;
- a push race followed by local reconstruction and selective check reuse;
- two accepted snapshots integrated as an auditable same-reviewer train;
- a whole-tree check which honestly reruns; and
- missing-receipt reconciliation from immutable acceptance and product history.

Negative fixtures reject:

- a later product-branch head substituted for `reviewed_commit`;
- current `main` which does not descend from `source_base`;
- a conflicting merge or reviewer-edited candidate tree;
- a changed dependency input hidden behind a reused check digest;
- an acceptance transferred to another reviewer;
- an out-of-scope path, missing author trailer, unresolved finding, blocking
  issue, unsupported merge input, injected parent, or missing check; and
- a receipt whose actual first parent, source parent, engine, tree, metadata, or
  checks differ from product history.

The implementation ratchet measures at least queue depths 1, 4, 16, and 64;
unrelated and overlapping `main` advances; cold and warm check caches; number of
full and selective check reruns; local candidate-construction latency; bus
round trips between final gate and push (required value: zero); wall time; and
peak memory. The acceptance criterion is linear work in accepted changes plus
work forced by actual invalidated inputs, not triangular work in queue depth.

## 10. Rejected alternatives

- **Keep candidate-specific preauthorization and publish faster.** This reduces
  one latency but retains the moving-head invalidation law.
- **Permit a stale candidate when its old `previous_main` is an ancestor.** The
  commit still has the wrong first parent and omits intervening product history.
- **Let a coordinator silently rebase an authorization.** That transfers merge
  judgment away from the nominated reviewer and changes the reviewed artifact.
- **Treat disjoint paths as sufficient check reuse.** Imports, generated
  registries, authority ledgers, and configuration create non-path-local inputs;
  only a checked dependency manifest justifies reuse.
- **Postpone all checks until after pushing `main`.** This makes an unchecked
  candidate authoritative product state and turns rollback into the normal
  safety gate.
- **Lock `main` while long checks run.** Cross-host leases recreate the stalled
  coordinator/CAS failure mode and make abandoned agents a liveness hazard.
