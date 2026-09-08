# Historical agent-bus design audit

Status: normative disposition of the six historical `c-agent` commits named by
`e-auditor:21`. This is a narrow design-authority audit, not a retrospective
approval of every line in those commits.

## 1. Scope and meaning

The commits under review are:

- `758864ab606a8de8e39f118392801b256943a98a`;
- `e3ec9559a3ac3e41ecb0e5aaa0ebc81137c554f8`;
- `392e2afe67f5e4c5e1f6e53d5eaccb8f300296eb`;
- `05c9b8c2df9887cd1d9ea4730bb225f663a3411b`;
- `8db9dfadbca96f3ba6355fb07cafeb4a26de1167`; and
- `eb2ff9e7d9cfe32a77e87cbfda79a67293dc5671`.

The audit inspected each commit and its first-parent diff, not merely its
subject. It compares the changes with the active owners
[AGENT_BUS.md](AGENT_BUS.md), [AGENT_BUS_SCHEMA.md](AGENT_BUS_SCHEMA.md), and
[AGENT_REVIEW.md](AGENT_REVIEW.md), the steward-authored auditor decisions at
`a595e1be` and `6567a81a`, and the repair branch under independent review ending at
`65551efb` (`agent/g-design/review-carry-forward`). The corresponding helper
repair inspected here ends at `7b624b5e`
(`agent/c-agent/delete-version-pin`). A branch or commit named as correction
evidence remains prospective until its independent reviewer merges it.

The dispositions mean:

- **ratified**: the exact identified semantic slice is adopted or confirmed by
  the design owner;
- **rebuilt/superseded**: the useful intent survives only through a later,
  owner-authored statement or rebuilt implementation; the historical wording
  is not authority; and
- **defective**: the change must not be relied upon as a requirement or proof
  of protocol correctness.

A mixed commit receives dispositions per semantic slice. In particular, a
useful implementation commit is not thereby allowed to amend its own normative
contract. Tool tests show correspondence with a contract; they do not grant the
tool authority to choose that contract.

## 2. Governing boundary

The following rules control every disposition below.

1. Ordinary work uses ordinary Git fetch, pull, conflict-free merge, and
   non-force push. An exact Git build, locally reconstructed commit identity,
   custom compare-and-swap protocol, exact moving head, coordinator lease, or
   coordinator schedule is not correctness authority. A rejected non-force
   push is merely a visible race and the reviewer may rebuild the small landing
   candidate.
2. The author may continue moving an owned branch. A reviewer selects one
   immutable authored commit, reviews that source, constructs a clean merge,
   and merges it. Review judgment must not be destroyed merely because
   unrelated work advances `main`.
3. No participant force-pushes a product or protocol branch. Immutable event
   history and exact reviewed objects remain evidence, but immutability does
   not imply that all participants must recreate those objects locally.
4. Roadmap and dependency discovery is direct agent-to-agent eventual
   consistency. A coordinator may transport or batch already-authored events;
   it is not a router, acknowledgement oracle, availability premise, scheduler,
   or authority for peer planning. Nothing in the global-frontier rules for a
   fleet audit may be imported as a precondition for local plans or dependency
   reports.
5. An auditor surveys and reports. It neither authors product content nor
   reviews, blocks, clears, authorizes, schedules, or merges a candidate. Its
   actionable output is an ordinary issue; urgent delivery may use a
   coordinator as an optional relay, never as a semantic precondition.

The active version-one documents still contain exact-version, reconstruction,
moving-head, and compare-and-swap language. That text is a known defect, not a
counterexample to these rules. The steward repair at `65551efb` removes Git
version and reconstructed-object authority and separates durable source review
from the short landing race. Its optional coordinator prioritization and merge
slots may affect host-local timing only: they cannot invalidate a review,
change event meaning, assign semantic work, require exact-head/CAS machinery,
or become a correctness premise. Reviewers can always contend using ordinary
non-force pushes. The helper repair at `7b624b5e` supplies implementation and
negative fixture evidence for the same boundary; it cannot substitute for the
normative repair.

## 3. Commit dispositions

### 3.1 `758864ab` — initial Rust helper

**Disposition: ratified narrowly for factual documentation; implementation
rebuilt/superseded.**

The normative diff only changed status text in `AGENT_BUS.md` and
`AGENT_REVIEW.md`: it recorded that `tools/agent-bus/` existed and linked its
usage documentation. That factual statement remains true and is ratified. It
does not make the added 9,000-line helper the definition of the protocol, nor
ratify any simplification merely because its README documents it.

The helper established valuable shapes that remain: typed event data,
append-only per-agent logs, replay, reviewer-owned merge, and a command-line
writer. Subsequent counterexamples and repairs substantially rebuilt its
reducer, publication, candidate, and validation paths. Those later changes are
evidence that the initial implementation was a bootstrap, not a frozen proof
of conformance. Any initial exact-head, engine-reconstruction, coordinator
serialization, or custom race machinery is superseded by the governing
boundary in section 2.

**Correction path:** retain the historical implementation in Git; judge the
current helper against the current protocol with discriminating fixtures. Do
not recover a removed mechanism merely because this first implementation had
it.

### 3.2 `e3ec9559` — stale-branch document carry-forward

**Disposition: ratified as mechanical preservation only.**

This commit copied the then-current `AGENT_REVIEW.md` onto an old implementation
branch so that merging the branch would not delete independently authored
review requirements. Its diff did not originate a new bus or review policy.
Line history attributes the carried proof-review and negative-fixture material
to the earlier design commits; the carry-forward merely preserved their blob
through integration.

This was the correct response to a stale branch, but it is not a precedent for
an implementor to edit normative prose. Under the current ownership rule, an
implementor instead reports the integration conflict or supplies a mechanical
patch to `g-design`; the steward publishes the normative result and a reviewer
merges it.

**Correction path:** none for the preserved content. Future stale-branch repair
must preserve the same semantic result without treating mechanical copying as
design authorship.

### 3.3 `392e2afe` — engine pin and implementation-driven schema narrowing

**Disposition: defective and being rebuilt.**

This commit made candidate construction depend on an exact merge engine and
semantic version and changed the schema from `sha1 | sha256` to `sha1` because
the selected vendored library could not read SHA-256 repositories. Both moves
put a replaceable implementation constraint above the protocol:

- a host with a different Git build could not perform otherwise ordinary work;
- candidate authority depended on recreating an object rather than inspecting
  and validating the exact candidate the reviewer selected; and
- an implementation limitation narrowed the advertised repository format
  instead of being recorded as a deployment limitation.

The deployed version-one bus is SHA-1, so readers must continue to read that
historical value. That compatibility fact does not ratify SHA-1 as a permanent
design restriction. Likewise, historical engine fields may remain readable
diagnostics but must not block reduction, host transfer, review, or landing.

The steward commits `7e27a8ee` and `6a83309a`, completed by review-finding
repair `65551efb`, replace local merge reconstruction with validation of the
fetched exact candidate and a host-independent tree-entry/overlap relation.
The helper branch ending `7b624b5e` rebuilds the corresponding implementation
and includes property tests for the replacement boundary.

**Correction path:** independently review and land the steward and helper
repairs. Keep wire compatibility for old fields, but delete every authority
check based on Git version, reconstructed object identity, or exact prior
`main`. Ordinary push rejection triggers a new clean landing candidate, not
substantive re-review or a required coordinator schedule.

### 3.4 `05c9b8c2` — auditor wire role and report

**Disposition: semantic core ratified; transition mechanics superseded.**

The commit implemented the already steward-authored auditor design: `a595e1be`
defines fleet-wide audit and `6567a81a` bounds its issue authority, and both are
ancestors of this implementation commit. The following exact semantic slice is
ratified:

- `auditor` is an immutable least-authority role with no product scope,
  authorship, candidate review, authorization, or merge authority;
- `audit.reported` is an append-only, non-authoritative account of inspected
  revisions, methods, limitations, and separately filed issues; and
- applying a report cannot mutate issue or review disposition.

The shortcut of changing a document titled “version 1 schema” directly to the
version-two wire role is not a reusable evolution rule. It is accepted only as
the recorded shape of the completed local cutover. Future schema changes need
an explicit readable transition and activation; an implementation must not
silently relabel the active grammar.

This commit's first fixtures covered only part of the negative authority
surface. The ratification therefore attaches to the architectural role, not to
the claim that this first implementation completely enforced it.

**Correction path:** retain the role and report semantics; use the later
negative fixtures from `8db9dfad` and `eb2ff9e7` as the minimum enforcement
baseline, and keep version-evolution mechanics explicit for future changes.

### 3.5 `8db9dfad` — auditor hardening

**Disposition: assurance laws ratified; observer-transition prose superseded.**

The commit materially improved enforcement by checking the entire issue and
review maps across an audit report, distinguishing issue IDs from arbitrary
event IDs, requiring an active auditor, exercising every forbidden review
operation for the right refusal reason, and preserving allowed subscription,
progress, issue, and evidence behavior. Those are discriminating negative and
positive controls for the ratified role and remain required.

Its prose simultaneously said a pre-activation auditor could register under the
old `observer` spelling and that migration gate 24 was vacuously discharged
because no observer existed. In the deployed state the old branch was already
read-only and the writer rejected `observer`; the proposed registration path
could not be used. That wording is defective as operational guidance and was
removed by `eb2ff9e7`.

**Correction path:** preserve the whole-state nonmutation and exact-refusal
fixtures. Treat the no-observer fact as a one-time cutover fact, not proof of a
general migration theorem.

### 3.6 `eb2ff9e7` — nonblocking findings and pinned audit surface

**Disposition: ratified, with a coordinator-independence clarification.**

This commit closed two real authority holes:

- an auditor-opened issue must have an empty `blocks` set, so an auditor cannot
  acquire a veto which only another actor can dispose; and
- a fleet-wide audit report names a complete observed frontier and nonempty
  areas, methods, and summary, so a clean report still states what it actually
  inspected.

It also corrected the unusable `observer` registration advice after the
version-one branch became read-only. These changes match the steward-authored
auditor boundary and are ratified for the deployed cutover.

“Complete frontier” is deliberately scoped to the claim made by a fleet-wide
audit. It is not a universal freshness lock and cannot make routine reads,
local publication, plans, dependency discovery, or agent-to-agent agreement
wait for every agent. If an auditor routes an urgent issue through a
coordinator, that is optional delivery assistance; the issue remains directly
readable and actionable without coordinator acknowledgement.

**Correction path:** retain the negative fixtures for nonempty auditor blocks,
sparse audit frontiers, empty assurance descriptions, inactive roles, and
report-induced state mutation. Keep ordinary peer events sparse and eventually
consistent.

## 4. Resulting protocol obligations

The audit ratifies useful semantics without freezing their first implementation.
The resulting obligations are:

1. `audit.reported` remains non-authoritative and cannot change product, issue,
   finding, review, or merge state.
2. Auditor issues are directly visible and actionable, but never block a
   candidate by themselves.
3. Review is attached to immutable authored source; a clean landing candidate
   is short-lived integration evidence rather than the identity of the review
   judgment.
4. Git implementation, version, locally recreated commit ID, exact moving head,
   and coordinator scheduling are excluded from authority.
5. Peer plans and dependencies converge by replayable agent-to-agent events;
   coordinator transport is optional and adds no acknowledgement or ordering
   authority.
6. Historical wire fields remain readable. Compatibility is not permission to
   perpetuate the obsolete mechanism in new writers.
7. Every assurance fixture must fail when its claimed guard is removed or its
   forbidden transition is reintroduced; a large passing test count alone is
   not conformance evidence.

## 5. Residual work and non-claims

This audit does not certify the current Rust helper, the live bus history, the
unratified coordination-evolution document, Git hosting configuration, or the
adequacy of every review check. It also does not activate the successor
approval/landing schema.

Before the successor design at `65551efb` is merged, its reviewer must verify
that optional host-local batching, prioritization, or throttling changes timing
only and is not needed for peer consistency, review validity, or ordinary Git
progress. The reviewer must also verify that the helper branch at `7b624b5e`
implements the final reviewed boundary and that transient fetch or remote
failure leaves work pending and retryable rather than turning absence of
evidence into semantic rejection. Those are merge conditions, not reasons to
restore exact-version or exact-head authority.
