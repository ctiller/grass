# Git agent bus protocol

Status: normative design for cooperative build coordination. The bus and its
helper are not implemented yet.

Grass will be implemented by agents running under different providers and in
different environments. GitHub is the only shared coordination substrate all
agents are assumed to possess. This document defines a small Git-native event
bus for scope, plans, progress, issues, dependencies, handoffs, and reviews.

The live bus is an orphan Git branch named `agent-bus`. It contains segmented,
append-only JSON Lines logs with one exclusively written directory per agent:

```text
refs/heads/agent-bus
├── .gitattributes
├── _bus/
│   └── BUS.json
├── alice/
│   ├── 000000.jsonl
│   └── 000001.jsonl
├── bob/
│   └── 000000.jsonl
└── verifier-3/
    └── 000000.jsonl
```

The product tree contains this protocol and, once implemented, the helper at
`tools/agent-bus/`. Live events never merge into `main`.

## 1. Goals and non-goals

The bus must:

- use ordinary Git fetch, rebase, commit, and push operations;
- work across Windows, Linux, macOS, providers, and agent implementations;
- avoid multi-writer files during correct operation;
- retain causal history without deleting resolved work;
- make current scope, progress, issues, dependencies, and review state
  mechanically queryable;
- tolerate offline work and concurrent publication;
- expose conflicts rather than silently choosing a winner; and
- remain inspectable using standard Git and text tools.

The bus is not a scheduler, consensus service, mutex, proof authority, source of
repository permission, chat transcript, secret store, or large-artifact store.
It coordinates claims about work. Product Git history, Lean checking, tests,
CI, and review remain their own authorities. GitHub pull requests are optional
presentation and do not participate in the protocol.

The protocol is cooperative. GitHub authenticates repository users, but the bus
does not cryptographically bind an event's `agent` field to a provider identity
or enforce per-directory writers on the server.

## 2. Branch model

The canonical ref is `refs/heads/agent-bus`. It is an orphan branch whose first
commit has no product-history parent. It contains bus logs and two immutable
bootstrap files only, is never merged into `main`, and is never merged into
product branches.

The human repository owner creates the orphan root commit before the protocol
becomes mandatory. It contains `_bus/BUS.json`, `.gitattributes`, and sequence
zero registration logs for the initially authorized coordinators. `BUS.json`
names schema version 1, the repository object format, those coordinator
identities, and the last product `main` commit exempt from the newly activated
review protocol. It also pins the V1 merge engine and exact version.
`.gitattributes` contains `*.jsonl -text` so Git never rewrites
line endings. Bootstrap registrations alone have `observed: null`. Both bootstrap
files are immutable afterward; changing either requires a new reviewed protocol
version rather than an ordinary bus commit. The human also arranges the first
implementor and reviewer identities needed to review the helper's product
branch. This is the sole bootstrap boundary, not an ongoing review exception.

GitHub rules should prohibit force pushes and branch deletion. Force pushes are
forbidden on `agent-bus`, `main`, and product branches even if server settings
fail to enforce the rule. Product CI should ignore bus-only pushes. Direct
cooperative bus pushes are intentional; a non-fast-forward rejection is a
normal synchronization race resolved by fetch, rebase, and ordinary push.

Agents use a separate bus checkout. Different machines may check out a local
`agent-bus` branch. Multiple agents sharing one clone use detached worktrees
based on `origin/agent-bus`, because Git cannot check one local branch out in
multiple worktrees. They publish explicitly to `HEAD:refs/heads/agent-bus`.

The product commit discussed by an event is event data. It need not be reachable
from the orphan branch.

Prepared merge candidates are published as immutable lightweight tags at
`refs/tags/agent-candidate/<reviewer>/<candidate-object-id>` before authorization.
They are never moved, force-pushed, or deleted. This makes losing CAS candidates
available to bus validation and audit without merging them into any branch.

## 3. Agent identity, roles, and single writers

The user or coordinator assigns each agent a stable name matching:

```text
[a-z][a-z0-9-]{0,47}
```

Names beginning with `_` are reserved. Lowercase, filename-safe names avoid
cross-platform ambiguity.

Each name owns one branch-root directory. Only that agent modifies that
directory during ordinary operation. One name must not have concurrent writer
processes. A replacement normally receives a new name; deliberate continuation
under an old name requires an `agent.resumed` event and exclusive custody.

Each identity declares exactly one immutable primary role at registration:

- `implementor` claims product scope, authors product commits, and nominates
  reviewers;
- `reviewer` takes nominations, reports findings, and performs reviewer-owned
  merges, but authors no product commits;
- `coordinator` records user-directed retirement and coordinates assignments
  without authoring or merging product content; or
- `observer` queries the bus and may report issues but owns no product scope.

This separation is intentional. Review is a dedicated workload, not a temporary
hat worn by the implementation identity. If one underlying agent changes role,
it registers a new name; roles never mutate in place. A reviewer may analyze or
suggest patches, but if its identity authors a product commit, that is a protocol
violation rather than an implicit role change. More specialized role vocabulary
requires a schema revision.

An agent communicates with another agent by writing an event to its own log
whose data names the target. The target replies in its own log and references
the original event. No ordinary operation requires two agents to edit one file.

## 4. Segmented JSONL storage

An agent log consists of zero-padded segments:

```text
alice/000000.jsonl
alice/000001.jsonl
```

Segments contain at most 1,000 events. Sequence numbers are zero-based:

```text
segment = seq / 1000
offset  = seq % 1000
path    = <agent>/<segment as six decimal digits>.jsonl
```

Thus `000000.jsonl` contains sequence numbers `0..999`, and `000001.jsonl`
contains `1000..1999`. The location of every event is derivable without a
shared index.

Files are UTF-8 with LF endings. Each nonempty line is exactly one compact JSON
object and is at most 65,536 bytes excluding LF. Blank lines, comments,
byte-order marks, CRLF, trailing whitespace, overlong lines, and partial final
lines are invalid. Event data contains summaries and references, never pasted
logs or large reports.

Every segment before the active tail contains exactly 1,000 events and is
closed. Closed segments are immutable. The active segment contains `1..1000`
events and may only receive valid appended lines. Empty files, sequence gaps,
and skipped segment numbers are forbidden.

The first event is `agent.registered` at sequence zero. A directory without a
valid registration event is not an agent log.

## 5. Event envelope

Version 1 events have this shape:

```rust
struct EventV1 {
    v: u32,
    id: String,
    agent: String,
    seq: u64,
    time: String,
    observed: Option<String>,
    kind: String,
    refs: Vec<String>,
    data: serde_json::Value,
}
```

Example:

```json
{"v":1,"id":"alice:17","agent":"alice","seq":17,"time":"2026-09-01T20:00:00Z","observed":"8af03c1000000000000000000000000000000000","kind":"issue.opened","refs":[],"data":{"blocks":[],"code_commit":"abc1230000000000000000000000000000000000","evidence":[],"issue_kind":"bug","locations":["Grass/Http2/Frame.lean:87"],"reproduction":[],"severity":"high","summary":"Reserved bit accepted","target":"bob"}}
```

Envelope laws:

- `v` is the positive schema version.
- `agent` equals the containing directory.
- `seq` equals the line-derived global sequence number.
- `id` equals `<agent>:<seq>` in canonical decimal without leading zeroes.
- `time` is an RFC 3339 UTC timestamp with `Z`; it is presentation data and
  never determines causality or conflict precedence.
- `observed` is the full object ID of the fetched bus head on which the local
  batch was based. Multiple unpublished same-agent events may share it. It is
  `null` only for bootstrap coordinator registrations.
- `kind` is an event kind defined by envelope schema `v`.
- `refs` is a byte-lexicographically ordered set of causal event IDs; this is a
  canonical encoding rule, not numeric event order.
- `data` is an object matching the exact schema for `kind`.

The helper writes fields in the displayed order as compact JSON. Nested object
keys are lexicographically ordered. Unknown envelope or event-data fields are
rejected in version 1 so misspellings cannot silently become inert.

Published events are immutable. Scope changes, corrections, resolutions, and
supersession are later events. There is one total order per agent by `seq`.
There is no invented global event order: cross-agent causality is expressed by
`refs` and `observed`, not timestamp or rebased commit position.

An event may reference only an event visible in its `observed` bus state or an
earlier contiguous event in the same agent's local log. The latter permits
causal offline batches. Cross-agent references always require publication in
`observed`; an agent cannot observe another agent's unpublished event. Since
published history rewriting is forbidden, the observed commit remains a stable
ancestor after later rebases.

## 6. Event kinds

The initial vocabulary is intentionally bounded. Exact required and optional
fields, sizes, reference cardinalities, role authority, and lifecycle laws are
owned by [AGENT_BUS_SCHEMA.md](AGENT_BUS_SCHEMA.md); the prose below supplies
orientation and must not be used to invent a different schema.

### 6.1 Agent lifecycle

`agent.registered` is sequence zero and has no references:

```json
{"display_name":"Alice","primary_role":"implementor","product_base":"abc1230000000000000000000000000000000000","product_branch":"refs/heads/agent/alice/x86","purpose":"x86 instruction semantics"}
```

Provider and model may be optional diagnostic strings. Credentials, account
identifiers, hidden prompts, and secrets are forbidden.

`agent.status` carries `status`, product branch/commit, and a short note. Valid
statuses are `active`, `blocked`, `paused`, `done`, and `abandoned`. `done` and
`abandoned` deactivate scope claims.

`agent.resumed` records a deliberate restart or custody transfer under an
existing name and references the previous lifecycle event. Custody transfer
does not change the registered role.

`agent.retired` is emitted only by a bootstrap-authorized `coordinator`, targets one registered
identity, records the user's authority and reason, and deactivates that
identity's scope. It exists for disappeared agents that cannot emit their own
`abandoned` status; it is not a coordinator power to interrupt active work
without user direction.

### 6.2 Scope

`scope.set` replaces the agent's complete active scope:

```json
{"base_code_commit":"abc1230000000000000000000000000000000000","depends_on":[{"agent":"bob","interface":"Memory.Access"}],"exclusive":["Grass/Assembly/X86/**","Grass/Instruction/X86/**"],"exports":["X86.Instruction","X86.step"],"note":"x86 model and decoder","shared":["lakefile.toml"]}
```

Claims are repository-relative and use `/`. Version 1 permits exact file paths
or directory prefixes ending in `/**`; arbitrary globs and `.` or `..` path
components are forbidden. This makes overlap deterministic.

Active exclusive/exclusive overlap is a conflict. Shared/shared overlap is
allowed. Exclusive/shared overlap is reported but not automatically invalid.
Claims coordinate writers; they do not grant permission or override Git.

Conflicting scope events remain valid and publishable. If one claimant's
`observed` state already contained the other's active claim, that causally later
claimant yields by publishing a replacement `scope.set` or explicitly escalates
with `issue.opened`. If neither observed the other, the claims are concurrent
and require coordinator/user disposition. Validation reports these states but
does not reject the bus merely because a scope conflict exists.

An empty `scope.set` releases all claims. Replacement rather than patch events
keeps current scope independent of missing incremental updates.

### 6.3 Plan and progress

`plan.set` replaces the current plan and contains a summary, stable step IDs,
step text and state, and known risks. Step states are `pending`, `active`,
`done`, and `dropped`.

`progress.reported` contains the exact product commit, completed/current/next
items, blockers, and verification commands reportedly run. It is a claim, not
proof that those commands succeeded.

### 6.4 Issues

`issue.opened` handles bugs, requests, questions, and scope conflicts. It names
one registered target, `issue_kind`, severity, summary, relevant product commit,
locations, expected/observed behavior, reproduction commands, and zero or more
exact event IDs it blocks. A review gate considers an issue blocking only when
its `blocks` set names a nomination or reassignment in that review chain; there
is no implicit repository-wide, branch-name, path-overlap, or severity-based
membership.

Valid kinds are `bug`, `request`, `question`, and `scope_conflict`. Severities
are `critical`, `high`, `normal`, and `low`.

`issue.acknowledged`, `issue.resolved`, and `issue.rejected` name the root
`issue.opened` and current assignment. Only its current target emits them. A code
resolution names the exact fix commit and verification commands. Rejection gives
a reason and may cite a normative document.

`issue.reassigned` references one open issue, preserves every field other than
target, names a replacement, and gives a reason. The opener or a
bootstrap-authorized coordinator emits it; the new target must acknowledge it. The old
target then has no disposition authority.

Reports are never cleared. Recurrence or dispute creates a new issue referencing
the earlier issue and disposition. Multiple contradictory terminal dispositions
for one issue are invalid.

### 6.5 Dependencies and handoffs

`dependency.requested` names a target, interface/artifact, needed-by milestone,
and blocking status. The target emits `dependency.acknowledged`,
`dependency.resolved`, or `dependency.rejected` with a causal reference.
`dependency.reassigned` has the same preservation, authority, replacement
acceptance, and old-target exclusion rules as `issue.reassigned`.

`handoff.offered` names scope, product branch/commit, completed verification,
known issues, and receiver. `handoff.accepted` is emitted by the receiver. Scope
transfers only after the giver releases it and the receiver publishes a new
`scope.set`.

### 6.6 Review

`review.nominated` is emitted by an `implementor` author and names exactly one
proposed agent whose primary role is `reviewer`, a named product branch, target
branch, expected author agents,
required checks, and reviewed scope. It intentionally does not freeze a head
commit: authors may continue pushing ordinary commits while review proceeds. A
reviewer is not silently assigned by an unaddressed broadcast.

The nominee emits `review.nomination_accepted` or `review.nomination_declined`.
Nomination acceptance means “I will review this branch,” not “its present or
future content is approved.” Only the agent who accepted that nomination may
emit `review.changes_requested`, `review.findings_cleared`, or
`review.merge_authorized`. `review.findings_cleared` references one changes event
after the reviewer inspects its fixes; later findings use another changes event.
`review.findings_superseded` lets the accepting reviewer reject a prior finding
with explicit rationale rather than pretending it was fixed.
The author may emit `review.withdrawn` while review is pending.

`review.reassigned` handles a reviewer that silently becomes unavailable,
including provider or token-quota loss. An author named by the nomination, or a
bootstrap-authorized `coordinator`, references exactly one unmerged nomination, names a different
eligible reviewer, gives a reason, and copies the branch, target, authors,
checks, scope, and summary exactly. It atomically closes the old nomination and
opens its successor; the replacement must accept before acting. Timestamps and
silence never change authority implicitly. Every prior open finding is inherited
as open. Only the accepting replacement reviewer may later clear it or supersede
it with rationale. A returning superseded reviewer has no new authority. If the
old reviewer had already published `review.merge_authorized`, reassignment does
not revoke that immutable authorization; the old and replacement candidates
race through ordinary `main` compare-and-swap, so at most one candidate based on
the same previous main can land.

`review.merge_authorized` is the positive review verdict and the pre-merge
authority. The accepting reviewer publishes it after checks, pinning the
nomination chain, observed bus state, previous `main`, reviewed product commit,
exact conflict-free merge candidate, check results, finding dispositions, and
review scope. Once published it authorizes only that reviewer and candidate.
The matching immutable candidate tag must already be fetchable. Later branch
commits are excluded. Later bus events cannot retroactively revoke
the pinned authorization; they govern later candidates and may require an
immediate corrective merge if they expose a defect.

`review.merged` is emitted by that reviewer after the non-force product push. It
references the authorization and records the resulting `main` commit. It is a
required audit receipt, not the authority that permitted the already completed
push.

If the reviewer becomes unavailable after the push but before that receipt, a
bootstrap-authorized coordinator may emit `review.merge_reconciled`. It records
the same facts plus user authority, and is valid only when product first-parent
history already contains the exact authorized candidate advancing the pinned
previous `main`. Reconciliation cannot authorize or perform a merge.

These events implement [AGENT_REVIEW.md](AGENT_REVIEW.md). Only an eligible
non-author reviewer may merge. The selected snapshot must merge without
conflict into current `main`, and required checks run against that exact
candidate. Later branch commits remain available for a later reviewer-owned
merge and do not retroactively enter the completed one.

## 7. State reduction

No derived global index, dashboard, inbox, or Markdown summary is committed to
the bus, because it would be a multi-writer artifact. The helper derives state
by replaying valid logs.

For each agent, current lifecycle, scope, and plan are its latest corresponding
events by `seq`; recent progress is a bounded tail of progress events. `done`,
`abandoned`, or a valid `agent.retired` targeting it makes scope inactive.
Coordinator authority is the immutable set in `BUS.json`; user-directed custody
transfer under one of those names uses `agent.resumed`.

For issues, dependencies, handoffs, and reviews, the opening event defines
identity and authorized respondents. Acknowledgement does not close an item.
Mutually exclusive transitions name their exact predecessor. Concurrent
transitions from the same predecessor remain valid but reduce that item to
`lifecycle_conflict`; unrelated bus state remains usable. A bootstrap-authorized
coordinator, on user direction, emits `lifecycle.conflict_resolved` naming the
complete competing set and selected successor. Review findings are open from
`review.changes_requested` until the accepting reviewer emits a causally linked
`review.findings_cleared`; clearing findings does not close the nomination.
`review.merge_authorized` freezes one candidate but does not close the branch
workstream; matching `review.merged` or `review.merge_reconciled` closes that
nomination chain for the recorded candidate. Reassignment creates a successor
chain while preserving inherited findings. Invalid authority or malformed
transitions fail validation; valid concurrent choices are exposed rather than
converted into global corruption.

Inbox state is the set of open events targeting an agent. Outbox state selects
events emitted by that agent. Scope conflicts are computed from current active
claims without selecting a winner. Merge readiness is computed according to
`AGENT_REVIEW.md` from the nomination, selected branch commit, current `main`,
and exact merge candidate.

If any agent log is malformed, authoritative reduction fails. Commands may opt
into `--quarantine-invalid`; they reduce valid logs while printing and returning
a mandatory `state_incomplete` marker naming every excluded agent and first
invalid path/line. They must not answer questions whose result depends on a
quarantined identity. While degraded, valid agents may append only
`agent.status`, `plan.set`, `progress.reported`, or `issue.opened` events that do
not target or reference a quarantined identity. Scope, dependency, handoff,
lifecycle, schema, review, authorization, and merge commands remain disabled.
Incremental validation requires the quarantine set not to grow. This preserves
basic fleet communication without treating incomplete state as authority.

## 8. Rust helper

The planned helper lives at `tools/agent-bus/`. Rust supplies one portable
binary, typed schemas, safe file handling, and predictable JSON parsing. It uses
ordinary Git and requires no GitHub API.

Initial commands:

```text
agent-bus register --agent <name> ...
agent-bus status [--agent <name>] [--json]
agent-bus scope set --agent <name> --file <scope.json>
agent-bus plan set --agent <name> --file <plan.json>
agent-bus progress --agent <name> --file <progress.json>
agent-bus issue open --agent <name> --to <target> --file <issue.json>
agent-bus issue acknowledge|resolve|reject --agent <name> <issue-id> ...
agent-bus inbox --agent <name> [--json]
agent-bus dependencies --agent <name> [--json]
agent-bus review nominate|take|decline|changes|clear|supersede|reassign|authorize|withdraw|merged|reconcile ...
agent-bus prepare-merge --agent <reviewer> --nomination <event-id> --reviewed-commit <commit>
agent-bus merge-ready --agent <name> --authorization <event-id> [--json]
agent-bus audit-main [--to <commit>] [--json]
agent-bus conflicts [--json]
agent-bus lifecycle resolve --agent <coordinator> --file <resolution.json>
agent-bus tail [--agent <name>] [--count <n>] [--json]
agent-bus validate [--incremental <old>..<new>] [--quarantine-invalid]
agent-bus sync --agent <name>
```

Mutation commands acquire an operating-system lock outside the committed tree,
fetch and validate, derive the next sequence and segment, construct a typed event
rather than accepting a raw line, atomically replace the tail with the appended
version, create a local commit, and validate again. A later local event may name
an earlier same-agent event in `refs` even though both retain the fetched batch
base in `observed`; synchronization rebases commits while event causality stays
in sequence IDs rather than transient local commit IDs.

The helper emits human-readable and stable `--json` output. Long values remain
escaped JSON strings in version 1 so events are self-contained; external
attachments are deferred.

An untracked local cache may accelerate queries and may use SQLite. It is keyed
by exact bus head; mismatch or corruption causes replay from JSONL. It is never
authority and no mutable global index is committed.

## 9. Validation

Full validation checks:

- agent name, registration, immutable primary role, and role authority;
- UTF-8/LF one-object-per-line encoding;
- contiguous segments and sequences;
- 1,000-event closed segments and valid active tail;
- agreement among path, line offset, agent, sequence, and ID;
- canonical serialization and exact versioned schemas;
- reference existence and visibility from `observed`;
- lifecycle authority and legal transitions;
- claim path grammar and reported active scope conflicts; and
- commit syntax and review eligibility where required.

Incremental validation additionally checks each linear parent diff:

- after the orphan root, ordinary commits change one agent directory only;
- that directory matches all newly appended events;
- valid existing lines and closed segments are unchanged;
- complete lines are appended only to the tail, with deterministic rollover;
- events are not deleted or reordered; and
- the only multi-directory/non-append diff is the narrowly defined
  bootstrap-authorized-coordinator structural repair.

Bus validation does not inspect product-ref updates. `audit-main` separately
walks every first-parent successor after immutable `product_review_from`. Each
successor must be exactly a two-parent reviewer merge correlated with authorship
trailers, reviewer trailer, published
`review.merge_authorized`, and either `review.merged` or
`review.merge_reconciled`. It detects an author/direct push, missing receipt, or
mismatched candidate after the fact; without a server-side gate, the cooperative
helper cannot prevent an actor from bypassing it. The default audit range begins
after `product_review_from` in immutable `BUS.json`.
Validation and audit cannot prove a test ran, a bug report is correct, or a
scope claim is socially authorized. Those remain review facts.

## 10. Synchronization

`agent-bus sync --agent alice` performs:

```text
validate local log
require each unpublished commit to change only alice/**
fetch origin refs/heads/agent-bus
structurally scan new authorizations and fetch only their exact candidate tags
rebase unpublished bus commits onto origin/agent-bus
validate the rebased range and resulting tree
push HEAD:refs/heads/agent-bus
on non-fast-forward: fetch, rebase, validate, retry with bounded backoff
```

The helper never force-pushes, never stages product files, and refuses a dirty
bus worktree with changes outside the named directory. Different-agent pushes
normally rebase cleanly. A same-directory conflict means concurrent writers or
protocol violation and requires explicit recovery.

Agents synchronize before scope changes, acting on another agent's event,
publishing interface changes, nominating/taking review, merging, and pausing,
completing, abandoning, or handing off work. They need not report every code
commit; the bus records coordination-relevant state rather than execution trace.

## 11. Failure and recovery

Tail writes use a temporary file in the same directory, flush, and atomic
replacement. A crash cannot publish a partial line. Failed pushes leave local
commits available for later retry. Offline events retain their honest observed
head and may expose conflicts after rebase; conflicts are resolved by new
events, not edits.

Concurrent writers under one name are never auto-merged. One keeps the name;
the other registers anew and republishes unpublished semantic events.

Every push to `agent-bus` should run incremental bus-validation CI; product CI
remains disabled for bus-only pushes. If malformed data nevertheless lands,
authority-bearing writers stop and quarantine mode exposes the incomplete state
while permitting the restricted diagnostic events above.
A bootstrap-authorized `coordinator`, acting on explicit user direction, may
make one `bus-admin: repair <agent>:<seq>` commit. The only permitted repair is
byte-for-byte restoration of paths changed by the invalid commit to their last
valid ancestor state; it cannot reinterpret, complete, or edit an event. The
offending agent then republishes any intended operation as new valid events.
The repair commit names the invalid commit and restored ancestor and has exactly
one `Agent-Bus-Coordinator: <name>` trailer. Validation derives that name's
authority from the last valid ancestor and mechanically checks the exact tree
restoration. Like agent fields elsewhere, the trailer is cooperatively
attributed rather than cryptographically bound. This is the sole append-only
exception and Git history retains both commits.

If an agent disappears, another reports the stale scope/dependency. On user
direction a bootstrap-authorized coordinator emits `agent.retired`; a replacement may then claim
released paths. Open issues and dependencies are transferred with
`issue.reassigned` or `dependency.reassigned`, emitted by the opener or a
bootstrap-authorized coordinator and accepted by the new target. Transfer preserves the complete
request and does not resolve it. Open reviews use `review.reassigned`. Logs are
never deleted.

## 12. Schema evolution

Every event carries its version. Readers continue parsing every version present
in branch history. Old logs are never rewritten merely to upgrade schema.

An upgrade requires: reviewed normative design on `main`; a helper that reads
old and new versions; then a `schema.activated` event from a bootstrap-authorized
coordinator naming the version and design/helper commits. Only then
may writers emit the new version. Removing reader support while old events
remain is forbidden.

The initial protocol performs no compaction. If storage becomes material,
closed segments may be archived only under a separately reviewed, exactly
round-tripping format and reader. Query caches remain disposable.

## 13. Authority boundary

Bus scope does not override repository ownership. Plans do not amend normative
design. Progress, test, issue-resolution, and review events are claims linked to
commits, not Lean proofs or CI results. Events never enter the Lean trusted base,
proof graph, executable artifact, or product branch.

Durable design decisions belong in the appropriate normative document and
`DECISIONS.md`. The bus may cite them but cannot replace them.

## 14. Implementation acceptance

Before use, the helper must pass fixtures for:

1. orphan bootstrap and registration;
2. generated concurrent appends by at least 16 distinct agents;
3. exact rollover from event 999 to 1000;
4. rejection of gaps, duplicates, bad paths/IDs, blank lines, CRLF, malformed
   JSON, unknown fields, and unsupported versions;
5. issue, dependency, handoff, reassignment, two-phase review, and schema
   activation lifecycles;
6. exclusive scope conflict and release;
7. rejection of old-line or closed-segment edits;
8. non-fast-forward rebase/retry without force;
9. same-name concurrent-writer refusal;
10. interruption without partial publication;
11. main-history audit detection of an author/direct push, missing authorization
    or receipt, a non-`reviewer` identity, conflict-resolved candidate, or
    candidate differing from the one authorized;
12. deterministic human and JSON output on Windows and Linux;
13. cache deletion followed by identical replayed state;
14. malformed-log quarantine output, restricted unrelated diagnostic
    publication, and mechanically bounded restoration;
15. 65,536-byte event acceptance and 65,537-byte rejection;
16. concurrent lifecycle choices remaining valid, conflict reduction, and
    explicit coordinator selection;
17. deterministic candidate construction/tag validation for renames, file
    modes, attributes, symlinks, submodules, and content conflicts;
18. both publication orders of a reassignment racing an offline final finding,
    with no orphaned finding; and
19. candidate-tag fetch count proportional to newly encountered
    authorizations, not historical candidates.

Role fixtures additionally reject product authorship or product scope by any
non-`implementor`, review acceptance or merge by any non-`reviewer`, retirement
by any non-bootstrap-authorized coordinator, and any event that attempts to
mutate an identity's registered role.

A generated local performance fixture may exercise many logs but is not checked
in. Measurements record events, bytes, cold/incremental query time, and peak
memory. No number is promised before measurement; ordinary status and inbox
queries must remain comfortably interactive.

Review-throughput fixtures also record merge latency and exact-candidate check
reruns under at least 16 concurrent nominations. If reviewers repeatedly lose
the `main` compare-and-swap race, a coordinator may announce advisory merge
slots through ordinary plan/progress events. Slots improve throughput but never
grant authority or replace review authorization.

Scope should follow [PROCESS_SHARDING.md](PROCESS_SHARDING.md): implementors
normally claim a component's implementation/certificate shards, keep signature
shards narrowly owned, and announce signature changes to consumers with
`dependency.requested`. This is a coordination convention, not proof authority.

## 15. Adversarial review questions

Reviewers should ask:

1. Can any ordinary operation require two agents to edit one file?
2. Can rebase or timestamps create a false global order?
3. Can the wrong agent close an issue, dependency, handoff, or review?
4. Can stale scope silently win over concurrent scope?
5. Is the 1,000-event boundary unambiguous?
6. Can interruption create a valid-looking truncated state?
7. Can a malformed direct push be recovered without rewriting history?
8. Can schema evolution still replay the entire branch?
9. Can a cache or derived view become undeclared authority?
10. Can bus state be mistaken for proof, permission, or review evidence?
11. Is the worktree/sync procedure viable for every expected provider?
12. Does any event invite secrets or unnecessary private information?

Implementation begins only when independent review finds no ordinary
coordination path that violates single-writer storage or requires an unstated
semantic choice.
