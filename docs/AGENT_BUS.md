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
commit has no product-history parent. It contains bus logs only, is never merged
into `main`, and is never merged into product branches.

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
object. Blank lines, comments, byte-order marks, CRLF, trailing whitespace, and
partial final lines are invalid.

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
{"v":1,"id":"alice:17","agent":"alice","seq":17,"time":"2026-09-01T20:00:00Z","observed":"8af03c1000000000000000000000000000000000","kind":"issue.opened","refs":[],"data":{"code_commit":"abc1230000000000000000000000000000000000","issue_kind":"bug","locations":["Grass/Http2/Frame.lean:87"],"severity":"high","summary":"Reserved bit accepted","target":"bob"}}
```

Envelope laws:

- `v` is the positive schema version.
- `agent` equals the containing directory.
- `seq` equals the line-derived global sequence number.
- `id` equals `<agent>:<seq>` in canonical decimal without leading zeroes.
- `time` is an RFC 3339 UTC timestamp with `Z`; it is presentation data and
  never determines causality or conflict precedence.
- `observed` is the full object ID of the fetched bus head on which the event
  was based. It is `null` only for initial branch bootstrap.
- `kind` is a versioned event kind.
- `refs` is a lexicographically ordered set of causal event IDs.
- `data` is an object matching the exact schema for `kind`.

The helper writes fields in the displayed order as compact JSON. Nested object
keys are lexicographically ordered. Unknown envelope or event-data fields are
rejected in version 1 so misspellings cannot silently become inert.

Published events are immutable. Scope changes, corrections, resolutions, and
supersession are later events. There is one total order per agent by `seq`.
There is no invented global event order: cross-agent causality is expressed by
`refs` and `observed`, not timestamp or rebased commit position.

An event may reference only an event visible in its `observed` bus state. Since
history rewriting is forbidden, that observed commit remains a stable ancestor
after later rebases.

## 6. Event kinds

The initial vocabulary is intentionally bounded.

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

`agent.retired` is emitted only by a `coordinator`, targets one registered
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
locations, expected/observed behavior, reproduction commands, and optionally
events it blocks.

Valid kinds are `bug`, `request`, `question`, and `scope_conflict`. Severities
are `critical`, `high`, `normal`, and `low`.

`issue.acknowledged`, `issue.resolved`, and `issue.rejected` reference exactly
one `issue.opened`. Only its target emits them. A code resolution names the exact
fix commit and verification commands. Rejection gives a reason and may cite a
normative document.

Reports are never cleared. Recurrence or dispute creates a new issue referencing
the earlier issue and disposition. Multiple contradictory terminal dispositions
for one issue are invalid.

### 6.5 Dependencies and handoffs

`dependency.requested` names a target, interface/artifact, needed-by milestone,
and blocking status. The target emits `dependency.acknowledged`,
`dependency.resolved`, or `dependency.rejected` with a causal reference.

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
emit `review.changes_requested`, `review.findings_cleared`, or personally merge
a reviewed branch snapshot. `review.findings_cleared` references one changes
event after the reviewer inspects its fixes; later findings use another changes
event. The author may emit `review.withdrawn` while review is pending.
`review.merged`, emitted by the reviewer after the merge, is both the positive
disposition and the record of the exact reviewed commit and resulting `main`
commit.

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
events by `seq`; recent progress is a bounded tail of progress events. `done` or
`abandoned` status makes scope inactive.

For issues, dependencies, handoffs, and reviews, the opening event defines
identity and authorized respondents. Acknowledgement does not close an item.
The first valid resolution, rejection, merge, withdrawal, or decline allowed by
its lifecycle closes or supersedes it. Review findings are open from
`review.changes_requested` until the accepting reviewer emits a causally linked
`review.findings_cleared`; clearing findings does not close the nomination.
Invalid or contradictory transitions fail validation rather than being ordered
by Git position.

Inbox state is the set of open events targeting an agent. Outbox state selects
events emitted by that agent. Scope conflicts are computed from current active
claims without selecting a winner. Merge readiness is computed according to
`AGENT_REVIEW.md` from the nomination, selected branch commit, current `main`,
and exact merge candidate.

If any agent log is malformed, normal reduction fails. The helper must not skip
bad lines and present remaining state as complete.

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
agent-bus review nominate|take|decline|changes|withdraw|merge ...
agent-bus merge-ready --agent <name> --branch <ref> --reviewed-commit <commit> --candidate <commit> [--json]
agent-bus conflicts [--json]
agent-bus tail [--agent <name>] [--count <n>] [--json]
agent-bus validate [--incremental <old>..<new>]
agent-bus sync --agent <name>
```

Mutation commands acquire an operating-system lock outside the committed tree,
fetch and validate, derive the next sequence and segment, construct a typed event
rather than accepting a raw line, atomically replace the tail with the appended
version, and validate again.

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
- claim path grammar and active scope conflicts; and
- commit syntax and review eligibility where required.

Incremental validation additionally checks each linear parent diff:

- ordinary commits change one agent directory only;
- that directory matches all newly appended events;
- valid existing lines and closed segments are unchanged;
- complete lines are appended only to the tail, with deterministic rollover;
- events are not deleted or reordered; and
- a product merge is performed by the nominated non-author reviewer, introduces
  the selected reviewed commit through a clean candidate, and has a matching
  receipt.

Validation cannot prove that a product commit exists on the same remote, a test
ran, a bug report is correct, or a scope claim is socially authorized. Those are
separate Git/review facts.

## 10. Synchronization

`agent-bus sync --agent alice` performs:

```text
validate local log
commit only alice/** as "bus(alice): <summary>"
fetch origin refs/heads/agent-bus
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

If malformed data is directly pushed despite the helper, normal writers stop.
A designated repository maintainer may make an explicit
`bus-admin: repair <agent>:<seq>` commit that minimally restores structural
validity without rewriting Git history. The repair preserves event identity and
intended meaning and is followed by an issue describing old/new object IDs and
reason. This is the sole exception to current-tree append-only editing. Valid
closed events may not be semantically revised through repair.

If an agent disappears, another reports the stale scope/dependency. A user or
coordinator records it `abandoned`; a replacement may then claim released paths.
Logs are never deleted.

## 12. Schema evolution

Every event carries its version. Readers continue parsing every version present
in branch history. Old logs are never rewritten merely to upgrade schema.

An upgrade requires: reviewed normative design on `main`; a helper that reads
old and new versions; a coordinator activation event; then new-version writers.
Removing reader support while old events remain is forbidden.

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
2. concurrent appends by at least three distinct agents;
3. exact rollover from event 999 to 1000;
4. rejection of gaps, duplicates, bad paths/IDs, blank lines, CRLF, malformed
   JSON, unknown fields, and unsupported versions;
5. issue, dependency, handoff, and review lifecycles;
6. exclusive scope conflict and release;
7. rejection of old-line or closed-segment edits;
8. non-fast-forward rebase/retry without force;
9. same-name concurrent-writer refusal;
10. interruption without partial publication;
11. attempted merge by an author, a non-`reviewer` identity, a
    conflict-resolved candidate, or a candidate differing from the one checked;
12. deterministic human and JSON output on Windows and Linux; and
13. cache deletion followed by identical replayed state.

Role fixtures additionally reject product authorship or product scope by any
non-`implementor`, review acceptance or merge by any non-`reviewer`, retirement
by any non-`coordinator`, and any event that attempts to mutate an identity's
registered role.

A generated local performance fixture may exercise many logs but is not checked
in. Measurements record events, bytes, cold/incremental query time, and peak
memory. No number is promised before measurement; ordinary status and inbox
queries must remain comfortably interactive.

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
