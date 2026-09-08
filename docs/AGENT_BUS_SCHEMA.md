# Agent bus version 1 schema

Status: normative companion to [AGENT_BUS.md](AGENT_BUS.md). The Rust helper and
machine-readable JSON Schema are generated from equivalent typed definitions;
neither may add policy absent here.

This document closes the version-one event vocabulary. Fields marked `?` are
optional. Every other field is required. Unknown fields, unknown enum values,
duplicate set members, and `null` in place of an omitted optional field are
invalid.

## 1. Scalar and collection types

| Name | Law |
| --- | --- |
| `Agent` | `[a-z][a-z0-9-]{0,47}` |
| `EventId` | `<Agent>:<canonical u64>` |
| `ObjectId` | lowercase hexadecimal full Git object ID in the object format named by `_bus/BUS.json` |
| `Timestamp` | UTC `YYYY-MM-DDTHH:MM:SSZ`, with no fractional seconds |
| `Branch` | full ref accepted by `git check-ref-format`; product branches additionally obey `refs/heads/agent/<Agent>/<topic>` |
| `Topic` | lowercase alphanumeric/hyphen, begins and ends alphanumeric, length `1..64` |
| `PathClaim` | repository-relative exact path or directory prefix ending `/**`; `/`, `.`, and `..` components forbidden |
| `TreePath` | repository-relative exact non-directory path; `/`, `.`, `..`, and `/**` components forbidden |
| `FileMode` | one of Git modes `100644`, `100755`, `120000`, or `160000` |
| `Short` | UTF-8 string of `1..256` bytes after JSON decoding |
| `Text` | UTF-8 string of `0..4096` bytes after JSON decoding |
| `StringSet<T>` | JSON array of unique `T`, byte-lexicographically sorted |
| `List<T>` | JSON array in semantic order |

All numeric values are JSON integers. Array length is at most 256 unless a
narrower bound is stated. An encoded event line is at most 65,536 bytes excluding
LF, which is the final bound even when the component bounds would permit more.
Commands are `Text` and must not contain credentials. Locations are `Text` in
`repo/path:line` form when a line is known. Empty optional collections are
omitted rather than encoded as `null`.

## 2. Envelope

The envelope field order and laws are defined in `AGENT_BUS.md`. `refs` is a
`StringSet<EventId>`. Every event ID occurring in `data` occurs in `refs`, and
`refs` equals exactly the unique event IDs contained in `data`. Events that cite
additional evidence carry an explicit `evidence : StringSet<EventId>` field.

Canonical JSON uses UTF-8 NFC strings. Object keys outside the fixed envelope
are byte-lexicographically sorted. Integers use canonical decimal without a
leading zero or exponent. Strings emit Unicode directly and use the shortest
JSON escape for quote, backslash, and control characters; `\/`, printable
`\uXXXX` escapes, and insignificant whitespace are invalid. Booleans are
lowercase JSON literals. The checked Rust serializer is the only normal writer;
these rules make direct-push validation deterministic across platforms.

For cross-agent references, every referenced event must be reachable from
`observed`. Same-agent references may instead name an earlier contiguous local
sequence. `observed` is `null` only for the bootstrap coordinator's first
`agent.registered` event; every later event names an `ObjectId`.

The immutable bootstrap file has canonical compact JSON plus LF:

```json
{"v":1,"object_format":"sha1","coordinators":["coordinator"],"product_review_from":"abc1230000000000000000000000000000000000","merge_engine":"git-ort","merge_engine_version":"2.51.0","merge_engine_epoch":"coordinator:0"}
```

Bootstrap fields use the fixed order displayed above.

**Deviation actually taken (2026-09), documented for the historical record.**
`object_format` was narrowed from `sha1` or `sha256` to `sha1` alone. The
helper reads and writes objects through a vendored libgit2 built without its
experimental sha256 support, so a `sha256` bus is one no reader could open;
`BusConfig::new` refuses to publish one and `BusConfig::parse` refuses to load
one. Leaving the wider set documented would have advertised a value the only
implementation rejects. Nothing observable is lost -- no `sha256` bus was ever
activated -- and widening it again is a matter of the object-store build, not
of this schema.

`object_format` is `sha1`; coordinator names form a nonempty
`StringSet<Agent>`; `product_review_from` is a full `ObjectId` reachable from
product `main` and is the last bootstrap-exempt product commit. The V1
`merge_engine`, `merge_engine_version`, and `merge_engine_epoch` fields are
retained historical data. The successor review protocol removes their authority
meaning: a
reader must not require that exact Git version in order to reduce the bus or do
ordinary work. The root
`.gitattributes` is exactly `*.jsonl -text` plus LF. Every named coordinator has
its sequence-zero registration in the same orphan root commit, and no other
agent log occurs there.

## 3. Common records

```text
DependencyImport = { agent : Agent, interface : Short }
PlanStep = { id : Short, state : pending|active|done|dropped, text : Text }
Finding = {
  id : Short,
  priority : critical|high|normal|low,
  locations : List<Text>,
  rationale : Text,
  closure_conditions : Text
}
FindingRef = { changes_event : EventId, finding_id : Short }
FindingDisposition = {
  changes_event : EventId,
  finding_id : Short,
  disposition : cleared|superseded,
  rationale : Text
}
CheckResult = { command : Text, result : passed, evidence? : Text }
```

Finding IDs are unique within one `review.changes_requested`. A finding's global
identity is `(changes_event, finding_id)`. `superseded` requires a nonempty
rationale and never means the finding was fixed.

`CheckResult` occurs only inside merge authorization, so `passed` is its sole
result. Failed runs are recorded in `progress.reported` and normally produce
`review.changes_requested`; they cannot appear as authorization evidence.

## 4. Bootstrap and lifecycle events

### `agent.registered`

```text
data = {
  display_name : Short,
  primary_role : implementor|reviewer|coordinator|auditor,
  purpose : Text,
  product_base? : ObjectId,
  product_branch? : Branch,
  provider? : Short,
  model? : Short
}
refs = []
```

This is sequence zero. A coordinator registration is valid only if its agent
name appears in immutable `_bus/BUS.json`. Product fields are permitted only for
an `implementor`.

**Deviation actually taken (2026-09), documented for the historical record.**
The least-authority role was spelled `observer` in version one and is spelled
`auditor` here. AGENT_COORDINATION_EVOLUTION.md section 2.2 renames the wire
role rather than carrying two overlapping ones, and nothing was migrated
because no `observer` was ever registered on this bus -- which is the reason
that section gives for the rename being safe rather than breaking. The design's V1 transition spelling -- registering as `observer` with
`purpose: auditor:<emphasis>` until migration -- is deliberately **not**
offered here, because it is already moot and following it would fail. The
v1-to-v2 cutover has happened (AGENT_COORDINATION_EVOLUTION.md section 2.6),
v1's `refs/heads/agent-bus` is read-only, so there is no v1 bus on which to
register the transition spelling; and this helper rejects the string
`observer` outright, so a reader who tried would get a parse error from
`register --role`. An audit identity registers as `auditor`.

Gate 24 ("a V1 `observer` registered for audit migrates to exactly one V2
`auditor` identity without acquiring implementor or reviewer authority") is
**discharged vacuously and deliberately, not implemented**. No `observer` has
ever been registered on this bus -- verified against the live roster and
against every published event on every stream before the rename -- so there is
nothing to migrate and no fixture that could exercise a migration. Recording
that here rather than leaving it implied, because the gap is otherwise
invisible: the helper rejects the string `observer` outright, and reduction
propagates that failure, so a single V1 `observer` registration appearing in
migrated history would make the bus unreducible on every host. If such an
identity is ever created before activation, the migration tool must rewrite
the wire string, and this note must become a test.

### `agent.status`

```text
data = {
  status : active|blocked|paused|done|abandoned,
  note : Text,
  product_branch? : Branch,
  product_commit? : ObjectId
}
refs = []
```

Product fields are permitted only for an implementor.

### `agent.resumed`

```text
data = { previous_lifecycle : EventId, reason : Text, user_authority : Text }
refs = [previous_lifecycle]
```

The referenced event is either the same identity's latest own lifecycle event of
any status or the latest `agent.retired` targeting it. User-directed exclusive
custody is required. The event reactivates the identity and role remains
unchanged.

### `agent.retired`

```text
data = { target : Agent, previous_lifecycle : EventId, reason : Text, user_authority : Text }
refs = [previous_lifecycle]
```

Only a bootstrap-authorized coordinator emits it. The target cannot be the
emitter and the referenced event is the target's latest lifecycle event.

### `schema.activated`

```text
data = { version : u32, design_commit : ObjectId, helper_commit : ObjectId }
refs = []
```

Only a bootstrap-authorized coordinator emits it. `version` is greater than all
previously activated versions. Linked validation requires both commits reachable
from product `main`; unavailable objects make the event `unverifiable`, while
present nonmatching/unreachable objects make it invalid.

### `merge_engine.activated`

```text
data = {
  previous_epoch : EventId,
  merge_engine : git-ort,
  merge_engine_version : Short,
  design_commit : ObjectId,
  helper_commit : ObjectId
}
refs = [previous_epoch]
```

This event remains in the grammar so existing V2 history is readable. New
writers do not emit it after the successor review protocol is activated. Its
engine/version fields are diagnostics, not requirements imposed on a reader or
host.

## 5. Scope, plan, and progress

### `scope.set`

```text
data = {
  base_code_commit : ObjectId,
  exclusive : StringSet<PathClaim>,
  shared : StringSet<PathClaim>,
  exports : StringSet<Short>,
  depends_on : List<DependencyImport>,
  note : Text
}
refs = []
```

Only an active implementor emits it. `depends_on` is sorted by `(agent,
interface)` and contains no duplicate pair. Empty `exclusive` and `shared`
release all claims.

### `plan.set`

```text
data = { summary : Text, steps : List<PlanStep>, risks : List<Text> }
refs = []
```

Step IDs are unique. At most one step is `active`.

### `progress.reported`

```text
data = {
  product_commit? : ObjectId,
  completed : List<Text>,
  current : List<Text>,
  next : List<Text>,
  blockers : List<Text>,
  verification : List<Text>
}
refs = []
```

`product_commit` is permitted only for an implementor. Verification entries are
commands reportedly run, not proof of success.

## 6. Issues

### `issue.opened`

```text
data = {
  target : Agent,
  issue_kind : bug|request|question|scope_conflict,
  severity : critical|high|normal|low,
  summary : Text,
  code_commit? : ObjectId,
  locations : List<Text>,
  expected? : Text,
  observed_behavior? : Text,
  reproduction : List<Text>,
  blocks : StringSet<EventId>,
  evidence : StringSet<EventId>
}
refs = unique (blocks + evidence)
```

Every `blocks` member is an opening review nomination or reassignment event.

An auditor-opened `issue.opened` must carry an empty `blocks` set, and the
helper rejects a nonempty one from an `auditor` identity
(AGENT_COORDINATION_EVOLUTION.md section 2.2, gate 21). `blocks` makes an
issue refuse the named reviewer's own `review.merge_authorized`, and only the
issue's *target* may dispose of it -- so without this rule an auditor could
halt a candidate at will and could not be made to release it, which is the
"unilateral or indefinite candidate veto that the named reviewer cannot
dispose" the design forbids. An auditor with an urgent finding routes the
evidence to the reviewer and coordinator instead; the reviewer decides whether
to publish a merge-blocking finding of its own.

### `issue.acknowledged`

```text
data = { issue : EventId, assignment : EventId, note : Text }
refs = unique [issue, assignment]
```

The current target emits it once.

### `issue.resolved`

```text
data = { issue : EventId, assignment : EventId, summary : Text, fix_commit? : ObjectId, verification : List<Text> }
refs = unique [issue, assignment]
```

The current target emits it. This is terminal.

### `issue.rejected`

```text
data = { issue : EventId, assignment : EventId, reason : Text, normative_refs : List<Text> }
refs = unique [issue, assignment]
```

The current target emits it. `assignment` is the opening issue or latest
`issue.reassigned`. This is terminal.

### `issue.reassigned`

```text
data = { issue : EventId, previous_assignment : EventId, previous_target : Agent, new_target : Agent, reason : Text }
refs = unique [issue, previous_assignment]
```

The original opener or a bootstrap-authorized coordinator emits it for an open
issue. `previous_assignment` is the opening issue or exact currently selected
reassignment, and `previous_target` must match it. The request fields are
inherited unchanged from the opening event. The new target acknowledges the
opening issue after observing this event; subsequent dispositions use the root
`issue` ID and selected assignment.

## 7. Dependencies and handoffs

### `dependency.requested`

```text
data = {
  target : Agent,
  interface : Short,
  needed_by : Text,
  blocking : bool,
  summary : Text,
  evidence : StringSet<EventId>
}
refs = evidence
```

### `dependency.acknowledged`

```text
data = { dependency : EventId, assignment : EventId, note : Text }
refs = unique [dependency, assignment]
```

### `dependency.resolved`

```text
data = { dependency : EventId, assignment : EventId, summary : Text, product_commit? : ObjectId, verification : List<Text> }
refs = unique [dependency, assignment]
```

### `dependency.rejected`

```text
data = { dependency : EventId, assignment : EventId, reason : Text }
refs = unique [dependency, assignment]
```

Acknowledgement and terminal dependency events are emitted by the current
target. `assignment` is the opening request or latest reassignment.

### `dependency.reassigned`

```text
data = { dependency : EventId, previous_assignment : EventId, previous_target : Agent, new_target : Agent, reason : Text }
refs = unique [dependency, previous_assignment]
```

The opener or a bootstrap-authorized coordinator emits it while open. Other
rules match `issue.reassigned`.

### `handoff.offered`

```text
data = {
  receiver : Agent,
  scope : StringSet<PathClaim>,
  product_branch : Branch,
  product_commit : ObjectId,
  verification : List<Text>,
  known_issues : StringSet<EventId>,
  evidence : StringSet<EventId>,
  summary : Text
}
refs = unique (known_issues + evidence)
```

Only an implementor offers a handoff.

### `handoff.accepted`

```text
data = { handoff : EventId, note : Text }
refs = [handoff]
```

Only the receiver emits it. Acceptance is terminal for the offer but scope
transfers only after the giver releases and receiver claims it.

### `handoff.declined`

```text
data = { handoff : EventId, reason : Text }
refs = [handoff]
```

Only the receiver emits it; this is terminal.

### `handoff.withdrawn`

```text
data = { handoff : EventId, reason : Text }
refs = [handoff]
```

Only the offerer emits it before acceptance; this is terminal.

## 8. Review

The opening request fields are:

```text
ReviewRequest = {
  authors : StringSet<Agent>,
  product_branch : Branch,
  reviewer : Agent,
  required_checks : List<Text>,
  review_scope : StringSet<PathClaim>,
  summary : Text,
  target_branch : Branch,
  evidence : StringSet<EventId>
}
```

In V1, `target_branch` is exactly `refs/heads/main`.

### `review.nominated`

```text
data = ReviewRequest
refs = evidence
```

An active implementor listed in `authors` emits it. Every author is an active
implementor; reviewer is an active dedicated reviewer and is not an author.

### `review.nomination_accepted`

```text
data = { nomination : EventId, note : Text }
refs = [nomination]
```

Only the named reviewer emits it once.

### `review.nomination_declined`

```text
data = { nomination : EventId, reason : Text }
refs = [nomination]
```

Only the named reviewer emits it before authorization; this closes that
nomination.

### `review.changes_requested`

```text
data = { nomination : EventId, reviewed_commit : ObjectId, findings : List<Finding>, evidence : StringSet<EventId> }
refs = unique ([nomination] + evidence)
```

The accepting reviewer emits it. `findings` is nonempty.

Publication validation requires the nomination still be current in the event
commit's parent tree. A finding and reassignment prepared from the same old bus
head cannot both publish unchanged: if the finding lands first, the rebased
reassignment must be rebuilt to inherit it; if reassignment lands first, the
rebased finding is stale and cannot publish. Unpublished events may be discarded
and recreated because append-only immutability begins at successful publication.

### `review.findings_cleared`

```text
data = {
  nomination : EventId,
  changes_event : EventId,
  finding_id : Short,
  resolved_commit : ObjectId,
  summary : Text
}
refs = [nomination, changes_event]
```

The accepting reviewer emits it after inspecting the named commit. The ID names
one still-open finding in `changes_event` and becomes terminally `cleared`.

### `review.findings_superseded`

```text
data = {
  nomination : EventId,
  changes_event : EventId,
  finding_id : Short,
  rationale : Text
}
refs = [nomination, changes_event]
```

Only the accepting reviewer for the current nomination emits it. The ID names
one still-open finding and becomes terminally `superseded`. An
author cannot emit or preselect this disposition.

### `review.reassigned`

```text
data = ReviewRequest + {
  replaces : EventId,
  reason : Text,
  inherited_findings : List<FindingRef>
}
refs = unique ([replaces] + every inherited_findings.changes_event + evidence)
```

The request equals the replaced request except for `reviewer`. The replacement
is different and eligible. Every still-open finding in the replaced nomination
chain occurs exactly once and remains open. An author in the request or a
bootstrap-authorized coordinator emits it. It is a new nomination and must be
accepted; only its accepting reviewer may later clear or supersede inherited
findings.

### `review.withdrawn`

```text
data = { nomination : EventId, reason : Text }
refs = [nomination]
```

An author named in the request emits it before authorization. It closes that
nomination.

### `review.merge_authorized`

```text
data = {
  nomination : EventId,
  product_branch : Branch,
  previous_main : ObjectId,
  reviewed_commit : ObjectId,
  candidate : ObjectId,
  merge_engine_epoch : EventId,
  checks : List<CheckResult>,
  finding_dispositions : List<FindingDisposition>,
  evidence : StringSet<EventId>,
  reviewed_scope : StringSet<PathClaim>,
  limitations : List<Text>,
  summary : Text
}
refs = unique ([nomination, merge_engine_epoch] + every finding_dispositions.changes_event + evidence)
```

Only the accepting reviewer emits it. The candidate is a prepared merge commit
not yet on `main`. Its first parent is `previous_main`, its second parent is
`reviewed_commit`, the reviewer reports an ordinary clean merge, and its message
contains exactly one matching
`Agent-Bus-Reviewer` trailer. It is invalid if the reviewer authored any commit
introduced relative to `previous_main`, any introduced non-review-merge commit
lacks an `Agent-Bus-Agent` trailer, its exact author set differs from the request,
a changed path falls outside `reviewed_scope`, a required check is absent, or
any finding lacks a terminal `cleared` or `superseded` disposition. Every check
result is `passed`.

`reviewed_scope` equals the active nomination's `review_scope` exactly; an
authorization cannot widen, narrow, or otherwise rewrite the author's review
request. Changed paths remain a subset of that unchanged scope.

`merge_engine_epoch` is retained in the V2 wire shape but is diagnostic after
the successor review protocol is activated. A version mismatch is not a
validation failure.

Before this event is published, the exact candidate is available at immutable
lightweight tag `refs/tags/agent-candidate/<reviewer>/<candidate>`. Structural
validation checks the event shape and lifecycle. Linked validation fetches the
exact tag and product objects and checks parents, tree, message, and tag. It does
not reconstruct the merge with local Git. A fetched mismatch is invalid; an unavailable remote
or object is `unverifiable` and blocks authorization/merge without making the
bus malformed.

Version two has no field for overlap disclosure, so its host-independent tree
check deliberately accepts only the safe subset. Let `review_base` here be the
required unique merge base of `previous_main` and `reviewed_commit`. Outside
paths changed by `review_base..reviewed_commit`, the candidate entry equals
`previous_main`; on every changed path, `previous_main` must equal `review_base`
and the candidate entry equals `reviewed_commit`. A clean merge with both-sides
changes to one path must wait for an author-published rebased commit or the
successor schema. This temporary restriction prevents reviewer-created tree
content without pinning a Git version.

### Successor approval/landing split

The active version-two record above remains authoritative until a later schema
activation. That activation replaces its overloaded proof role with two events;
old events retain their historical meaning during replay.

`review.approved` is independent of a target-branch head:

```text
data = {
  nomination : EventId,
  review_base : ObjectId,
  reviewed_commit : ObjectId,
  reviewed_scope : StringSet<PathClaim>,
  review_checks : List<CheckResult>,
  finding_dispositions : List<FindingDisposition>,
  limitations : List<Text>,
  summary : Text
}
refs = unique ([nomination] + every finding_dispositions.changes_event)
```

Only the accepting reviewer emits it. `review_base` is an ancestor of both the
selected source and the target branch at selection; a later landing base must
descend from it. `reviewed_commit` is reachable from the nominated product branch
at publication time. Commits in the exact `review_base..reviewed_commit` range
have authors and trailers equal to the nomination authors; its changed paths are
a subset of the exact nomination scope; every open finding has one terminal
disposition; and every nominated review check passed. Publication freezes only
this selected source judgment. Later product-branch commits and later `main`
commits do not enter it.

The successor `review.merge_authorized` is the bounded landing authority:

```text
data = {
  approval : EventId,
  product_branch : Branch,
  previous_main : ObjectId,
  candidate : ObjectId,
  overlap_resolutions : List<OverlapResolution>,
  landing_checks : List<CheckResult>,
  reviewed_scope : StringSet<PathClaim>,
  summary : Text
}
refs = [approval]
```

where:

```text
TreeEntry = absent | { mode : FileMode, object : ObjectId }
OverlapResolution = {
  path : TreePath,
  base : TreeEntry,
  reviewed : TreeEntry,
  previous_main : TreeEntry,
  candidate : TreeEntry,
  rationale : Text
}
```

Only the reviewer who emitted `approval` emits it. The helper derives the
reviewed commit from that approval and fetches the exact candidate the reviewer
constructed with `previous_main` as first parent and that commit as second
parent. The reviewer reports an ordinary clean merge and never edits the
prepared candidate tree. Every changed path lies in the frozen scope, the
candidate tree satisfies the host-independent relation below, and every
mandatory landing check derived from the protected-path registry is
present and passed. The registry and check classification come from
`previous_main`; neither author nor reviewer can omit a protected check.

The tree relation is stated over recursively enumerated Git tree entries, where
an entry is `absent` or the exact `(mode, object-id)` pair. Let `B`, `A`, `M`,
and `C` be the trees of `review_base`, `reviewed_commit`, `previous_main`, and
`candidate`. Let `changed(A,B)` be every path whose entry differs between the
reviewed source and its base. Linked validation checks:

- outside `changed(A,B)`, `C[p] = M[p]`;
- where `M[p] = B[p]`, `C[p] = A[p]`; and
- every remaining path is represented exactly once by an
  `overlap_resolutions` row containing `p`, `B[p]`, `A[p]`, `M[p]`, `C[p]`,
  and the reviewer's explanation of the ordinary clean merge result.

There are no extra rows, and each row's entries must equal the fetched trees.
Renames are represented by their deleted and added paths; modes, symlinks, and
submodule entries are compared without platform interpretation. This does not
reconstruct a merge or demand a cross-host candidate object ID. It does make
every tree entry not inherited verbatim from an unopposed parent explicit and
independently checkable, so a reviewer cannot silently inject content into the
merge candidate. An overlap row is disclosure, not permission to hand-edit: if
ordinary Git cannot make the candidate without manual resolution, the author
must publish a new reviewed source commit.

No exact Git version or merge-engine epoch participates in successor authority.
Git is required only to fetch/pull and perform a normal non-force push. A version
string may be retained in diagnostic output but is not a schema field or gate.

Review checks bind to the selected authored source. Landing checks bind to the
exact combined candidate and are intentionally small: affected Lean/build
typechecking plus the registered exceptional gates for trust-critical paths.
Post-merge corroboration is not represented as merge authority. A failed
post-merge check opens an urgent issue and leads to a reviewed repair or revert.

If a push loses to a newer `main`, the approval remains current. The reviewer
constructs another exact candidate and emits another landing authorization
after rerunning only landing checks. No event authorizes a candidate whose first
parent differs from its recorded `previous_main`.
An authorization may be published after `main` has advanced: publication records
the exact attempted candidate and is not rejected merely for staleness.
`merge-ready` then reports that it cannot land, and the same approval is used for
a fresh candidate on the new base. Thus event-publication latency cannot destroy
the substantive source review.

The successor nomination schema replaces each free-form required-check string
with `{ command, phase }`, where `phase` is `review`, `landing`, or
`post_merge`. The accepting reviewer may strengthen a phase but cannot weaken
it. The helper unions the nomination with mandatory phase assignments from the
protected-path registry in `previous_main`. Thus an
author cannot move a trust-critical check after landing, while ordinary
substantive review and expensive audit commands are not repeated for every new
base.

The registry is the reviewed product-tree file
`Tools/agent-bus/protected-paths.json`. It is a versioned JSON object containing
an ordered `classes` array; each class has a stable `key`, a nonempty list of
repository-relative path globs, and a nonempty list of landing checks shaped as
`{ key, argv : List<Text> }`. Duplicate keys and ambiguous duplicate check keys
are invalid. A glob uses `/`-separated normalized path segments; a segment is
literal or exactly `*`, and only the final segment may be `**`. Character
classes, `?`, negation, backslashes, and parent/current-directory components are
invalid. Matching classes are unioned by check key. This section and
`AGENT_REVIEW.md` own the registry's normative meaning; `g-design` owns changes
to that meaning or to the protected classes, and the agent-bus implementor owns
the checked reader. Selecting only `previous_main` is monotone at landing time:
a path that became protected after source approval cannot be classified away by
the author or reviewer.
The registry must exist before successor activation and contain a class matching
its own path and the checked registry reader, so a candidate cannot weaken the
mechanism that selects its landing checks.

### `review.merged`

```text
data = {
  authorization : EventId,
  previous_main : ObjectId,
  main_commit : ObjectId,
  product_branch : Branch,
  reviewed_commit : ObjectId,
  summary : Text
}
refs = [authorization]
```

Only the authorizing reviewer emits it. Values equal the authorization and
`main_commit = candidate`. The product push must have advanced `main` from
`previous_main` to `main_commit` without force.

### `review.merge_reconciled`

```text
data = {
  authorization : EventId,
  previous_main : ObjectId,
  main_commit : ObjectId,
  product_branch : Branch,
  reviewed_commit : ObjectId,
  reason : Text,
  user_authority : Text
}
refs = [authorization]
```

Only a bootstrap-authorized coordinator emits it when no merged or reconciled
receipt exists. Values equal the authorization, `main_commit = candidate`, and
product first-parent history already proves that exact candidate advanced the
pinned previous main. This event records a completed product fact; it grants no
merge authority.

A concurrently published reviewer receipt with identical authorization-derived
values is a valid redundant receipt, not a lifecycle conflict. Any disagreement
with the authorization or product history is invalid.

## 9. Lifecycle conflict resolution

### `lifecycle.conflict_resolved`

```text
data = {
  root : EventId,
  competing : StringSet<EventId>,
  selected : EventId,
  reason : Text,
  user_authority : Text
}
refs = unique ([root] + competing)
```

Only a bootstrap-authorized coordinator emits it on explicit user direction.
`competing` is the complete set of mutually exclusive transitions from the same
selected predecessor, has at least two members, and contains `selected`. The
selected transition becomes current and the others remain visible but inert.
The event cannot select a transition outside that exact conflict set.

## 10. Cross-kind lifecycle laws

- Mutually exclusive transitions from the same predecessor are each valid when
  concurrent. Reduction marks the item `lifecycle_conflict`; dependent mutation
  and merge authorization stop until `lifecycle.conflict_resolved` selects one.
  The bus itself remains valid and unrelated work continues.
- Exclusive sets are: issue resolve/reject/reassign from one assignment;
  dependency resolve/reject/reassign from one assignment; handoff
  accept/decline/withdraw; review decline/withdraw/reassign from one nomination;
  and clear/supersede for one finding. Acknowledgements and independently pinned
  merge authorizations are not exclusive transitions.
- Concurrent `merge_engine.activated` events naming one `previous_epoch` form a
  lifecycle conflict whose root is that epoch.
- `review.changes_requested` has the stronger current-nomination publication
  precondition above. It never becomes an orphaned concurrent successor of a
  published reassignment.
- Reassignment closes future authority under the replaced opening event and
  creates a successor opening event. A published merge authorization remains
  immutable and can only win or lose its ordinary non-force product push. A receipt for
  an authorization remains valid after reassignment if that candidate won.
- Retirement removes scope and new-action authority but does not silently close
  work. Open targeted work is explicitly reassigned, resolved, rejected, or
  withdrawn by its authorized actor.
- Only unresolved issues whose `blocks` set names an event in the active
  nomination chain block authorization.
- An authorization consumes the bus state named by its envelope `observed`.
  Later events cannot alter that historical verdict or candidate.
- Event authority is derived from registration role, bootstrap coordinator list,
  opening event, current reassignment chain, and causal references. Timestamp
  never grants, expires, or orders authority.
- Structural validity and linked status are separate. `unverifiable` linked
  claims remain pending and block dependent authority; linked-invalid claims are
  unusable and excluded from lifecycle selection without corrupting unrelated
  structurally valid logs.

## 11. Generated artifacts

Before bus bootstrap, the helper implementation must generate and check in:

- Rust tagged-enum/struct definitions equivalent to this document;
- a JSON Schema for every envelope version and event data variant;
- canonical valid and invalid fixture JSONL; and
- a schema fingerprint printed by `agent-bus --version`.

The generated JSON Schema is validation convenience. This normative document
and reviewed Rust types define intended semantics; disagreement is an
implementation defect and blocks bootstrap.

## 12. Fleet-wide assurance

### `audit.reported`

```text
data = {
  inspected_commits : StringSet<ObjectId>,
  areas : List<Text>,
  methods : List<Text>,
  limitations : List<Text>,
  issues : StringSet<EventId>,
  summary : Text
}
refs = issues
```

The auditor's fleet-wide summary (AGENT_COORDINATION_EVOLUTION.md section 2.2).
Valid only from an active agent whose immutable primary role is `auditor`.

Deliberately **non-authoritative**, and the type carries no status,
disposition or verdict field of any kind so that it cannot become otherwise.
Actionable findings live in separate `issue.opened` events referenced by
`issues`; every id there must name an issue that exists, so a report cannot
cite a fiction. Reducing this event touches nothing else -- no issue status,
no assignment, no finding disposition -- because an auditor that could close
what it reports would be clearing its own findings, which section 2.2 forbids
(gate 22). A nominated reviewer may cite an audit as evidence but must still
publish its own dispositions and authorization judgment (gate 23).

Requires a **complete** frontier, and is therefore currency-sensitive: it may
not be published from a stale local cut. The frontier is the report's only
record of what it observed, and a sparse one names just the agents the payload
happens to reference -- a clean report would otherwise pin nothing at all
about the streams it claims to have examined, which is exactly the
assurance-without-evidence `limitations` exists to prevent.

`areas`, `methods` and `summary` must be nonempty. `inspected_commits` and
`issues` may both be empty: an audit of coordination history alone inspects no
product commit, and a clean surface is reportable "without manufacturing empty
issues". `limitations` is where blind spots are
stated, because absence of a finding is not assurance that unexamined
behavior is correct. The observed event frontier the report pins is the
envelope's own `observed` field, not a field here.

### Successor `ci.run_observed`

Machine-readable post-merge CI custody uses a distinct event after the next
schema activation; it does not overload the deliberately verdict-free
`audit.reported` event:

```text
data = {
  landed_commit : ObjectId,
  check_key : Short,
  provider : Short,
  run_identity : Text,
  conclusion : green | red | cancelled | timed_out | artifact_missing | unavailable,
  observed_at : Timestamp,
  issues : StringSet<EventId>,
  limitations : List<Text>,
  summary : Text
}
refs = issues
```

Only an active `auditor` emits it. `run_identity` is the provider's immutable run
identifier, not a dashboard label or branch name. `red`, `cancelled`,
`timed_out`, and `artifact_missing` require at least one targeted issue;
`unavailable` requires an infrastructure issue and states that no product
conclusion was observed. `green` requires an empty issue set. The conclusion is
a machine-readable observation, **not authority**: reduction appends the record
to the audit view and changes no issue, review, gate, nomination, or merge state.
No merge-ready predicate may consume it. A later run may supersede operational
attention but cannot rewrite the historical observation.

For each landed first-parent `main` commit, the CI auditor emits one
`ci.run_observed` per post-merge check selected from that commit. A human-facing
`audit.reported` may cite those event ids as evidence in its summary, but remains
a broad audit report rather than the CI verdict carrier. Coverage is therefore
machine-decidable without granting the auditor merge authority: the required
pair `(landed_commit, check_key)` has a terminal observation whose immutable run
identity can be inspected. Silence remains absence of evidence, never green.
