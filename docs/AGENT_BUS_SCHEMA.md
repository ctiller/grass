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
{"v":1,"object_format":"sha1","coordinators":["coordinator"],"product_review_from":"abc1230000000000000000000000000000000000","merge_engine":"git-ort","merge_engine_version":"2.51.0"}
```

Bootstrap fields use the fixed order displayed above.

`object_format` is `sha1` or `sha256`; coordinator names form a nonempty
`StringSet<Agent>`; `product_review_from` is a full `ObjectId` reachable from
product `main` and is the last bootstrap-exempt product commit. `merge_engine`
is `git-ort` in V1 and `merge_engine_version` is the exact semantic version
validated by the helper at bootstrap. The example version is illustrative; the
implemented helper publishes its reviewed supported version before bootstrap,
fixes all merge options, and refuses to run on a different version. The root
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

## 4. Bootstrap and lifecycle events

### `agent.registered`

```text
data = {
  display_name : Short,
  primary_role : implementor|reviewer|coordinator|observer,
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
data = { previous_lifecycle : EventId, reason : Text }
refs = [previous_lifecycle]
```

The referenced event belongs to the same identity and is its latest terminal or
paused lifecycle event. Role remains unchanged.

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
previously activated versions and both commits must be reachable from product
`main` when checked locally.

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
  checks : List<CheckResult>,
  finding_dispositions : List<FindingDisposition>,
  evidence : StringSet<EventId>,
  reviewed_scope : StringSet<PathClaim>,
  limitations : List<Text>,
  summary : Text
}
refs = unique ([nomination] + every finding_dispositions.changes_event + evidence)
```

Only the accepting reviewer emits it. The candidate is a prepared merge commit
not yet on `main`. Its first parent is `previous_main`, its second parent is
`reviewed_commit`, its tree is the pinned helper's conflict-free merge result,
and its message contains exactly one matching
`Agent-Bus-Reviewer` trailer. It is invalid if the reviewer authored any commit
introduced relative to `previous_main`, any introduced non-review-merge commit
lacks an `Agent-Bus-Agent` trailer, its exact author set differs from the request,
a changed path falls outside `reviewed_scope`, a required check is absent, or
any finding lacks a terminal `cleared` or `superseded` disposition. Every check
result is `passed`.

Before this event is published, the exact candidate is available at immutable
lightweight tag `refs/tags/agent-candidate/<reviewer>/<candidate>`. Full bus
validation checks parents, tree, message, merge-engine reconstruction, and tag;
absence or mismatch is invalid.

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
- `review.changes_requested` has the stronger current-nomination publication
  precondition above. It never becomes an orphaned concurrent successor of a
  published reassignment.
- Reassignment closes future authority under the replaced opening event and
  creates a successor opening event. A published merge authorization remains
  immutable and can only win or lose its product compare-and-swap. A receipt for
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

## 11. Generated artifacts

Before bus bootstrap, the helper implementation must generate and check in:

- Rust tagged-enum/struct definitions equivalent to this document;
- a JSON Schema for every envelope version and event data variant;
- canonical valid and invalid fixture JSONL; and
- a schema fingerprint printed by `agent-bus --version`.

The generated JSON Schema is validation convenience. This normative document
and reviewed Rust types define intended semantics; disagreement is an
implementation defect and blocks bootstrap.
