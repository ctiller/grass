# agent-bus

Rust helper implementing the [Git agent bus protocol](../../docs/AGENT_BUS.md),
its [event schema](../../docs/AGENT_BUS_SCHEMA.md), and the
[review/merge protocol](../../docs/AGENT_REVIEW.md).

## Build

```sh
cargo build --release
```

## One-time repository setup

```sh
agent-bus bootstrap-init --coordinator <name> --product-review-from <commit>
```

Creates the orphan `refs/heads/agent-bus` root commit with `_bus/BUS.json`,
`.gitattributes`, and the named coordinators' `agent.registered` events.

## Everyday use

```sh
agent-bus register --agent alice --display-name Alice --role implementor --purpose "..."
agent-bus scope set --agent alice --file scope.json
agent-bus review nominate --agent alice --file nomination.json
agent-bus review take --agent bob <nomination-id>
agent-bus prepare-merge --agent bob --nomination <id> --reviewed-commit <sha>
agent-bus review authorize --agent bob --file authorization.json
agent-bus merge-ready --agent bob --authorization <id>
# bob then pushes the printed candidate: git push origin <candidate>:refs/heads/main
agent-bus review merged --agent bob --file receipt.json
agent-bus audit-main
agent-bus validate
```

Run `agent-bus --help` for the complete command tree (issues, dependencies,
handoffs, lifecycle, sync, tail, conflicts, ...). Mutating commands whose
payload is more than a couple of scalars take `--file <path.json>` containing
exactly the event kind's `data` fields from AGENT_BUS_SCHEMA.md; the helper
fills in envelope bookkeeping (`v`, `id`, `seq`, `time`, `observed`, `refs`)
and any identifiers already implied by other flags (e.g. `issue resolve`
looks up the issue's current assignment itself).

## Design notes / known simplifications

- **Canonical encoding**: enforced by comparing the parsed, re-serialized
  typed struct against the original line bytes (envelope and `_bus/BUS.json`
  each have a fixed field order; everything nested inside `data` is
  alphabetically sorted "for free" because `serde_json::Value`'s `Map` is a
  `BTreeMap`), plus an explicit Unicode-NFC walk.
- **Causality/concurrency**: the bus branch is a real linear (non-merge)
  history, so "is event X reachable from commit C" reduces to comparing the
  walk-order index of X's publishing commit against C's — no invented
  cross-agent ordering from timestamps is needed. `publish_event` fixes an
  event's `observed` once, at construction, and *rebases* (never rebuilds) an
  already-committed local commit onto a moved tip on a push race, so a
  genuinely concurrent pair of events can retain the same `observed` even
  though one ends up published causally after the other — which is exactly
  the input the section 10 concurrent-vs-causally-later distinction needs.
  Effects for exclusive-transition events (issue/dependency resolution,
  handoff disposition, review decline/withdraw/reassign, finding
  clear/supersede, merge-engine epoch activation) are applied *eagerly*, the
  moment the first transition for a predecessor is walked — so an ordinary,
  uncontested reassign-then-act sequence (the overwhelmingly common case)
  replays correctly even within a single linear pass. If a second, genuinely
  concurrent transition for the *same* predecessor is later found (neither
  observed the other), the predecessor's derived "current" state (status,
  current target/assignment, current nomination) is reset back to a neutral
  `LifecycleConflict` marker — reverting whatever the first transition
  optimistically set — rather than silently keeping whichever transition
  happened to be walked first. A referential fact a transition establishes
  (e.g. "this reassignment id names this target," so its named target can act
  on it) is recorded regardless of Apply/Concurrent outcome, since other
  agents may legitimately act on a transition before it's known whether it
  ultimately wins its own race. `lifecycle.conflict_resolved` then applies
  the selected transition's effect for good. One earlier design (deferring
  *every* exclusive-transition effect to a pass after the whole walk) was
  tried and reverted: it handled the concurrent case correctly but broke the
  ordinary sequential case outright (no event later in the same walk could
  see any earlier transition's effect) — a second adversarial review round
  caught this before it shipped.
- **`review.*` / merge git cross-checks** (candidate tag existence + exact
  reconstruction, commit trailer authorship, changed-path-within-scope, `main`
  compare-and-swap) live in `review_cmds.rs`, deliberately separate from the
  pure bus-log replay in `apply.rs`, so replay/validate never needs a
  product-repo checkout beyond the bus branch itself. Candidate commits are
  fully deterministic (fixed author/committer identity, timestamp one second
  past the later parent, exact message) and `review authorize` independently
  *reconstructs* the candidate from `previous_main`/`reviewed_commit`/reviewer
  and requires a byte-exact match — not just structural checks — before
  publishing, so authorship/eligibility can't be bypassed by skipping
  `prepare-merge` and hand-building a candidate.
- **`--quarantine-invalid`**: on a full-validation failure, falls back to a
  per-agent structural-only scan (each agent's own JSONL segments, via
  `storage::read_agent_log`) rather than a full incremental semantic replay
  that excludes just the bad agent. This satisfies the "expose the incomplete
  state, keep other agents legible" intent without a second replay engine; it
  does not yet enforce the exact degraded-mode publish whitelist from
  AGENT_BUS.md section 7 (only `agent.status`/`plan.set`/`progress.reported`/
  `issue.opened` targeting non-quarantined identities) — today all publication
  is simply blocked while quarantined, which is fail-safe but stricter than
  the spec allows.
- **`--linked`** (AGENT_BUS_SCHEMA.md section 9's linked validation): checks
  every `review.merge_authorized` event's candidate tag, parents, and reviewer
  trailer against locally-fetchable git objects; independently *reconstructs*
  the candidate from `previous_main`/`reviewed_commit`/reviewer (same
  `reconstruct_candidate` used by `review authorize`) and re-checks
  introduced-commit authorship trailers, so a `review.merge_authorized` line
  appended by a direct push that bypassed `authorize` is caught the same way
  a normal `authorize` call would catch it. Reports `invalid` (present but
  mismatched) separately from `unverifiable` (absent locally). It does not
  yet fetch from a separate declared product remote beyond `origin`, and does
  not cover `schema.activated`/`merge_engine.activated` design/helper-commit
  reachability.
- **Repair commits** (`bus-admin: repair ...`, AGENT_BUS.md section 11):
  content- and authority-checked (byte-for-byte restoration of every path the
  *named invalid commit* changed, exactly one `Agent-Bus-Coordinator` trailer
  naming a bootstrap coordinator, and the named ancestor is verified to
  actually be an ancestor of the invalid commit) as part of the structural
  walk itself (`history.rs`), so every consumer gets the same guarantee
  `validate` does, not just `validate`. The message grammar this helper
  expects is `bus-admin: repair <invalid-commit> restore <ancestor-commit>`;
  the spec does not pin an exact grammar beyond "names the invalid commit and
  restored ancestor". **Known gap**: because `history::walk_one_commit`
  returns an error immediately on any structurally invalid commit, a repair
  commit appearing *later* in history than the invalid commit it fixes is
  never reached by a single forward walk — the walk stops at the invalid
  commit before it can discover the repair. Recovering in that situation
  today requires inspecting the reported error externally and constructing
  the repair with that knowledge; `--quarantine-invalid` remains available as
  a degraded-but-live fallback in the meantime.
- **Generated artifacts** (AGENT_BUS_SCHEMA.md section 11 — standalone JSON
  Schema files, canonical fixture corpus, `--version` schema fingerprint) are
  not yet produced; `agent-bus validate --json` reports `schema_version` and
  `schema_kinds` (the count of implemented event kinds) as a lighter-weight
  substitute today.
- **Local cache** (AGENT_BUS.md section 8's optional SQLite query
  accelerator) is not implemented; every command replays from JSONL, which is
  fast enough at the log sizes this protocol expects.
- **Array-length bound** (AGENT_BUS_SCHEMA.md section 1: "at most 256 unless a
  narrower bound is stated") is enforced for `StringSet`-typed fields but not
  yet for every plain `List<T>` field individually; the 65,536-byte
  encoded-line cap remains a hard backstop regardless.
