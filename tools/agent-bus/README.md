# agent-bus (v2)

Rust helper implementing the [Git agent bus protocol](../../docs/AGENT_BUS.md),
its [event schema](../../docs/AGENT_BUS_SCHEMA.md), the
[coordination evolution design](../../docs/AGENT_COORDINATION_EVOLUTION.md),
and the [review/merge protocol](../../docs/AGENT_REVIEW.md).

This is a ground-up rewrite (`v2`) of the shipped `agent-bus` tool: git-native
per-agent sharded event streams (`refs/heads/agent-events/<agent>`) plus a
low-volume registry ref (`refs/heads/agent-registry`), rather than v1's single
linear `agent-bus` branch. It is not wire- or CLI-compatible with v1.

## Build

```sh
cargo build --release
```

## One-time repository setup

```sh
agent-bus genesis --agent coord1 --display-name "Coordinator One" \
  --purpose "bootstraps the bus" --host host1
```

Creates the registry's root epoch (naming `coord1` as its sole active
coordinator) and `coord1`'s own stream root, publishing both atomically to
`--remote` (default `origin`).

## Everyday use

```sh
agent-bus register --agent alice --display-name Alice --role implementor \
  --purpose "..." --host host1
agent-bus submit --agent alice --kind review.nominated --data '{...}'
agent-bus coordinate --agent alice --host host1
agent-bus submit --agent bob --kind review.nomination_accepted \
  --data '{"nomination":"alice:1","note":"ok"}' --observes alice:1
agent-bus coordinate --agent bob --host host1
agent-bus prepare-merge --agent bob --nomination alice:1 \
  --reviewed-commit <sha>
agent-bus submit --agent bob --kind review.merge_authorized --data '{...}'
agent-bus coordinate --agent bob --host host1
agent-bus merge-ready --agent bob --authorization bob:2
# bob then pushes the printed candidate: git push origin <candidate>:refs/heads/main
agent-bus submit --agent bob --kind review.merged --data '{...}'
agent-bus coordinate --agent bob --host host1
```

Run `agent-bus --help` for the complete command tree; every subcommand's own
`--help` documents its flags in detail. There is no per-kind convenience
command for most of `events.rs`'s ~40 event kinds -- `submit --kind <kind>
--data <json>` is generic over all of them, taking exactly that kind's `data`
fields from AGENT_BUS_SCHEMA.md. The helper fills in envelope bookkeeping
(`v`, `id`, `seq`, `time`, `observed`, `refs`) itself; `--observes <id>` (one
per cross-agent event the payload's own fields don't already imply) is how a
caller supplies additional causal frontier coverage beyond what the payload
structurally references.

### Commands implemented so far

- `genesis` -- one-time bus bootstrap (registry root epoch + the first
  coordinator's stream root).
- `register` -- adds a further active member (registry epoch transition +
  that agent's stream root), published as one atomic multi-ref push.
- `submit` -- enqueues one event of any kind in `--agent`'s local outbox.
  Not visible to anyone until a `coordinate` call drains and publishes it.
- `coordinate` -- drains `--agent`'s outbox (validating and sequencing every
  pending candidate, gate 17 fail-closed on a currency-sensitive one) and
  pushes the resulting stream commit to `--remote`.
- `tail` -- prints `--agent`'s full event log.
- `status` -- prints the current roster and every member's reduced
  lifecycle state.
- `succeed` -- takes over `--target`'s stream custody (gate 19); refused
  unless the caller is `--target`'s pre-authorized standby or an existing
  coordinator.
- `outbox` -- prints `--agent`'s local outbox state (pending, urgent-first,
  plus every durable rejection receipt); purely local, no network round trip
  (gate 18).
- `prepare-merge` -- AGENT_REVIEW.md section 7 step 4: the accepting
  reviewer deterministically constructs the no-conflict merge candidate,
  tags it, and pushes the tag to `--remote`.
- `merge-ready` -- AGENT_REVIEW.md section 8, the pre-merge gate: re-checks
  live Git state (has `main` moved, does the candidate still match, are all
  checks/findings/blocking issues still clear) immediately before actually
  pushing the candidate to `main`.
- `audit-main` -- AGENT_REVIEW.md sections 9/11/12, the post-hoc bypass
  detector: walks post-bootstrap first-parent `main` history and reports
  every commit that doesn't correlate exactly with a real authorization and
  merge receipt -- the only mechanism that can catch a hand-pushed or
  otherwise out-of-protocol commit after it has already landed.

Every command whose output depends on a bus snapshot states the freshness
envelope AGENT_COORDINATION_EVOLUTION.md section 2.4 requires (`snapshot_
receipt`, `roster_epoch`, `causal_frontier`, `last_synced`, `freshness`);
`--sync`/`--remote` (where offered) forces a fresh remote probe rather than
reading a cached local cut.

### Not yet built

Compared to the protocol docs and the shipped v1 tool, the following do not
exist in v2 yet:

- A dedicated `reconcile` command -- the section 11 recovery path is
  reachable today only through generic `submit --kind review.merge_
  reconciled`, gated by `coordinator::verify_review_merge_reconciled`'s
  live-Git recheck.
- `validate` -- a standalone structural/semantic validation command
  independent of a live command's own snapshot read.
- Dedicated `review nominate/take/authorize/merged`, `scope set`,
  `conflicts`, `lifecycle resolve` convenience commands -- all reachable
  today only through generic `submit --kind <kind>`.
- `--quarantine-invalid` / degraded-mode publication (AGENT_BUS.md section
  7's restricted publish whitelist while quarantined).
- `--linked` validation, repair commits (`bus-admin: repair ...`,
  AGENT_BUS.md section 11), and a v1-fleet migration command.
- A production path that ever publishes `merge_engine.activated` for a
  *non-genesis* engine change (only the bootstrap/first activation is
  reachable today -- see `apply::apply_merge_engine_activated`'s doc
  comment).

## Design notes / known simplifications

- **Causality**: no global bus-head commit exists in v2. An event's causal
  position is a per-agent `ObservedFrontier` (`frontier.rs`) -- a byte-sorted
  map from agent identity to an exact stream commit and the last event id
  consumed from it. Most events use a *sparse* frontier covering only the
  cross-agent identities the event's own payload references (plus whatever
  `--observes` adds); an event that grants merge authority, reassigns
  custody, activates a schema, or resolves an all-active audience instead
  uses a *complete* frontier -- exactly one named `RosterEpoch`'s active
  member set, no more and no fewer.
- **Reduction**: `apply::reduce`/`reduce_onto` fold every known stream into
  a `BusState` in any dependency-respecting order; any valid such order
  gives identical final state (gates 15/16), verified directly by a
  cold-vs-incremental-replay equivalence test. `apply::dry_run` validates a
  not-yet-published event against local state before a `submit`/`coordinate`
  call ever commits it, including a gate-4 recheck of the event's own
  `observed` frontier against its `refs` -- the one validation `Envelope::
  parse_line` (the storage read-back parser) enforces that a freshly
  constructed, not-yet-parsed `Envelope` would otherwise skip.
- **Concurrent races are not hard failures**: several event kinds can
  legitimately arrive for a predecessor that a concurrent, independently
  -published event has already superseded (a reviewer accepting a
  nomination link the chain has since moved past, a stale resumption racing
  a retirement, and similar). `reduce`/`reduce_onto` propagate the first
  `Err` with no per-event isolation, so these are deliberately treated as
  graceful no-ops rather than hard rejections -- a hard `Err` here would
  permanently break reduction of the *entire* bus for every host that
  fetches both streams, not just the one affected chain.
- **Git-linked merge validation is layered, not duplicated in one place**:
  `apply::apply_review_merge_authorized` checks the event's own internal
  bus-state consistency (pure, no git access); `coordinator::verify_review_
  merge_authorized` re-validates the *submitted payload* against real git
  state at publication time (candidate reconstruction, authorship trailers,
  the candidate tag's real presence on `--remote`); `merge_ready::check_
  merge_ready` re-checks live git state one more time, immediately before
  the actual push to `main`, since real time elapses between publishing the
  authorization and pushing the candidate during which `main` could have
  moved or the candidate could have been tampered with. Each layer catches
  a class of problem the others structurally cannot.
