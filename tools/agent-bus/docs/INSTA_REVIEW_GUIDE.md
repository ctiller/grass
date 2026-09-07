# Reviewing `insta` snapshot changes

`agent-bus` uses [`insta`](https://insta.rs) (`insta = { version = "1", features = ["json", "redactions"] }`
in `Cargo.toml`) for report/JSON-shaped assertions: things like `audit-main
--json` output, `status --json`, or a replayed `BusState` — where hand-writing
`assert_eq!` against a multi-field struct is unreadable and a one-field diff
in a hand-rolled comparison is easy to miss. Tests call
`insta::assert_json_snapshot!(...)` or `insta::assert_debug_snapshot!(...)`;
the expected value lives in a `.snap` file next to the test module, under a
`snapshots/` directory (e.g. `src/snapshots/agent_bus__review_cmds__tests__*.snap`
or `tests/snapshots/cli_dispatch__*.snap`).

## What a `.snap` file actually is

A `.snap` file is **the literal serialized expected output**, plus a small
metadata header (source file, expression). For example:

```
---
source: src/review_cmds.rs
expression: findings
---
[]
```

It is not generated boilerplate and it is not noise. **A snapshot diff IS a
behavior diff.** If a PR changes a `.snap` file, some function's actual
output changed — review the new snapshot content exactly as you would review
a changed `assert_eq!` right-hand side: read the whole new file, not just the
diff markers, and ask "is this the output I'd expect given what the rest of
this PR changed?"

## Author workflow (`cargo insta`)

`cargo-insta` is installed as a CLI (`cargo insta --version`). From
`tools/agent-bus/`:

1. **Run the tests.** `cargo insta test` runs the suite and, for every
   snapshot assertion whose actual output no longer matches the committed
   `.snap`, writes a `<name>.snap.new` file alongside it instead of failing
   silently — the test still fails, but you get the proposed new content on
   disk.
2. **Review what changed.** `cargo insta review` walks you through every
   pending `.snap.new` interactively, showing a diff against the current
   `.snap` (or "new snapshot" if none exists yet), and lets you accept or
   reject each one individually.
3. **Accept deliberately.** If the new output is correct — you changed
   `audit_main`'s finding shape on purpose, for instance — accept it (via
   `cargo insta review`, or in bulk with `cargo insta accept` once you've
   eyeballed every `.snap.new` yourself). This deletes the `.snap.new` and
   overwrites the checked-in `.snap` with its content.
4. **Reject to fix code instead.** If the new output is wrong, run
   `cargo insta reject` (or answer "no" in `review`) to delete the
   `.snap.new` and leave the old `.snap` as the still-failing expectation,
   then go fix the code.
5. **Commit only the promoted `.snap` files.** Stage the updated `.snap`
   files together with the code change that caused them, in the same commit,
   with a message that says what changed and why.

## `.snap.new` files must never be committed

`cargo insta test` / a plain `cargo test` failure on a stale snapshot leaves
`*.snap.new` files on disk — they are insta's working state, not a
deliverable. If `git status` ever shows a `.snap.new` file, that PR is
incomplete: either run `cargo insta accept` to promote it (if correct) or
delete it and fix the code (if not). A `.snap.new` in a diff is itself a
signal something in CI or the author's local flow was skipped.

## Legitimate vs. suspicious snapshot update

A snapshot-file change in a PR diff is **legitimate** when:

- The PR's stated intent explains it — e.g. "add `reviewed_scope` to
  `audit-main --json` findings" and the `.snap` diff shows exactly a new
  `reviewed_scope` field appearing.
- The diff is scoped to the field(s) the PR's code change actually touches.
  A one-line fix to `commands::dependencies`'s JSON shape should not also
  perturb an unrelated `review_cmds` snapshot.
- The new snapshot content still makes semantic sense against
  `docs/AGENT_BUS_SCHEMA.md` / `docs/AGENT_REVIEW.md` — field names, ordering,
  and value shapes still match the schema those commands are supposed to
  implement.

Treat a snapshot update as **suspicious** and dig in before approving when:

- **An unrelated field changed.** The PR title/description is about X, but
  the `.snap` diff also touches a field or code path Y that X shouldn't
  affect. This is the classic sign of an accidental regression that got
  silently baked into the new expectation instead of being caught.
- **A security- or protocol-relevant check's error message or finding
  disappeared or weakened.** e.g. a `.snap` for `audit-main --json` that used
  to contain a `"problem": "reviewer authored an introduced commit"` finding
  and now contains `[]` — that is not a formatting change, it's a check that
  stopped firing. Read the corresponding code diff before accepting; if there
  isn't one, treat this as a red flag (see below).
- **The `.snap` changed with no corresponding code change in the diff at
  all.** If `git diff` shows only files under `snapshots/` and no change to
  the `src/` (or `tests/`) file the snapshot's `source:` header names, ask
  why. The most common innocent explanation is a dependency or Rust `Debug`
  formatting change; the most common non-innocent explanation is someone ran
  `cargo insta accept` to make a red test suite go green without
  understanding (or fixing) why it went red. Don't approve until the author
  explains which one it is.
- **The diff is large and the PR description doesn't mention it.** A
  reviewer should never have to reverse-engineer "what behavior change made
  this snapshot move" from the bytes alone — that's the author's job to
  explain in the PR description or commit message.

## Reviewer checklist

- [ ] Every `.snap.new` file is absent from the diff (only promoted `.snap`
      files are present).
- [ ] Each changed `.snap` file's diff was read in full, not skimmed.
- [ ] Each changed `.snap` file has a corresponding code change in the same
      PR that plausibly explains it.
- [ ] No unrelated field, ordering, or finding silently changed alongside the
      intended change.
- [ ] Any check or finding that used to fire and no longer does is explained
      and intentional, not a quietly dropped validation.
- [ ] New snapshot content still matches the shape described in
      `docs/AGENT_BUS_SCHEMA.md` / `docs/AGENT_REVIEW.md` where applicable.
- [ ] If you're unsure whether a diff is legitimate, ask the author to run
      `cargo insta test` locally and paste the `cargo insta review` diff
      explanation in the PR description, rather than accepting on faith.
