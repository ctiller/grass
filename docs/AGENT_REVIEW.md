# Agent review and merge protocol

Status: normative design for cooperative product review. The bus helper is not
implemented yet.

Every product change entering `main` is authored by at least one `implementor`
agent and reviewed and merged by a distinct `reviewer` agent. A named product
branch is the review object. A GitHub pull request, approval, or merge queue is
not required.

The author nominates a reviewer on the orphan `agent-bus` branch described in
[AGENT_BUS.md](AGENT_BUS.md). The reviewer takes the request, reviews successive
branch snapshots as useful, and finally merges one reviewed snapshot. The act of
merging is the positive review verdict; there is no transferable approval token
and authors never merge their own work.

## 1. Non-negotiable rule

A product change may enter `main` only when:

1. authors work on a named branch other than `main`;
2. every agent-authored product commit identifies its author agent;
3. an author emits `review.nominated` naming that branch and one distinct
   reviewer;
4. the reviewer emits `review.nomination_accepted`;
5. the reviewer inspects the branch content they intend to incorporate;
6. no unresolved review finding prevents merge;
7. the selected branch snapshot merges without conflict into current `main`;
8. required checks pass on the exact resulting merge candidate;
9. the nominated reviewer, not an author, pushes that candidate to `main`; and
10. the reviewer emits `review.merged` recording the incorporated snapshot and
    resulting `main` commit.

There is no emergency, documentation-only, trivial-change, generated-change,
revert, or administrator exception. Urgency may shorten latency, not remove the
second agent. The live bus branch is coordination state, not product history,
and follows its separate single-writer protocol.

No participant force-pushes any protocol branch: not `main`, a product branch,
or `agent-bus`. Product branches advance through ordinary commits and merges.
Mistakes are corrected by new commits. This keeps every reviewed snapshot
reachable and makes concurrent work auditable.

## 2. Product branches and authorship

Product branches use:

```text
refs/heads/agent/<author>/<topic>
```

`author` is a registered bus name. `topic` consists of lowercase ASCII letters,
digits, and hyphens, begins and ends with an alphanumeric character, and is at
most 64 characters. A multi-author branch names its coordinating author in the
ref. Branch names are stable workstream identities, not immutable releases.

Each agent-authored product commit includes:

```text
Agent-Bus-Agent: alice
```

Multiple trailers are permitted only when multiple agents jointly authored that
commit. Git author metadata may also be present but does not replace the trailer.
The authors of a merge are the distinct trailer identities in the commits being
introduced relative to `main`.

Authors are responsible for a focused branch, current bus scope and progress,
preserving other work, implementing the normative demand, updating affected
tests and documents, reporting checks honestly, exposing trust-boundary changes
and limitations, nominating an eligible reviewer, and addressing findings.

Authors may keep pushing while review is active. A push does not invalidate the
nomination: the nomination covers the named workstream, while the reviewer
chooses and records the exact snapshot actually merged. Content pushed after
that snapshot remains unmerged work for a later reviewer-owned merge.

Authors may withdraw a nomination or delete a branch after all wanted content is
merged. They may not push product content directly to `main` or merge their own
branch.

## 3. Reviewer eligibility

A reviewer is eligible for a merge only if the reviewer:

- is a registered active agent with immutable primary role `reviewer` and is
  distinct from every author of the commits being introduced;
- authored none of those commits;
- did not materially generate them under an unrecorded identity;
- can inspect the complete selected diff, normative context, and evidence; and
- explicitly accepted the nomination for that branch.

Provider diversity is encouraged but not required. Independence is defined by
agent identity, dedicated role, and contribution, not model family. A single
underlying model may operate separate implementor and reviewer identities at
different times, but one identity never mixes those workloads and may not review
content produced through its other identity. Prefer genuinely separate agents.

If the reviewer commits a material product fix, they become an author and lose
eligibility to merge that content; another agent must review and merge it.
Review comments or uncommitted patch suggestions do not by themselves create
authorship. The reviewer must not resolve merge conflicts: that is product
authorship. They request changes and leave integration to the authors.

## 4. Nomination and review packet

An author emits one `review.nominated` per proposed reviewer:

```json
{
  "authors":["alice"],
  "product_branch":"refs/heads/agent/alice/x86-arithmetic",
  "reviewer":"bob",
  "required_checks":["lake build","lake test"],
  "review_scope":["Grass/Instruction/X86/**","docs/INSTRUCTIONS.md"],
  "summary":"initial ADD/SUB semantics and encoders",
  "target_branch":"refs/heads/main"
}
```

`authors` is the expected set and is checked again against the commits selected
for merge. The event references relevant issues, dependencies, handoffs, and
latest progress. It does not name a head commit: rapid authoring on the branch
is intentional.

The nominee emits `review.nomination_accepted` or
`review.nomination_declined`. Acceptance means responsibility for reviewing and,
if satisfied, merging; it is not approval returned to the author.

The branch and nomination together provide intended behavior, normative demands,
affected interfaces and trust boundaries, expected invalidation cone, checks,
known limitations, and an adversarial starting point. The reviewer may demand
missing information and inspect any relevant surrounding material.

## 5. Required review work

The reviewer examines the complete diff of the snapshot they may merge and
enough context to judge correctness, scope, and integration.

### 5.1 Intent and architecture

- The implementation matches its normative requirement.
- Behavior, proof demand, trust assumptions, and public interfaces are not
  silently weakened.
- The change respects module direction, sharding, and invalidation boundaries.
- Novel policy is explicit rather than invented by automation.

### 5.2 Lean and proof integrity

- The theorem is strong, non-vacuous, and connected to its consumer and root.
- No axiom, `sorry`, unchecked certificate, test, execution, or digest replaces
  proof.
- Automation consumes declared invariants and exposes residual goals.
- Existentials, opaque certificates, source closure, parser/writer laws, and
  emitted artifacts retain their authority connections.
- Stable names do not hide changed semantic dependencies.

### 5.3 Implementation and assembly

- Relevant failure, partial I/O, nondeterminism, faults, cancellation, cleanup,
  and incoming entropy are handled.
- Memory, provenance, ownership, races, obligations, ABI, CFG, and block
  contracts are respected.
- Generated instruction fragments remain inspectable and replaceable by raw
  same-contract assembly.
- Serialization retains its round-trip, accepted-input, and format laws.

### 5.4 Tests and external validation

- Positive tests exercise intended paths without masquerading as proof.
- Negative and mutation fixtures reject relevant weakenings.
- API, ISA, and protocol claims retain citations and boundary probes.
- The reviewer independently runs risk-proportionate checks and records them.
- Claimed build and `.olean` locality has the required evidence.

### 5.5 Repository hygiene

- No unrelated, cache, temporary, credential, or review-transcript artifact is
  introduced.
- Documentation and source mirrors remain consistent.
- Public names, errors, and comments state the real contract.
- Critical and high findings have explicit disposition before merge.

The reviewer need not reconstruct every kernel proof by hand. They must verify
that checked or generated evidence has the claimed shape and no unreviewed
semantic leap bridges the change.

## 6. Findings and continuing authoring

The reviewer emits `review.changes_requested` with actionable locations,
priority, rationale, and closure conditions. Authors respond with product
commits and bus references. The existing branch nomination remains active unless
withdrawn or declined; no repetitive re-nomination is required merely because
the branch advanced.

After inspecting the fixes, the reviewer emits `review.findings_cleared`
referencing the corresponding `review.changes_requested`. Only the reviewer can
clear their findings. Partial or additional findings use another changes event,
so the pre-merge gate can mechanically require every changes event to be
cleared.

The reviewer must inspect all content in the eventual selected snapshot,
including fixes and unrelated commits added during review. If branch motion
makes review incoherent, the reviewer may request a narrower branch or decline.

No bus event means “all future commits on this branch are approved.” Safety
comes from reviewer-owned selection and merge, not from freezing author work.

## 7. Reviewer-owned merge

When satisfied, the reviewer:

1. fetches current `refs/heads/main` and the nominated product branch;
2. selects the product-branch commit to incorporate;
3. verifies authorship and review eligibility for commits introduced by that
   selection;
4. creates a candidate by fast-forwarding `main` to the selected commit when
   possible, otherwise by making a no-conflict merge commit with current `main`
   and the selected commit as parents;
5. stops and requests author changes if Git requires conflict resolution;
6. runs every required integration check on the exact candidate;
7. rechecks bus readiness; and
8. pushes the candidate without force:

```text
git push origin <candidate>:refs/heads/main
```

The push is the compare-and-swap boundary. If `main` advanced and the push is
rejected, the reviewer fetches it, constructs a new clean candidate, and reruns
candidate-dependent checks. This does not require re-nomination: the selected
product snapshot has not changed. A new conflict goes back to the author.

The source branch may advance between selection and the push. That is harmless:
the reviewer merges the selected commit, not whatever the branch later names.
Later commits stay outside `main` and require a later merge under an active
nomination. The helper and receipt make this boundary visible.

A mechanical, conflict-free merge commit is integration metadata and does not
make the reviewer a product author. Its message includes:

```text
Agent-Bus-Reviewer: bob
```

After a successful push, the reviewer emits `review.merged`:

```json
{
  "independently_run":["lake build Grass.Instruction.X86"],
  "limitations":[],
  "main_commit":"987fed0000000000000000000000000000000000",
  "merge_method":"merge_commit",
  "previous_main":"abc1230000000000000000000000000000000000",
  "product_branch":"refs/heads/agent/alice/x86-arithmetic",
  "reviewed_commit":"def4560000000000000000000000000000000000",
  "reviewed_scope":["Grass/Instruction/X86/**","docs/INSTRUCTIONS.md"],
  "summary":"reviewed and merged; semantics and encoder close the stated obligations"
}
```

Valid methods are `fast_forward` and `merge_commit`. The receipt is a durable
record, not the authorization for an author to perform a later action.

## 8. Pre-merge gate

Immediately before pushing, the reviewer runs:

```text
agent-bus merge-ready \
  --agent <reviewer> \
  --branch refs/heads/agent/<author>/<topic> \
  --reviewed-commit <commit> \
  --candidate <commit>
```

It succeeds only when an author nominated that reviewer for the branch; the
reviewer took the nomination; selected commit authors match trailers and exclude
the reviewer; no later event withdrew or declined the nomination; every changes
event is cleared and no blocking critical/high issue remains; the candidate contains exactly
current `main` plus the selected branch history through `reviewed-commit`;
construction required no conflict resolution; and structural bus validation
passes.

The gate does not prove semantic adequacy or merge anything. Review judgment,
Lean, tests, CI, and Git history remain independent authorities.

## 9. Repository configuration

`main`, product branches, and `agent-bus` prohibit force pushes and deletion
while active. Normal direct pushes to `main` are reserved by convention for the
nominated reviewer performing the protocol above. Required server checks may
supplement the reviewer's candidate checks, but must not silently replace them
or produce different content.

Shared GitHub credentials may prevent the server from distinguishing agents;
the bus identity, commit trailers, merge receipt, and Git history are the
cooperative audit trail. A future enforcement service may check them without
changing event semantics.

## 10. Scale and delegation

Branches should be reviewable workstreams, not artificial one-commit packages.
The branch nomination permits continuous authoring and incremental reviewer
inspection while preserving a precise commit boundary for each merge.

Large changes should still be split along stable subsystem interfaces. Version
1 gives one eligible reviewer responsibility for each merge. Specialist reviews
may inform that reviewer but do not divide or dilute their responsibility.

A reviewer may use subagents for analysis, but personally owns the judgment and
merge. An unregistered subagent cannot satisfy independent review. Review depth
follows novelty, risk, trust-boundary impact, and blast radius, not a fixed
duration or comment count.

## 11. Disputes and failures

- If no eligible reviewer merges, the work does not enter `main`.
- Another reviewer may be nominated; unresolved critical/high findings require
  explicit disposition.
- A flawed merged change is fixed or reverted through another reviewed branch
  merge.
- If a reviewer resolves a conflict or adds a material fix, another reviewer is
  required for that content.
- If `main` changes during merge, the reviewer retries from the new main; authors
  need act only if the merge no longer stays clean.
- If the reviewer merges but omits `review.merged`, product history remains
  authoritative, but the missing receipt must be repaired before that reviewer
  takes more review work.

## 12. Acceptance fixtures

The helper and workflow must reject:

1. self-nomination or an inactive, unregistered, or non-`reviewer` nominee;
2. merge without accepted nomination for the product branch;
3. reviewer authorship in the selected commit range;
4. incomplete or false author identities;
5. unresolved changes requested or critical/high issues;
6. a candidate that omits current `main` or contains unreviewed side content;
7. a merge requiring conflict resolution;
8. a candidate differing from the one checked;
9. a force push to any protocol branch or an author push to `main`;
10. a merge receipt not matching product Git history; and
11. treating post-selection branch commits as included in the completed merge.

It also rejects product commits attributed to a `reviewer` identity and any
attempt to change an identity's registered role.

Positive fixtures cover one and multiple authors, continued branch pushes during
review, declined nomination followed by a new reviewer, requested changes fixed
without re-nomination, fast-forward merge, clean merge commit after unrelated
`main` advancement, push-race retry, and post-selection commits left for a later
merge.

## 13. Adversarial review questions

1. Can an author manufacture or impersonate a reviewer?
2. Can content enter the selected snapshot without reviewer inspection?
3. Can commits pushed after selection leak into the merge?
4. Does reviewer-authored product content force a different reviewer?
5. Can an unresolved finding be hidden by branch motion?
6. Does a clean Git merge still receive exact-candidate integration checks?
7. Does the rule work when agents share one GitHub credential?
8. Can any “trivial” exception become an unreviewed path?
9. Can a long-lived nomination accidentally approve future content?
10. Does reviewer-owned merging support rapid authors without transferring a
    reusable approval token?

No product content enters `main` until one or more agents author it and a
distinct eligible nominated agent reviews and merges a clean candidate
containing that content.
