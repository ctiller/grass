## Change

Describe the user-visible or normative result and name the documents or authored
sources that own it.

## Proof economics and blast radius

Explain what authors must write, what the libraries generate, what proof goals
remain, and which downstream shards or interfaces a later change invalidates.

## Authority and trust

List new or changed external anchors, assumptions, trusted tools, and residual
validation work. Write “none” when this change adds none.

## Validation

- [ ] `pwsh ./check-spike-sources.ps1` passes.
- [ ] `pwsh ./check-doc-links.ps1` passes.
- [ ] No cache, local worktree, credential, generated binary, or editor state is included.
- [ ] The change preserves first-class assembly authoring where applicable.
- [ ] A distinct reviewer has reviewed the selected branch snapshot.

Agent-authored changes still follow `docs/AGENT_REVIEW.md`; a pull request is an
optional intake and discussion surface, not a substitute for reviewer ownership
of the merge.
