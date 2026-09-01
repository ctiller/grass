# Contributing to Grass

Grass is currently a pre-implementation specification corpus. Contributions
should improve the reviewed architecture, its proof-economics pressure tests,
or the small validation tools around them. The imported `Grass.*` Lean modules
shown in `Spikes/` do not exist yet; the spike files are design fixtures, not a
package that can currently be built.

Start with the [specification corpus index](docs/README.md), which defines
document authority and the meaning of normative language. For spike changes,
also read the [spike authoring contract](docs/SPIKE_AUTHORING.md) and compare
both the annotated document and its comment-free authored source.

## Making a change

1. Keep the precious portable specification minimal. Generated expansions,
   routine adapters, manifests, and bookkeeping do not belong in it.
2. Keep first-class assembly visible and authorable. Helpers may remove proof
   ceremony, but raw instructions and novel implementations must remain legal.
3. State new trust assumptions, external authorities, residual proof goals, and
   invalidation boundaries explicitly.
4. Cite primary vendor, standards-body, or research sources for externally
   defined behavior. Add reusable anchors to `docs/REFERENCES.md`.
5. Do not use `axiom`, `sorry`, `admit`, unsafe proof authority,
   `native_decide`, execution, tests, or digests as substitutes for universal
   proofs. Tests and fuzzers validate models; they do not prove them.
6. Keep caches, local worktrees, credentials, generated binaries, and editor
   state out of commits.

Run the repository's current consistency check from its root:

```powershell
pwsh ./check-spike-sources.ps1
pwsh ./check-doc-links.ps1
```

These check that every spike code block is classified, that each authored Lean
block exactly matches its file under `Spikes/`, and that relative documentation
targets exist. They are not a Lean build or an end-to-end proof check.

## Review

Every product change requires a distinct author and reviewer. Agent-authored
work follows [the agent review protocol](docs/AGENT_REVIEW.md): the author
nominates a reviewer on the coordination bus, and the reviewer merges a named
branch only after it merges cleanly and the review is satisfied. Force-pushes
are prohibited by that protocol.

Public contribution hosting may add pull requests as an intake mechanism, but
a pull request does not replace substantive review. Reviewers should challenge
specification adequacy, proof feasibility, proof economics, assembly freedom,
change blast radius, source authority, and whether the proposed program is one
we would actually ship.

Do not include confidential vulnerability details in an ordinary issue or
review. Follow [SECURITY.md](SECURITY.md) instead.

All project participation is governed by
[the code of conduct](CODE_OF_CONDUCT.md).

## Contribution licensing

Unless explicitly marked otherwise, a contribution intentionally submitted for
inclusion in Grass is provided under the
[Apache License, Version 2.0](LICENSE), as described by section 5 of that
license. Do not submit material that you do not have the right to contribute.
