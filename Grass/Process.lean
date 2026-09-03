import Grass.Process.Acceptance
import Grass.Process.Correct
import Grass.Process.Network.Plan
import Grass.Process.Sequential.Machine

/-!
# The process authoring facade

`docs/DECISIONS.md` decision 134, ruling `c-spike:4`'s third question and
`c-process`'s note on it:

> `Grass.Process` will be a bounded signature-only authoring facade exporting
> the small public vocabulary used by process-author modules, not the Lake root
> and not an aggregate of `Grass/Process/**`.

The spikes write `import Grass.Process`, and until this module existed that line
named nothing. `docs/OLEAN_SHARDING.md` §2 forbids a leaf importing a
whole-program umbrella and forbids an aggregate that imports every leaf, so the
question the ruling settled was not whether to add the module but what shape it
could have.

## What "bounded" can and cannot mean in Lean

It cannot mean hiding. Importing a module makes its whole transitive closure
visible, and `export` does not take anything away — so a facade cannot show an
author less than what it imports. Saying otherwise would be the kind of claim
this repository treats as a defect.

What it *can* mean is that the closure is **small, declared, and checked**. This
file imports four modules and nothing else, so a name outside their closure is
not reachable through it. `Tests/Process/FacadeFixtures.lean` is where that stops
being a promise: it authors a process against this import line alone, and then
guards that seven modules' worth of vocabulary — mailboxes, structural networks,
child bindings, cross-vocabulary delivery, the transition family, commit
coalescing, and cancellation — does *not* resolve. Widening this import list
breaks those guards, which is the point: growing the facade is a visible change
rather than a quiet one.

`Grass.lean`, the Lake root, remains a different thing and still imports
nothing. This module is not it and must not become it.

## What is in, and why

The four imports are the four things a process-author module names, as
`Spikes/4_Web_Server/Process.lean` and its siblings actually write them:

* `Correct` — `ProcessSpec`, and the `ProcessCorrect` record an author
  discharges, together with the run and progress relations it is stated over.
* `Acceptance` — the acceptance predicate a specification consumes.
* `Network.Plan` — `ProcessPlan`, `LogicalProcessNetwork`, and the channel
  contracts a plan installs.
* `Sequential.Machine` — the serial authoring surface, for the majority of
  processes that never mention a channel.

`Grass.Specification.Boundary` arrives through the last of those, and that is
not leakage: `agent-bus` disposition `coord1:5` puts the neutral vocabulary
*below* both Semantics and Process, so a process author naming `DriverBoundary`
is reaching down the diamond rather than across it.

## What is deliberately out

Cancellation is `Grass/Process/Cancellation.lean`, a separate facet, because
decision 134 makes it one and because most process authors never write a
cancellation policy. The rest — mailboxes, escrow ledgers, the structural
network, child bindings, delivery classification, the transition family and the
commit law — is machinery a *realization* consumes, not vocabulary an author
writes, and an author who needs one imports the module that owns it.

This module declares nothing of its own. If a definition ever appears here, it
has stopped being a facade.
-/
